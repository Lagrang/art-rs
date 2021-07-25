use std::borrow::Borrow;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::{cmp, ptr};

pub struct Art<K, V> {
    root: Option<TypedNode<K, V>>,
    phantom: PhantomData<K>,
}

impl<K: Borrow<[u8]> + Eq, V> Art<K, V> {
    pub fn new() -> Self {
        Self {
            root: None,
            phantom: PhantomData {},
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> bool {
        debug_assert!(
            !key.borrow().is_empty(),
            "Key must have non empty byte string representation"
        );

        // create root node if not exists
        if self.root.is_none() {
            self.root = Some(TypedNode::Leaf(Leaf { key, value }));
            true
        } else {
            let mut node = self.root.as_mut().unwrap();
            let mut key = key;
            let key_vec = key.borrow().to_vec();
            let mut key_bytes = key_vec.as_slice();
            let mut val = value;
            loop {
                match Self::try_insert(node, key, key_bytes, val) {
                    Ok(res) => return res,
                    Err((next_node, kb, k, v)) => {
                        node = next_node;
                        key_bytes = kb;
                        key = k;
                        val = v;
                    }
                }
            }
        }
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        debug_assert!(
            !key.borrow().is_empty(),
            "Key must have non empty byte string representation"
        );

        let mut next_node = self.root.as_ref();
        let mut key_bytes = key.borrow();
        while let Some(node) = next_node {
            match node {
                TypedNode::Leaf(leaf) => {
                    return if &leaf.key == key {
                        Some(&leaf.value)
                    } else {
                        None
                    }
                }
                TypedNode::Interim(interim) => {
                    let prefix = interim.prefix();
                    if Self::common_prefix_len(prefix, &key_bytes[..key_bytes.len()])
                        != prefix.len()
                    {
                        // node has prefix which is not prefix of search key
                        return None;
                    } else {
                        if key_bytes.len() == prefix.len() {
                            // prefix of node exactly the same as key => no matches to key
                            // because all keys inside interim node longer at least by 1 byte.
                            return None;
                        }
                        next_node = Self::find_node(interim, key_bytes[prefix.len()]);
                        if key_bytes.len() > prefix.len() + 1 {
                            key_bytes = &key_bytes[prefix.len() + 1..];
                        } else {
                            key_bytes = &[];
                        }
                    }
                }
            }
        }
        None
    }

    fn try_insert<'a, 'k>(
        node_holder: &'a mut TypedNode<K, V>,
        key: K,
        key_bytes: &'k [u8],
        value: V,
    ) -> Result<bool, (&'a mut TypedNode<K, V>, &'k [u8], K, V)> {
        let node_holder_ptr = node_holder as *mut TypedNode<K, V>;
        match node_holder {
            TypedNode::Leaf(leaf) => {
                if key != leaf.key {
                    let leaf_key = leaf.key.borrow();
                    // do not account last byte of keys in prefix computation
                    // because this byte will be used in interim node as pointer to leaf node
                    let prefix_size = Self::common_prefix_len(
                        &leaf_key[..leaf_key.len() - 1],
                        &key_bytes[..key_bytes.len() - 1],
                    );

                    // safely move out value from node holder because
                    // later we will override it without drop
                    let leaf = unsafe { ptr::read(leaf) };
                    let mut new_interim = Node4::new(&leaf_key[0..prefix_size]);
                    let res = new_interim.insert(
                        key_bytes[prefix_size],
                        TypedNode::Leaf(Leaf::new(key, value)),
                    );
                    debug_assert!(res.is_none());
                    let res = new_interim.insert(leaf_key[prefix_size], TypedNode::Leaf(leaf));
                    debug_assert!(res.is_none());

                    let new_interim = TypedNode::Interim(Node::Size4(Box::new(new_interim)));
                    unsafe { ptr::write(node_holder, new_interim) };
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            TypedNode::Interim(interim) => {
                let prefix = interim.prefix();
                let prefix_size =
                    Self::common_prefix_len(&prefix, &key_bytes[..key_bytes.len() - 1]);

                // Node prefix and key has partial common sequence. For instance, node prefix is
                // "abc" and key is "abde", common sequence will be "ab". This sequence will be
                // used as prefix for new interim node and it will point to new leaf(with passed
                // KV) and previous interim(with prefix "abc").
                if prefix_size < prefix.len() {
                    let mut new_interim = Node4::new(&prefix[0..prefix_size]);
                    new_interim.insert(
                        key_bytes[prefix_size],
                        TypedNode::Leaf(Leaf::new(key, value)),
                    );
                    let mut interim = unsafe { ptr::read(interim) };
                    // update prefix of existing interim to remaining part of old prefix.
                    // e.g., prefix was "abcd", prefix of new node is "ab".
                    // Updated prefix will be "d" because "c" used as pointer inside new interim.
                    if prefix_size + 1 < prefix.len() {
                        interim.set_prefix(&prefix[prefix_size + 1..]);
                    }
                    new_interim.insert(prefix[prefix_size], TypedNode::Interim(interim));
                    unsafe {
                        ptr::write(
                            node_holder_ptr,
                            TypedNode::Interim(Node::Size4(Box::new(new_interim))),
                        )
                    };
                    return Ok(true);
                }

                let interim_ptr = unsafe { &mut *(interim as *mut Node<TypedNode<K, V>>) };
                if let Some(next_node) = Self::find_node_mut(interim, key_bytes[prefix_size]) {
                    // go to the next level of tree
                    Err((next_node, &key_bytes[prefix_size + 1..], key, value))
                } else {
                    // we find interim node which should contain new KV
                    let leaf = TypedNode::Leaf(Leaf::new(key, value));
                    match interim_ptr.insert(key_bytes[prefix_size], leaf) {
                        Some(InsertError::Overflow(val)) => {
                            let interim = unsafe { ptr::read(interim_ptr) };
                            let mut new_interim = interim.expand();
                            let res = new_interim.insert(key_bytes[prefix_size], val);
                            debug_assert!(
                                res.is_none(),
                                "Insert failed after node expand (unexpected duplicate key)"
                            );
                            unsafe { ptr::write(node_holder_ptr, TypedNode::Interim(new_interim)) }
                            Ok(true)
                        }
                        Some(InsertError::DuplicateKey) => Ok(false),
                        None => Ok(true),
                    }
                }
            }
        }
    }

    fn find_node<T>(node: &Node<T>, key: u8) -> Option<&T> {
        match node {
            Node::Size4(node) => node.get(key),
            Node::Size16(node) => node.get(key),
            Node::Size48(node) => node.get(key),
            Node::Size256(node) => node.get(key),
        }
    }

    fn find_node_mut<T>(node: &mut Node<T>, key: u8) -> Option<&mut T> {
        match node {
            Node::Size4(node) => node.get_mut(key),
            Node::Size16(node) => node.get_mut(key),
            Node::Size48(node) => node.get_mut(key),
            Node::Size256(node) => node.get_mut(key),
        }
    }

    fn common_prefix_len(prefix: &[u8], key: &[u8]) -> usize {
        let mut len = 0;
        for i in 0..cmp::min(prefix.len(), key.len()) {
            len += 1;
            if prefix[i] != key[i] {
                break;
            }
        }
        len
    }
}

enum TypedNode<K, V> {
    Interim(Node<TypedNode<K, V>>),
    Leaf(Leaf<K, V>),
}

struct Leaf<K, V> {
    key: K,
    value: V,
}

impl<K, V> Leaf<K, V> {
    fn new(key: K, value: V) -> Self {
        Self { key, value }
    }
}

enum Node<V> {
    Size4(Box<Node4<V>>),
    Size16(Box<Node16<V>>),
    Size48(Box<Node48<V>>),
    Size256(Box<Node256<V>>),
}

impl<V> Node<V> {
    fn prefix(&self) -> &[u8] {
        match self {
            Node::Size4(node) => &node.prefix,
            Node::Size16(node) => &node.prefix,
            Node::Size48(node) => &node.prefix,
            Node::Size256(node) => &node.prefix,
        }
    }

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        match self {
            Node::Size4(node) => node.insert(key, value),
            Node::Size16(node) => node.insert(key, value),
            Node::Size48(node) => node.insert(key, value),
            Node::Size256(node) => node.insert(key, value),
        }
    }

    fn set_prefix(&mut self, prefix: &[u8]) {
        match self {
            Node::Size4(node) => node.prefix = prefix.to_vec(),
            Node::Size16(node) => node.prefix = prefix.to_vec(),
            Node::Size48(node) => node.prefix = prefix.to_vec(),
            Node::Size256(node) => node.prefix = prefix.to_vec(),
        }
    }

    fn expand(mut self) -> Node<V> {
        match self {
            Node::Size4(node) => Node::Size16(Box::new(node.expand())),
            Node::Size16(node) => Node::Size48(Box::new(node.expand())),
            Node::Size48(node) => Node::Size256(Box::new(node.expand())),
            Node::Size256(_) => return self,
        }
    }
}

struct Node4<V> {
    prefix: Vec<u8>,
    len: usize,
    keys: [u8; 4],
    values: [MaybeUninit<V>; 4],
}

impl<V> Node4<V> {
    fn new(prefix: &[u8]) -> Self {
        let vals: MaybeUninit<[MaybeUninit<V>; 4]> = MaybeUninit::uninit();
        Self {
            prefix: prefix.to_vec(),
            len: 0,
            keys: [0; 4],
            values: unsafe { vals.assume_init() },
        }
    }

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        self.keys[..self.len].binary_search(&key).map_or_else(
            |i| {
                if self.len >= self.keys.len() {
                    return Some(InsertError::Overflow(value));
                }

                // shift array elements to right side to get free space for insert
                unsafe {
                    ptr::copy(
                        self.keys[i..].as_ptr(),
                        self.keys[i + 1..].as_mut_ptr(),
                        self.len - i,
                    );
                    ptr::copy(
                        self.values[i..].as_ptr(),
                        self.values[i + 1..].as_mut_ptr(),
                        self.len - i,
                    );
                }
                self.len += 1;
                self.keys[i] = key;
                self.values[i] = MaybeUninit::new(value);
                None
            },
            |_| Some(InsertError::DuplicateKey),
        )
    }

    fn expand(self) -> Node16<V> {
        let mut new_node = Node16::new(&self.prefix);
        new_node.len = self.len;
        // TODO: use simd
        new_node.keys[..self.len].copy_from_slice(&self.keys[..self.len]);
        unsafe {
            ptr::copy_nonoverlapping(
                self.values[..self.len].as_ptr(),
                new_node.values[..self.len].as_mut_ptr(),
                self.len,
            );
        };

        new_node
    }

    fn get(&self, key: u8) -> Option<&V> {
        // TODO: use simd
        for (i, k) in self.keys[..self.len].iter().enumerate() {
            if *k == key {
                unsafe {
                    return Some(&*self.values[i].as_ptr());
                }
            }
        }
        None
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        // TODO: use simd
        for (i, k) in self.keys[..self.len].iter().enumerate() {
            if *k == key {
                unsafe {
                    return Some(&mut *self.values[i].as_mut_ptr());
                }
            }
        }
        None
    }
}

struct Node16<V> {
    prefix: Vec<u8>,
    len: usize,
    keys: [u8; 16],
    values: [MaybeUninit<V>; 16],
}

impl<V> Node16<V> {
    fn new(prefix: &[u8]) -> Self {
        let vals: MaybeUninit<[MaybeUninit<V>; 16]> = MaybeUninit::uninit();
        Self {
            prefix: prefix.to_vec(),
            len: 0,
            keys: [0; 16],
            values: unsafe { vals.assume_init() },
        }
    }

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        // TODO: replace binary search with SIMD seq scan
        self.keys[..self.len].binary_search(&key).map_or_else(
            |i| {
                if self.len >= self.keys.len() {
                    return Some(InsertError::Overflow(value));
                }
                // shift array elements to right side to get free space for insert
                unsafe {
                    ptr::copy(
                        self.keys[i..].as_ptr(),
                        self.keys[i + 1..].as_mut_ptr(),
                        self.len - i,
                    );
                    ptr::copy(
                        self.values[i..].as_ptr(),
                        self.values[i + 1..].as_mut_ptr(),
                        self.len - i,
                    );
                }
                self.len += 1;
                self.keys[i] = key;
                self.values[i] = MaybeUninit::new(value);
                None
            },
            |_| Some(InsertError::DuplicateKey),
        )
    }

    fn expand(self) -> Node48<V> {
        let mut new_node = Node48::new(&self.prefix);
        for (i, key) in self.keys[..self.len].iter().enumerate() {
            let val = unsafe { ptr::read(&self.values[i]).assume_init() };
            let res = new_node.insert(*key, val);
            debug_assert!(res.is_none());
        }
        new_node
    }

    fn get(&self, key: u8) -> Option<&V> {
        // TODO: use simd
        for (i, k) in self.keys[..self.len].iter().enumerate() {
            if *k == key {
                unsafe {
                    return Some(&*self.values[i].as_ptr());
                }
            }
        }
        None
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        // TODO: use simd
        for (i, k) in self.keys[..self.len].iter().enumerate() {
            if *k == key {
                unsafe {
                    return Some(&mut *self.values[i].as_mut_ptr());
                }
            }
        }
        None
    }
}

struct Node48<V> {
    prefix: Vec<u8>,
    len: usize,
    keys: [u8; 256],
    values: [MaybeUninit<V>; 48],
}

impl<V> Node48<V> {
    fn new(prefix: &[u8]) -> Self {
        let vals: MaybeUninit<[MaybeUninit<V>; 48]> = MaybeUninit::uninit();
        Self {
            prefix: prefix.to_vec(),
            len: 0,
            keys: [0; 256],
            values: unsafe { vals.assume_init() },
        }
    }

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        let i = key as usize;
        if self.keys[i] != 0 {
            return Some(InsertError::DuplicateKey);
        }
        if self.len >= 48 {
            return Some(InsertError::Overflow(value));
        }

        self.values[self.len as usize] = MaybeUninit::new(value);
        self.len += 1;
        self.keys[i] = self.len as u8;
        None
    }

    fn expand(self) -> Node256<V> {
        let mut new_node = Node256::new(&self.prefix);
        for (i, key) in self.keys.iter().enumerate() {
            if *key > 0 {
                let val = unsafe { ptr::read(&self.values[*key as usize]).assume_init() };
                let res = new_node.insert(i as u8, val);
                debug_assert!(res.is_none());
            }
        }
        new_node
    }

    fn get(&self, key: u8) -> Option<&V> {
        let i = self.keys[key as usize] as usize;
        if i > 0 {
            unsafe {
                return Some(&*self.values[i].as_ptr());
            }
        }
        None
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        let i = self.keys[key as usize] as usize;
        if i > 0 {
            unsafe {
                return Some(&mut *self.values[i].as_mut_ptr());
            }
        }
        None
    }
}

struct Node256<V> {
    prefix: Vec<u8>,
    values: [Option<V>; 256],
}

impl<V> Node256<V> {
    #[allow(clippy::uninit_assumed_init)]
    fn new(prefix: &[u8]) -> Self {
        let mut values: [Option<V>; 256] =
            unsafe { MaybeUninit::<[Option<V>; 256]>::uninit().assume_init() };
        values.fill_with(|| None);
        Self {
            prefix: prefix.to_vec(),
            values,
        }
    }

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        let i = key as usize;
        if self.values[i].is_none() {
            self.values[i] = Some(value);
            None
        } else {
            Some(InsertError::DuplicateKey)
        }
    }

    fn get(&self, key: u8) -> Option<&V> {
        return self.values[key as usize].as_ref();
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        return self.values[key as usize].as_mut();
    }
}

enum InsertError<V> {
    DuplicateKey,
    Overflow(V),
}

#[cfg(test)]
mod tests {
    use crate::Node4;

    #[test]
    fn test() {
        let prefix = vec![0u8, 1u8];
        let mut node4 = Node4::new(prefix.as_slice());
        node4.insert(3, 3);
        node4.insert(1, 1);
        node4.insert(2, 2);
        let node16 = node4.expand();
        assert_eq!(node16.len, 3);
        assert_eq!(prefix, node16.prefix);
        assert_eq!(&node16.keys[0..node16.len], &[1, 2, 3]);
        unsafe {
            assert_eq!(1, node16.values[0].assume_init());
            assert_eq!(2, node16.values[1].assume_init());
            assert_eq!(3, node16.values[2].assume_init());
        }
    }
}
