use std::borrow::Borrow;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::{cmp, ptr};

struct Art<K, V> {
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
        let mut key_bytes = key.borrow();
        assert!(
            key_bytes.len() > 0,
            "Key must have non empty byte string representation"
        );

        // create root node if not exists
        if self.root.is_none() {
            self.root = Some(TypedNode::Leaf(Leaf { key, value }));
            return true;
        } else {
            let mut node = &mut self.root.unwrap();
            let mut val = value;
            loop {
                match Self::insert_to_node(node, key, key_bytes, val) {
                    Ok(res) => return res,
                    Err((next_node, key, v)) => {
                        node = next_node;
                        key_bytes = key;
                        val = v;
                    }
                }
            }
        }
    }

    fn insert_to_node<'a, 'k>(
        node_holder: &'a mut TypedNode<K, V>,
        key: K,
        key_bytes: &'k [u8],
        value: V,
    ) -> Result<bool, (&'a mut TypedNode<K, V>, &'k [u8], V)> {
        match node_holder {
            TypedNode::Leaf(leaf) => {
                if key != leaf.key {
                    let leaf_key = leaf.key.borrow();
                    // do not account last byte of keys in prefix computation
                    // because this byte will be used in interim node as pointer to leaf node
                    let mut prefix_size = Self::common_prefix_len(
                        &leaf_key[..leaf_key.len() - 1],
                        &key_bytes[..key_bytes.len() - 1],
                    );

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
                let mut prefix_size =
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
                            node_holder,
                            TypedNode::Interim(Node::Size4(Box::new(new_interim))),
                        )
                    };
                    return Ok(true);
                }

                if let Some(next_node) = Self::find_node(interim, key_bytes[prefix_size]) {
                    // go to the next level of tree
                    Err((next_node, &key_bytes[prefix_size + 1..], value))
                } else {
                    let leaf = TypedNode::Leaf(Leaf::new(key, value));
                    match interim.insert(key_bytes[prefix_size], leaf) {
                        Some(InsertError::Overflow) => {
                            let mut interim = unsafe { ptr::read(interim) };
                            let mut new_interim = interim.expand();
                            let res = new_interim.insert(prefix[prefix_size], leaf);
                            debug_assert!(
                                res.is_none(),
                                "Insert failed after node expand (unexpected duplicate key)"
                            );
                            unsafe { ptr::write(node_holder, TypedNode::Interim(new_interim)) }
                            Ok(true)
                        }
                        Some(InsertError::DuplicateKey) => Ok(false),
                        None => Ok(true),
                    }
                }
            }
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

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError> {
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

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError> {
        self.keys[..self.len].binary_search(&key).map_or_else(
            |i| {
                if self.len >= self.keys.len() {
                    return Some(InsertError::Overflow);
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

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError> {
        // TODO: replace binary search with SIMD seq scan
        self.keys[..self.len].binary_search(&key).map_or_else(
            |i| {
                if self.len >= self.keys.len() {
                    return Some(InsertError::Overflow);
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
            unsafe {
                let res = new_node.insert(*key, self.values[i].assume_init());
                debug_assert!(res.is_none());
            }
        }
        new_node
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

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError> {
        let i = key as usize;
        if self.keys[i] != 0 {
            return Some(InsertError::DuplicateKey);
        }
        if self.len >= 48 {
            return Some(InsertError::Overflow);
        }

        self.values[self.len as usize] = MaybeUninit::new(value);
        self.len += 1;
        self.keys[i] = self.len as u8;
        None
    }

    fn expand(self) -> Node256<V> {
        let mut new_node = Node256::new(&self.prefix);
        for (i, key) in self.keys.iter().enumerate() {
            if *key == 0 {
                continue;
            }
            unsafe {
                let res = new_node.insert(i as u8, self.values[*key as usize].assume_init());
                debug_assert!(res.is_none());
            }
        }
        new_node
    }
}

struct Node256<V> {
    prefix: Vec<u8>,
    values: [Option<V>; 256],
}

impl<V> Node256<V> {
    fn new(prefix: &[u8]) -> Self {
        Self {
            prefix: prefix.to_vec(),
            values: [None; 256],
        }
    }

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError> {
        let i = key as usize;
        if self.values[i].is_none() {
            self.values[i] = Some(value);
            None
        } else {
            Some(InsertError::DuplicateKey)
        }
    }
}

enum InsertError {
    DuplicateKey,
    Overflow,
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
