pub mod keys;

use std::mem::MaybeUninit;
use std::option::Option::Some;
use std::{cmp, mem, ptr};

pub struct Art<K, V> {
    root: Option<TypedNode<K, V>>,
}

/// Trait represent [Art] key.
/// Trait define method which convert key into byte comparable sequence. This sequence will be
/// used to order keys inside tree. [Art] crate has several implementation of [Key] trait inside
/// `keys` module.
pub trait Key: Eq {
    fn to_bytes(&self) -> Vec<u8>;
}

impl<K: Key, V> Default for Art<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Key, V> Art<K, V> {
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn insert(&mut self, key: K, value: V) -> bool {
        let key_bytes = key.to_bytes();
        assert!(
            !key_bytes.is_empty(),
            "Key must have non empty byte string representation"
        );

        // create root node if not exists
        if let Some(root) = &mut self.root {
            let mut node = root;
            let mut key = key;
            let mut offset = 0;
            let mut val = value;
            loop {
                let res = match node {
                    TypedNode::Leaf(_) => {
                        Ok(Self::replace_leaf(node, key, val, &key_bytes, offset))
                    }
                    TypedNode::Combined(interim, _) => {
                        if key_bytes.is_empty() {
                            // no more key bytes left for this tree level. Combined node already
                            // contains leaf node for the same key.
                            Ok(false)
                        } else {
                            Err((interim.as_mut(), offset, key, val))
                        }
                    }
                    TypedNode::Interim(_) => {
                        Self::interim_insert(node, key, val, &key_bytes, offset)
                    }
                };
                match res {
                    Ok(is_inserted) => return is_inserted,
                    Err((next_node, i, k, v)) => {
                        node = next_node;
                        offset = i;
                        key = k;
                        val = v;
                    }
                }
            }
        } else {
            self.root = Some(TypedNode::Leaf(Leaf { key, value }));
            true
        }
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        if let Some(root) = &mut self.root {
            let key_bytes_vec = key.to_bytes();
            let mut key_bytes = key_bytes_vec.as_slice();
            let mut parent_link = 0;
            let mut parent: Option<&mut Node<TypedNode<K, V>>> = None;
            let mut node_ptr = root as *mut TypedNode<K, V>;
            loop {
                match unsafe { &mut *node_ptr } {
                    TypedNode::Leaf(leaf) => {
                        // TODO: merge nodes if parent contains only link to child node
                        return if key == &leaf.key {
                            if let Some(p) = parent {
                                if p.should_shrink() {
                                    unsafe {
                                        let new_node = ptr::read(p).shrink();
                                        ptr::write(p, new_node);
                                    };
                                }
                                Some(p.remove(parent_link).unwrap().take_leaf().value)
                            } else {
                                Some(
                                    mem::replace(&mut self.root, None)
                                        .unwrap()
                                        .take_leaf()
                                        .value,
                                )
                            }
                        } else {
                            None
                        };
                    }
                    TypedNode::Interim(interim) => {
                        if let Some((next_node, rem_key_bytes, key)) =
                            Self::find_in_interim_mut(interim, key_bytes)
                        {
                            node_ptr = next_node as *mut TypedNode<K, V>;
                            parent = Some(interim);
                            parent_link = key;
                            key_bytes = rem_key_bytes;
                        } else {
                            return None;
                        }
                    }
                    TypedNode::Combined(interim, leaf) => {
                        if key == &leaf.key {
                            let leaf = unsafe { ptr::read(leaf) };
                            unsafe { ptr::write(node_ptr, *ptr::read(interim)) };
                            return Some(leaf.value);
                        } else {
                            node_ptr = interim.as_mut() as *mut TypedNode<K, V>;
                        }
                    }
                }
            }
        } else {
            None
        }
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let key_vec = key.to_bytes();
        assert!(
            !key_vec.is_empty(),
            "Key must have non empty byte string representation"
        );

        let mut node = self.root.as_ref();
        let mut key_bytes = key_vec.as_slice();
        while let Some(typed_node) = node {
            match typed_node {
                TypedNode::Leaf(leaf) => {
                    return if &leaf.key == key {
                        Some(&leaf.value)
                    } else {
                        None
                    }
                }
                TypedNode::Interim(interim) => {
                    if let Some((next_node, rem_key_bytes, _)) =
                        Self::find_in_interim(interim, key_bytes)
                    {
                        node = Some(next_node);
                        key_bytes = rem_key_bytes;
                    } else {
                        node = None;
                    }
                }
                TypedNode::Combined(interim, leaf) => {
                    if key == &leaf.key {
                        return Some(&leaf.value);
                    } else {
                        node = Some(interim);
                    }
                }
            }
        }
        None
    }

    fn find_in_interim<'k, 'n>(
        interim: &'n Node<TypedNode<K, V>>,
        key_bytes: &'k [u8],
    ) -> Option<(&'n TypedNode<K, V>, &'k [u8], u8)> {
        let node = unsafe {
            #[allow(clippy::cast_ref_to_mut)]
            &mut *(interim as *const Node<TypedNode<K, V>> as *mut Node<TypedNode<K, V>>)
        };
        Self::find_in_interim_mut(node, key_bytes)
            .map(|(node, bytes, key)| (unsafe { &*(node as *const TypedNode<K, V>) }, bytes, key))
    }

    fn find_in_interim_mut<'k, 'n>(
        interim: &'n mut Node<TypedNode<K, V>>,
        key_bytes: &'k [u8],
    ) -> Option<(&'n mut TypedNode<K, V>, &'k [u8], u8)> {
        let prefix = interim.prefix().to_vec();
        if key_bytes.len() == prefix.len() || common_prefix_len(&prefix, key_bytes) != prefix.len()
        {
            // prefix of node exactly the same as key => no matches to key
            // because all keys inside interim node longer at least by 1 byte
            // or
            // node has prefix which is not prefix of search key.
            None
        } else {
            // we have a prefix match, now try to find next byte of key which follows immediately
            // after prefix.
            interim.get_mut(key_bytes[prefix.len()]).map(|node| {
                let key_in_parent = key_bytes[prefix.len()];
                let key_bytes = if key_bytes.len() > prefix.len() + 1 {
                    &key_bytes[prefix.len() + 1..]
                } else {
                    &[]
                };
                (node, key_bytes, key_in_parent)
            })
        }
    }

    fn replace_leaf(
        node: &mut TypedNode<K, V>,
        key: K,
        value: V,
        key_bytes: &[u8],
        key_start_offset: usize,
    ) -> bool {
        let leaf = node.as_leaf_mut();
        if key == leaf.key {
            return false;
        }

        let leaf_key_bytes = leaf.key.to_bytes();
        let leaf_key = &leaf_key_bytes[key_start_offset..];
        let key_bytes = &key_bytes[key_start_offset..];

        let prefix_size = common_prefix_len(leaf_key, key_bytes);

        let prefix = &leaf_key[..prefix_size];
        let leaf_key = &leaf_key[prefix_size..];
        let key_bytes = &key_bytes[prefix_size..];

        let new_interim = if leaf_key.is_empty() {
            // existing leaf key is shorter than new key.
            let mut new_interim = Node4::new(prefix);
            // safely move out value from node holder because
            // later we will override it without drop
            let err = new_interim.insert(key_bytes[0], TypedNode::Leaf(Leaf::new(key, value)));
            debug_assert!(err.is_none());

            let existing_leaf = unsafe { ptr::read(leaf) };
            TypedNode::Combined(
                Box::new(TypedNode::Interim(Node::Size4(Box::new(new_interim)))),
                existing_leaf,
            )
        } else if key_bytes.is_empty() {
            // no more bytes left in key of new KV => create combined node which will
            // point to new key and existing leaf will be moved into new interim node.
            // in this case, key of existing leaf is always longer(length in bytes) than new
            // key(if leaf key has the same length as new key, then keys are equal).
            let mut new_interim = Node4::new(prefix);
            // safely move out value from node holder because
            // later we will override it without drop
            let existing_leaf = unsafe { ptr::read(leaf) };
            let err = new_interim.insert(leaf_key[0], TypedNode::Leaf(existing_leaf));
            debug_assert!(err.is_none());

            TypedNode::Combined(
                Box::new(TypedNode::Interim(Node::Size4(Box::new(new_interim)))),
                Leaf::new(key, value),
            )
        } else {
            // safely move out value from node holder because
            // later we will override it without drop
            let leaf = unsafe { ptr::read(leaf) };
            let mut new_interim = Node4::new(prefix);
            let err = new_interim.insert(key_bytes[0], TypedNode::Leaf(Leaf::new(key, value)));
            debug_assert!(err.is_none());
            let err = new_interim.insert(leaf_key[0], TypedNode::Leaf(leaf));
            debug_assert!(err.is_none());
            TypedNode::Interim(Node::Size4(Box::new(new_interim)))
        };
        unsafe { ptr::write(node, new_interim) };
        true
    }

    fn interim_insert<'n, 'k>(
        node: &'n mut TypedNode<K, V>,
        key: K,
        value: V,
        key_bytes: &'k [u8],
        key_start_offset: usize,
    ) -> Result<bool, (&'n mut TypedNode<K, V>, usize, K, V)> {
        let node_ptr = node as *mut TypedNode<K, V>;
        let interim = node.as_interim_mut();
        if key_bytes.len() <= key_start_offset {
            // no more bytes in key to go deeper inside the tree => replace interim by combined node
            // which will contains link to existing interim and leaf node with new KV.
            unsafe {
                let interim = ptr::read(interim);
                ptr::write(
                    node_ptr,
                    TypedNode::Combined(
                        Box::new(TypedNode::Interim(interim)),
                        Leaf::new(key, value),
                    ),
                )
            }
            return Ok(true);
        }

        let key_bytes = &key_bytes[key_start_offset..];
        let prefix = interim.prefix();
        let prefix_size = common_prefix_len(prefix, key_bytes);

        if prefix_size == key_bytes.len() {
            // existing interim prefix fully equals to new key: replace existing interim by combined
            // node which will contain new key and link to existing values of interim
            unsafe {
                let interim = ptr::read(interim);
                ptr::write(
                    node_ptr,
                    TypedNode::Combined(
                        Box::new(TypedNode::Interim(interim)),
                        Leaf::new(key, value),
                    ),
                )
            };
            Ok(true)
        } else if prefix_size < prefix.len() {
            // Node prefix and key has common byte sequence. For instance, node prefix is
            // "abc" and key is "abde", common sequence will be "ab". This sequence will be
            // used as prefix for new interim node and this interim will point to new leaf(with passed
            // KV) and previous interim(with prefix "abc").
            let mut new_interim = Node4::new(&prefix[..prefix_size]);
            let res = new_interim.insert(
                key_bytes[prefix_size],
                TypedNode::Leaf(Leaf::new(key, value)),
            );
            debug_assert!(res.is_none());
            let mut interim = unsafe { ptr::read(interim) };
            let interim_key = prefix[prefix_size];
            // update prefix of existing interim to remaining part of old prefix.
            // e.g, prefix was "abcd", prefix of new node is "ab".
            // Updated prefix will be "d" because "c" used as pointer inside new interim.
            if prefix_size + 1 < prefix.len() {
                interim.set_prefix(&prefix[prefix_size + 1..]);
            } else {
                interim.set_prefix(&[]);
            }
            let res = new_interim.insert(interim_key, TypedNode::Interim(interim));
            debug_assert!(res.is_none());
            unsafe {
                ptr::write(
                    node_ptr,
                    TypedNode::Interim(Node::Size4(Box::new(new_interim))),
                )
            };
            Ok(true)
        } else {
            let interim_ptr = unsafe { &mut *(interim as *mut Node<TypedNode<K, V>>) };
            if let Some(next_node) = interim.get_mut(key_bytes[prefix_size]) {
                // try to insert on the next level of tree
                Err((next_node, key_start_offset + prefix_size + 1, key, value))
            } else {
                // we find interim node which should contain new KV
                let leaf = TypedNode::Leaf(Leaf::new(key, value));
                match interim_ptr.insert(key_bytes[prefix_size], leaf) {
                    Some(InsertError::Overflow(val)) => {
                        let interim = unsafe { ptr::read(interim_ptr) };
                        let mut new_interim = interim.expand();
                        let err = new_interim.insert(key_bytes[prefix_size], val);
                        debug_assert!(
                            err.is_none(),
                            "Insert failed after node expand (unexpected duplicate key)"
                        );
                        unsafe { ptr::write(node_ptr, TypedNode::Interim(new_interim)) }
                        Ok(true)
                    }
                    Some(InsertError::DuplicateKey) => panic!("Should not happen"),
                    None => Ok(true),
                }
            }
        }
    }
}

fn common_prefix_len(prefix: &[u8], key: &[u8]) -> usize {
    let mut len = 0;
    for i in 0..cmp::min(prefix.len(), key.len()) {
        if prefix[i] != key[i] {
            break;
        }
        len += 1;
    }
    len
}

enum TypedNode<K, V> {
    /// Interim node contains links to leaf and interim nodes on next level of tree.
    Interim(Node<TypedNode<K, V>>),
    /// Leaf node inside Art contains 1 key value pair.
    Leaf(Leaf<K, V>),
    /// Node which contains leaf and interim pointers at the same time.
    /// This can happen when last byte of leaf key is same as byte which points to interim.
    /// For instance, we have root with prefix "a" which points to interim node using byte
    /// representations of char "b". Such interim will point to keys like "abc", "abb", "aba", etc.
    /// Now we try to insert new key "ab" to the tree. Root node has same prefix as key(i.e, "a")
    /// and hence we try to insert leaf node as root child. Because root already have pointer "b"
    /// to existing interim, we can't simply insert our key into tree. We should "enhance" interim
    /// node by new key by replacing interim node by special combined node.
    Combined(Box<TypedNode<K, V>>, Leaf<K, V>),
}

impl<K, V> TypedNode<K, V> {
    fn as_leaf_mut(&mut self) -> &mut Leaf<K, V> {
        match self {
            TypedNode::Leaf(node) => node,
            _ => panic!("Only leaf can be retrieved"),
        }
    }

    fn take_leaf(self) -> Leaf<K, V> {
        match self {
            TypedNode::Leaf(node) => node,
            _ => panic!("Only leaf can be retrieved"),
        }
    }

    fn as_interim_mut(&mut self) -> &mut Node<TypedNode<K, V>> {
        match self {
            TypedNode::Interim(node) => node,
            _ => panic!("Only interim can be retrieved"),
        }
    }

    fn as_interim(&self) -> &Node<TypedNode<K, V>> {
        match self {
            TypedNode::Interim(node) => node,
            _ => panic!("Only interim can be retrieved"),
        }
    }
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

    fn remove(&mut self, key: u8) -> Option<V> {
        match self {
            Node::Size4(node) => node.remove(key),
            Node::Size16(node) => node.remove(key),
            Node::Size48(node) => node.remove(key),
            Node::Size256(node) => node.remove(key),
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

    fn expand(self) -> Node<V> {
        match self {
            Node::Size4(node) => Node::Size16(Box::new(node.expand())),
            Node::Size16(node) => Node::Size48(Box::new(node.expand())),
            Node::Size48(node) => Node::Size256(Box::new(node.expand())),
            Node::Size256(_) => self,
        }
    }

    fn should_shrink(&self) -> bool {
        match self {
            Node::Size4(_) => false,
            Node::Size16(node) => node.len <= 4,
            Node::Size48(node) => node.len <= 16,
            Node::Size256(node) => node.len <= 48,
        }
    }

    fn shrink(self) -> Node<V> {
        match self {
            Node::Size4(_) => self,
            Node::Size16(node) => Node::Size4(Box::new(node.shrink())),
            Node::Size48(node) => Node::Size16(Box::new(node.shrink())),
            Node::Size256(node) => Node::Size48(Box::new(node.shrink())),
        }
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        match self {
            Node::Size4(node) => node.get_mut(key),
            Node::Size16(node) => node.get_mut(key),
            Node::Size48(node) => node.get_mut(key),
            Node::Size256(node) => node.get_mut(key),
        }
    }

    fn get(&self, key: u8) -> Option<&V> {
        match self {
            Node::Size4(node) => node.get(key),
            Node::Size16(node) => node.get(key),
            Node::Size48(node) => node.get(key),
            Node::Size256(node) => node.get(key),
        }
    }
}

struct Node4<V> {
    prefix: Vec<u8>,
    len: usize,
    keys: [u8; 4],
    values: [MaybeUninit<V>; 4],
}

impl<V> Drop for Node4<V> {
    fn drop(&mut self) {
        for value in &self.values[..self.len] {
            unsafe {
                ptr::read(value.as_ptr());
            }
        }
    }
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
                self.keys[i] = key;
                self.values[i] = MaybeUninit::new(value);
                self.len += 1;
                None
            },
            |_| Some(InsertError::DuplicateKey),
        )
    }

    fn remove(&mut self, key: u8) -> Option<V> {
        self.keys[..self.len].binary_search(&key).map_or_else(
            |_| None,
            |i| {
                let val = unsafe {
                    mem::replace(&mut self.values[i], MaybeUninit::uninit()).assume_init()
                };
                self.len -= 1;
                if self.len > 0 {
                    // shift array elements to left side to compact value space
                    unsafe {
                        ptr::copy(
                            self.keys[i + 1..].as_ptr(),
                            self.keys[i..].as_mut_ptr(),
                            self.len - i,
                        );
                        ptr::copy(
                            self.values[i + 1..].as_ptr(),
                            self.values[i..].as_mut_ptr(),
                            self.len - i,
                        );
                    }
                }
                Some(val)
            },
        )
    }

    fn expand(mut self) -> Node16<V> {
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

        // emulate that all values was moved out from node before drop
        self.len = 0;
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

impl<V> Drop for Node16<V> {
    fn drop(&mut self) {
        for value in &self.values[..self.len] {
            unsafe {
                ptr::read(value.as_ptr());
            }
        }
    }
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
                self.keys[i] = key;
                self.values[i] = MaybeUninit::new(value);
                self.len += 1;
                None
            },
            |_| Some(InsertError::DuplicateKey),
        )
    }

    fn remove(&mut self, key: u8) -> Option<V> {
        self.keys[..self.len].binary_search(&key).map_or_else(
            |_| None,
            |i| {
                let val = unsafe {
                    mem::replace(&mut self.values[i], MaybeUninit::uninit()).assume_init()
                };
                self.len -= 1;
                if self.len > 0 {
                    // shift array elements to left side to compact value space
                    unsafe {
                        ptr::copy(
                            self.keys[i + 1..].as_ptr(),
                            self.keys[i..].as_mut_ptr(),
                            self.len - i,
                        );
                        ptr::copy(
                            self.values[i + 1..].as_ptr(),
                            self.values[i..].as_mut_ptr(),
                            self.len - i,
                        );
                    }
                }
                Some(val)
            },
        )
    }

    fn expand(mut self) -> Node48<V> {
        let mut new_node = Node48::new(&self.prefix);
        for (i, key) in self.keys[..self.len].iter().enumerate() {
            let val = unsafe { ptr::read(&self.values[i]).assume_init() };
            let res = new_node.insert(*key, val);
            debug_assert!(res.is_none());
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
        new_node
    }

    fn shrink(mut self) -> Node4<V> {
        debug_assert!(self.len <= 4);
        let mut new_node = Node4::new(&self.prefix);
        for (i, key) in self.keys[..self.len].iter().enumerate() {
            let val = unsafe { ptr::read(&self.values[i]).assume_init() };
            let res = new_node.insert(*key, val);
            debug_assert!(res.is_none());
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
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

impl<V> Drop for Node48<V> {
    fn drop(&mut self) {
        for value in &self.values[..self.len] {
            unsafe {
                ptr::read(value.as_ptr());
            }
        }
    }
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
        self.keys[i] = self.len as u8 + 1;
        self.len += 1;
        None
    }

    fn remove(&mut self, key: u8) -> Option<V> {
        let key_idx = key as usize;
        if self.keys[key_idx] == 0 {
            return None;
        }
        let val_idx = self.keys[key_idx] as usize - 1;
        let val =
            unsafe { mem::replace(&mut self.values[val_idx], MaybeUninit::uninit()).assume_init() };
        self.keys[key_idx] = 0;
        // TODO: replace by SIMD search
        for i in 0..self.keys.len() {
            // find key which uses last cell inside values array
            if self.keys[i] == self.len as u8 {
                // move value of key which points to last array cell
                self.keys[i] = val_idx as u8 + 1;
                self.values[val_idx] =
                    mem::replace(&mut self.values[self.len - 1], MaybeUninit::uninit());
                break;
            }
        }
        self.len -= 1;
        Some(val)
    }

    fn expand(mut self) -> Node256<V> {
        let mut new_node = Node256::new(&self.prefix);
        for (key, i) in self.keys.iter().enumerate() {
            let val_idx = *i as usize;
            if val_idx > 0 {
                let val = unsafe { ptr::read(&self.values[val_idx - 1]).assume_init() };
                let err = new_node.insert(key as u8, val);
                debug_assert!(err.is_none());
            }
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
        new_node
    }

    fn shrink(mut self) -> Node16<V> {
        debug_assert!(self.len <= 16);
        let mut new_node = Node16::new(&self.prefix);
        for (i, key) in self.keys.iter().enumerate() {
            let val_idx = *key as usize;
            if val_idx > 0 {
                let val = unsafe { ptr::read(&self.values[val_idx - 1]).assume_init() };
                let err = new_node.insert(i as u8, val);
                debug_assert!(err.is_none());
            }
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
        new_node
    }

    fn get(&self, key: u8) -> Option<&V> {
        let i = self.keys[key as usize] as usize;
        if i > 0 {
            unsafe {
                return Some(&*self.values[i - 1].as_ptr());
            }
        }
        None
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        let i = self.keys[key as usize] as usize;
        if i > 0 {
            unsafe {
                return Some(&mut *self.values[i - 1].as_mut_ptr());
            }
        }
        None
    }
}

struct Node256<V> {
    prefix: Vec<u8>,
    len: usize,
    values: [Option<V>; 256],
}

impl<V> Node256<V> {
    #[allow(clippy::uninit_assumed_init)]
    fn new(prefix: &[u8]) -> Self {
        let mut values: [Option<V>; 256] =
            unsafe { MaybeUninit::<[Option<V>; 256]>::uninit().assume_init() };
        for v in &mut values {
            unsafe {
                ptr::write(v, None);
            }
        }
        Self {
            prefix: prefix.to_vec(),
            len: 0,
            values,
        }
    }

    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        let i = key as usize;
        if self.values[i].is_none() {
            self.values[i] = Some(value);
            self.len += 1;
            None
        } else {
            Some(InsertError::DuplicateKey)
        }
    }

    fn remove(&mut self, key: u8) -> Option<V> {
        let i = key as usize;
        mem::replace(&mut self.values[i], None).map(|v| {
            self.len -= 1;
            v
        })
    }

    fn shrink(mut self) -> Node48<V> {
        debug_assert!(self.len <= 48);
        let mut new_node = Node48::new(&self.prefix);
        for i in 0..self.values.len() {
            if let Some(val) = mem::replace(&mut self.values[i], None) {
                let res = new_node.insert(i as u8, val);
                debug_assert!(res.is_none());
            }
        }

        self.len = 0;
        new_node
    }

    fn get(&self, key: u8) -> Option<&V> {
        self.values[key as usize].as_ref()
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        self.values[key as usize].as_mut()
    }
}

enum InsertError<V> {
    DuplicateKey,
    Overflow(V),
}

#[cfg(test)]
mod tests {
    use crate::keys::ByteString;
    use crate::Art;
    use rand::seq::SliceRandom;
    use rand::{thread_rng, Rng};
    use std::collections::HashSet;

    #[test]
    fn seq_insert_u8() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
        }

        for i in 0..=u8::MAX {
            assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string()));
        }
    }

    #[test]
    fn seq_insert_u16() {
        let mut art = Art::new();
        for i in 0..=u16::MAX {
            assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
        }

        for i in 0..=u16::MAX {
            assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string()));
        }
    }

    #[test]
    fn seq_insert_u32() {
        let mut art = Art::new();
        for shift in 0..2 {
            let start = (u16::MAX as u32 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(
                    matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string())
                );
            }
        }
    }

    #[test]
    fn seq_insert_u64() {
        let mut art = Art::new();
        for shift in 0..4 {
            let start = (u32::MAX as u64 + 1) << (shift * 8);
            let end = start + 100_000;
            for i in start..=end {
                assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(
                    matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string())
                );
            }
        }
    }

    #[test]
    fn seq_remove_u8() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
        }

        for i in 0..=u8::MAX {
            assert!(matches!(art.remove(&ByteString::from(i)), Some(val) if val == i.to_string()));
            assert!(matches!(art.get(&ByteString::from(i)), None));
        }
    }

    #[test]
    fn seq_remove_u16() {
        let mut art = Art::new();
        for i in 0..=u16::MAX {
            assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
        }

        for i in 0..=u16::MAX {
            assert!(matches!(art.remove(&ByteString::from(i)), Some(val) if val == i.to_string()));
            assert!(matches!(art.get(&ByteString::from(i)), None));
        }
    }

    #[test]
    fn seq_remove_u32() {
        let mut art = Art::new();
        for shift in 0..2 {
            let start = (u16::MAX as u32 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(
                    matches!(art.remove(&ByteString::from(i)), Some(val) if val == i.to_string())
                );
                assert!(matches!(art.get(&ByteString::from(i)), None));
            }
        }
    }

    #[test]
    fn seq_remove_u64() {
        let mut art = Art::new();
        for shift in 0..4 {
            let start = (u32::MAX as u64 + 1) << (shift * 8);
            let end = start + 100_000;
            for i in start..=end {
                assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
            }
            for i in start..=end {
                assert!(
                    matches!(art.remove(&ByteString::from(i)), Some(val) if val == i.to_string())
                );
                assert!(matches!(art.get(&ByteString::from(i)), None));
            }
        }
    }

    #[test]
    fn modifications_with_seq_keys_with_increasing_size() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
            assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string()));
        }
        for i in 0..=u8::MAX {
            assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string()));
        }

        for i in u8::MAX as u16 + 1..=u16::MAX {
            assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
            assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string()));
        }
        for i in u8::MAX as u16 + 1..=u16::MAX {
            assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string()));
        }

        for i in u16::MAX as u32 + 1..=(1 << 21) as u32 {
            assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
            assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string()));
        }
        for i in u16::MAX as u32 + 1..=(1 << 21) as u32 {
            assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string()));
        }

        for i in 0..=u8::MAX {
            assert!(matches!(art.remove(&ByteString::from(i)), Some(val) if val == i.to_string()));
        }
        for i in u8::MAX as u16 + 1..=u16::MAX {
            assert!(matches!(art.remove(&ByteString::from(i)), Some(val) if val == i.to_string()));
        }
        for i in u16::MAX as u32 + 1..=(1 << 21) as u32 {
            assert!(matches!(art.remove(&ByteString::from(i)), Some(val) if val == i.to_string()));
        }
    }

    #[test]
    fn insert_with_long_prefix() {
        let mut art = Art::new();
        long_prefix_test(&mut art, |art, key| {
            assert!(
                art.insert(ByteString::new(key.as_bytes()), key.clone()),
                "{}",
                key
            );
            assert!(matches!(art.get(&ByteString::new(key.as_bytes())), Some(val) if val == &key));
        });
    }

    #[test]
    fn remove_with_long_prefix() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            assert!(
                art.insert(ByteString::new(key.as_bytes()), key.clone()),
                "{}",
                key
            );
            existing.insert(key);
        });

        for key in existing {
            assert!(
                matches!(art.remove(&ByteString::new(key.as_bytes())), Some(val) if val == key),
                "{}",
                key
            );
            assert!(matches!(art.get(&ByteString::new(key.as_bytes())), None));
        }
    }

    fn long_prefix_test<F: FnMut(&mut Art<ByteString, String>, String)>(
        art: &mut Art<ByteString, String>,
        mut test_fn: F,
    ) {
        let mut existing = HashSet::new();
        let mut chars = ['a', 'b', 'c', 'd', 'e', 'f', 'x', 'y', 'z'];
        chars.shuffle(&mut thread_rng());
        let chars = &chars[..thread_rng().gen_range(1..chars.len())];
        for i in 0..chars.len() {
            let level1_prefix = chars[i].to_string().repeat(thread_rng().gen_range(1..8));
            for i in 0..chars.len() {
                let level2_prefix = chars[i].to_string().repeat(thread_rng().gen_range(1..8));
                let key_prefix = level1_prefix.clone() + &level2_prefix;
                for _ in 0..=u8::MAX {
                    let suffix: String = (0..thread_rng().gen_range(0..8))
                        .map(|_| chars[thread_rng().gen_range(0..chars.len())])
                        .collect();
                    let string = key_prefix.clone() + &suffix;
                    if existing.contains(&string) {
                        continue;
                    }
                    existing.insert(string.clone());
                    test_fn(art, string);
                }
            }
        }
    }
}
