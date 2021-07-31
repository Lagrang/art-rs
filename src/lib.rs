pub mod keys;

use std::collections::HashMap;
use std::mem::MaybeUninit;
use std::{cmp, ptr};

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
        if self.root.is_none() {
            self.root = Some(TypedNode::Leaf(Leaf { key, value }));
            true
        } else {
            let mut node = self.root.as_mut().unwrap();
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
                            Self::interim_insert(interim, key, val, &key_bytes, offset)
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
        }
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let key_vec = key.to_bytes();
        assert!(
            !key_vec.is_empty(),
            "Key must have non empty byte string representation"
        );

        fn find_in_interim<'k, 'n, K, V>(
            interim: &'n Node<TypedNode<K, V>>,
            key_bytes: &'k [u8],
        ) -> Option<(Option<&'n TypedNode<K, V>>, &'k [u8])> {
            let prefix = interim.prefix();
            if common_prefix_len(prefix, &key_bytes[..key_bytes.len()]) != prefix.len() {
                // node has prefix which is not prefix of search key
                return None;
            } else {
                if key_bytes.len() == prefix.len() {
                    // prefix of node exactly the same as key => no matches to key
                    // because all keys inside interim node longer at least by 1 byte.
                    return None;
                }
                let next_node = interim.get(key_bytes[prefix.len()]);
                let key_bytes = if key_bytes.len() > prefix.len() + 1 {
                    &key_bytes[prefix.len() + 1..]
                } else {
                    &[]
                };
                Some((next_node, key_bytes))
            }
        }

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
                    if let Some((next_node, rem_key_bytes)) = find_in_interim(interim, key_bytes) {
                        node = next_node;
                        key_bytes = rem_key_bytes;
                    } else {
                        return None;
                    }
                }
                TypedNode::Combined(interim, leaf) => {
                    if key == &leaf.key {
                        return Some(&leaf.value);
                    } else if let Some((next_node, rem_key_bytes)) =
                        find_in_interim(interim.as_interim(), key_bytes)
                    {
                        node = next_node;
                        key_bytes = rem_key_bytes;
                    } else {
                        return None;
                    }
                }
            }
        }
        None
    }

    fn replace_leaf(
        node: &mut TypedNode<K, V>,
        key: K,
        value: V,
        key_bytes: &[u8],
        key_start_offset: usize,
    ) -> bool {
        let leaf = node.as_leaf_mut();
        if key != leaf.key {
            let leaf_key_bytes = leaf.key.to_bytes();
            // debug_assert!(leaf_key_bytes.len() > key_bytes.len());
            let leaf_key = &leaf_key_bytes[key_start_offset..];
            let new_interim = if key_bytes.len() <= key_start_offset {
                // no more bytes left in key, create combined node which will point to new key
                // and existing leaf will be moved into new interim node.
                // in this case, key of existing leaf is always longer(length in bytes) than new
                // key. If leaf key has the same length as new key, then keys are equal.
                let mut new_interim = if leaf_key.len() > 1 {
                    Node4::new(&leaf_key[..leaf_key.len() - 1])
                } else {
                    Node4::new(&[])
                };
                // safely move out value from node holder because
                // later we will override it without drop
                let existing_leaf = unsafe { ptr::read(leaf) };
                let err = new_interim
                    .insert(leaf_key[leaf_key.len() - 1], TypedNode::Leaf(existing_leaf));
                debug_assert!(err.is_none());

                TypedNode::Combined(
                    Box::new(TypedNode::Interim(Node::Size4(Box::new(new_interim)))),
                    Leaf::new(key, value),
                )
            } else {
                // do not account last byte of keys in prefix computation
                // because this byte will be used in interim node as pointer to leaf node
                let key_bytes = &key_bytes[key_start_offset..];
                let prefix_size = common_prefix_len(
                    &leaf_key[..leaf_key.len() - 1],
                    &key_bytes[..key_bytes.len() - 1],
                );

                // safely move out value from node holder because
                // later we will override it without drop
                let leaf = unsafe { ptr::read(leaf) };
                let mut new_interim = Node4::new(&leaf_key[0..prefix_size]);
                let err = new_interim.insert(
                    key_bytes[prefix_size],
                    TypedNode::Leaf(Leaf::new(key, value)),
                );
                debug_assert!(err.is_none());
                let err = new_interim.insert(leaf_key[prefix_size], TypedNode::Leaf(leaf));
                debug_assert!(err.is_none());
                TypedNode::Interim(Node::Size4(Box::new(new_interim)))
            };
            unsafe { ptr::write(node, new_interim) };
            true
        } else {
            false
        }
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
        let prefix_size = common_prefix_len(prefix, &key_bytes[..key_bytes.len() - 1]);

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
                    node_ptr,
                    TypedNode::Interim(Node::Size4(Box::new(new_interim))),
                )
            };
            return Ok(true);
        }

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
                self.len += 1;
                self.keys[i] = key;
                self.values[i] = MaybeUninit::new(value);
                None
            },
            |_| Some(InsertError::DuplicateKey),
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
                self.len += 1;
                self.keys[i] = key;
                self.values[i] = MaybeUninit::new(value);
                None
            },
            |_| Some(InsertError::DuplicateKey),
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
        self.len += 1;
        self.keys[i] = self.len as u8;
        None
    }

    fn expand(mut self) -> Node256<V> {
        let mut new_node = Node256::new(&self.prefix);
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

    #[test]
    fn test_seq_insert() {
        let mut art = Art::new();
        for i in 0..=u16::MAX {
            assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
        }

        for i in 0..u16::MAX {
            assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &i.to_string()));
        }
    }
}
