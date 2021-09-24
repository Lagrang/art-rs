pub mod keys;
mod node;
mod scanner;

use crate::scanner::Scanner;
use node::*;
use std::ops::RangeBounds;
use std::option::Option::Some;
use std::{cmp, mem, ptr};

/// Trait represent [Art] key.
/// Trait define method which convert key into byte comparable sequence. This sequence will be
/// used to order keys inside tree. [Art] crate has several implementation of [Key] trait inside
/// `keys` module.
pub trait Key: Eq + Ord {
    fn to_bytes(&self) -> Vec<u8>;
}

pub struct Art<K, V> {
    root: Option<TypedNode<K, V>>,
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
        self.insert_internal(key, value, false)
    }

    pub fn upsert(&mut self, key: K, value: V) -> bool {
        self.insert_internal(key, value, true)
    }

    fn insert_internal(&mut self, key: K, value: V, upsert: bool) -> bool {
        let key_bytes = key.to_bytes();
        assert!(
            !key_bytes.is_empty(),
            "Key must have non empty byte string representation"
        );

        if self.root.is_none() {
            self.root.replace(TypedNode::Leaf(Leaf { key, value }));
            true
        } else {
            let mut node = self.root.as_mut().unwrap();
            let mut key = key;
            let mut offset = 0;
            let mut val = value;
            loop {
                let node_ptr = node as *mut TypedNode<K, V>;
                let res = match node {
                    TypedNode::Leaf(_) => Ok(Self::replace_leaf(
                        node, key, val, &key_bytes, offset, upsert,
                    )),
                    TypedNode::Combined(interim, leaf) => {
                        if leaf.key == key {
                            if upsert {
                                leaf.value = val;
                                Ok(true)
                            } else {
                                Ok(false)
                            }
                        } else if leaf.key > key {
                            // new key is 'less' than any key in this level
                            Self::replace_combined(unsafe { &mut *node_ptr }, key, val);
                            Ok(true)
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
        }
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        if let Some(root) = &mut self.root {
            let key_bytes_vec = key.to_bytes();
            let mut key_bytes = key_bytes_vec.as_slice();
            let mut parent_link = 0;
            let mut parent: Option<&mut BoxedNode<TypedNode<K, V>>> = None;
            let mut node_ptr = root as *mut TypedNode<K, V>;
            loop {
                let x: &mut TypedNode<K, V> = unsafe { &mut *node_ptr };
                match x {
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

    pub fn range(&self, range: impl RangeBounds<K>) -> impl DoubleEndedIterator<Item = (&K, &V)> {
        if let Some(root) = self.root.as_ref() {
            Scanner::new(root, range)
        } else {
            Scanner::empty(range)
        }
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> {
        self.range(..)
    }

    fn find_in_interim<'n, 'k>(
        interim: &'n BoxedNode<TypedNode<K, V>>,
        key_bytes: &'k [u8],
    ) -> Option<(&'n TypedNode<K, V>, &'k [u8], u8)> {
        let node = unsafe {
            #[allow(clippy::cast_ref_to_mut)]
            &mut *(interim as *const BoxedNode<TypedNode<K, V>> as *mut BoxedNode<TypedNode<K, V>>)
        };
        Self::find_in_interim_mut(node, key_bytes)
            .map(|(node, bytes, key)| (unsafe { &*(node as *const TypedNode<K, V>) }, bytes, key))
    }

    fn find_in_interim_mut<'n, 'k>(
        interim: &'n mut BoxedNode<TypedNode<K, V>>,
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

    fn replace_combined(node: &mut TypedNode<K, V>, key: K, value: V) {
        let existing_node = unsafe { ptr::read(node) };
        let new_node = TypedNode::Combined(Box::new(existing_node), Leaf::new(key, value));
        unsafe { ptr::write(node, new_node) };
    }

    fn replace_leaf(
        node: &mut TypedNode<K, V>,
        key: K,
        value: V,
        key_bytes: &[u8],
        key_start_offset: usize,
        upsert: bool,
    ) -> bool {
        let leaf = node.as_leaf_mut();
        if key == leaf.key {
            return if upsert {
                leaf.value = value;
                true
            } else {
                false
            };
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
            let mut new_interim = FlatNode::new(prefix);
            // safely move out value from node holder because
            // later we will override it without drop
            let err = new_interim.insert(key_bytes[0], TypedNode::Leaf(Leaf::new(key, value)));
            debug_assert!(err.is_none());

            let existing_leaf = unsafe { ptr::read(leaf) };
            TypedNode::Combined(
                Box::new(TypedNode::Interim(BoxedNode::Size4(Box::new(new_interim)))),
                existing_leaf,
            )
        } else if key_bytes.is_empty() {
            // no more bytes left in key of new KV => create combined node which will
            // point to new key and existing leaf will be moved into new interim node.
            // in this case, key of existing leaf is always longer(length in bytes) than new
            // key(if leaf key has the same length as new key, then keys are equal).
            let mut new_interim = FlatNode::new(prefix);
            // safely move out value from node holder because
            // later we will override it without drop
            let existing_leaf = unsafe { ptr::read(leaf) };
            let err = new_interim.insert(leaf_key[0], TypedNode::Leaf(existing_leaf));
            debug_assert!(err.is_none());

            TypedNode::Combined(
                Box::new(TypedNode::Interim(BoxedNode::Size4(Box::new(new_interim)))),
                Leaf::new(key, value),
            )
        } else {
            // safely move out value from node holder because
            // later we will override it without drop
            let leaf = unsafe { ptr::read(leaf) };
            let mut new_interim = FlatNode::new(prefix);
            let err = new_interim.insert(key_bytes[0], TypedNode::Leaf(Leaf::new(key, value)));
            debug_assert!(err.is_none());
            let err = new_interim.insert(leaf_key[0], TypedNode::Leaf(leaf));
            debug_assert!(err.is_none());
            TypedNode::Interim(BoxedNode::Size4(Box::new(new_interim)))
        };
        unsafe { ptr::write(node, new_interim) };
        true
    }

    fn interim_insert<'n>(
        node: &'n mut TypedNode<K, V>,
        key: K,
        value: V,
        key_bytes: &[u8],
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
            let mut new_interim = FlatNode::new(&prefix[..prefix_size]);
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
                    TypedNode::Interim(BoxedNode::Size4(Box::new(new_interim))),
                )
            };
            Ok(true)
        } else {
            let interim_ptr = unsafe { &mut *(interim as *mut BoxedNode<TypedNode<K, V>>) };
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

fn common_prefix_len(vec1: &[u8], vec2: &[u8]) -> usize {
    let mut len = 0;
    let mut rem = cmp::min(vec1.len(), vec2.len());
    // #[cfg(all(
    //     any(target_arch = "x86", target_arch = "x86_64"),
    //     not(feature = "disable_simd")
    // ))]
    // unsafe {
    //     while rem >= 8 {
    //         let v1 = _mm_loadu_si64(vec1[len..].as_ptr());
    //         let v2 = _mm_loadu_si64(vec2[len..].as_ptr());
    //         let res_mask = _mm_cmpeq_epi8(v1, v2);
    //         let equal_elements = _tzcnt_u32(!(_mm_movemask_epi8(res_mask) as u32)) as usize;
    //         if equal_elements < 8 {
    //             return len + equal_elements;
    //         }
    //         len += 8;
    //         rem -= 8;
    //     }
    // }

    for i in len..len + rem {
        if vec1[i] != vec2[i] {
            break;
        }
        len += 1;
    }
    len
}

#[cfg(test)]
mod tests {
    use crate::keys::ByteString;
    use crate::Art;
    use rand::prelude::IteratorRandom;
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
    fn mixed_upsert_and_delete() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            if thread_rng().gen_bool(0.3) && !existing.is_empty() {
                let key: &String = existing.iter().choose(&mut thread_rng()).unwrap();
                let key = key.clone();
                art.remove(&ByteString::new(key.as_bytes())).unwrap();
                existing.remove(&key);
            } else {
                art.upsert(ByteString::new(key.as_bytes()), key.clone());
                existing.insert(key);
            }
        });

        let res: Vec<&String> = art.iter().map(|(_, v)| v).collect();
        let mut expected: Vec<&String> = existing.iter().collect();
        expected.sort();
        assert_eq!(expected, res);
    }

    #[test]
    fn upsert() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            if existing.insert(key.clone()) {
                art.insert(ByteString::new(key.as_bytes()), key.clone());
            }
        });

        for (i, key) in existing.iter().enumerate() {
            let new_val = i.to_string();
            assert!(
                art.upsert(ByteString::new(key.as_bytes()), new_val.clone()),
                "{}",
                key
            );
            assert!(matches!(
                art.get(&ByteString::new(key.as_bytes())),
                Some(v) if v == &new_val
            ));
        }
    }

    #[test]
    fn existed_elements_cannot_be_inserted() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            if existing.insert(key.clone()) {
                assert!(
                    art.insert(ByteString::new(key.as_bytes()), key.clone()),
                    "{} not exist in tree, but insertion failed",
                    key
                );
            } else {
                assert!(
                    !art.insert(ByteString::new(key.as_bytes()), key.clone()),
                    "{} already exists but inserted again",
                    key
                );
            }
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
        let mut chars: Vec<char> = ('a'..='z').collect();
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
                    if !existing.insert(string.clone()) {
                        continue;
                    }
                    test_fn(art, string);
                    if existing.len() >= 10_000 {
                        return;
                    }
                }
            }
        }
    }
}
