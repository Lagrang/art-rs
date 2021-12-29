use std::arch::x86_64::*;
use std::cmp::Ordering;
use std::mem::MaybeUninit;
use std::ptr::slice_from_raw_parts;
use std::{mem, ptr};

pub trait Node<V> {
    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>>;
    fn remove(&mut self, key: u8) -> Option<V>;
    fn get_mut(&mut self, key: u8) -> Option<&mut V>;
    fn drain(self) -> Vec<(u8, V)>;
}

pub struct FlatNode<V, const N: usize> {
    prefix: Vec<u8>,
    len: usize,
    keys: [u8; N],
    values: [MaybeUninit<V>; N],
}

impl<V, const N: usize> Drop for FlatNode<V, N> {
    fn drop(&mut self) {
        for value in &self.values[..self.len] {
            unsafe {
                ptr::read(value.as_ptr());
            }
        }
        self.len = 0;
    }
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "sse2")]
unsafe fn key_index_sse(key: u8, keys_vec: __m128i, vec_len: usize) -> Option<usize> {
    debug_assert!(vec_len <= 16);
    let search_key_vec = _mm_set1_epi8(key as i8);
    let cmp_res = _mm_cmpeq_epi8(keys_vec, search_key_vec);
    let zeroes_from_start = _tzcnt_u32(_mm_movemask_epi8(cmp_res) as u32) as usize;
    if zeroes_from_start >= vec_len {
        None
    } else {
        Some(zeroes_from_start)
    }
}

impl<V, const N: usize> Node<V> for FlatNode<V, N> {
    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        if self.len >= N {
            Some(InsertError::Overflow(value))
        } else if self.get_mut(key).is_none() {
            self.keys[self.len] = key;
            self.values[self.len] = MaybeUninit::new(value);
            self.len += 1;
            None
        } else {
            Some(InsertError::DuplicateKey)
        }
    }

    fn remove(&mut self, key: u8) -> Option<V> {
        if let Some(i) = self.get_key_index(key) {
            let val =
                unsafe { mem::replace(&mut self.values[i], MaybeUninit::uninit()).assume_init() };
            self.keys[i] = self.keys[self.len - 1];
            self.values[i] = mem::replace(&mut self.values[self.len - 1], MaybeUninit::uninit());
            self.len -= 1;
            Some(val)
        } else {
            None
        }
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        self.get_key_index(key)
            .map(|i| unsafe { &mut *self.values[i].as_mut_ptr() })
    }

    fn drain(mut self) -> Vec<(u8, V)> {
        let mut res = Vec::with_capacity(self.len);
        for i in 0..self.len {
            unsafe {
                let value = mem::replace(&mut self.values[i], MaybeUninit::uninit()).assume_init();
                res.push((self.keys[i], value));
            }
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
        res
    }
}

impl<V, const N: usize> FlatNode<V, N> {
    pub fn new(prefix: &[u8]) -> Self {
        let vals: MaybeUninit<[MaybeUninit<V>; N]> = MaybeUninit::uninit();
        Self {
            prefix: prefix.to_vec(),
            len: 0,
            keys: [0; N],
            values: unsafe { vals.assume_init() },
        }
    }

    fn get_key_index(&self, key: u8) -> Option<usize> {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        unsafe {
            if N == 4 {
                let keys = _mm_set_epi8(
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    self.keys[3] as i8,
                    self.keys[2] as i8,
                    self.keys[1] as i8,
                    self.keys[0] as i8,
                );
                return key_index_sse(key, keys, self.len);
            } else if N == 16 {
                let keys = _mm_loadu_si128(self.keys.as_ptr() as *const __m128i);
                return key_index_sse(key, keys, self.len);
            }
        }

        self.keys[..self.len]
            .iter()
            .enumerate()
            .filter_map(|(i, k)| if *k == key { Some(i) } else { None })
            .next()
    }

    fn from(node: Node48<V>) -> Self {
        debug_assert!(node.len <= N);
        let mut new_node = FlatNode::new(&node.prefix);
        for (k, v) in node.drain() {
            let err = new_node.insert(k as u8, v);
            debug_assert!(err.is_none());
        }
        new_node
    }

    fn resize<const NEW_SIZE: usize>(mut self) -> FlatNode<V, NEW_SIZE> {
        debug_assert!(NEW_SIZE >= self.len);
        let mut new_node = FlatNode::new(&self.prefix);
        new_node.len = self.len;
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

    fn iter(&self) -> impl DoubleEndedIterator<Item = &V> {
        let mut kvs: Vec<(u8, &V)> = self.keys[..self.len]
            .iter()
            .zip(&self.values[..self.len])
            .map(|(k, v)| (*k, unsafe { &*v.as_ptr() }))
            .collect();
        kvs.sort_unstable_by_key(|(k, _)| *k);
        kvs.into_iter().map(|(_, v)| v)
    }
}

pub struct Node48<V> {
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
        self.len = 0;
    }
}

impl<V> Node<V> for Node48<V> {
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

        if self.len == 1 {
            self.len = 0;
            return Some(val);
        }

        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        unsafe {
            for offset in (0..256).step_by(16) {
                let keys = _mm_loadu_si128(self.keys[offset..].as_ptr() as *const __m128i);
                if let Some(i) = key_index_sse(self.len as u8, keys, 16).map(|i| i + offset) {
                    // move value of key which points to last array cell of values
                    self.keys[i] = val_idx as u8 + 1;
                    self.values[val_idx] =
                        mem::replace(&mut self.values[self.len - 1], MaybeUninit::uninit());
                    break;
                }
            }
            self.len -= 1;
            return Some(val);
        };

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

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        let i = self.keys[key as usize] as usize;
        if i > 0 {
            unsafe {
                return Some(&mut *self.values[i - 1].as_mut_ptr());
            }
        }
        None
    }

    fn drain(mut self) -> Vec<(u8, V)> {
        let mut res = Vec::with_capacity(self.len);
        for (k, v) in self.keys.iter().enumerate().filter(|(_, v)| **v > 0) {
            let val_idx = *v as usize;
            let value = unsafe {
                mem::replace(&mut self.values[val_idx - 1], MaybeUninit::uninit()).assume_init()
            };
            res.push((k as u8, value));
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
        res
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

    fn from_node256(node: Node256<V>) -> Node48<V> {
        debug_assert!(node.len <= 48);
        let mut new_node = Node48::new(&node.prefix);
        for (k, v) in node.drain() {
            new_node.values[new_node.len as usize] = MaybeUninit::new(v);
            new_node.keys[k as usize] = new_node.len as u8 + 1;
            new_node.len += 1;
        }
        new_node
    }

    fn from_flat_node<const N: usize>(node: FlatNode<V, N>) -> Node48<V> {
        debug_assert!(node.len <= 48);
        let mut new_node = Node48::new(&node.prefix);
        for (k, v) in node.drain() {
            new_node.values[new_node.len as usize] = MaybeUninit::new(v);
            new_node.keys[k as usize] = new_node.len as u8 + 1;
            new_node.len += 1;
        }
        new_node
    }

    fn iter(&self) -> impl DoubleEndedIterator<Item = &V> {
        let slice = unsafe { &*slice_from_raw_parts(self.values.as_ptr(), self.values.len()) };
        self.keys.iter().filter_map(move |k| {
            if *k > 0 {
                let val_index = *k as usize - 1;
                unsafe { Some(&*slice[val_index].as_ptr()) }
            } else {
                None
            }
        })
    }
}

pub struct Node256<V> {
    prefix: Vec<u8>,
    len: usize,
    values: [Option<V>; 256],
}

impl<V> Node<V> for Node256<V> {
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
        self.values[i].take().map(|v| {
            self.len -= 1;
            v
        })
    }

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        self.values[key as usize].as_mut()
    }

    fn drain(mut self) -> Vec<(u8, V)> {
        let mut res = Vec::with_capacity(self.len);
        for i in 0..self.values.len() {
            if let Some(v) = self.values[i].take() {
                res.push((i as u8, v))
            }
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
        res
    }
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

    fn from(node: Node48<V>) -> Self {
        let mut new_node = Node256::new(&node.prefix);
        for (k, v) in node.drain() {
            new_node.values[k as usize] = Some(v);
            new_node.len += 1;
        }

        new_node
    }

    fn iter(&self) -> impl DoubleEndedIterator<Item = &V> {
        self.values.iter().filter_map(|v| v.as_ref())
    }
}

pub struct NodeIter<'a, V> {
    node: Box<dyn DoubleEndedIterator<Item = &'a V> + 'a>,
}

impl<'a, V> NodeIter<'a, V> {
    fn new<I>(iter: I) -> Self
    where
        I: DoubleEndedIterator<Item = &'a V> + 'a,
    {
        Self {
            node: Box::new(iter),
        }
    }
}

impl<'a, V> DoubleEndedIterator for NodeIter<'a, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.node.next_back()
    }
}

impl<'a, V> Iterator for NodeIter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.node.next()
    }
}

pub enum TypedNode<K, V> {
    /// Interim node contains links to leaf and interim nodes on next level of tree.
    Interim(BoxedNode<TypedNode<K, V>>),
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
    pub fn as_leaf_mut(&mut self) -> &mut Leaf<K, V> {
        match self {
            TypedNode::Leaf(node) => node,
            _ => panic!("Only leaf can be retrieved"),
        }
    }

    pub fn take_leaf(self) -> Leaf<K, V> {
        match self {
            TypedNode::Leaf(node) => node,
            _ => panic!("Only leaf can be retrieved"),
        }
    }

    pub fn as_interim_mut(&mut self) -> &mut BoxedNode<TypedNode<K, V>> {
        match self {
            TypedNode::Interim(node) => node,
            _ => panic!("Only interim can be retrieved"),
        }
    }
}

pub struct Leaf<K, V> {
    pub key: K,
    pub value: V,
}

impl<K, V> Leaf<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Self { key, value }
    }
}

impl<K: PartialEq, V> PartialEq for Leaf<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl<K: Eq, V> Eq for Leaf<K, V> {}

impl<K: PartialOrd, V> PartialOrd for Leaf<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.key.partial_cmp(&other.key)
    }
}

impl<K: Ord, V> Ord for Leaf<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key.cmp(&other.key)
    }
}

pub enum BoxedNode<V> {
    Size4(Box<FlatNode<V, 4>>),
    Size16(Box<FlatNode<V, 16>>),
    Size48(Box<Node48<V>>),
    Size256(Box<Node256<V>>),
}

impl<V> BoxedNode<V> {
    pub fn prefix(&self) -> &[u8] {
        match self {
            BoxedNode::Size4(node) => &node.prefix,
            BoxedNode::Size16(node) => &node.prefix,
            BoxedNode::Size48(node) => &node.prefix,
            BoxedNode::Size256(node) => &node.prefix,
        }
    }

    pub fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        match self {
            BoxedNode::Size4(node) => node.insert(key, value),
            BoxedNode::Size16(node) => node.insert(key, value),
            BoxedNode::Size48(node) => node.insert(key, value),
            BoxedNode::Size256(node) => node.insert(key, value),
        }
    }

    pub fn remove(&mut self, key: u8) -> Option<V> {
        match self {
            BoxedNode::Size4(node) => node.remove(key),
            BoxedNode::Size16(node) => node.remove(key),
            BoxedNode::Size48(node) => node.remove(key),
            BoxedNode::Size256(node) => node.remove(key),
        }
    }

    pub fn set_prefix(&mut self, prefix: &[u8]) {
        match self {
            BoxedNode::Size4(node) => node.prefix = prefix.to_vec(),
            BoxedNode::Size16(node) => node.prefix = prefix.to_vec(),
            BoxedNode::Size48(node) => node.prefix = prefix.to_vec(),
            BoxedNode::Size256(node) => node.prefix = prefix.to_vec(),
        }
    }

    pub fn expand(self) -> BoxedNode<V> {
        match self {
            BoxedNode::Size4(node) => BoxedNode::Size16(Box::new(node.resize())),
            BoxedNode::Size16(node) => BoxedNode::Size48(Box::new(Node48::from_flat_node(*node))),
            BoxedNode::Size48(node) => BoxedNode::Size256(Box::new(Node256::from(*node))),
            BoxedNode::Size256(_) => self,
        }
    }

    pub fn should_shrink(&self) -> bool {
        match self {
            BoxedNode::Size4(_) => false,
            BoxedNode::Size16(node) => node.len <= 4,
            BoxedNode::Size48(node) => node.len <= 16,
            BoxedNode::Size256(node) => node.len <= 48,
        }
    }

    pub fn shrink(self) -> BoxedNode<V> {
        match self {
            BoxedNode::Size4(_) => self,
            BoxedNode::Size16(node) => BoxedNode::Size4(Box::new(node.resize())),
            BoxedNode::Size48(node) => BoxedNode::Size16(Box::new(FlatNode::from(*node))),
            BoxedNode::Size256(node) => BoxedNode::Size48(Box::new(Node48::from_node256(*node))),
        }
    }

    pub fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        match self {
            BoxedNode::Size4(node) => node.get_mut(key),
            BoxedNode::Size16(node) => node.get_mut(key),
            BoxedNode::Size48(node) => node.get_mut(key),
            BoxedNode::Size256(node) => node.get_mut(key),
        }
    }

    pub fn iter(&self) -> NodeIter<V> {
        match self {
            BoxedNode::Size4(node) => NodeIter::new(node.iter()),
            BoxedNode::Size16(node) => NodeIter::new(node.iter()),
            BoxedNode::Size48(node) => NodeIter::new(node.iter()),
            BoxedNode::Size256(node) => NodeIter::new(node.iter()),
        }
    }
}

pub enum InsertError<V> {
    DuplicateKey,
    Overflow(V),
}

#[cfg(test)]
mod tests {
    use crate::node::{FlatNode, InsertError, Node, Node256, Node48};

    #[test]
    fn flat_node() {
        node_test(FlatNode::<usize, 4>::new(&[]), 4);
        node_test(FlatNode::<usize, 16>::new(&[]), 16);
        node_test(FlatNode::<usize, 32>::new(&[]), 32);
        node_test(FlatNode::<usize, 48>::new(&[]), 48);
        node_test(FlatNode::<usize, 64>::new(&[]), 64);

        // resize from 16 to 4
        let mut node = FlatNode::<usize, 16>::new(&[]);
        for i in 0..4 {
            node.insert(i as u8, i);
        }
        let mut resized: FlatNode<usize, 4> = node.resize();
        assert_eq!(resized.len, 4);
        for i in 0..4 {
            assert!(matches!(resized.get_mut(i as u8), Some(v) if *v == i));
        }

        // resize from 4 to 16
        let mut node = FlatNode::<usize, 4>::new(&[]);
        for i in 0..4 {
            node.insert(i as u8, i);
        }
        let mut resized: FlatNode<usize, 16> = node.resize();
        assert_eq!(resized.len, 4);
        for i in 4..16 {
            resized.insert(i as u8, i);
        }
        assert_eq!(resized.len, 16);
        for i in 0..16 {
            assert!(matches!(resized.get_mut(i as u8), Some(v) if *v == i));
        }
    }

    #[test]
    fn node48() {
        node_test(Node48::<usize>::new(&[]), 48);

        // resize from 48 to 16
        let mut node = Node48::<usize>::new(&[]);
        for i in 0..16 {
            node.insert(i as u8, i);
        }
        let mut resized: FlatNode<usize, 16> = FlatNode::from(node);
        assert_eq!(resized.len, 16);
        for i in 0..16 {
            assert!(matches!(resized.get_mut(i as u8), Some(v) if *v == i));
        }

        // resize from 48 to 4
        let mut node = Node48::<usize>::new(&[]);
        for i in 0..4 {
            node.insert(i as u8, i);
        }
        let mut resized: FlatNode<usize, 4> = FlatNode::from(node);
        assert_eq!(resized.len, 4);
        for i in 0..4 {
            assert!(matches!(resized.get_mut(i as u8), Some(v) if *v == i));
        }
    }

    #[test]
    fn node256() {
        node_test(Node256::<usize>::new(&[]), 256);

        // resize from 48 to 256
        let mut node = Node48::<usize>::new(&[]);
        for i in 0..48 {
            node.insert(i as u8, i);
        }
        let mut resized = Node256::from(node);
        assert_eq!(resized.len, 48);
        for i in 0..48 {
            assert!(matches!(resized.get_mut(i as u8), Some(v) if *v == i));
        }
    }

    fn node_test(mut node: impl Node<usize>, size: usize) {
        for i in 0..size {
            assert!(node.insert(i as u8, i).is_none());
            assert!(node.insert(i as u8, i).is_some());
        }

        if size + 1 < u8::MAX as usize {
            assert!(matches!(
                node.insert((size + 1) as u8, size + 1),
                Some(InsertError::Overflow(_))
            ));
        } else {
            assert!(matches!(
                node.insert((size + 1) as u8, size + 1),
                Some(InsertError::DuplicateKey)
            ));
        }

        for i in 0..size {
            assert!(matches!(node.get_mut(i as u8), Some(v) if *v == i));
        }

        if size + 1 < u8::MAX as usize {
            assert!(matches!(node.get_mut((size + 1) as u8), None));
        }

        for i in 0..size {
            assert!(matches!(node.remove(i as u8), Some(v) if v == i));
        }
        assert!(matches!(node.remove((size + 1) as u8), None));
    }
}
