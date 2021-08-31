use std::arch::x86_64::*;
use std::cmp::Ordering;
use std::mem::MaybeUninit;
use std::{mem, ptr};

pub trait Node<V> {
    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>>;
    fn remove(&mut self, key: u8) -> Option<V>;
    fn get_mut(&mut self, key: u8) -> Option<&mut V>;
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
    }
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "sse2")]
unsafe fn key_index_sse(key: u8, keys: __m128i, len: usize) -> Option<usize> {
    debug_assert!(len <= 16);
    let search_key_vec = _mm_set1_epi8(key as i8);
    let cmp_res = _mm_cmpeq_epi8(keys, search_key_vec);
    let zeroes_from_start = _tzcnt_u32(_mm_movemask_epi8(cmp_res) as u32) as usize;
    if zeroes_from_start >= len {
        None
    } else {
        Some(zeroes_from_start)
    }
}

impl<V, const N: usize> Node<V> for FlatNode<V, N> {
    fn insert(&mut self, key: u8, value: V) -> Option<InsertError<V>> {
        self.keys[..self.len].binary_search(&key).map_or_else(
            |i| {
                if self.len >= N {
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

    fn get_mut(&mut self, key: u8) -> Option<&mut V> {
        self.get_key_index(key)
            .map(|i| unsafe { &mut *self.values[i].as_mut_ptr() })
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
        #[cfg(all(
            any(target_arch = "x86", target_arch = "x86_64"),
            not(feature = "disable_simd")
        ))]
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

    pub fn expand<const NEW_SIZE: usize>(mut self) -> FlatNode<V, NEW_SIZE> {
        debug_assert!(NEW_SIZE > self.len);
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

    pub fn shrink<const NEW_SIZE: usize>(mut self) -> FlatNode<V, NEW_SIZE> {
        debug_assert!(self.len <= NEW_SIZE);
        let mut new_node = FlatNode::new(&self.prefix);
        for (i, key) in self.keys[..self.len].iter().enumerate() {
            let val = unsafe { ptr::read(&self.values[i]).assume_init() };
            let res = new_node.insert(*key, val);
            debug_assert!(res.is_none());
        }

        // emulate that all values was moved out from node before drop
        self.len = 0;
        new_node
    }

    pub fn get_at(&self, i: usize) -> (Option<&V>, Option<usize>) {
        let e = if i < self.len {
            unsafe { Some(&*self.values[i].as_ptr()) }
        } else {
            None
        };

        let next_idx = if i + 1 < self.len { Some(i + 1) } else { None };
        (e, next_idx)
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

        #[cfg(all(
            any(target_arch = "x86", target_arch = "x86_64"),
            not(feature = "disable_simd")
        ))]
        unsafe {
            let keys = _mm_loadu_si128(self.keys.as_ptr() as *const __m128i);
            let res1 = key_index_sse(self.len as u8, keys, 16);
            let keys = _mm_loadu_si128(self.keys[16..].as_ptr() as *const __m128i);
            let res2 = key_index_sse(self.len as u8, keys, 16).map(|i| i + 16);
            let keys = _mm_loadu_si128(self.keys[32..].as_ptr() as *const __m128i);
            let res3 = key_index_sse(self.len as u8, keys, 16).map(|i| i + 32);
            res1.or(res2).or(res3).map(|i| {
                // move value of key which points to last array cell
                self.keys[i] = val_idx as u8 + 1;
                self.values[val_idx] =
                    mem::replace(&mut self.values[self.len - 1], MaybeUninit::uninit());
            });
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
}

impl<V> Node48<V> {
    pub fn new(prefix: &[u8]) -> Self {
        let vals: MaybeUninit<[MaybeUninit<V>; 48]> = MaybeUninit::uninit();
        Self {
            prefix: prefix.to_vec(),
            len: 0,
            keys: [0; 256],
            values: unsafe { vals.assume_init() },
        }
    }

    pub fn expand_from<const N: usize>(mut node: FlatNode<V, N>) -> Node48<V> {
        debug_assert!(node.len <= 48);
        let mut new_node = Node48::new(&node.prefix);
        for (i, key) in node.keys[..node.len].iter().enumerate() {
            let val = unsafe { ptr::read(&node.values[i]).assume_init() };
            let res = new_node.insert(*key, val);
            debug_assert!(res.is_none());
        }

        // emulate that all values was moved out from node before drop
        node.len = 0;
        new_node
    }

    pub fn should_shrink(&self) -> bool {
        self.len <= 16
    }

    pub fn expand(mut self) -> Node256<V> {
        let mut new_node = Node256::new(&self.prefix);
        for (key, val_loc) in self.keys.iter().enumerate() {
            let val_idx = *val_loc as usize;
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

    pub fn shrink(mut self) -> FlatNode<V, 16> {
        debug_assert!(self.len <= 16);
        let mut new_node = FlatNode::new(&self.prefix);
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

    pub fn get_at(&self, index: usize) -> (Option<&V>, Option<usize>) {
        let e = if index < self.keys.len() && self.keys[index] > 0 {
            unsafe {
                let val_index = self.keys[index] as usize - 1;
                Some(&*self.values[val_index].as_ptr())
            }
        } else {
            None
        };

        let next_idx = if index + 1 < self.keys.len() {
            self.keys[index + 1..]
                .iter()
                .enumerate()
                .filter_map(|(i, j)| if *j > 0 { Some(i) } else { None })
                .next()
                .map_or_else(|| None, |i| Some(i + index + 1))
        } else {
            None
        };

        (e, next_idx)
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
}

impl<V> Node256<V> {
    #[allow(clippy::uninit_assumed_init)]
    pub fn new(prefix: &[u8]) -> Self {
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

    pub fn shrink(mut self) -> Node48<V> {
        debug_assert!(self.len <= 48);
        let mut new_node = Node48::new(&self.prefix);
        for i in 0..self.values.len() {
            if let Some(val) = self.values[i].take() {
                let res = new_node.insert(i as u8, val);
                debug_assert!(res.is_none());
            }
        }

        self.len = 0;
        new_node
    }

    pub fn get_at(&self, index: usize) -> (Option<&V>, Option<usize>) {
        let e = if index < self.values.len() && self.values[index].is_some() {
            self.values[index].as_ref().map(|v| v)
        } else {
            None
        };

        let next_idx = if index + 1 < self.values.len() {
            self.values[index + 1..]
                .iter()
                .enumerate()
                .filter_map(|(i, val)| val.as_ref().map(|_| i))
                .next()
                .map_or_else(|| None, |i| Some(i + index + 1))
        } else {
            None
        };

        (e, next_idx)
    }

    pub fn should_shrink(&self) -> bool {
        self.len <= 48
    }
}

pub struct NodeIter<'a, V> {
    node: &'a BoxedNode<V>,
    index: Option<usize>,
}

impl<'a, V> NodeIter<'a, V> {
    fn new(node: &'a BoxedNode<V>) -> Self {
        Self {
            node,
            index: Some(0),
        }
    }
}

impl<'a, V> Iterator for NodeIter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(index) = self.index {
            match self.node.get_at(index) {
                (Some(val), Some(next_element)) => {
                    self.index = Some(next_element);
                    return Some(val);
                }
                (Some(val), None) => {
                    self.index = None;
                    return Some(val);
                }
                (None, Some(next_element)) => {
                    // this can happen only once per iterator: if node doesn't contain any element
                    // at 0 position a iterator beginning.
                    self.index = Some(next_element);
                }
                _ => return None,
            }
        }
        None
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
            BoxedNode::Size4(node) => BoxedNode::Size16(Box::new(node.expand())),
            BoxedNode::Size16(node) => BoxedNode::Size48(Box::new(Node48::expand_from(*node))),
            BoxedNode::Size48(node) => BoxedNode::Size256(Box::new(node.expand())),
            BoxedNode::Size256(_) => self,
        }
    }

    pub fn should_shrink(&self) -> bool {
        match self {
            BoxedNode::Size4(_) => false,
            BoxedNode::Size16(node) => node.len <= 4,
            BoxedNode::Size48(node) => node.should_shrink(),
            BoxedNode::Size256(node) => node.should_shrink(),
        }
    }

    pub fn shrink(self) -> BoxedNode<V> {
        match self {
            BoxedNode::Size4(_) => self,
            BoxedNode::Size16(node) => BoxedNode::Size4(Box::new(node.shrink())),
            BoxedNode::Size48(node) => BoxedNode::Size16(Box::new(node.shrink())),
            BoxedNode::Size256(node) => BoxedNode::Size48(Box::new(node.shrink())),
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

    pub fn get_at(&self, index: usize) -> (Option<&V>, Option<usize>) {
        match self {
            BoxedNode::Size4(node) => node.get_at(index),
            BoxedNode::Size16(node) => node.get_at(index),
            BoxedNode::Size48(node) => node.get_at(index),
            BoxedNode::Size256(node) => node.get_at(index),
        }
    }

    pub fn iter(&self) -> NodeIter<V> {
        NodeIter::new(self)
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
    }

    #[test]
    fn node48() {
        node_test(Node48::<usize>::new(&[]), 48);
    }

    #[test]
    fn node256() {
        node_test(Node256::<usize>::new(&[]), 256);
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
