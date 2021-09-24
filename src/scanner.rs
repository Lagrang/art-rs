use crate::node::*;
use crate::{Key, Leaf, TypedNode};
use std::collections::{BinaryHeap, VecDeque};
use std::ops::Bound;
use std::ops::RangeBounds;

pub struct Scanner<'a, K, V, R> {
    forward: ScannerState<'a, K, V>,
    last_forward_key: Option<&'a K>,
    backward: BackwardScannerState<'a, K, V>,
    last_backward_key: Option<&'a K>,
    range: R,
}

struct ScannerState<'a, K, V> {
    interims: Vec<NodeIter<'a, TypedNode<K, V>>>,
    leafs: VecDeque<&'a Leaf<K, V>>,
}

struct BackwardScannerState<'a, K, V> {
    interims: Vec<NodeIter<'a, TypedNode<K, V>>>,
    leafs: BinaryHeap<&'a Leaf<K, V>>,
}

impl<'a, K, V, R> Scanner<'a, K, V, R>
where
    K: Ord,
    R: RangeBounds<K>,
{
    pub(crate) fn empty(range: R) -> Self {
        Self {
            forward: ScannerState::empty(),
            backward: BackwardScannerState::empty(),
            last_forward_key: None,
            last_backward_key: None,
            range,
        }
    }

    pub(crate) fn new(node: &'a TypedNode<K, V>, range: R) -> Self
    where
        R: RangeBounds<K>,
    {
        Self {
            forward: ScannerState::forward_scan(node, &range),
            backward: BackwardScannerState::backward_scan(node, &range),
            last_forward_key: None,
            last_backward_key: None,
            range,
        }
    }
}

impl<'a, K, V> ScannerState<'a, K, V>
where
    K: Ord,
{
    pub(crate) fn empty() -> Self {
        Self {
            interims: Vec::new(),
            leafs: VecDeque::new(),
        }
    }

    fn forward_scan<R>(node: &'a TypedNode<K, V>, range: &R) -> Self
    where
        R: RangeBounds<K>,
    {
        let mut node = node;
        let mut leafs = VecDeque::new();
        let mut interims = Vec::new();
        loop {
            match node {
                TypedNode::Leaf(leaf) => {
                    if range.contains(&leaf.key) {
                        leafs.push_back(leaf);
                    }
                    break;
                }
                TypedNode::Interim(interim) => {
                    interims.push(interim.iter());
                    break;
                }
                TypedNode::Combined(interim, leaf) => {
                    node = interim;
                    if range.contains(&leaf.key) {
                        leafs.push_back(leaf);
                    }
                }
            }
        }

        Self { interims, leafs }
    }
}

impl<'a, K, V> BackwardScannerState<'a, K, V>
where
    K: Ord,
{
    pub(crate) fn empty() -> Self {
        Self {
            interims: Vec::new(),
            leafs: BinaryHeap::new(),
        }
    }

    fn backward_scan<R>(node: &'a TypedNode<K, V>, range: &R) -> Self
    where
        R: RangeBounds<K>,
    {
        let mut node = node;
        let mut leafs = BinaryHeap::new();
        let mut interims = Vec::new();
        loop {
            match node {
                TypedNode::Leaf(leaf) => {
                    if range.contains(&leaf.key) {
                        leafs.push(leaf);
                    }
                    break;
                }
                TypedNode::Interim(interim) => {
                    interims.push(interim.iter());
                    break;
                }
                TypedNode::Combined(interim, leaf) => {
                    node = interim;
                    if range.contains(&leaf.key) {
                        leafs.push(leaf);
                    }
                }
            }
        }

        Self { interims, leafs }
    }
}

impl<'a, K: 'a + Key, V, R: RangeBounds<K>> DoubleEndedIterator for Scanner<'a, K, V, R> {
    fn next_back(&mut self) -> Option<Self::Item> {
        'outer: while let Some(node) = self.backward.interims.last_mut() {
            let mut e = node.next_back();
            loop {
                match e {
                    Some(TypedNode::Leaf(leaf)) => {
                        if self.range.contains(&leaf.key) {
                            self.backward.leafs.push(leaf);
                            break 'outer;
                        } else {
                            // match self.range.start_bound() {
                            //     Bound::Included(k) if &leaf.key < k => {
                            //         self.backward.interims.clear()
                            //     }
                            //     Bound::Excluded(k) if &leaf.key <= k => {
                            //         self.backward.interims.clear()
                            //     }
                            //     _ => {}
                            // }
                        }
                        break;
                    }
                    Some(TypedNode::Interim(interim)) => {
                        self.backward.interims.push(interim.iter());
                        break;
                    }
                    Some(TypedNode::Combined(interim, leaf)) => {
                        if self.range.contains(&leaf.key) {
                            self.backward.leafs.push(leaf);
                        }
                        // next interim can be combined node
                        e = Some(interim);
                    }
                    None => {
                        self.backward.interims.pop().unwrap();
                        break;
                    }
                }
            }
        }

        self.backward.leafs.pop().and_then(|leaf| {
            self.last_backward_key = Some(&leaf.key);
            if self
                .last_backward_key
                .zip(self.last_forward_key)
                .map_or(true, |(k1, k2)| k1 > k2)
            {
                Some((&leaf.key, &leaf.value))
            } else {
                self.backward.interims.clear();
                self.backward.leafs.clear();
                None
            }
        })
    }
}

impl<'a, K: 'a + Key, V, R: RangeBounds<K>> Iterator for Scanner<'a, K, V, R> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.forward.interims.last_mut() {
            let mut e = node.next();
            loop {
                match e {
                    Some(TypedNode::Leaf(leaf)) => {
                        if self.range.contains(&leaf.key) {
                            if self.forward.leafs.is_empty() {
                                self.last_forward_key = Some(&leaf.key);
                                if self
                                    .last_forward_key
                                    .zip(self.last_backward_key)
                                    .map_or(true, |(k1, k2)| k1 < k2)
                                {
                                    return Some((&leaf.key, &leaf.value));
                                } else {
                                    self.forward.interims.clear();
                                    self.forward.leafs.clear();
                                    return None;
                                }
                            } else {
                                self.forward.leafs.push_back(leaf);
                            }
                        } else {
                            match self.range.end_bound() {
                                Bound::Included(k) if &leaf.key > k => {
                                    self.forward.interims.clear()
                                }
                                Bound::Excluded(k) if &leaf.key >= k => {
                                    self.forward.interims.clear()
                                }
                                _ => {}
                            }
                        }

                        if let Some(leaf) = self.forward.leafs.pop_front() {
                            self.last_forward_key = Some(&leaf.key);
                            if self
                                .last_forward_key
                                .zip(self.last_backward_key)
                                .map_or(true, |(k1, k2)| k1 < k2)
                            {
                                return Some((&leaf.key, &leaf.value));
                            } else {
                                self.forward.interims.clear();
                                self.forward.leafs.clear();
                                return None;
                            }
                        }
                        break;
                    }
                    Some(TypedNode::Interim(interim)) => {
                        self.forward.interims.push(interim.iter());
                        break;
                    }
                    Some(TypedNode::Combined(interim, leaf)) => {
                        if self.range.contains(&leaf.key) {
                            self.forward.leafs.push_back(leaf);
                            // next interim can be combined node
                            e = Some(interim);
                        } else {
                            match self.range.end_bound() {
                                Bound::Included(k) if &leaf.key > k => {
                                    self.forward.interims.clear()
                                }
                                Bound::Excluded(k) if &leaf.key >= k => {
                                    self.forward.interims.clear()
                                }
                                _ => {}
                            }
                            break;
                        }
                    }
                    None => {
                        self.forward.interims.pop().unwrap();
                        break;
                    }
                }
            }
        }

        self.forward.leafs.pop_front().and_then(|leaf| {
            self.last_forward_key = Some(&leaf.key);
            if self
                .last_forward_key
                .zip(self.last_backward_key)
                .map_or(true, |(k1, k2)| k1 < k2)
            {
                Some((&leaf.key, &leaf.value))
            } else {
                self.forward.interims.clear();
                self.forward.leafs.clear();
                None
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::keys::ByteString;
    use crate::Art;
    use rand::prelude::SliceRandom;
    use rand::{thread_rng, Rng};
    use std::cmp;
    use std::collections::HashSet;

    #[test]
    fn seq_insert_u8() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
        }

        let mut len = 0usize;
        let mut expected = 0u8;
        for (k, v) in art.range(ByteString::from(0u8)..=ByteString::from(u8::MAX)) {
            assert_eq!(&ByteString::from(expected), k);
            assert_eq!(&expected.to_string(), v);
            expected = expected.wrapping_add(1);
            len += 1;
        }
        assert_eq!(len, u8::MAX as usize + 1);
    }

    #[test]
    fn seq_insert_u16() {
        let mut art = Art::new();
        for i in 0..=u16::MAX {
            assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
        }

        let mut len = 0usize;
        let mut expected = 0u16;
        for (k, v) in art.range(ByteString::from(0u16)..=ByteString::from(u16::MAX)) {
            assert_eq!(&ByteString::from(expected), k);
            assert_eq!(&expected.to_string(), v);
            expected = expected.wrapping_add(1);
            len += 1;
        }
        assert_eq!(len, u16::MAX as usize + 1);
    }

    #[test]
    fn range_scan_on_sequential_u32_keys() {
        let mut art = Art::new();
        for shift in 0..2 {
            let start = (u16::MAX as u32 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(ByteString::from(i), i.to_string()), "{}", i);
            }

            let mut len = 0;
            let mut expected = start;
            for (k, v) in art.range(ByteString::from(start)..=ByteString::from(end)) {
                assert_eq!(&ByteString::from(expected), k);
                assert_eq!(&expected.to_string(), v);
                expected += 1;
                len += 1;
            }
            assert_eq!(len, end - start + 1);
        }
    }

    #[test]
    fn range_scan_on_sequential_u64_keys() {
        let mut art = Art::new();
        for shift in 0..4 {
            let start = (u32::MAX as u64 + 1) << (shift * 8);
            let end = start + 100_000;
            for i in start..=end {
                let key = ByteString::from(i);
                art.insert(key, i.to_string());
            }

            let mut len = 0;
            let mut expected = start;
            for (k, v) in art.range(ByteString::from(start)..=ByteString::from(end)) {
                assert_eq!(&ByteString::from(expected), k);
                assert_eq!(&expected.to_string(), v);
                expected += 1;
                len += 1;
            }
            assert_eq!(len, end - start + 1);
        }
    }

    #[test]
    fn iter_with_long_prefix() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            assert!(
                art.insert(ByteString::new(key.as_bytes()), key.clone()),
                "{} already exists",
                key
            );
            existing.insert(key);
        });

        let mut sorted: Vec<String> = existing.iter().cloned().collect();
        sorted.sort();
        assert_eq!(
            sorted,
            art.iter().map(|(_, v)| v.clone()).collect::<Vec<String>>()
        );

        sorted
            .choose_multiple(&mut thread_rng(), sorted.len() / 4)
            .for_each(|key| {
                art.remove(&ByteString::new(key.as_bytes()));
                existing.remove(key);
            });

        let mut sorted: Vec<String> = existing.iter().cloned().collect();
        sorted.sort();
        assert_eq!(
            sorted,
            art.iter().map(|(_, v)| v.clone()).collect::<Vec<String>>()
        );
    }

    #[test]
    fn range_scan_with_long_prefix() {
        let mut art = Art::new();
        long_prefix_test(&mut art, |art, key| {
            art.insert(ByteString::new(key.as_bytes()), key.clone());
        });

        let keys: Vec<ByteString> = art.iter().map(|(k, _)| k.clone()).collect();
        for _ in 0..500 {
            let bound1 = keys.choose(&mut thread_rng()).unwrap();
            let bound2 = keys.choose(&mut thread_rng()).unwrap();
            let range = cmp::min(bound1, bound2)..cmp::max(bound1, bound2);
            art.range(range.clone())
                .map(|(k, _)| k.clone())
                .all(|k| range.contains(&&k));
            let range = cmp::min(bound1, bound2)..=cmp::max(bound1, bound2);
            art.range(range.clone())
                .map(|(k, _)| k.clone())
                .all(|k| range.contains(&&k));
            let range = ..cmp::max(bound1, bound2);
            art.range(range)
                .map(|(k, _)| k.clone())
                .all(|k| range.contains(&&k));
            let range = ..=cmp::max(bound1, bound2);
            art.range(range)
                .map(|(k, _)| k.clone())
                .all(|k| range.contains(&&k));
            let range = cmp::max(bound1, bound2)..;
            art.range(range.clone())
                .map(|(k, _)| k.clone())
                .all(|k| range.contains(&&k));
        }
        // TODO: add test for range scans which starts with non-existing keys
    }

    #[test]
    fn double_ended_iter() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            art.insert(ByteString::new(key.as_bytes()), key.clone());
            existing.insert(key);
        });

        let mut iter = art.iter().peekable();
        let mut fwd = Vec::new();
        let mut bwd = Vec::new();
        while iter.peek().is_some() {
            if thread_rng().gen_bool(0.5) {
                (0..thread_rng().gen_range(1..25)).for_each(|_| {
                    iter.next().map(|(_, v)| fwd.push(v.clone()));
                });
            } else {
                (0..thread_rng().gen_range(1..25)).for_each(|_| {
                    iter.next_back().map(|(_, v)| bwd.push(v.clone()));
                });
            }
        }

        let mut expected: Vec<String> = existing.iter().cloned().collect();
        expected.sort();
        bwd.reverse();
        fwd.append(&mut bwd);
        assert_eq!(expected, fwd);
    }

    #[test]
    fn double_ended_iter_seq_keys() {
        let mut art = Art::new();
        for i in 0..2500u32 {
            art.insert(ByteString::from(i), i);

            let mut iter = art.iter().peekable();
            let mut fwd = Vec::new();
            let mut bwd = Vec::new();
            while iter.peek().is_some() {
                if thread_rng().gen_bool(0.5) {
                    (0..thread_rng().gen_range(1..25)).for_each(|_| {
                        iter.next().map(|(_, v)| fwd.push(v.clone()));
                    });
                } else {
                    (0..thread_rng().gen_range(1..25)).for_each(|_| {
                        iter.next_back().map(|(_, v)| bwd.push(v.clone()));
                    });
                }
            }

            let expected: Vec<u32> = (0..=i).collect();
            bwd.reverse();
            fwd.append(&mut bwd);
            assert_eq!(expected, fwd);
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
                    if existing.len() >= 70 {
                        return;
                    }
                }
            }
        }
    }
}
