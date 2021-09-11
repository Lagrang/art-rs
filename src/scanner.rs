use crate::node::*;
use crate::{Key, Leaf, TypedNode};
use std::collections::VecDeque;
use std::ops::Bound;
use std::ops::RangeBounds;

pub struct Scanner<'a, K, V, R> {
    interims: Vec<NodeIter<'a, TypedNode<K, V>>>,
    leafs: VecDeque<&'a Leaf<K, V>>,
    range: R,
}

impl<'a, K, V, R> Scanner<'a, K, V, R>
where
    R: RangeBounds<K>,
    K: Ord,
{
    pub(crate) fn empty(range: R) -> Self {
        Self {
            interims: Vec::new(),
            leafs: VecDeque::new(),
            range,
        }
    }

    pub(crate) fn new(node: &'a TypedNode<K, V>, range: R) -> Self {
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

        Self {
            interims,
            leafs,
            range,
        }
    }
}

impl<'a, K: 'a + Key, V, R: RangeBounds<K>> Iterator for Scanner<'a, K, V, R> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.interims.last_mut() {
            let mut e = node.next();
            loop {
                match e {
                    Some(TypedNode::Leaf(leaf)) => {
                        if self.range.contains(&leaf.key) {
                            if self.leafs.is_empty() {
                                return Some((&leaf.key, &leaf.value));
                            } else {
                                self.leafs.push_back(leaf);
                            }
                        } else {
                            match self.range.end_bound() {
                                Bound::Included(k) if &leaf.key > k => self.interims.clear(),
                                Bound::Excluded(k) if &leaf.key >= k => self.interims.clear(),
                                _ => {}
                            }
                        }

                        if let Some(leaf) = self.leafs.pop_front() {
                            return Some((&leaf.key, &leaf.value));
                        }
                        break;
                    }
                    Some(TypedNode::Interim(interim)) => {
                        self.interims.push(interim.iter());
                        break;
                    }
                    Some(TypedNode::Combined(interim, leaf)) => {
                        if self.range.contains(&leaf.key) {
                            self.leafs.push_back(leaf);
                            // next interim can be combined node
                            e = Some(interim);
                        } else {
                            match self.range.end_bound() {
                                Bound::Included(k) if &leaf.key > k => self.interims.clear(),
                                Bound::Excluded(k) if &leaf.key >= k => self.interims.clear(),
                                _ => {}
                            }
                            break;
                        }
                    }
                    None => {
                        self.interims.pop().unwrap();
                        break;
                    }
                }
            }
        }

        self.leafs.pop_front().map(|leaf| (&leaf.key, &leaf.value))
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
            existing.insert(key.clone());
        });

        let mut sorted: Vec<String> = existing.iter().map(|v| v.clone()).collect();
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

        let mut sorted: Vec<String> = existing.iter().map(|v| v.clone()).collect();
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
