use crate::node::*;
use crate::{Key, Leaf, TypedNode};
use std::cmp;
use std::collections::BinaryHeap;
use std::ops::RangeBounds;

pub struct Scanner<'a, K, V, R> {
    node_stack: Vec<NodeIter<'a, TypedNode<K, V>>>,
    pending_leafs: BinaryHeap<cmp::Reverse<&'a Leaf<K, V>>>,
    range: R,
}

impl<'a, K, V, R> Scanner<'a, K, V, R>
where
    R: RangeBounds<K>,
    K: Ord,
{
    pub(crate) fn empty(range: R) -> Self {
        Self {
            node_stack: Vec::new(),
            pending_leafs: BinaryHeap::new(),
            range,
        }
    }

    pub(crate) fn new(node: &'a TypedNode<K, V>, range: R) -> Self {
        match node {
            TypedNode::Leaf(leaf) => Self {
                node_stack: Vec::new(),
                pending_leafs: vec![cmp::Reverse(leaf)].into(),
                range,
            },
            TypedNode::Interim(interim) => Self {
                node_stack: vec![interim.iter()],
                pending_leafs: BinaryHeap::new(),
                range,
            },
            TypedNode::Combined(interim, leaf) => Self {
                node_stack: vec![interim.as_interim().iter()],
                pending_leafs: vec![cmp::Reverse(leaf)].into(),
                range,
            },
        }
    }
}

impl<'a, K: 'a + Key, V, R: RangeBounds<K>> Iterator for Scanner<'a, K, V, R> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        //TODO: optimize scan by skipping nodes which is not under requested range
        while let Some(node) = self.node_stack.last_mut() {
            let mut e = node.next();
            loop {
                match e {
                    Some(TypedNode::Leaf(leaf)) => {
                        if self.range.contains(&leaf.key) {
                            self.pending_leafs.push(std::cmp::Reverse(leaf));
                        }
                        if let Some(cmp::Reverse(leaf)) = self.pending_leafs.pop() {
                            return Some((&leaf.key, &leaf.value));
                        }
                        break;
                    }
                    Some(TypedNode::Interim(interim)) => {
                        self.node_stack.push(interim.iter());
                        break;
                    }
                    Some(TypedNode::Combined(interim, leaf)) => {
                        // next interim can be combined node
                        e = Some(interim);
                        if self.range.contains(&leaf.key) {
                            self.pending_leafs.push(std::cmp::Reverse(leaf));
                        }
                    }
                    None => {
                        self.node_stack.pop().unwrap();
                        break;
                    }
                }
            }
        }

        self.pending_leafs
            .pop()
            .map(|leaf| (&leaf.0.key, &leaf.0.value))
    }
}

#[cfg(test)]
mod tests {
    use crate::keys::ByteString;
    use crate::Art;
    use rand::prelude::SliceRandom;
    use rand::{thread_rng, Rng};
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
    fn scan_with_long_prefix() {
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

        let mut sorted: Vec<String> = existing.iter().map(|v| v.clone()).collect();
        sorted.sort();

        assert_eq!(
            sorted,
            art.iter().map(|(k, v)| v.clone()).collect::<Vec<String>>()
        );

        // for key in sorted {
        //     assert!(
        //         matches!(art.remove(&ByteString::new(key.as_bytes())), Some(val) if val == key),
        //         "{}",
        //         key
        //     );
        //     assert!(matches!(art.get(&ByteString::new(key.as_bytes())), None));
        // }
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
