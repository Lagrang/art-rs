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
        while let Some(node) = self.node_stack.last_mut() {
            match node.next() {
                Some(TypedNode::Leaf(leaf)) => {
                    if self.range.contains(&leaf.key) {
                        self.pending_leafs.push(std::cmp::Reverse(leaf));
                    }
                    if let Some(cmp::Reverse(leaf)) = self.pending_leafs.pop() {
                        return Some((&leaf.key, &leaf.value));
                    }
                    //TODO: we outside of range, think how to stop scanner
                }
                Some(TypedNode::Interim(interim)) => {
                    self.node_stack.push(interim.iter());
                }
                Some(TypedNode::Combined(interim, leaf)) => {
                    self.node_stack.push(interim.as_interim().iter());
                    if self.range.contains(&leaf.key) {
                        self.pending_leafs.push(std::cmp::Reverse(leaf));
                    }
                }
                None => {
                    self.node_stack.pop().unwrap();
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

    #[test]
    fn iter_on_sequential_keys() {
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
            println!("{}", expected);
            for (k, v) in art.iter() {
                assert_eq!(&ByteString::from(expected), k, "{}", expected);
                assert_eq!(&expected.to_string(), v);
                expected += 1;
                len += 1;
            }
            assert_eq!(len, end - start + 1);
        }
    }
}
