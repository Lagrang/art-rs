[![Crate](https://img.shields.io/crates/v/art-tree.svg)](https://crates.io/crates/art-tree)
[![API](https://docs.rs/art-tree/badge.svg)](https://docs.rs/art-tree)

# The Adaptive Radix Tree
The radix tree based on [The Adaptive Radix Tree:
ARTful Indexing for Main-Memory Databases](https://15721.courses.cs.cmu.edu/spring2016/papers/leis-icde2013.pdf)
paper.

 ```
 use art_tree::ByteString;
 use art_tree::Art;

 let mut art = Art::<ByteString, u16>::new();
 for i in 0..u8::MAX as u16 {
     assert!(art.insert(ByteString::from(i), i), "{}", i);
     assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &i));
 }

 for i in 0..u8::MAX as u16 {
     art.upsert(ByteString::from(i), i + 1);
     assert!(matches!(art.get(&ByteString::from(i)), Some(val) if val == &(i + 1)));
 }

 assert_eq!(art.range(ByteString::from(0u16)..=ByteString::from(140u16)).count(), 141);
 assert_eq!(art.iter().count(), u8::MAX as usize);

 for i in 0..u8::MAX as u16 {
     assert!(matches!(art.remove(&ByteString::from(i)), Some(val) if val == i + 1));
 }
 ```