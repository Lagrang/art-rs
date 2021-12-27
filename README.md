[![Crate](https://img.shields.io/crates/v/art-tree.svg)](https://crates.io/crates/art-tree)
[![API](https://docs.rs/art-tree/badge.svg)](https://docs.rs/art-tree)

# The Adaptive Radix Tree
The radix tree based on [The Adaptive Radix Tree:
ARTful Indexing for Main-Memory Databases](https://15721.courses.cs.cmu.edu/spring2016/papers/leis-icde2013.pdf)
paper.

```rust
use art_tree::ByteString;
use art_tree::KeyBuilder;
use art_tree::Art;

pub fn art_example() {
    let mut art = Art::<u16, u16>::new();
    for i in 0..u8::MAX as u16 {
        assert!(art.insert(i, i), "{}", i);
        assert!(matches!(art.get(&i), Some(val) if val == &i));
    }
    for i in 0..u8::MAX as u16 {
        assert!(matches!(art.remove(&i), Some(val) if val == i));
    }
    let mut art = Art::<ByteString, u16>::new();
    for i in 0..u8::MAX as u16 {
        let key = KeyBuilder::new().append(i).append(ByteString::new("abc".to_string().as_bytes())).build();
        art.upsert(key.clone(), i + 1);
        assert!(matches!(art.get(&key), Some(val) if val == &(i + 1)));
    }
    let from_key = KeyBuilder::new().append(16u16).append(ByteString::new("abc".to_string().as_bytes())).build();
    let until_key = KeyBuilder::new().append(20u16).append(ByteString::new("abc".to_string().as_bytes())).build();
    assert_eq!(art.range(from_key..=until_key).count(), 5);
    assert_eq!(art.iter().count(), u8::MAX as usize);   
}
```