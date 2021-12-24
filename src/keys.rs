use std::cmp::Ordering;
use std::mem;

/// Trait represent [Art] key.
/// Trait define method which convert key into byte comparable sequence. This sequence will be
/// used to order keys inside tree. [Art] crate has several implementation of [Key] trait inside
/// `keys` module.
pub trait Key {
    /// Converts key to byte comparable sequence. This sequence used to represent key inside
    /// [Art] tree.
    fn to_bytes(&self) -> Vec<u8>;
}

/// Implementation of [Key] which can represent basic primitive Rust types(`u32`, `&[u8]`, etc) as
/// byte comparable sequence.
#[derive(Clone, PartialOrd, Ord, Debug)]
#[repr(transparent)]
pub struct ByteString {
    bytes: Vec<u8>,
}

impl ByteString {
    pub fn new(bytes: &[u8]) -> Self {
        Self {
            bytes: bytes.to_vec(),
        }
    }
}

impl Key for ByteString {
    fn to_bytes(&self) -> Vec<u8> {
        self.bytes.clone()
    }
}

impl Eq for ByteString {}

impl PartialEq for ByteString {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl Key for u8 {
    fn to_bytes(&self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }
}

impl Key for u16 {
    fn to_bytes(&self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }
}

impl Key for u32 {
    fn to_bytes(&self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }
}

impl Key for u64 {
    fn to_bytes(&self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }
}

impl Key for u128 {
    fn to_bytes(&self) -> Vec<u8> {
        self.to_be_bytes().to_vec()
    }
}

impl Key for i8 {
    fn to_bytes(&self) -> Vec<u8> {
        // flip upper bit of signed value to get comparable byte sequence:
        // -128 => 0
        // -127 => 1
        // 0 => 128
        // 1 => 129
        // 127 => 255
        let v: u8 = unsafe { mem::transmute(*self) };
        // flip upper bit and set to 0 other bits:
        // (0000_1100 ^ 1000_0000) & 1000_0000 = 1000_0000
        // (1000_1100 ^ 1000_0000) & 1000_0000 = 0000_0000
        let i = (v ^ 0x80) & 0x80;
        // repair bits(except upper bit) of value:
        // self = -127
        // i = 0 (0b0000_0000)
        // v = 129 (0b1000_0001)
        // j = 0b0000_0000 | (0b1000_0001 & 0b0111_1111) = 0b0000_0000 | 0b0000_0001 = 0b0000_0001 = 1
        let j = i | (v & 0x7F);
        j.to_be_bytes().to_vec()
    }
}

impl Key for i16 {
    fn to_bytes(&self) -> Vec<u8> {
        let v: u16 = unsafe { mem::transmute(*self) };
        let xor = 1 << 15;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u16::MAX >> 1));
        j.to_be_bytes().to_vec()
    }
}

impl Key for i32 {
    fn to_bytes(&self) -> Vec<u8> {
        let v: u32 = unsafe { mem::transmute(*self) };
        let xor = 1 << 31;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u32::MAX >> 1));
        j.to_be_bytes().to_vec()
    }
}

impl Key for i64 {
    fn to_bytes(&self) -> Vec<u8> {
        let v: u64 = unsafe { mem::transmute(*self) };
        let xor = 1 << 63;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u64::MAX >> 1));
        j.to_be_bytes().to_vec()
    }
}

impl Key for i128 {
    fn to_bytes(&self) -> Vec<u8> {
        let v: u128 = unsafe { mem::transmute(*self) };
        let xor = 1 << 127;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u128::MAX >> 1));
        j.to_be_bytes().to_vec()
    }
}

#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Float32 {
    key: [u8; 4],
}

impl Eq for Float32 {}

impl PartialEq<Float32> for Float32 {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Ord for Float32 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd<Float32> for Float32 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.key.cmp(&other.key))
    }
}

impl From<f32> for Float32 {
    fn from(v: f32) -> Self {
        assert!(v.is_normal());
        let v: u32 = v.to_bits();
        let xor = 1 << 31;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u32::MAX >> 1));
        Self {
            key: j.to_be_bytes(),
        }
    }
}

#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Float64 {
    key: [u8; 8],
}

impl Eq for Float64 {}

impl PartialEq<Float64> for Float64 {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Ord for Float64 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PartialOrd<Float64> for Float64 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.key.cmp(&other.key))
    }
}

impl From<f64> for Float64 {
    fn from(v: f64) -> Self {
        assert!(v.is_normal());
        let v: u64 = v.to_bits();
        let xor = 1 << 63;
        let i = (v ^ xor) & xor;
        let j = i | (v & (u64::MAX >> 1));
        Self {
            key: j.to_be_bytes(),
        }
    }
}

impl Key for Float32 {
    fn to_bytes(&self) -> Vec<u8> {
        self.key.to_vec()
    }
}

impl Key for Float64 {
    fn to_bytes(&self) -> Vec<u8> {
        self.key.to_vec()
    }
}

/// Builder to create keys based on several other keys.
/// For instance, we have a structure:
/// ```
/// struct MyStruct(u8, String, u32, Box<f64>);
/// ```
/// and we want to store this structure inside [Art](crate::Art) tree. This structure can identified
/// by first 2 fields: `(u8, String)`. We can create compound key based on them and use it as
/// tree key.
/// ```
/// use art_tree::Art;
///
/// struct MyStruct(u8, String, u32, Box<f64>);
///
/// let mut art = Art::new();
/// let key = KeyBuilder::new().append(1).append("abc".to_string()).build();
/// let val = MyStruct(1, "abc".to_string(), 200, Box::new(0.1));
/// assert!(art.insert(key.clone(), val));
/// assert!(art.get(&key).is_some());
/// ```
#[repr(transparent)]
pub struct KeyBuilder {
    key: ByteString,
}

impl KeyBuilder {
    pub fn new() -> Self {
        Self {
            key: ByteString { bytes: Vec::new() },
        }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            key: ByteString {
                bytes: Vec::with_capacity(cap),
            },
        }
    }

    pub fn append(mut self, key_part: impl Key) -> Self {
        self.key.bytes.append(&mut key_part.to_bytes());
        self
    }

    pub fn build(self) -> ByteString {
        self.key
    }
}
