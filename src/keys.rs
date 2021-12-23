use std::mem;

/// Trait represent [Art] key.
/// Trait define method which convert key into byte comparable sequence. This sequence will be
/// used to order keys inside tree. [Art] crate has several implementation of [Key] trait inside
/// `keys` module.
pub trait Key: Eq + Ord {
    /// Converts key to byte comparable sequence. This sequence used to represent key inside
    /// [Art] tree.
    fn to_bytes(&self) -> Vec<u8>;
}

/// Implementation of [Key] which can represent basic primitive Rust types(`u32`, `&[u8]`, etc) as
/// byte comparable sequence.
#[derive(Clone, PartialOrd, Ord, Debug)]
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

impl From<u128> for ByteString {
    fn from(val: u128) -> Self {
        Self {
            bytes: val.to_be_bytes().to_vec(),
        }
    }
}

impl From<u64> for ByteString {
    fn from(val: u64) -> Self {
        Self {
            bytes: val.to_be_bytes().to_vec(),
        }
    }
}

impl From<u32> for ByteString {
    fn from(val: u32) -> Self {
        Self {
            bytes: val.to_be_bytes().to_vec(),
        }
    }
}

impl From<u16> for ByteString {
    fn from(val: u16) -> Self {
        Self {
            bytes: val.to_be_bytes().to_vec(),
        }
    }
}

impl From<u8> for ByteString {
    fn from(val: u8) -> Self {
        Self {
            bytes: val.to_be_bytes().to_vec(),
        }
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
