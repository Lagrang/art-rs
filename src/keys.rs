use crate::Key;

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
