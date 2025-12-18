use crate::long::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Bytes<const L: usize>(pub [Single; L]);
