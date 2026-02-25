#![allow(unsafe_code)]

use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum MemoryError {}

pub trait Memory: Sized {
    fn alloc() -> Result<Self, MemoryError>;
}

pub trait MemoryDyn: Sized {
    fn alloc(len: usize) -> Result<Self, MemoryError>;
}
