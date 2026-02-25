#![allow(unsafe_code)]

use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum MemoryError {}

pub trait Memory {
    fn alloc() -> Result<(), MemoryError>;
}

pub trait MemoryDyn {
    fn alloc() -> Result<(), MemoryError>;
}
