#![doc = include_str!("../README.md")]

#[cfg(feature = "core")]
pub use ndcore::{convert, iter, ops};
#[cfg(feature = "mem")]
pub use ndmem as mem;
#[cfg(feature = "num")]
pub use ndnum as num;
