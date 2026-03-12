#![doc = include_str!("../README.md")]

#[cfg(feature = "core")]
#[doc(inline)]
pub use ndcore::{convert, iter, ops};
#[cfg(feature = "mem")]
#[doc(inline)]
pub use ndmem as mem;
#[cfg(feature = "num")]
#[doc(inline)]
pub use ndnum as num;
