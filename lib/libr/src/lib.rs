#![doc = include_str!("../README.md")]

#[cfg(feature = "core")]
#[doc(inline)]
pub use ndext as ext;
#[cfg(feature = "crypto")]
#[doc(inline)]
pub use ndcrypto as crypto;
#[cfg(feature = "mem")]
#[doc(inline)]
pub use ndmem as mem;
#[cfg(feature = "num")]
#[doc(inline)]
pub use ndnum as num;
