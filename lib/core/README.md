# NdCore

**Rust std-extenions library**

The crate provides special-case extensions for standard Rust library.

- [Iter](#iter) - extends standard iterators.
- [Convert](#convert) - extends standard converts.
- [Ops](#ops) - extends standard operations.

## Start

```toml
[dependencies]
ndcore = "*"
```

## Features

### Iter

`ndcore::iter::*` provides [`IteratorExt`](crate::iter::IteratorExt) that auto-implemented for every [`Iterator`] and contains:

- `iter.collect_with()` - collects iterator with pre-allocated collection by value.
- `iter.collect_with_mut()` - collect iterator with pre-allocated collection by mutable reference.

**Comparison**:

- `iter.collect()` is general-case and allows to collect iterators of any size.
- `iter.collect_with(_mut)()` is special-case and allows **not** to collect iterators of any size.

Instead, they require pre-allocated collection that is used as destination for iterator values.
It runs until either **iterator** or **collection** is over and allows to collect with **static arrays**.

#### Example

```rust
use ndcore::iter::IteratorExt;

let vec = (0..=u8::MAX).into_iter().collect::<Vec<u8>>();                   // Collects all values into Vec<u8> of size 1 << 8
let vec = (0..=u8::MAX).into_iter().collect_with(vec![0; 1usize << 12]);    // Collects all values into Vec<u8> of size 1 << 12
let vec = (0..=u8::MAX).into_iter().collect_with(vec![0; 1usize << 8]);     // Collects all values into Vec<u8> of size 1 << 8
let vec = (0..=u8::MAX).into_iter().collect_with(vec![0; 1usize << 4]);     // Collects  16 values into Vec<u8> of size 1 << 4
let arr = (0..=u8::MAX).into_iter().collect_with([0; 1usize << 8]);         // Collects all values into [u8; 1 << 8]
let arr = (0..=u8::MAX).into_iter().collect_with([0; 1usize << 4]);         // Collects  16 values into [u8; 1 << 4]
```

### Convert

`ndcore::convert::*` provides `NdFrom` and `NdTryFrom`.

- Like `std::convert::*`, they can be used to describe conversion.
- Unlike `std::convert::*`, they can be used **[simultaneously](https://github.com/rust-lang/rust/issues/50133)**.

**Relations**:

- `From` does auto-implement `NdFrom`
- `TryFrom` does auto-implement `NdTryFrom`
- `From` does auto-implement `TryFrom`
- `NdFrom` does **not** auto-implement `NdTryFrom`

### Ops

`ndcore::ops::*` provides all operation-related traits like `std::ops::{Add, Sub, ...}` but in different form.

- Like `std::ops::*`, they can be used to describe operations.
- Unlike `std::ops::*`, they define **reference-only** arguments only.
- Unlike `std::ops::*`, they define implementation on **any** type.

It allows to use them efficiently in generics and traits context without [Higher-Rank Trait Bounds](https://doc.rust-lang.org/nomicon/hrtb.html) and expensive cloning.
They are also implemented for all standard Rust types and operations over them.

`ndcore::ops::*` also provides convenience traits for describing types that support all standard Rust operations of `Std-kind` or `Nd-kind`.

- `ndcore::ops::Ops` - all binary ops of `Std-kind`
- `ndcore::ops::NdOps` - all binary ops of `Nd-kind`
- `ndcore::ops::OpsAssign` - all assign ops of `Std-kind`
- `ndcore::ops::NdOpsAssign` - all assign ops of `Nd-kind`
