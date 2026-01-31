# nd-libr

A Rust general-facilities library

## Features

### Ops

Traits `ndlib::ops::Ops` and `ndlib::ops::OpsAssign` describe all standard Rust operations for types and auto-implemented for every applicable type.

```rust
/// T supports all binary `std::ops::*` by value
fn add_mul<T: Ops>(a: T, b: T, c: T) -> T {
    (a + b) * c
}

/// T supports all binary `std::ops::*` by value and by reference
fn add_mul_ref<T: Ops>(a: &T, b: &T, c: &T) -> T
where
    for<'s> &'s T: Ops<T>,
{
    &(a + b) * c
}

/// T supports all binary `std::ops::*` by value and by reference
/// T supports all mutable `std::ops::*` by value and by reference
fn add_mul_mut<T>(x: &mut T, a: &T, b: &T, c: &T)
where
    for<'s> T: Ops + OpsAssign + OpsAssign<&'s T>,
    for<'s> &'s T: Ops<T>,
{
    *x += a;
    *x += b;
    *x *= c;
}
```

### Ops Generation

Macroses `ndproc::ops_impl` and `ndproc::ops_impl_auto` implement all standard Rust operations for types.

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct A<N>(N);

/// Implements `std::ops::Neg` and `std::ops::Not` for A<N>
/// Condition: N is Neg and Not
/// Condition: N ref is Neg and Not
/// Note: asterisk in `*op` specifies implementation by value and by reference
ops_impl!(@un <N: Clone + Copy + Neg<Output = N> + Not<Output = N>> where
    for<'s> &'s N: Neg<Output = N> + Not<Output = N>
    |*op: &A<N>| -> A::<N>,
    - A::<N>(-op.0),
    ! A::<N>(!op.0));

/// Implements `std::ops::Add`, `std::ops::Sub`, `std::ops::Mul`, `std::ops::Div`, `std::ops::Rem` for A<N>
/// Condition: N is Ops
/// Condition: N ref is Ops<N>
/// Note: asterisk in `*a` and `*b` specifies implementation by value and by reference
ops_impl!(@bin <N: Clone + Copy + Ops> where for<'s> &'s N: Ops<N>
    |*a: &A<N>, *b: &A<N>| -> A::<N>,
    + A::<N>(a.0 + b.0),
    - A::<N>(a.0 - b.0),
    * A::<N>(a.0 * b.0),
    / A::<N>(a.0 / b.0),
    % A::<N>(a.0 % b.0));
```

### Forward Generation

Macroses `ndproc::forward_std`, `ndproc::forward_cmp` and `ndproc::forward_fmt` conditionally implement standard Rust traits by forwarding to `expr`.

- `forward_std`: Implements `Deref`, `DerefMut`, `AsRef`, `AsMut`, `FromIterator` (requires `From<T>`)
- `forward_cmp`: Implements `PartialEq`, `PartialOrd`, `Eq`, `Ord`
- `forward_fmt`: Implements `Display`, `Binary`, `Octal`, `LowerHex`, `UpperHex`

```rust
#[forward_std(self.0 with T)]
#[forward_cmp(self.0 with T)]
#[forward_fmt(self.0 with T)]
#[derive(Debug, Default, Clone, Copy)]
pub struct A<T>(pub T);

impl<T> From<T> for A<T> {
    fn from(value: T) -> Self {
        A(value)
    }
}
```

Macroses `ndproc::forward_decl` and `ndproc::forward_def` conditionally implement user-defined traits by forwarding to inner field.

- `forward_decl`: Used on user-defined trait to generate forwarding
- `forward_def`: Used on user-defined structs, enums, unions to generate forwarding implementation

Macroses `ndproc::forward_into`, `ndproc::forward_self` and `ndproc::forward_with` specify forwarding result expression.

- Raw: returns raw result
- `forward_into`: returns `expr.call().into()`. Useful for `fn() -> Self`
- `forward_self`: returns `expr.call(); expr`. Useful for `fn() -> &mut Self`
- `forward_with`: returns `(closure)(expr.call())`. Useful for `fn() -> (Self, Self)`

```rust
#[forward_def(self.0 with Impl: crate::X)]
struct A(Impl);

struct Impl(i32);

#[forward_decl]
trait X {
    fn op(x: usize) -> usize;
}

impl X for Impl {
    fn op(x: usize) -> usize {
        x * x
    }
}
```

### Long Numbers

Types `ndlib::long::Signed`, `ndlib::long::Unsigned` and `ndlib::long::Bytes` specify long-numbers and long-bytes of fixed length, specified in native words. By default, all representations are little-endian.

```rust
let word = std::mem::size_of::<usize>();

assert_eq!(std::mem::size_of::<Signed<8>>(), 8 * word);
assert_eq!(std::mem::size_of::<Unsigned<8>>(), 8 * word);
assert_eq!(std::mem::size_of::<Bytes<8>>(), 8 * word);
```

Aliases `S256`, `S512`, `U256`, `U512`, `B256`, `B512` and others specify long-numbers and long-bytes of at least specified length.

```rust
let word = std::mem::size_of::<usize>();

assert_eq!(std::mem::size_of::<S8>(), 8.div_ceil(word) * word);
assert_eq!(std::mem::size_of::<U8>(), 8.div_ceil(word) * word);
assert_eq!(std::mem::size_of::<B8>(), 8.div_ceil(word) * word);

assert_eq!(std::mem::size_of::<S16>(), 16.div_ceil(word) * word);
assert_eq!(std::mem::size_of::<U16>(), 16.div_ceil(word) * word);
assert_eq!(std::mem::size_of::<B16>(), 16.div_ceil(word) * word);
```

Types and aliases can be used with `ndlib::num::Width` and `ndlib::num::Modular` [types](#composable-types) for precise control.

#### API (Compile-time)

- `from_i8`, `from_i16`, `from_i32`, `from_i64`, `from_i128`, `from_isize` - conversions from signed primitives (`Signed`)
- `from_u8`, `from_u16`, `from_u32`, `from_u64`, `from_u128`, `from_usize` - conversions from unsigned primitives (`Unsigned`, `Bytes`)
- `from_bytes` - conversion from bytes slice (`Signed`, `Unsigned`, `Bytes`)

#### API (Conversions)

- `From::from` - conversions from primitives (**overflow is wrapped**)
  - Signed primitives (`Signed`)
  - Unsigned primitives (`Unsigned`, `Bytes`)
  - Booleans (`Signed`, `Unsigned`, `Bytes`)
- `NdFrom::nd_from` - [conversions](#conversions) from arrays and slices (**overflow is wrapped**)
  - Supported types: arrays and slices of unsigned primitives up-to native word size
- `NdTryFrom::nd_try_from` - [conversions](#conversions) from arrays and slices (**overflow is checked**)
  - Supported types: arrays and slices of unsigned primitives up-to native word size
- `FromIterator::from_iter` - conversion from iterators (**overflow is wrapped**)
  - Supported types: iters of unsigned primitives up-to native word size
- `FromStr::from_str` - conversions from string slices (**overflow is checked**)
  - Without-prefix - dec interpretation
  - `0b`/`0B`-prefix - bin interpretation
  - `0o`/`0O`-prefix - oct interpretation
  - `0x`/`0X`-prefix - hex interpretation (case-insensitive)
- `AsRef<[W]>` - conversion to ref slice of unsigned primitives up-to native word size
- `AsMut<[W]>` - conversion to mut slice of unsigned primitives up-to native word size
- `Display`, `Binary`, `Octal`, `LowerHex`, `UpperHex` - conversions to string
  - `Display` as dec for `Signed`, `Unsigned`
  - `Display` as hex for `Bytes`

#### API (Conversions Extra Impl)

Types `ndlib::long::ExpImpl` and `ndlib::long::RadixImpl` specify implementation for conversion from/to/into digits.

- `ExpImpl` - specifies digits radix as `1 << exp`
- `RadixImpl` - specifies digits radix as raw

#### API (Conversions Extra)

- `FromDigits::from_digits` - conversion from digits (as slice) of arbitrary radix/exp
  - For `RadixImpl`, with radix being power of 2, exp implementation is automatically used
  - Supported types: slices of unsigned primitives up-to native word size
- `FromDigitsIter::from_digits_iter` - conversion from digits (as iter) of arbitrary radix/exp
  - For `RadixImpl`, with radix being power of 2, exp implementation is automatically used
  - Supported types: iters of unsigned primitives up-to native word size
- `ToDigits::to_digits` - conversion to digits vec of arbitrary exp
- `ToDigitsIter::to_digits_iter` - conversion to digits iter of arbitrary exp
- `IntoDigits::into_digits` - conversion into digits vec of arbitrary radix
- `IntoDigitsIter::into_digits_iter` - conversion into digits iter of arbitrary radix

```rust
let s1024exp   = S1024::from_digits(&[1, 3, 3, 7], ExpImpl { exp: 3u8 })?;     // Value: (1 * 2^0) + (3 * 2^3) + (3 * 2^6) + (7 * 2^9)
let u1024exp   = U1024::from_digits(&[1, 3, 3, 7], ExpImpl { exp: 3u8 })?;     // Value: (1 * 2^0) + (3 * 2^3) + (3 * 2^6) + (7 * 2^9)
let s1024radix = S1024::from_digits(&[1, 3, 3, 7], RadixImpl { radix: 9u8 })?; // Value: (1 * 9^0) + (3 * 9^1) + (3 * 9^2) + (7 * 9^3)
let u1024radix = U1024::from_digits(&[1, 3, 3, 7], RadixImpl { radix: 9u8 })?; // Value: (1 * 9^0) + (3 * 9^1) + (3 * 9^2) + (7 * 9^3)

let s1024v = s1024exp.to_digits(ExpImpl { exp: 3u8 })?;      // Vec:  [1, 3, 3, 7]
let u1024v = u1024exp.to_digits(ExpImpl { exp: 3u8 })?;      // Vec:  [1, 3, 3, 7]
let s1024i = s1024exp.to_digits_iter(ExpImpl { exp: 3u8 })?; // Iter: [1, 3, 3, 7]
let u1024i = u1024exp.to_digits_iter(ExpImpl { exp: 3u8 })?; // Iter: [1, 3, 3, 7]

let s1024v = s1024radix.into_digits(RadixImpl { radix: 9u8 })?;    // Vec:  [1, 3, 3, 7]
let u1024v = u1024radix.into_digits(RadixImpl { radix: 9u8 })?;    // Vec:  [1, 3, 3, 7]
let s1024i = s1024radix.into_digits_iter(RadixImpl { exp: 9u8 })?; // Iter: [1, 3, 3, 7]
let u1024i = u1024radix.into_digits_iter(RadixImpl { exp: 9u8 })?; // Iter: [1, 3, 3, 7]
```

#### API (Eq/Cmp)

- `PartialEq`, `Eq` - const-time eq (`Signed`, `Unsigned`, `Bytes`)
- `PartialOrd`, `Ord` - const-time cmp (`Signed`, `Unsigned`)

#### API (Ops)

Types `ndlib::num::Signed`, `ndlib::num::Unsigned` and `ndlib::num::Bytes` implement all[^1] standard Rust operations in const-time (**overflow is wrapped**).

- `Signed`: all unary/binary/mutable operations with `Signed` and all signed primitives
- `Unsigned`: all unary/binary/mutable operaions with `Unsigned` and all unsigned primitives
- `Bytes`: all unary/binary/mutable operations with `Bytes` and all unsigned primitives
- All operations are implemented for all combinations of value/reference types

Operations with primitive support:

- Primitive as Rhs - all operations
- Primitive as Lhs - add and mul operations

[^1]: Type `Bytes` implements only operations with bitwise/shift semantics

### Prime Numbers

```rust

```

### Composable Types

Type `ndlib::arch::Aligned` aligns according to approximate target cacheline size and forwards implementation for most of standard Rust traits.

- `x86`: 64 bytes
- `x86_64`: 64 bytes
- `arm`: 64 bytes
- `aarch64`: 128 bytes

Types `ndlib::num::Width` and `ndlib::num::Modular` specifies numbers and forwards implementation for most of standard Rust traits.

- `Width<N, BITS>`: number `N` width `BITS`
- `Modular<N, M>`: number `N` modulo `M::MOD`

```rust
let s1337 = Width::<S1536, 1337>::default(); // Signed of length 1337-bits and statically allocated size of at least 1536-bits
let u1337 = Width::<U1536, 1337>::default(); // Unsigned of length 1337-bits and statically allocated size of at least 1536-bits
let b1337 = Width::<B1536, 1337>::default(); // Bytes of length 1337-bits and statically allocated size of at least 1536-bits
```

### Conversions

Traits `ndlib::NdFrom` and `ndlib::NdTryFrom` describes conversion from types.

- Like `std::convert::From` and `std::convert::TryFrom`, they can be used for conversion
- Unlike `std::convert::From` and `std::convert::TryFrom`, they can be used [simultaneously](https://github.com/rust-lang/rust/issues/50133)

Relations:

- `From` does auto-implement `NdFrom`
- `TryFrom` does auto-implement `NdTryFrom`
- `From` does auto-implement `TryFrom`
- `NdFrom` does **not** auto-implement `NdTryFrom`

## Dev Requirements

- [Cargo Asm](https://github.com/pacak/cargo-show-asm) (`cargo asm`/`optional`)

## Dev Commands

### Clone

```shell
git clone https://github.com/godilov/nd-libr.git
```

### Build

Compiles `ndcli`/`ndlib`/`ndproc` packages

```shell
cargo build
```

### Verify

Executes all tests to verify correctness

```shell
cargo test
```

Executes all benches to verify performance (report: `target/criterion/report/index.html`)

```shell
cargo bench
```

Emits Assembly for functions in `ndlib` package. `asm` submodules contain monomorphized versions for generics

```shell
cargo asm -p ndlib --lib
```

### Execute

Calculates primes by count - first 256

```shell
cargo run -- primes by-count 256
```

Calculates primes by limit - up-to 256

```shell
cargo run -- primes by-limit 256
```
