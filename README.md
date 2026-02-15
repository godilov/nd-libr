# nd-libr

A Rust collection of numerical, cryptography, blockchain and memory-related libraries

## Features

1. [Ops](#ops)
2. [Ops Generation](#ops-generation)
3. [Forward Generation](#forward-generation)
4. [Long Numbers](#long-numbers)
5. [Prime Numbers](#prime-numbers)
6. [Composable Types](#composable-types)
7. [Conversions](#conversions)
8. [EVM ABI](#evm-abi)

### Ops

Traits `ndnum::ops::Ops` (requires `Copy`) and `ndnum::ops::OpsAssign` (requires `Copy`) describe all standard Rust operations for types and auto-implemented for every applicable type.

```rust
/// T supports all binary `std::ops::*`
fn add_mul<T: Ops<Type = T>>(a: T, b: T, c: T) -> T {
    (a + b) * c
}

/// T supports all assign `std::ops::*`
fn add_mul_assign<T: OpsAssign>(x: &mut T, a: T, b: T, c: T) {
    *x += a;
    *x += b;
    *x *= c;
}
```

Traits `ndnum::ops::NdAdd`, `ndnum::ops::NdSub`, etc. and `ndnum::ops::NdAddAssign`, `ndnum::ops::NdSubAssign`, etc. describe all standard Rust operations for types.

- Like `std::ops`, they describe operations
- Unlike `std::ops`, they describe operations with reference operands only
- Unlike `std::ops`, they can be implemented for types and used by reference without [HRTB](https://doc.rust-lang.org/nomicon/hrtb.html)
- Unlike `std::ops`, they can be implemented for types other than `Lhs`, `Rhs` or `Output`

### Ops Generation

Macroses `ndops::all` and `ndops::all_auto` with `@stdun`/`@stdbin`/`@stdmut` implement all specified standard Rust operations from `std::ops::*`.

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct A<N>(N);

/// Implements `std::ops::Neg` and `std::ops::Not` for A<N>
/// Note: asterisk in `*value` specifies implementation by value and by reference
ndops::all!(@stdun <N: Clone + Copy + Neg<Output = N> + Not<Output = N>> (*value: &A<N>) -> A<N>,
    - A::<N>(-value.0),
    ! A::<N>(!value.0));

/// Implements `std::ops::Add`, `std::ops::Sub`, `std::ops::Mul`, `std::ops::Div`, `std::ops::Rem` for A<N>
/// Note: asterisk in `*lhs` and `*rhs` specifies implementation by value and by reference
ndops::all!(@stdbin <N: Ops<Type = N>> (*lhs: &A<N>, *rhs: &A<N>) -> A<N>,
    + A::<N>(lhs.0 + rhs.0),
    - A::<N>(lhs.0 - rhs.0),
    * A::<N>(lhs.0 * rhs.0),
    / A::<N>(lhs.0 / rhs.0),
    % A::<N>(lhs.0 % rhs.0));

/// Implements `std::ops::AddAssign`, `std::ops::SubAssign`, `std::ops::MulAssign`, `std::ops::DivAssign`, `std::ops::RemAssign` for A<N>
/// Note: asterisk in `*rhs` specifies implementation by value and by reference
ndops::all!(@stdmut <N: OpsAssign> (lhs: &mut A<N>, *rhs: &A<N>),
    += { lhs.0 += rhs.0; },
    -= { lhs.0 -= rhs.0; },
    *= { lhs.0 *= rhs.0; },
    /= { lhs.0 /= rhs.0; },
    %= { lhs.0 %= rhs.0; });
```

Macroses `ndops::all` and `ndops::all_auto` with `@ndun`/`@ndbin`/`@ndmut` implement all specified standard Rust operations from `ndnum::ops::*`.

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct A<N>(N);

/// Implements `ndnum::ops::Neg` and `ndnum::ops::Not` for A<N>
ndops::all!(@ndun crate <N: NdNeg<Type = N> + NdNot<Type = N>> (value: &A<N>) -> A<N>,
    - A::<N>(N::neg(&value.0)),
    ! A::<N>(N::not(&value.0)));

/// Implements `ndnum::ops::Add`, `ndnum::ops::Sub`, `ndnum::ops::Mul`, `ndnum::ops::Div`, `ndnum::ops::Rem` for A<N>
ndops::all!(@ndbin crate <N: NdOps<All = N>> (lhs: &A<N>, rhs: &A<N>) -> A<N>,
    + A::<N>(N::add(&lhs.0, &rhs.0)),
    - A::<N>(N::sub(&lhs.0, &rhs.0)),
    * A::<N>(N::mul(&lhs.0, &rhs.0)),
    / A::<N>(N::div(&lhs.0, &rhs.0)),
    % A::<N>(N::rem(&lhs.0, &rhs.0)));

/// Implements `ndnum::ops::AddAssign`, `ndnum::ops::SubAssign`, `ndnum::ops::MulAssign`, `ndnum::ops::DivAssign`, `ndnum::ops::RemAssign` for A<N>
ndops::all!(@ndmut crate <N: NdOpsAssign> (lhs: &mut A<N>, rhs: &A<N>),
    += { N::add_assign(&mut lhs.0, &rhs.0); },
    -= { N::sub_assign(&mut lhs.0, &rhs.0); },
    *= { N::mul_assign(&mut lhs.0, &rhs.0); },
    /= { N::div_assign(&mut lhs.0, &rhs.0); },
    %= { N::rem_assign(&mut lhs.0, &rhs.0); });
```

### Forward Generation

Macroses `ndfwd::std`, `ndfwd::cmp` and `ndfwd::fmt` conditionally implement standard Rust traits by forwarding to `expr`.

- `std`: Implements `Deref`, `DerefMut`, `AsRef`, `AsMut`, `FromIterator` (requires `From<T>`)
- `cmp`: Implements `PartialEq`, `PartialOrd`, `Eq`, `Ord`
- `fmt`: Implements `Display`, `Binary`, `Octal`, `LowerHex`, `UpperHex`

```rust
#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[derive(Debug, Default, Clone, Copy)]
pub struct A<T>(pub T);

impl<T> From<T> for A<T> {
    fn from(value: T) -> Self {
        A(value)
    }
}
```

Macroses `ndfwd::decl` and `ndfwd::def` conditionally implement user-defined traits by forwarding to inner field.

- `decl`: Used on user-defined trait to generate forwarding
- `def`: Used on user-defined structs, enums, unions to generate forwarding implementation

Macroses `ndfwd::as_into`, `ndfwd::as_self` and `ndfwd::as_expr` specify forwarding result expression.

- Raw: returns raw result
- `as_into`: returns `expr.call().into()`. Needed for `fn() -> Self`
- `as_self`: returns `expr.call(); expr`. Needed for `fn() -> &mut Self`
- `as_expr`: returns `(closure)(expr.call())`. Needed for `fn() -> (Self, Self)`

```rust
#[ndfwd::def(self.0 with Impl: crate::X)]
struct A(Impl);

struct Impl(i32);

#[ndfwd::decl]
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

Types `ndnum::long::Signed`, `ndnum::long::Unsigned` and `ndnum::long::Bytes` specify long-numbers and long-bytes of fixed length, specified in native words. By default, all representations are little-endian.

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

Types and aliases can be used with `ndnum::Width` and `ndnum::Modular` [types](#composable-types) for precise control.

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

Types `ndnum::long::ExpImpl` and `ndnum::long::RadixImpl` specify implementation for conversion from/to/into digits.

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
let sexp   = S1024::from_digits(&[1, 3, 3, 7], ExpImpl { exp: 3u8 })?;     // Value: (1 * 2^0) + (3 * 2^3) + (3 * 2^6) + (7 * 2^9)
let uexp   = U1024::from_digits(&[1, 3, 3, 7], ExpImpl { exp: 3u8 })?;     // Value: (1 * 2^0) + (3 * 2^3) + (3 * 2^6) + (7 * 2^9)
let sradix = S1024::from_digits(&[1, 3, 3, 7], RadixImpl { radix: 9u8 })?; // Value: (1 * 9^0) + (3 * 9^1) + (3 * 9^2) + (7 * 9^3)
let uradix = U1024::from_digits(&[1, 3, 3, 7], RadixImpl { radix: 9u8 })?; // Value: (1 * 9^0) + (3 * 9^1) + (3 * 9^2) + (7 * 9^3)

let sv = sexp.to_digits(ExpImpl { exp: 3u8 })?;      // Vec:  [1, 3, 3, 7]
let uv = uexp.to_digits(ExpImpl { exp: 3u8 })?;      // Vec:  [1, 3, 3, 7]
let si = sexp.to_digits_iter(ExpImpl { exp: 3u8 })?; // Iter: [1, 3, 3, 7]
let ui = uexp.to_digits_iter(ExpImpl { exp: 3u8 })?; // Iter: [1, 3, 3, 7]

let sv = sradix.into_digits(RadixImpl { radix: 9u8 })?;    // Vec:  [1, 3, 3, 7]
let uv = uradix.into_digits(RadixImpl { radix: 9u8 })?;    // Vec:  [1, 3, 3, 7]
let si = sradix.into_digits_iter(RadixImpl { exp: 9u8 })?; // Iter: [1, 3, 3, 7]
let ui = uradix.into_digits_iter(RadixImpl { exp: 9u8 })?; // Iter: [1, 3, 3, 7]
```

#### API (Comparison)

- `PartialEq`, `Eq` - naive eq (`Signed`, `Unsigned`, `Bytes`)
- `PartialOrd`, `Ord` - naive cmp (`Signed`, `Unsigned`)
- `eq_ct` - const-time equality comparison (`Signed`, `Unsigned`, `Bytes`)
- `lt_ct` - const-time less-then comparison (`Signed`, `Unsigned`)
- `gt_ct` - const-time greater-then comparison (`Signed`, `Unsigned`)
- `le_ct` - const-time less-then or equal comparison (`Signed`, `Unsigned`)
- `ge_ct` - const-time greater-then or equal comparison (`Signed`, `Unsigned`)

#### API (Ops)

Types `ndnum::Signed`, `ndnum::Unsigned` and `ndnum::Bytes` implement all[^1] standard Rust operations in const-time (**overflow is wrapped**).

- `Signed`: all unary/binary/mutable operations with `Signed` and all signed primitives
- `Unsigned`: all unary/binary/mutable operaions with `Unsigned` and all unsigned primitives
- `Bytes`: all unary/binary/mutable operations with `Bytes` and all unsigned primitives
- All operations are implemented for all combinations of value/reference types

Operations with primitive support:

- Primitive as Rhs - all operations
- Primitive as Lhs - add and mul operations

[^1]: Type `Bytes` implements only operations with bitwise/shift semantics

### Prime Numbers

Type `ndnum::prime::Primes` is empty and exposes functions to generate prime numbers.

- `Primes::by_count_full` - iterate prime numbers by count (divisibility by prime numbers up to square root)
- `Primes::by_limit_full` - iterate prime numbers by limit (divisibility by prime numbers up to square root)
- `Primes::by_count_fast` - iterate prime numbers by count (Miller-Rabin)
- `Primes::by_limit_fast` - iterate prime numbers by limit (Miller-Rabin)

Traits `ndnum::prime::Primality` and `ndnum::prime::PrimalityExtension` describe prime number container types and facilities.

- `Primality::primes` - prime numbers to check against (Miller-Rabin)
- `Primality::is_prime` - prime numbes check (Miller-Rabin)
- `PrimalityExtension::rand_prime` - generate prime number of binary order
- `PrimalityExtension::rand_primes` - generate prime numbers of binary order and count

### Composable Types

Type `ndnum::arch::Aligned` specifies aligned type according to approximate target cacheline size and forwards implementation for most of standard Rust traits.

Alignment:

- `x86`: 64 bytes
- `x86_64`: 64 bytes
- `arm`: 64 bytes
- `aarch64`: 128 bytes

Forwards:

- `Deref`, `DerefMut`, `AsRef`, `AsMut`, `FromIterator`
- `PartialEq`, `PartialOrd`, `Eq`, `Ord`
- `Display`, `Binary`, `Octal`, `LowerHex`, `UpperHex`
- `Num`, `NumExt`, `Signed`, `Unsigned`
- `ndnum::ops::*` (conditionally)
- `std::ops::*` (conditionally)

Types `ndnum::Width` and `ndnum::Modular` specify numbers and forwards implementation for most of standard Rust traits.

- `Width<N, BITS>`: number `N` width `BITS`
- `Modular<N, M>`: number `N` modulo `M::MOD`

```rust
let s1337 = Width::<S1536, 1337>::default(); // Signed of length 1337-bits and statically allocated size of at least 1536-bits
let u1337 = Width::<U1536, 1337>::default(); // Unsigned of length 1337-bits and statically allocated size of at least 1536-bits
let b1337 = Width::<B1536, 1337>::default(); // Bytes of length 1337-bits and statically allocated size of at least 1536-bits
```

### Conversions

Traits `ndlib::NdFrom` and `ndlib::NdTryFrom` describe conversion from types.

- Like `std::convert::From` and `std::convert::TryFrom`, they can be used for conversion
- Unlike `std::convert::From` and `std::convert::TryFrom`, they can be used [simultaneously](https://github.com/rust-lang/rust/issues/50133)

Relations:

- `From` does auto-implement `NdFrom`
- `TryFrom` does auto-implement `NdTryFrom`
- `From` does auto-implement `TryFrom`
- `NdFrom` does **not** auto-implement `NdTryFrom`

### EVM ABI

Crate `ndevm` defines EVM ABI encoding implementation for all standard Rust types and Alloy primitives.

Trait `ndevm::Abi` describe EVM ABI encoding types.

- `bool`
- `u8`, `u16`, `u32`, `u64`, `u128`, `usize`
- `i8`, `i16`, `i32`, `i64`, `i128`, `isize`
- `&[A; N]`, where `A` implements `Abi`
- `&[A]`, where `A` implements `Abi`
- `str`
- Tuples
- All Alloy Signed primitives up-to `I256`
- All Alloy Unsigned primitives up-to `U256`

Traits `ndevm::Memory` and `ndevm::MemoryDyn` describe static and dynamic memory for encoding and implemented for `[u8; N]` and `Vec<u8>`.

```rust
let arr = ("Hello, EVM ABI Array!", U256::from(1337)).encode_as::<[u8; 1024]>()?;
let vec = ("Hello, EVM ABI Vector!", U256::from(1337)).encode_as_dyn::<Vec<u8>>()?;
```

Types `ndevm::AsBytes`, `ndevm::AsRelative`, `ndevm::AsEncode`, `ndevm::AsEncodePacked` specify encoding effects.

- `AsBytes` - encode with raw bytes
- `AsRelative` - encode with relative offsets
- `AsEncode` - encode with standard encoding (even for packed)
- `AsEncodePacked` - encode with packed encoding (even for standard)

## Dev Requirements

- [Cargo Asm](https://github.com/pacak/cargo-show-asm) (`cargo asm`/`optional`)

## Dev Commands

### Clone

```shell
git clone https://github.com/godilov/nd-libr.git
```

### Build

Compiles `cli`/`lib`/`proc` packages

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

Emits Assembly for functions in `ndnum` package. `asm` submodules contain monomorphized versions for generics

```shell
cargo asm -p ndnum --lib
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
