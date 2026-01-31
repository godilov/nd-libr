# nd-libr

A Rust general-facilities library

## Features

### Ops

Traits `ndlibr::ops::Ops` and `ndlibr::ops::OpsAssign` describes all standard Rust operations for types and auto-implemented for every applicable type.

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

Macroses `ndproc::ops_impl` and `ndproc::ops_impl_auto` implements all standard Rust operations for types.

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

Macroses `ndproc::forward_std`, `ndproc::forward_cmp` and `ndproc::forward_fmt` conditionally implements standard Rust traits by forwarding to `expr`.

- `forward_std`: Implements `Deref`, `DerefMut`, `AsRef`, `AsMut`, `FromIterator`, requires `From<T>`
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

Macroses `ndproc::forward_decl` and `ndproc::forward_def` conditionally implements user-defined traits by forwarding to inner field.

- `forward_decl`: Used on user-defined trait to generate forwarding
- `forward_def`: Used on user-defined structs, enums, unions to generate forwarding implementation

Macroses `ndproc::forward_into`, `ndproc::forward_self` and `ndproc::forward_with` specifies forwarding result expression.

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

Types `ndlib::long::Signed`, `ndlib::long::Unsigned` and `ndlib::long::Bytes` specifies long-numbers and long-bytes of fixed length, specified in native words.

```rust
let word = std::mem::size_of::<usize>();

assert_eq!(std::mem::size_of::<Signed<8>>(), 8 * word);
assert_eq!(std::mem::size_of::<Unsigned<8>>(), 8 * word);
assert_eq!(std::mem::size_of::<Bytes<8>>(), 8 * word);
```

Aliases `S256`, `S512`, `U256`, `U512`, `B256`, `B512` and others specifies long-numbers and long-bytes of at least specified length.

```rust
let word = std::mem::size_of::<usize>();

assert_eq!(std::mem::size_of::<S8>(), 8.div_ceil(word) * word);
assert_eq!(std::mem::size_of::<U8>(), 8.div_ceil(word) * word);
assert_eq!(std::mem::size_of::<B8>(), 8.div_ceil(word) * word);

assert_eq!(std::mem::size_of::<S16>(), 16.div_ceil(word) * word);
assert_eq!(std::mem::size_of::<U16>(), 16.div_ceil(word) * word);
assert_eq!(std::mem::size_of::<B16>(), 16.div_ceil(word) * word);
```

Types and aliases can be used with `ndlibr::num::Width` and `ndlibr::num::Modular` [types](#composable-types) for precise control.

#### Interface

- `Signed`: `from_i8`, `from_i16`, `from_i32`, `from_i64`, `from_i128`, `from_isize` - compile-time constructors from signed integers
- `Unsigned`: `from_u8`, `from_u16`, `from_u32`, `from_u64`, `from_u128`, `from_usize` - compile-time constructors from unsigned integers
- `Bytes`: `from_u8`, `from_u16`, `from_u32`, `from_u64`, `from_u128`, `from_usize` - compile-time constructors from unsigned integers

### Prime Numbers

```rust

```

### Composable Types

Type `ndlibr::arch::Aligned` aligns according to approximate target cacheline size and forwards implementation for most of standard Rust traits.

- `x86`: 64 bytes
- `x86_64`: 64 bytes
- `arm`: 64 bytes
- `aarch64`: 128 bytes

Types `ndlibr::num::Width` and `ndlibr::num::Modular` specifies numbers and forwards implementation for most of standard Rust traits.

- `Width<N, BITS>`: number `N` width `BITS`
- `Modular<N, M>`: number `N` modulo `M::MOD`

```rust
let s1337 = Width<S1536, 1337>::default(); // Signed of length 1337-bits and allocated size of at least 1536-bits
let u1337 = Width<U1536, 1337>::default(); // Unsigned of length 1337-bits and allocated size of at least 1536-bits
let b1337 = Width<B1536, 1337>::default(); // Bytes of length 1337-bits and allocated size of at least 1536-bits
```

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
