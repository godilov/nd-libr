# NdAssert

**Structured assertions procedural macros**

The crate allows to define complex and structured assertion cases involving multiple independent arguments in all combinations.

- [`ndassert::check!`](check) generates structured assertions.
- [`ndassert::range!`](range) generates range of primitive type with prime number step.
- [`ndassert::rand!`](range) generates seeded random number generator.
- [`ndassert::prime!`](prime) generates prime number.
- [`ndassert::catch!`](catch) generates prime number.

## Start

```toml
[dependencies]
ndassert = "*"
```

## Syntax

### [`ndassert::check!`](check)

```text
ndassert::check! { KIND?
    ((ARG_EXPR),*)
    [(CHECK_EXPR),*]
}
```

The macro consists of three parts:

- `KIND` - Specifies type of asserts to produce. Values: None/`@eq`/`@ne`.
- `ARG_EXPR` - Expression for assertion argument.
- `CHECK_EXPR` - Expression for assertions check.

`ARG_EXPR` can be in next forms:

- `IDENT in EXPR` for iteration over multiple argument values.
- `IDENT as EXPR` for iteration over single argument value.

`CHECK_EXPR` varies depending on `KIND`:

- For None, it expects expression to return `bool` value and then checks as `assert!`
- For `@eq`, it expectes expression to return `(T, T)` value and then checks as `assert_eq!`
- For `@ne`, it expectes expression to return `(T, T)` value and then checks as `assert_ne!`

Every `assert!` includes associated with failed case information like specific expression, arguments values, asserted values (for `@eq` and `@ne`).

### [`ndassert::range!`](range)

```text
ndassert::range!(TY, LEN, CLASS?)
```

The macro consists of tree parts:

- `TY` - Primitive type of range to produce.
- `LEN` - Length of step in binary. Useful for controlling execution complexity.
  - Should be `4 * N`, where `N in [1; 15]`.
- `CLASS` - Class of step. Useful for controlling relations between arguments ranges.
  - Optional, 0 by default

`LEN` and `CLASS` both determine which `PRIME` step will be applied.
`LEN` defines a `PRIME` step of approximately `LEN` bits length.
`CLASS` defines a distinct congruence class modulo `PRIME` for produced range.

- For the **same** `TY` and the **same** `CLASS`, the range is guaranteed to be the same.
- For the **same** `TY` and the **different** `CLASS`, the range is **not** guaranteed to be the same.

It means that different classes **may** or **may not** produce the same ranges.
`CLASS` is used as index in pre-defined prime number arrays and is taken by modulo.

See [examples](#examples) for more information.

### [`ndassert::range!`](range)

```text
ndassert::rand!(TY, LEN, CLASS?)
```

- `TY` - `rand` type implementing `TY::seed_from_u64()`.

`LEN` and `CLASS` are the same as [`ndassert::range!`](#ndassertrangerange).

### [`ndassert::prime!`](prime)

```text
ndassert::prime!(LEN, CLASS?)
```

`LEN` and `CLASS` are the same as [`ndassert::range!`](#ndassertrangerange).

## Examples

Asserts `verify` for every `value` in `[i16::MIN, ..., i16::MAX]`.

```rust
fn verify(_: i8) -> bool {
    true
}

// Complexity: 2 ^ i8::BITS
ndassert::check! { (value in (i8::MIN..i8::MAX)) [
    verify(value),
] }
```

Asserts `verify` for every `(lhs, rhs)` in `[i16::MIN, ..., i16::MAX] x [i16::MIN, ..., i16::MAX]`.

```rust
fn verify(_: i8, _: i8) -> bool {
    true
}

// Complexity: 2 * 2 ^ i8::BITS * 2 ^ i8::BITS
ndassert::check! { (
    lhs in (i8::MIN..i8::MAX),
    rhs in (i8::MIN..i8::MAX),
) [
    verify(lhs, rhs), // Direct
    verify(rhs, lhs), // Inverse
] }
```

Asserts `verify` for every `value` in `i64::MIN + k * PRIME`, where `k > 0`, `PRIME` is `60bit`.

```rust
fn verify(_: i64) -> bool {
    true
}

// Complexity: 2 ^ (i64::BITS - 60)
ndassert::check! { (value in ndassert::range!(i64, 60)) [
    verify(value),
] }
```

Asserts `verify` for every `(lhs, rhs)`

- `lhs`: `i64::MIN + k * PRIME`, where `k > 0`, `PRIME` is `60bit`.
- `rhs`: `i64::MIN + k * PRIME`, where `k > 0`, `PRIME` is `60bit`.

```rust
fn verify(_: i64, _: i64) -> bool {
    true
}

// Complexity: 2 * 2 ^ (i64::BITS - 60) * 2 ^ (i64::BITS - 60)
ndassert::check! { (
    lhs in ndassert::range!(i64, 60),
    rhs in ndassert::range!(i64, 60),
) [
    verify(lhs, rhs), // Direct
    verify(rhs, lhs), // Inverse
] }
```

Asserts `verify` for every `(lhs, rhs)`:

- `lhs`: `i64::MIN + k * PRIME0`, where `k > 0`, `PRIME0` is `60bit`.
- `rhs`: `i64::MIN + k * PRIME1`, where `k > 0`, `PRIME1` is `60bit`.
- `PRIME0 != PRIME1`

```rust
fn verify(_: i64, _: i64) -> bool {
    true
}

// Complexity: 2 * 2 ^ (i64::BITS - 60) * 2 ^ (i64::BITS - 60)
ndassert::check! { (
    lhs in ndassert::range!(i64, 60, 0),
    rhs in ndassert::range!(i64, 60, 1),
) [
    verify(lhs, rhs), // Direct
    verify(rhs, lhs), // Inverse
] }
```
