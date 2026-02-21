# NdAssert

**Structured assertions**

The crate allows to define complex and structured assertion cases involving multiple independent arguments in all combinations.

- [`ndassert::check!`]([check]) allows to specify arguments and expressions to assert.
- [`ndassert::range!`]([range]) allows to specify primitive argument range with prime number step.

## Start

```toml
[dependencies]
ndassert = "*"
```

## Syntax

### [`ndassert::check!`]([check])

```text
ndassert::check! { KIND?
    ((ITER_EXPR),*)
    [(CHECK_EXPR),*]
}
```

The macro consists of 3 parts:

- `KIND` - Specifies type of asserts to produce. Values: None/`@eq`/`@ne`.
- `ITER_EXPR` - Expression for corresponding argument, should be iterable.
- `CHECK_EXPR` - Expression for assertions over arguments, should be closure.

`CHECK_EXPR` varies depending on `KIND`:

- For None, it expects expression to return `bool` value and then checks as `assert!`
- For `@eq`, it expectes expression to return `(T, T)` value and then checks as `assert_eq!`
- For `@ne`, it expectes expression to return `(T, T)` value and then checks as `assert_ne!`

Every `assert!` includes associated with failed case information like specific expression and arguments values.

### [`ndassert::range!`]([range])

```text
ndassert::range!(TY, LEN, CLASS?)
```

The macro consists of 3 parts:

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

## Examples

Asserts `verify` for every `value` in `[i16::MIN, ..., i16::MAX]`.

```rust
fn verify(_: i16) -> bool {
    true
}

// Complexity: 2 ^ i16::BITS
ndassert::check! { (
    (i16::MIN..i16::MAX),
) [
    |value: i16| verify(value),
] }
```

Asserts `verify` for every `(lhs, rhs)` in `[i16::MIN, ..., i16::MAX] x [i16::MIN, ..., i16::MAX]`.

```rust
fn verify(_: i16, _: i16) -> bool {
    true
}

// Complexity: 2 * 2 ^ i16::BITS * 2 ^ i16::BITS
ndassert::check! { (
    (i16::MIN..i16::MAX),
    (i16::MIN..i16::MAX),
) [
    |lhs: i16, rhs: i16| verify(lhs, rhs), // Direct
    |lhs: i16, rhs: i16| verify(rhs, lhs), // Inverse
] }
```

Asserts `verify` for every `value` in `i64::MIN + k * PRIME`, where `k > 0`, `PRIME` is `60bit`.

```rust
fn verify(_: i64) -> bool {
    true
}

// Complexity: 2 ^ (i64::BITS - 60)
ndassert::check! { (
    ndassert::range!(i64, 60),
) [
    |value: i64| verify(value),
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
    ndassert::range!(i64, 60),
    ndassert::range!(i64, 60),
) [
    |lhs: i64, rhs: i64| verify(lhs, rhs), // Direct
    |lhs: i64, rhs: i64| verify(rhs, lhs), // Inverse
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
    ndassert::range!(i64, 60, 0),
    ndassert::range!(i64, 60, 1),
) [
    |lhs: i64, rhs: i64| verify(lhs, rhs), // Direct
    |lhs: i64, rhs: i64| verify(rhs, lhs), // Inverse
] }
```
