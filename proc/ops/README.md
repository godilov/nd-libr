# Nd Ops

Zero-boilerplate operator implementation macros for Rust.

`ndops` provides two procedural macros — [`all!`] and [`all_auto!`] — that generate
complete `impl` blocks for the standard [`std::ops`] arithmetic and bitwise traits,
as well as the `ndnum::ops` _nd-style_ operator traits. A single macro invocation
can expand to dozens of `impl` blocks covering every combination of reference and
value operands, letting you focus on the scalar expression rather than the structural
glue.

## Quick start

Add the crate to your `Cargo.toml`:

```toml
[dependencies]
ndops = "*"
```

Then import and use the macros:

```rust
use ndops::{all, all_auto};

#[derive(Clone, Copy)]
struct Meters(f64);

impl From<f64> for Meters {
    fn from(v: f64) -> Self { Meters(v) }
}

// Generate Add / Sub for all four &Meters × &Meters ref-combinations,
// and AddAssign / SubAssign accepting both owned and borrowed rhs.
ndops::all_auto!(@stdbin (*lhs: &Meters, *rhs: &Meters) -> Meters,
    (lhs.0)(rhs.0) [+, -]
);
ndops::all_auto!(@stdmut (lhs: &mut Meters, *rhs: &Meters),
    (lhs.0)(rhs.0) [+=, -=]
);
```

## Macros

### [`all!`] — explicit expressions

```text
ndops::all!(
    @<kind> <signature>,
    <op> <expr> [where [<predicates>]],
    ...
)
```

Every operator entry in the definition list carries its own expression. Use this
macro when the implementation body differs between operators or cannot be derived
mechanically from the operator token.

### [`all_auto!`] — derived expressions

```text
// binary / assign kinds:
ndops::all_auto!(
    @<kind> <signature>,
    (<lhs_expr>) (<rhs_expr>) [<op> [where [<predicates>]], ...]
)

// unary kinds:
ndops::all_auto!(
    @<kind> <signature>,
    (<self_expr>) [<op> [where [<predicates>]], ...]
)
```

You provide the operand sub-expressions once; the macro applies each listed operator
token to them automatically. Individual operators may still carry `where […]`
clauses for per-operator bounds.

## Kinds

Both macros support the same six kinds, selected by an `@` keyword:

| Kind      | Traits generated                         | Valid operators                                      |
| --------- | ---------------------------------------- | ---------------------------------------------------- |
| `@stdmut` | `std::ops::XxxAssign`                    | `+=` `-=` `*=` `/=` `%=` `\|=` `&=` `^=` `<<=` `>>=` |
| `@stdbin` | `std::ops::Xxx`                          | `+` `-` `*` `/` `%` `\|` `&` `^` `<<` `>>`           |
| `@stdun`  | `std::ops::Neg`, `std::ops::Not`         | `-` `!`                                              |
| `@ndmut`  | `ndnum::ops::NdXxxAssign`                | same as `@stdmut`                                    |
| `@ndbin`  | `ndnum::ops::NdXxx`                      | same as `@stdbin`                                    |
| `@ndun`   | `ndnum::ops::NdNeg`, `ndnum::ops::NdNot` | same as `@stdun`                                     |

## Signature reference

### `@stdmut`

```text
[<generics>] [where <clause>] (lhs: &mut LhsTy, [*]rhs: [&]RhsTy)
```

`lhs` must be typed `&mut LhsTy`; the macro derives the implementing type as `LhsTy`.
Placing `*` before `rhs` causes the macro to emit `impl XxxAssign<RhsTy>` _and_
`impl XxxAssign<&RhsTy>` from the same expression. Without `*`, only the form you
declare is emitted.

### `@stdbin`

```text
[<generics>] [where <clause>] ([*]lhs: [&]LhsTy, [*]rhs: [&]RhsTy) -> ResTy
```

`*` on either operand independently expands to both the reference and owned form.
`*lhs: &A` with `*rhs: &B` therefore produces four `impl` blocks — one for every
combination of `A`/`&A` × `B`/`&B`. The expression result is wrapped in
`<ResTy>::from(…)`.

### `@stdun`

```text
[<generics>] [where <clause>] ([*]self: [&]SelfTy) -> ResTy
```

Same `*` semantics as `@stdbin`.

### `@ndmut`

```text
[<generics>] [where <clause>] (lhs: LhsTy, rhs: RhsTy) [for ImplTy | for [ImplTy, ...]]
```

`lhs` and `rhs` become the literal function parameters of the trait method, so you
may use reference patterns (e.g. `lhs: &mut Elem`, `&rhs: &Elem`). The optional
`for` clause selects the implementing type; omitting it defaults to the base type of
`lhs`. `for [A, B, C]` emits a separate `impl` block for each listed type.

### `@ndbin`

```text
[<generics>] [where <clause>] (lhs: LhsTy, rhs: RhsTy) -> ResTy [for ImplTy | for [ImplTy, ...]]
```

Same `for` semantics as `@ndmut`. When `for` is omitted the implementing type
defaults to `ResTy`.

### `@ndun`

```text
[<generics>] [where <clause>] (value: SelfTy) -> ResTy [for ImplTy | for [ImplTy, ...]]
```

## Examples

### Newtype wrapper — all `std::ops` variants

```rust
#[derive(Clone, Copy, PartialEq, Debug)]
struct Px(i32);

impl From<i32> for Px {
    fn from(v: i32) -> Self { Px(v) }
}

// Binary: all four ref-combinations of Px × Px
ndops::all_auto!(@stdbin (*lhs: &Px, *rhs: &Px) -> Px,
    (lhs.0)(rhs.0) [+, -, *, /]
);

// Assign: rhs by reference or by value
ndops::all_auto!(@stdmut (lhs: &mut Px, *rhs: &Px),
    (lhs.0)(rhs.0) [+=, -=, *=, /=]
);

// Unary: both &Px and Px
ndops::all_auto!(@stdun (*value: &Px) -> Px,
    (value.0) [-]
);
```

### Generic newtype

```rust
use std::ops::{Add, Sub, Neg};

#[derive(Clone, Copy)]
struct Wrapper<T>(T);

impl<T: Copy> From<T> for Wrapper<T> {
    fn from(v: T) -> Self { Wrapper(v) }
}

ndops::all_auto!(
    @stdbin
    <T: Copy + Add<Output = T> + Sub<Output = T>>
    (*lhs: &Wrapper<T>, *rhs: &Wrapper<T>) -> Wrapper<T>,
    (lhs.0)(rhs.0) [+, -]
);

ndops::all_auto!(
    @stdun
    <T: Copy + Neg<Output = T>>
    (*value: &Wrapper<T>) -> Wrapper<T>,
    (value.0) [-]
);
```

### Explicit expressions with `all!`

```rust
struct Matrix([[f64; 2]; 2]);

impl From<[[f64; 2]; 2]> for Matrix {
    fn from(v: [[f64; 2]; 2]) -> Self { Matrix(v) }
}

// Custom expression — matrix multiplication differs from element-wise multiply
ndops::all!(@stdbin (*lhs: &Matrix, *rhs: &Matrix) -> Matrix,
    + { Matrix([[lhs.0[0][0] + rhs.0[0][0], lhs.0[0][1] + rhs.0[0][1]],
                [lhs.0[1][0] + rhs.0[1][0], lhs.0[1][1] + rhs.0[1][1]]]) },
    * { Matrix([[lhs.0[0][0] * rhs.0[0][0] + lhs.0[0][1] * rhs.0[1][0],
                 lhs.0[0][0] * rhs.0[0][1] + lhs.0[0][1] * rhs.0[1][1]],
                [lhs.0[1][0] * rhs.0[0][0] + lhs.0[1][1] * rhs.0[1][0],
                 lhs.0[1][0] * rhs.0[0][1] + lhs.0[1][1] * rhs.0[1][1]]]) },
);
```

### nd-style traits with a `for` clause

```rust
struct ArrayOps;

ndops::all_auto!(@ndbin (&lhs: &[f64], &rhs: &[f64]) -> Vec<f64> for ArrayOps,
    (lhs)(rhs) [+, -, *, /]
);

ndops::all_auto!(@ndun (&value: &[f64]) -> Vec<f64> for ArrayOps,
    (value) [-]
);
```

### Per-operator bounds

```rust
ndops::all_auto!(@stdbin (*lhs: &Scalar, *rhs: &Scalar) -> Scalar,
    (lhs.0)(rhs.0) [
        +,
        - where [Scalar: std::fmt::Debug],
    ]
);
```

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT License](LICENSE-MIT) at your option.
