Implement one or more operator traits with automatically derived body expressions.

# When to use

Use `all_auto!` when the body of each operator is simply `lhs OP rhs` or `OP self`.
The macro derives the body automatically from the operator symbol; no per-operator
expression is required. When the body is distinct or non-trivial, use [`all!`]
instead.

# Syntax

```text
ndops::all_auto! { @KIND SIGNATURE,
    OPERAND_EXPRS [OP [where [PREDICATE, ...]], ...]
}
```

- **`@KIND`** — selects the trait family and the signature shape.
- **`SIGNATURE`** — operand types with optional generics and `where` clause
  ([kind-specific](#kinds), see reference below).
- **`OPERAND_EXPRS`** — parenthesised Rust expressions spliced verbatim into
  the generated body.
- **`[OP, ...]`** — bracket-delimited operator list. Each entry may be followed
  by `where [P, ...]` to add per-operation predicates.
- **`where [P, ...]`** — optional per-operation predicates in square brackets,
  added only to the impl for that single operator.

`OPERAND_EXPRS` per-kind:

- `@stdmut`/`@ndmut` → `OPERAND_EXPRS`: `(lhs_expr) (rhs_expr)`
- `@stdbin`/`@ndbin` → `OPERAND_EXPRS`: `(lhs_expr) (rhs_expr)`
- `@stdun`/`@ndun` → `OPERAND_EXPRS`: `(val_expr)`

## Kinds

| Token     | Trait family                       | Valid operators                    |
| --------- | ---------------------------------- | ---------------------------------- |
| `@stdmut` | `std::ops::{AddAssign, ...}`       | `+= -= *= /= %= \|= &= ^= <<= >>=` |
| `@stdbin` | `std::ops::{Add, Sub, ...}`        | `+ - * / % \| & ^ << >>`           |
| `@stdun`  | `std::ops::{Neg, Not}`             | `- !`                              |
| `@ndmut`  | `ndcore::ops::{NdAddAssign, ...}`  | `+= -= *= /= %= \|= &= ^= <<= >>=` |
| `@ndbin`  | `ndcore::ops::{NdAdd, NdSub, ...}` | `+ - * / % \| & ^ << >>`           |
| `@ndun`   | `ndcore::ops::{NdNeg, NdNot}`      | `- !`                              |

The macro constructs the body from `OPERAND_EXPRS` and the operator token:

| Kind family | Generated body                          |
| ----------- | --------------------------------------- |
| assign      | `{ lhs_expr OP= rhs_expr; }`            |
| binary      | `<Res>::from({ lhs_expr OP rhs_expr })` |
| unary       | `<Res>::from({ OP self_expr })`         |

Use field access (`lhs.0`) or a deref (`*lhs`) in `OPERAND_EXPRS` to unwrap
the bound variable before the operation. The `From` wrapping for binary and
unary kinds is why example types implement `From` for their inner type.

`macro@std` kinds implement the standard library operator traits. `nd` kinds implement
the corresponding `ndcore` traits, whose methods take operands by reference rather
than by value.

## Std-kind Signatures

#### `@stdbin` signature

```text
[<G>] [where W]  ([*]lhs: [&]Lhs, [*]rhs: [&]Rhs) -> Res
```

#### `@stdmut` signature

```text
[<G>] [where W]  (lhs: &mut Lhs, [*]rhs: [&]Rhs)
```

#### `@stdun` signature

```text
[<G>] [where W]  ([*]v: [&]Self) -> Res
```

A `*` before a reference-typed parameter fans out: the macro additionally emits an
impl for the non-reference (owned) form of that operand. `*` is independent on
each side, so `(*lhs: &T, *rhs: &T)` produces all four ownership combinations.

## Nd-kind Signatures

#### `@ndbin` signature

```text
[crate]  [<G>] [where W]  (lhs: [&]Lhs, rhs: [&]Rhs) -> Res  [for Impl | for [Impl, ...]]
```

#### `@ndmut` signature

```text
[crate]  [<G>] [where W]  (lhs: [&mut]Lhs, rhs: [&]Rhs)  [for Impl | for [Impl, ...]]
```

#### `@ndun` signature

```text
[crate]  [<G>] [where W]  (v: [&]Self) -> Res  [for Impl | for [Impl, ...]]
```

The optional `crate` keyword resolves trait paths as `crate::ops::NdAdd` instead of
`ndcore::ops::NdAdd`. Use it when writing impls inside `ndcore` itself.

The optional `for` clause overrides the implementing type; without it the macro
defaults to `Res`. `for [T, ...]` emits the same impl body on every listed type.

# Examples

#### Std-kind Operations

```rust
#[derive(Clone, Copy, Default)]
struct Num(i32);

impl From<i32> for Num {
    fn from(v: i32) -> Self {
        Num(v)
    }
}

#[derive(Clone, Copy)]
struct Wrap<T: Copy>(T);

impl<T: Copy> From<T> for Wrap<T> {
    fn from(v: T) -> Self {
        Wrap(v)
    }
}

// Implements Neg and Not for Num and &Num
ndops::all_auto! { @stdun (*value: &Num) -> Num, (value.0) [-, !] }

// Implements Neg and Not for Wrap and &Wrap
ndops::all_auto! { @stdun <T: Copy> (*value: &Wrap<T>) -> Wrap<T>, (value.0) [
    -  where [T: std::ops::Neg<Output = T>],
    !  where [T: std::ops::Not<Output = T>],
] }

// Implements Add and Sub for (Num, Num), (Num, &Num), (&Num, Num) and (&Num, &Num)
ndops::all_auto! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num, (lhs.0) (rhs.0) [+, -] }

// Implements Add and Sub for (Wrap, Wrap), (Wrap, &Wrap), (&Wrap, Wrap) and (&Wrap, &Wrap)
ndops::all_auto! { @stdbin <T: Copy> (*lhs: &Wrap<T>, *rhs: &Wrap<T>) -> Wrap<T>, (lhs.0) (rhs.0) [
    + where [T: std::ops::Add<T, Output = T>],
    - where [T: std::ops::Sub<T, Output = T>],
] }

// Implements AddAssign and SubAssign for (&mut Num, Num) and (&mut Num, &Num)
ndops::all_auto! { @stdmut (lhs: &mut Num, *rhs: &Num), (lhs.0) (rhs.0) [+=, -=] }

// Implements AddAssign and SubAssign for (&mut Wrap, Wrap) and (&mut Wrap, &Wrap)
ndops::all_auto! { @stdmut <T: Copy> (lhs: &mut Wrap<T>, *rhs: &Wrap<T>), (lhs.0) (rhs.0) [
    += where [T: std::ops::AddAssign<T>],
    -= where [T: std::ops::SubAssign<T>],
] }
```

#### Nd-kind Operations

```rust
#[derive(Clone, Copy, Default)]
struct Num(i32);

impl From<i32> for Num {
    fn from(v: i32) -> Self {
        Num(v)
    }
}

#[derive(Clone, Copy)]
struct Wrap<T: Copy>(T);

impl<T: Copy> From<T> for Wrap<T> {
    fn from(v: T) -> Self {
        Wrap(v)
    }
}

// Implements NdNeg and NdNot for &Num (within Num type)
ndops::all_auto! { @ndun (value: &Num) -> Num, (value.0) [-, !] }

// Implements NdNeg and NdNot for &Wrap (within Wrap<T> type)
ndops::all_auto! { @ndun <T: Copy> (value: &Wrap<T>) -> Wrap<T>, (value.0) [
    -  where [T: std::ops::Neg<Output = T>],
    !  where [T: std::ops::Not<Output = T>],
] }

// Implements NdAdd and NdSub for (&Num, &Num) (within Num type)
ndops::all_auto! { @ndbin (lhs: &Num, rhs: &Num) -> Num, (lhs.0) (rhs.0) [+, - ] }

// Implements NdAdd and NdSub for (&Wrap, &Wrap) (within Wrap<T> type)
ndops::all_auto! { @ndbin <T: Copy> (lhs: &Wrap<T>, rhs: &Wrap<T>) -> Wrap<T>, (lhs.0) (rhs.0) [
    + where [T: std::ops::Add<T, Output = T>],
    - where [T: std::ops::Sub<T, Output = T>],
] }

// Implements NdAddAssign and NdSubAssign for (&mut Num, &Num) (within Num type)
ndops::all_auto! { @ndmut (lhs: &mut Num, rhs: &Num), (lhs.0) (rhs.0) [+=, -=] }

// Implements NdAddAssign and NdSubAssign for (&mut Wrap, &Wrap) (within Wrap<T> type)
ndops::all_auto! { @ndmut <T: Copy> (lhs: &mut Wrap<T>, rhs: &Wrap<T>), (lhs.0) (rhs.0) [
    += where [T: std::ops::AddAssign<T>],
    -= where [T: std::ops::SubAssign<T>],
] }
```

# See also

[`all!`] — same kinds and signatures, but requires an explicit body expression for
each operator. Use it when the body is distinct or non-trivial.
