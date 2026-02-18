# Nd Ops

**Zero-boilerplate operator implementation macros for Rust.**

`ndops` provides two procedural macros — [`all!`] and [`all_auto!`] — that eliminate the
repetitive plumbing of writing `std::ops` and `ndcore::ops` trait implementations by hand.
Both macros share the same set of six **kinds**, which determine which trait family is
implemented and how the signature is written.

## Quick start

```toml
[dependencies]
ndops = "*"
ndcore = "*"
```

## Syntax

#### `all!`

```text
ndops::all! { @KIND SIGNATURE,
    OP EXPR [where [PREDICATE, ...]],
    ...
}
```

#### `all_auto!`

```text
ndops::all_auto! { @KIND SIGNATURE,
    OPERAND_EXPRS [OP [where [PREDICATE, ...]], ...]
}
```

`OPERAND_EXPRS` per-kind:

- `@stdmut`/`@ndmut` → `OPERAND_EXPRS`: `(lhs_expr) (rhs_expr)`
- `@stdbin`/`@ndbin` → `OPERAND_EXPRS`: `(lhs_expr) (rhs_expr)`
- `@stdun`/`@ndun` → `OPERAND_EXPRS`: `(val_expr)`

### Kinds

| Kind      | Trait family                       | Valid operators                    |
| --------- | ---------------------------------- | ---------------------------------- |
| `@stdmut` | `std::ops::{AddAssign, ...}`       | `+= -= *= /= %= \|= &= ^= <<= >>=` |
| `@stdbin` | `std::ops::{Add, Sub, ...}`        | `+ - * / % \| & ^ << >>`           |
| `@stdun`  | `std::ops::{Neg, Not}`             | `- !`                              |
| `@ndmut`  | `ndcore::ops::{NdAddAssign, ...}`  | `+= -= *= /= %= \|= &= ^= <<= >>=` |
| `@ndbin`  | `ndcore::ops::{NdAdd, NdSub, ...}` | `+ - * / % \| & ^ << >>`           |
| `@ndun`   | `ndcore::ops::{NdNeg, NdNot}`      | `- !`                              |

`macro@std` kinds implement the standard library operator traits. `nd` kinds implement the
corresponding `ndcore` traits, whose methods take operands by reference rather than by
value.

### Std-kind Signatures

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

A `*` before a reference-typed parameter is a **fan-out** instruction. The macro emits
one impl for the reference form and one for the owned form, covering every ownership
combination without repetition.

On binary kinds `*` is independent per side, so `(*lhs: &T, *rhs: &T)` produces all
four combinations: `(&T, &T)`, `(T, &T)`, `(&T, T)`, `(T, T)`.

### Nd-kind Signatures

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

The optional `crate` keyword (nd kinds only) resolves trait paths as `crate::ops::Nd*`
instead of `ndcore::ops::Nd*`. Use it when writing impls inside `ndcore` itself.

The optional `for` clause (nd kinds only) overrides the implementing type. Without it
the macro defaults to `Res` for binary/unary kinds or `Lhs` for assign kinds.
`for [T, ...]` emits the same impl body on every listed type.

## Examples

#### [`all!`] - explicit operations

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
ndops::all! { @stdun (*value: &Num) -> Num,
    - -value.0,
    ! !value.0,
}

// Implements Neg and Not for Wrap and &Wrap
ndops::all! { @stdun <T: Copy> (*value: &Wrap<T>) -> Wrap<T>,
    - -value.0 where [T: std::ops::Neg<Output = T>],
    ! !value.0 where [T: std::ops::Not<Output = T>],
}

// Implements Add and Sub for (Num, Num), (Num, &Num), (&Num, Num) and (&Num, &Num)
ndops::all! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num,
    + lhs.0 + rhs.0,
    - lhs.0 - rhs.0,
}

// Implements Add and Sub for (Wrap, Wrap), (Wrap, &Wrap), (&Wrap, Wrap) and (&Wrap, &Wrap)
ndops::all! { @stdbin <T: Copy> (*lhs: &Wrap<T>, *rhs: &Wrap<T>) -> Wrap<T>,
    + lhs.0 + rhs.0 where [T: std::ops::Add<T, Output = T>],
    - lhs.0 - rhs.0 where [T: std::ops::Sub<T, Output = T>],
}

// Implements AddAssign and SubAssign for (&mut Num, Num) and (&mut Num, &Num)
ndops::all! { @stdmut (lhs: &mut Num, *rhs: &Num),
    += lhs.0 += rhs.0,
    -= lhs.0 -= rhs.0,
}

// Implements AddAssign and SubAssign for (&mut Wrap, Wrap) and (&mut Wrap, &Wrap)
ndops::all! { @stdmut <T: Copy> (lhs: &mut Wrap<T>, *rhs: &Wrap<T>),
    += lhs.0 += rhs.0 where [T: std::ops::AddAssign<T>],
    -= lhs.0 -= rhs.0 where [T: std::ops::SubAssign<T>],
}
```

#### [`all_auto!`] - derived operations

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

#### Derive Std-kind from Nd-kind

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

ndops::all! { @stdun (*value: &Num) -> Num,
    - <i32 as ndcore::ops::NdNeg>::neg(&value.0), // Forwards Neg to NdNeg
    ! <i32 as ndcore::ops::NdNot>::not(&value.0), // Forwards Not to NdNot
}

ndops::all! { @stdun <T: Copy> (*value: &Wrap<T>) -> Wrap<T>,
    - T::neg(&value.0) where [T: ndcore::ops::NdNeg<Type = T>], // Conditionally forwards Neg to NdNeg
    ! T::not(&value.0) where [T: ndcore::ops::NdNot<Type = T>], // Conditionally forwards Not to NdNot
}

ndops::all! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num,
    + <i32 as ndcore::ops::NdAdd>::add(&lhs.0, &rhs.0), // Forwards Add to NdAdd
    - <i32 as ndcore::ops::NdSub>::sub(&lhs.0, &rhs.0), // Forwards Sub to NdSub
}

ndops::all! { @stdbin <T: Copy> (*lhs: &Wrap<T>, *rhs: &Wrap<T>) -> Wrap<T>,
    + T::add(&lhs.0, &rhs.0) where [T: ndcore::ops::NdAdd<Type = T>], // Conditionally forwards Add to NdAdd
    - T::sub(&lhs.0, &rhs.0) where [T: ndcore::ops::NdSub<Type = T>], // Conditionally forwards Sub to NdSub
}

ndops::all! { @stdmut (lhs: &mut Num, *rhs: &Num),
    += <i32 as ndcore::ops::NdAddAssign>::add_assign(&mut lhs.0, &rhs.0), // Forwards AddAssign to NdAddAssign
    -= <i32 as ndcore::ops::NdSubAssign>::sub_assign(&mut lhs.0, &rhs.0), // Forwards SubAssign to NdSubAssign
}

ndops::all! { @stdmut <T: Copy> (lhs: &mut Wrap<T>, *rhs: &Wrap<T>),
    += T::add_assign(&mut lhs.0, &rhs.0) where [T: ndcore::ops::NdAddAssign], // Conditionally forwards AddAssign to NdAddAssign
    -= T::sub_assign(&mut lhs.0, &rhs.0) where [T: ndcore::ops::NdSubAssign], // Conditionally forwards SubAssign to NdSubAssign
}
```

## License

Licensed under [MIT License](LICENSE-MIT).
