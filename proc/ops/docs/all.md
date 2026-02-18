Implement one or more operator traits with explicitly written body expressions.

# When to use

Use `all!` when the body of each operator is distinct or non-trivial.
When the body is simply `lhs OP rhs` or `OP self`, prefer [`all_auto!`],
which derives the body from the operator symbol and requires no per-operator
expression.

# Syntax

```text
ndops::all! { @KIND SIGNATURE,
    OP EXPR [where [PREDICATE, …]],
    …
}
```

- **`@KIND`** — selects the trait family and the signature shape.
- **`SIGNATURE`** — operand types with optional generics and `where` clause
  ([kind-specific](#kinds), see reference below).
- **`OP EXPR`** — an operator token (`+`, `-`, `+=`, `-=`, …) followed by an
  arbitrary Rust block forming the method body.
- **`where [P, …]`** — optional per-operation predicates in square brackets,
  added only to the impl for that single operator.

## Kinds

| Token     | Trait family                     | Valid operators                    |
| --------- | -------------------------------- | ---------------------------------- |
| `@stdmut` | `std::ops::{AddAssign, …}`       | `+= -= *= /= %= \|= &= ^= <<= >>=` |
| `@stdbin` | `std::ops::{Add, Sub, …}`        | `+ - * / % \| & ^ << >>`           |
| `@stdun`  | `std::ops::{Neg, Not}`           | `- !`                              |
| `@ndmut`  | `ndcore::ops::{NdAddAssign, …}`  | `+= -= *= /= %= \|= &= ^= <<= >>=` |
| `@ndbin`  | `ndcore::ops::{NdAdd, NdSub, …}` | `+ - * / % \| & ^ << >>`           |
| `@ndun`   | `ndcore::ops::{NdNeg, NdNot}`    | `- !`                              |

The macro constructs the body from `SIGNATURE` and `EXPR`:

| Kind family | Generated body                                     |
| ----------- | -------------------------------------------------- |
| assign      | `(\|SIGNATURE\| { EXPR })(self, rhs)`              |
| binary      | `<Res>::from((\|SIGNATURE\| { EXPR })(self, rhs))` |
| unary       | `<Res>::from((\|SIGNATURE\| { EXPR })(self, rhs))` |

Use expressions with defined from `SIGNATURE` argumets in `EXPR` to produce
new value for the operation. The `From` wrapping for binary and
unary kinds is why example types implement `From` for their inner type.

`std` kinds implement the standard library operator traits. `nd` kinds implement
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
[crate]  [<G>] [where W]  (lhs: [&]Lhs, rhs: [&]Rhs) -> Res  [for Impl | for [Impl, …]]
```

#### `@ndmut` signature

```text
[crate]  [<G>] [where W]  (lhs: [&mut]Lhs, rhs: [&]Rhs)  [for Impl | for [Impl, …]]
```

#### `@ndun` signature

```text
[crate]  [<G>] [where W]  (v: [&]Self) -> Res  [for Impl | for [Impl, …]]
```

The optional `crate` keyword resolves trait paths as `crate::ops::NdAdd` instead of
`ndcore::ops::NdAdd`. Use it when writing impls inside `ndcore` itself.

The optional `for` clause overrides the implementing type; without it the macro
defaults to `Res`. `for [T, …]` emits the same impl body on every listed type.

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
ndops::all! { @ndun (value: &Num) -> Num,
    - -value.0,
    ! !value.0,
}

// Implements NdNeg and NdNot for &Wrap (within Wrap<T> type)
ndops::all! { @ndun <T: Copy> (value: &Wrap<T>) -> Wrap<T>,
    - -value.0 where [T: std::ops::Neg<Output = T>],
    ! !value.0 where [T: std::ops::Not<Output = T>],
}

// Implements NdAdd and NdSub for (&Num, &Num) (within Num type)
ndops::all! { @ndbin (lhs: &Num, rhs: &Num) -> Num,
    + lhs.0 + rhs.0,
    - lhs.0 - rhs.0,
}

// Implements NdAdd and NdSub for (&Wrap, &Wrap) (within Wrap<T> type)
ndops::all! { @ndbin <T: Copy> (lhs: &Wrap<T>, rhs: &Wrap<T>) -> Wrap<T>,
    + lhs.0 + rhs.0 where [T: std::ops::Add<T, Output = T>],
    - lhs.0 - rhs.0 where [T: std::ops::Sub<T, Output = T>],
}

// Implements NdAddAssign and NdSubAssign for (&mut Num, &Num) (within Num type)
ndops::all! { @ndmut (lhs: &mut Num, rhs: &Num),
    += lhs.0 += rhs.0,
    -= lhs.0 -= rhs.0,
}

// Implements NdAddAssign and NdSubAssign for (&mut Wrap, &Wrap) (within Wrap<T> type)
ndops::all! { @ndmut <T: Copy> (lhs: &mut Wrap<T>, rhs: &Wrap<T>),
    += lhs.0 += rhs.0 where [T: std::ops::AddAssign<T>],
    -= lhs.0 -= rhs.0 where [T: std::ops::SubAssign<T>],
}
```

# See also

[`all_auto!`] — same kinds and signatures, but derives the operator body
automatically from the operator symbol. Use it when the body is simply
`lhs OP rhs` or `OP self`.
