# NdForward

**Zero-boilerplate trait implementation procedural macros**

The crate allows to implement standard and user-defined traits by forwarding it to expression.

- [`ndfwd::std`](macro@std) implements [`Deref`](std::ops::Deref), [`DerefMut`](std::ops::DerefMut), [`AsRef`](std::convert::AsRef), [`AsMut`](std::convert::AsMut), [`FromIterator`](std::iter::FromIterator).
- [`ndfwd::cmp`](macro@cmp) implements [`PartialEq`](std::cmp::PartialEq), [`Eq`](std::cmp::Eq), [`PartialOrd`](std::cmp::PartialOrd), [`Ord`](std::cmp::Ord).
- [`ndfwd::fmt`](macro@fmt) implements [`Display`](std::fmt::Display), [`Binary`](std::fmt::Binary), [`Octal`](std::fmt::Octal), [`LowerHex`](std::fmt::LowerHex), [`UpperHex`](std::fmt::UpperHex).
- [`ndfwd::def`](macro@def) defines forwardable trait for **struct**, **enum** or **union**.
- [`ndfwd::decl`](macro@decl) declares forwardable trait.

## Start

```toml
[dependencies]
ndfwd = "*"
```

## Features

### Standard Traits Forwarding

**Standard** traits are forwarded to user-specified expressions.

#### [`ndfwd::std`](macro@std)

| Trait                                     | Expression                     | Conditions                         |
| ----------------------------------------- | ------------------------------ | ---------------------------------- |
| [`Deref`](std::ops::Deref)\*              | `&EXPR`                        | `None`                             |
| [`DerefMut`](std::ops::DerefMut)\*        | `&mut EXPR`                    | `None`                             |
| [`AsRef`](std::convert::AsRef)            | `EXPR.as_ref()`                | `TY: AsRef`                        |
| [`AsMut`](std::convert::AsMut)            | `EXPR.as_mut()`                | `TY: AsMut`                        |
| [`FromIterator`](std::iter::FromIterator) | `<TY>::from_iter(iter).into()` | `TY: FromIterator, Self: From<TY>` |

\* Note that `Deref` and `DerefMut` **do not** call `deref()` or `deref_mut()`, but rather return the expression itself.

#### [`ndfwd::cmp`](macro@cmp)

| Trait                                | Expression                        | Conditions       |
| ------------------------------------ | --------------------------------- | ---------------- |
| [`Eq`](std::cmp::Eq)                 | `None`                            | `TY: Eq`         |
| [`Ord`](std::cmp::Ord)               | `EXPR.cmp(EXPR as other)`         | `TY: Ord`        |
| [`PartialEq`](std::cmp::PartialEq)   | `EXPR.partial_eq(EXPR as other)`  | `TY: PartialEq`  |
| [`PartialOrd`](std::cmp::PartialOrd) | `EXPR.partial_cmp(EXPR as other)` | `TY: PartialOrd` |

#### [`ndfwd::fmt`](macro@fmt)

| Trait                            | Expression    | Conditions     |
| -------------------------------- | ------------- | -------------- |
| [`Display`](std::fmt::Display)   | `EXPR.fmt(f)` | `TY: Display`  |
| [`Binary`](std::fmt::Binary)     | `EXPR.fmt(f)` | `TY: Binary`   |
| [`Octal`](std::fmt::Octal)       | `EXPR.fmt(f)` | `TY: Octal`    |
| [`LowerHex`](std::fmt::LowerHex) | `EXPR.fmt(f)` | `TY: LowerHex` |
| [`UpperHex`](std::fmt::UpperHex) | `EXPR.fmt(f)` | `TY: UpperHex` |

### User-defined Traits Forwarding

**User-defined** trait are forwarded to user-specified expression in two steps:

1. [`ndfwd::decl`](macro@decl) - declare forwardable trait.
2. [`ndfwd::def`](macro@def) - define forwardable trait for **struct**, **enum** or **union**.

All traits, structs, enums and unions **must** be within **the same** crate.

The first step creates a private `macro_rules!` definition with all partially-defined associated types, constants, functions and methods.
The second step creates a private `module` with auxiliary definitions and trait implementation for the type.

#### Types

- All `Self`-**independent** types in associated types, constants, functions and methods are **supported**.
- All `Self`-**dependent** types in associated types, constants, functions and methods are **partailly-supported**,

**Limitations**:

- For associated constants, `Self`-dependent types **can not** be used.
- For associated function and method arguments, `Never` and `Macro` types **can not** be used.
- For associated function and method arguments, `Self`-dependent types **can not** be used within **arrays** and **slices**.
- For associated function and method arguments, `Function Ptr`, `Impl Trait` and `dyn &Trait` types are forwarded **as-is**.
- For associated function and method arguments, every other `Self`-dependent type is forwarded according to signature and adapted when needed.

For return types, there are four options:

| Type                          | Expression               | Usecase                      |
| ----------------------------- | ------------------------ | ---------------------------- |
| **As-is**                     | `EXPR.call()`            | `Default`                    |
| [`ndfwd::as_into`](as_into)\* | `EXPR.call().into()`     | `fn(self) -> Self`           |
| [`ndfwd::as_self`](as_self)\* | `EXPR.call(); self`      | `fn(&mut self) -> &mut Self` |
| [`ndfwd::as_expr`](as_expr)\* | `(CLOSURE)(EXPR.call())` | `fn(self) -> (Self, Self)`   |

\* Note that modifiers **must** be used as fully qualified path in forwardable trait declaration.

## Syntax

For [`ndfwd::std`](macro@std), [`ndfwd::cmp`](macro@cmp) and [`ndfwd::fmt`](macro@fmt):

```text
#[ndfwd::METHOD(EXPR with TY)]
(STRUCT | ENUM | UNION)
```

For [`ndfwd::decl`](macro@decl):

```text
#[ndfwd::decl]
TRAIT
```

For [`ndfwd::def`](macro@def):

```text
#[ndfwd::def(EXPR with TY: TRAIT (where (PREDICATE),*)?)]
(STRUCT | ENUM | UNION)
```

- `TRAIT` **must** be **absolute** or **relative** path to forwardable trait instead of `use` keyword.
- `TRAIT` **must** be within **the same** crate with `STRUCT`, `ENUM` or `UNION`.

## Examples
