# NdForward

**Zero-boilerplate trait implementation procedural macros**

The crate allows to implement standard and user-defined traits by forwarding it to expression.

- [`ndfwd::std`]([macro@std]) implements `Deref`, `DerefMut`, `AsRef`, `AsMut`, `FromIterator`.
- [`ndfwd::cmp`]([macro@cmp]) implements `PartialEq`, `Eq`, `PartialOrd`, `Ord`.
- [`ndfwd::fmt`]([macro@fmt]) implements `Display`, `Binary`, `Octal`, `LowerHex`, `UpperHex`.
- [`ndfwd::def`]([macro@def]) declares forwardable trait.
- [`ndfwd::decl`]([macro@decl]) defines forwardable trait.

## Start

```toml
[dependencies]
ndfwd = "*"
```

## Features

### Standard Traits Forwarding

**Standard** traits are forwarded to user-specified expressions.

#### [`ndfwd::std`]([macro@std])

| Trait          | Expression                     | Conditions                         |
| -------------- | ------------------------------ | ---------------------------------- |
| `Deref`\*      | `&EXPR`                        | `None`                             |
| `DerefMut`\*   | `&mut EXPR`                    | `None`                             |
| `AsRef`        | `EXPR.as_ref()`                | `TY: AsRef`                        |
| `AsMut`        | `EXPR.as_mut()`                | `TY: AsMut`                        |
| `FromIterator` | `<TY>::from_iter(iter).into()` | `TY: FromIterator, Self: From<TY>` |

\* Note that `Deref` and `DerefMut` **do not** call `deref()` or `deref_mut()`, but rather return the expression itself.

#### [`ndfwd::cmp`]([macro@cmp])

| Trait        | Expression                            | Conditions       |
| ------------ | ------------------------------------- | ---------------- |
| `Eq`         | `None`                                | `TY: Eq`         |
| `Ord`        | `self.FIELD.cmp(other.FILED)`         | `TY: Ord`        |
| `PartialEq`  | `self.FIELD.partial_eq(other.FIELD)`  | `TY: PartialEq`  |
| `PartialOrd` | `self.FIELD.partial_cmp(other.FIELD)` | `TY: PartialOrd` |

#### [`ndfwd::fmt`]([macro@fmt])

| Trait      | Expression    | Conditions     |
| ---------- | ------------- | -------------- |
| `Display`  | `EXPR.fmt(f)` | `TY: Display`  |
| `Binary`   | `EXPR.fmt(f)` | `TY: Binary`   |
| `Octal`    | `EXPR.fmt(f)` | `TY: Octal`    |
| `LowerHex` | `EXPR.fmt(f)` | `TY: LowerHex` |
| `UpperHex` | `EXPR.fmt(f)` | `TY: UpperHex` |

### User-defined Traits Forwarding

**User-defined** trait are forwarded to user-specified expression in two steps:

1. [`ndfwd::decl`]([macro@decl]) - declare forwardable trait.
2. [`ndfwd::def`]([macro@def]) - define forwardable trait for **struct**, **enum** or **union**.

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

In return types, there are four options:

| Type                            | Expression               | Required for                 |
| ------------------------------- | ------------------------ | ---------------------------- |
| **As-is**                       | `EXPR.call()`            | `Default`                    |
| [`ndfwd::as_into`]([as_into])\* | `EXPR.call().into()`     | `fn(self) -> Self`           |
| [`ndfwd::as_self`]([as_self])\* | `EXPR.call(); self`      | `fn(&mut self) -> &mut Self` |
| [`ndfwd::as_expr`]([as_expr])\* | `(CLOSURE)(EXPR.call())` | `fn(self) -> (Self, Self)`   |

\* Note that modifiers **must** be used as fully qualified path.

## Syntax

## Examples
