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

```rust
#[ndfwd::decl]
trait Greeter {
    type Type;

    const HELLO: Self::Type;
    const GOODBYE: Self::Type;

    fn hello() -> Self::Type;
    fn goodbye() -> Self::Type;
}

#[ndfwd::decl]
trait Builder: Sized {
    #[ndfwd::as_into]
    fn new() -> Self;

    #[ndfwd::as_self]
    fn set_x(&mut self, value: usize) -> &mut Self;

    #[ndfwd::as_self]
    fn set_y(&mut self, value: usize) -> &mut Self;

    #[ndfwd::as_self]
    fn set_z(&mut self, value: usize) -> &mut Self;

    #[ndfwd::as_into]
    fn with_x(self, value: usize) -> Self;

    #[ndfwd::as_into]
    fn with_y(self, value: usize) -> Self;

    #[ndfwd::as_into]
    fn with_z(self, value: usize) -> Self;
}

#[ndfwd::decl]
trait Split: Sized {
    #[ndfwd::as_expr(|(a, b)| (Self::from(a), Self::from(b)))]
    fn split(value: &Self) -> (Self, Self);
}

#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::def(self.0 with T: Greeter)]
#[ndfwd::def(self.0 with T: Builder)]
#[ndfwd::def(self.0 with T: Split)]
#[derive(Debug, Clone, Copy)]
struct Any<T>(T);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BuilderImpl(usize, usize, usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GreeterImpl;

impl<T> From<T> for Any<T> {
    fn from(value: T) -> Self {
        Any(value)
    }
}

impl Greeter for GreeterImpl {
    type Type = &'static str;

    const HELLO: Self::Type = "Hello!";
    const GOODBYE: Self::Type = "Goodbye!";

    fn hello() -> Self::Type {
        Self::HELLO
    }

    fn goodbye() -> Self::Type {
        Self::GOODBYE
    }
}

impl Builder for BuilderImpl {
    fn new() -> Self {
        Self(0, 0, 0)
    }

    fn set_x(&mut self, value: usize) -> &mut Self {
        self.0 = value;
        self
    }

    fn set_y(&mut self, value: usize) -> &mut Self {
        self.1 = value;
        self
    }

    fn set_z(&mut self, value: usize) -> &mut Self {
        self.2 = value;
        self
    }

    fn with_x(self, value: usize) -> Self {
        Self(value, self.1, self.2)
    }

    fn with_y(self, value: usize) -> Self {
        Self(self.0, value, self.2)
    }

    fn with_z(self, value: usize) -> Self {
        Self(self.0, self.1, value)
    }
}

impl Split for usize {
    fn split(value: &Self) -> (Self, Self) {
        (value / 2, value - value / 2)
    }
}

let mut builder = Any::<BuilderImpl>::new();

builder.set_x(1).set_y(2).set_z(3);

assert_eq!(builder, Any::<BuilderImpl>::new().with_x(1).with_y(2).with_z(3));
assert_ne!(builder, Any::<BuilderImpl>::new().with_x(3).with_y(2).with_z(1));

assert_eq!(Any::<GreeterImpl>::HELLO, GreeterImpl::HELLO);
assert_eq!(Any::<GreeterImpl>::GOODBYE, GreeterImpl::GOODBYE);

assert_eq!(Any::<GreeterImpl>::hello(), GreeterImpl::hello());
assert_eq!(Any::<GreeterImpl>::goodbye(), GreeterImpl::goodbye());

assert_eq!(Any::split(&Any(4usize)).0.0, usize::split(&4).0);
assert_eq!(Any::split(&Any(4usize)).1.0, usize::split(&4).1);
```
