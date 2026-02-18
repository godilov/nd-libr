# Nd Forward

**Zero-boilerplate trait forwarding macros for Rust.**

`ndfwd` provides attribute macros that implement standard and user-defined traits on
wrapper types by delegating to an inner field, eliminating the repetitive boilerplate of
writing forwarding impls by hand.

## Quick start

```toml
[dependencies]
ndfwd = "*"
```

## Macros

### Forwarding standard traits

These three attribute macros each implement a related family of standard library traits on
the annotated type. All traits in the family are emitted at once; each impl is conditional
on the inner type implementing the corresponding trait, so unused traits add no bounds. All
three macros can be applied to **structs**, **enums**, and **unions**.

| Attribute     | Implemented traits                                    |
| ------------- | ----------------------------------------------------- |
| [`macro@std`] | `Deref`, `DerefMut`, `AsRef`, `AsMut`, `FromIterator` |
| [`macro@cmp`] | `PartialEq`, `Eq`, `PartialOrd`, `Ord`                |
| [`macro@fmt`] | `Display`, `Binary`, `Octal`, `LowerHex`, `UpperHex`  |

#### Syntax

```text
#[ndfwd::MACRO(EXPR with TYPE)]
```

- **`EXPR`** — a Rust expression that accesses the inner field (e.g. `self.0` or
  `self.inner`). Used as the forwarding target in every generated method body.
- **`TYPE`** — the type of the inner field. Used to forward associated functions
  and form the trait bounds on the generated impls.

### Forwarding user-defined traits

For custom traits, `ndfwd` provides a two-step workflow:

1. Annotate the trait with [`decl`] to declare it as forwardable.
2. Annotate each implementing type with [`def`] to generate a forwarding impl.

#### Decl Syntax

```text
#[ndfwd::decl]
```

#### Def Syntax

```text
#[ndfwd::def(EXPR with TYPE: TRAIT [where [PREDICATE, ...]])]
```

- **`EXPR`** — a Rust expression that accesses the inner field (e.g. `self.0` or
  `self.inner`). Used as the forwarding target in every generated method body.
- **`TYPE`** — the type of the inner field. Used to forward associated functions.
- **`TRAIT`** — the trait to be forwarded with `EXPR` and `TYPE`. Used to locate
  generated implementation macro. It **must** be located within the same crate
  and specified as **absolute** or **relative** path instead of `use` keyword.
- **`where [P, ...]`** — optional `TYPE` predicates.

#### Method return modifiers

Inside a `#[decl]` trait, individual methods can carry modifier attributes that control
how `#[def]` generates the forwarding body for that method. These modifiers are inert
by themselves; they are read and erased by `#[def]` at the call site. They also
**must** be specified in a fully qualified path only.

| Attribute   | Generated body                                  |
| ----------- | ----------------------------------------------- |
| [`as_into`] | Wraps the result with `.into()`                 |
| [`as_self`] | Discards the result and returns `self` instead  |
| [`as_expr`] | Transforms the result with an arbitrary closure |

## Examples

#### Standard traits

```rust
#[ndfwd::std(self.0 with i32)] // Implements Deref, DerefMut, AsRef, AsMut, and FromIterator — all forwarded to i32.
#[ndfwd::cmp(self.0 with i32)] // Implements PartialEq, Eq, PartialOrd, Ord — all forwarded to i32.
#[ndfwd::fmt(self.0 with i32)] // Implements Display, Binary, Octal, LowerHex, UpperHex — all forwarded to i32.
struct Num(i32);

impl From<i32> for Num {
    fn from(value: i32) -> Self {
        Num(value)
    }
}

#[ndfwd::std(self.0 with T)] // Conditionally implements Deref, DerefMut, AsRef, AsMut, and FromIterator — all forwarded to T.
#[ndfwd::cmp(self.0 with T)] // Conditionally implements PartialEq, Eq, PartialOrd, Ord — all forwarded to T.
#[ndfwd::fmt(self.0 with T)] // Conditionally implements Display, Binary, Octal, LowerHex, UpperHex — all forwarded to T.
struct Wrap<T: Copy>(T);

impl<T: Copy> From<T> for Wrap<T> {
    fn from(value: T) -> Self {
        Wrap(value)
    }
}

assert_eq!(Num(0).cmp(&Num(0)), 0.cmp(&0));
assert_eq!(Num(0).cmp(&Num(1)), 0.cmp(&1));
assert_eq!(Num(1).cmp(&Num(0)), 1.cmp(&0));

assert_eq!(Wrap(0).cmp(&Wrap(0)), 0.cmp(&0));
assert_eq!(Wrap(0).cmp(&Wrap(1)), 0.cmp(&1));
assert_eq!(Wrap(1).cmp(&Wrap(0)), 1.cmp(&0));

// All other forms are also supported
println!("{:#}", Num(1337));
println!("{:#}", Wrap(1337));
```

#### User-defined traits

```rust
#[ndfwd::decl]
pub trait Trait {
    fn function(&self) -> String;
}

// Implements Trait — forwarded to Inner.
#[ndfwd::def(self.0 with Inner: Trait)]
struct Struct(Inner);

// Conditionally implements Trait — forwarded to T.
#[ndfwd::def(self.0 with T: Trait where T: Trait)]
struct StructGen<T: Copy>(T);

#[derive(Clone, Copy)]
struct Inner;

impl Trait for Inner {
    fn function(&self) -> String {
        "Hello, World!".into()
    }
}

assert_eq!(Struct(Inner).function(), "Hello, World!");
assert_eq!(StructGen(Inner).function(), "Hello, World!");

// Fails to compile, i32 does not implement Trait
// assert_eq!(StructGen(0).function(), "Hello, World!");
```

## License

Licensed under the [MIT License](LICENSE-MIT).
