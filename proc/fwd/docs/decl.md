Declare a trait as a forwardable interface.

# When to use

Use `#[ndfwd::decl]` to mark a trait so that [`def`] can generate forwarding
impls for it on wrapper types. The macro processes the trait's items — associated types,
constants, functions, and methods — and emits a companion macro that `#[def]` calls internally.

`#[decl]` is the first step in the two-step forwarding workflow for user-defined traits.
After declaring a trait, apply [`def`] to each implementing wrapper type.

For standard library trait families, use the dedicated single-step macros
[`macro@std`], [`cmp`], and [`fmt`] instead.

# Syntax

```text
#[ndfwd::decl]
TRAIT_DEFINITION
```

The attribute takes no arguments and must be applied directly to a `trait` item.

## Method return modifiers

Individual methods inside a `#[decl]` trait can carry modifier attributes that control
how [`def`] generates the forwarding body for that method. The modifier
attributes are erased from the trait definition and have no effect at the declaration
site; they are read by `#[def]` at each use site. They also
**must** be specified in a fully qualified path only.

| Modifier                       | Effect on the forwarded return value            |
| ------------------------------ | ----------------------------------------------- |
| [`#[ndfwd::as_into]`]          | Wraps the result with `.into()`                 |
| [`#[ndfwd::as_self]`]          | Discards the result and returns `self` instead  |
| [`#[ndfwd::as_expr(CLOSURE)]`] | Transforms the result with an arbitrary closure |

See the individual modifier docs for details and examples.

# What the macro emits

`#[decl]` leaves the trait definition itself unchanged and additionally emits a private
companion `macro_rules!` macro named `__forward_impl_TRAIT`. This macro is used
internally by [`def`] and is not part of the public API.

# Examples

## Basic trait

```rust
#[ndfwd::decl]
pub trait Summary {
    fn summarize(&self) -> String;
    fn word_count(&self) -> usize;
}

// Now implement it on a wrapper type using #[def]:
#[ndfwd::def(self.0 with String: Summary)]
struct Article(String);
```

## Trait with an associated type and constant

```rust
#[ndfwd::decl]
pub trait Container {
    type Item;
    const CAPACITY: usize;
    fn get(&self, index: usize) -> Option<&Self::Item>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

#[ndfwd::def(self.0 with Vec<i32>: Container)]
struct Store(Vec<i32>);
```

## Trait with return modifiers

```rust
#[ndfwd::decl]
pub trait Builder: Sized {
    // #[as_self] discards the inner builder's return value and returns `self`,
    // which is needed when the inner method returns the inner type but the
    // wrapping type needs to be returned for method chaining.
    #[ndfwd::as_self]
    fn set_value(&mut self, value: i32) -> &mut Self;

    // #[as_into] wraps the inner return value with `.into()`,
    // useful when the inner method returns the inner type
    // but the caller expects the outer type.
    #[ndfwd::as_into]
    fn build(&self) -> Self;
}

#[ndfwd::def(self.0 with InnerBuilder: Builder)]
struct MyBuilder(InnerBuilder);
```

## Generic trait

```rust
#[ndfwd::decl]
pub trait Transform<T> {
    fn apply(&self, input: T) -> T;
}

#[ndfwd::def(self.0 with Processor: Transform<String>)]
struct StringProcessor(Processor);
```

# See also

- [`def`] — applies a `#[decl]`-declared trait to a wrapper type.
- [`as_into`], [`as_self`], [`as_expr`] — method-level
  return modifiers used inside `#[decl]` traits.
- [`macro@std`], [`cmp`], [`fmt`] — single-step forwarding for
  standard library trait families.
