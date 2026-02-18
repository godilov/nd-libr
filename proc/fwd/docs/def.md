Implement a forwardable trait on a type by delegating to an inner field.

# When to use

Use `#[ndfwd::def]` to generate a forwarding impl of a trait previously declared with
[`decl`]. The macro reads the companion infrastructure emitted by `#[decl]`
and produces a complete trait impl whose every item — associated types, constants,
functions and methods — delegates to the corresponding item on the inner field.

`#[def]` is the second step in the two-step forwarding workflow for user-defined traits.
The trait must have been annotated with [`decl`] before `#[def]` can be used
with it.

For standard library trait families, use the dedicated single-step macros
[`macro@std`], [`macro@std`], and [`macro@std`] instead.

# Syntax

```text
#[ndfwd::def(EXPR with TYPE: PATH [where PREDICATE, ...])]
ITEM
```

- **`EXPR`** — a Rust expression that accesses the inner field (e.g. `self.0` or
  `self.inner`). Used as the forwarding target in every generated method body.
- **`TYPE`** — the type of the inner field. Used to forward associated functions.
- **`TRAIT`** — the trait to be forwarded with `EXPR` and `TYPE`. Used to locate
  generated implementation macro. It **must** be located within the same crate
  and specified as **absolute** or **relative** path instead of `use` keyword.
- **`where [P, ...]`** — optional extra `TYPE` predicates.

The macro can be applied to **structs**, **enums** and **unions**.

# Generated impl

For each item in the `#[decl]` trait, `#[def]` generates a corresponding forwarding
item:

| Trait item          | Generated forwarding body            |
| ------------------- | ------------------------------------ |
| Associated type     | `type Item = <TYPE as Trait>::Item;` |
| Associated const    | `const N: T = <TYPE as Trait>::N;`   |
| Associated function | `<TYPE as Trait>::FUNCTION(args)`    |
| `&self` method      | `self.forward_ref().method(args)`    |
| `&mut self` method  | `self.forward_mut().method(args)`    |
| `self` method       | `self.forward().method(args)`        |

Methods whose arguments are of type `Self` or `&Self` / `&mut Self` are automatically
unwrapped to the inner type before being passed to the forwarded call. Methods annotated
with [`as_into`], [`as_self`], or [`as_expr`] in the `#[decl]` trait have their return
value transformed accordingly.

# Examples

## Basic usage

```rust
#[ndfwd::decl]
pub trait Summary {
    fn summarize(&self) -> String;
    fn word_count(&self) -> usize;
}

// Generates `impl Summary for Article` that forwards to `String`.
#[ndfwd::def(self.0 with String: Summary)]
struct Article(String);
```

## Named fields

```rust
#[ndfwd::decl]
pub trait Classify {
    fn category(&self) -> &str;
    fn score(&self) -> f64;
}

#[ndfwd::def(self.data with Classifier: Classify)]
struct Item {
    data: Classifier,
    label: String,
}
```

## With extra where bounds

Use the optional `where` clause when the impl needs bounds beyond `TYPE: PATH` — for
example, when the wrapper is generic.

```rust
#[ndfwd::decl]
pub trait Process<T> {
    fn run(&self, input: T) -> T;
}

#[ndfwd::def(self.0 with Inner: Process<T> where T: Clone)]
struct Wrapper<T>(Inner);
```

## Generic inner type

```rust
#[ndfwd::decl]
pub trait Collection {
    type Item;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

// Forwards Collection to Vec<T> for any T.
#[ndfwd::def(self.0 with Vec<T>: Collection)]
struct Bag<T>(Vec<T>);
```

# See also

- [`decl`] — declares a trait as forwardable before `#[def]` can be used.
- [`as_into`], [`as_self`], [`as_expr`] — method-level
  return modifiers that affect how `#[def]` generates each forwarding body.
- [`macro@std`], [`cmp`], [`fmt`] — single-step forwarding for
  standard library trait families.
