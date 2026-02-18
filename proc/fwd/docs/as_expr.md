Transform a forwarded method's return value with an arbitrary closure.

# When to use

Use `#[ndfwd::as_expr(CLOSURE)]` on a method inside a [`decl`] trait when the
return value of the forwarded call needs a transformation that neither `.into()` nor
returning `self` can express. The modifier instructs [`def`] to apply the
provided closure to the result of the inner method call.

- Use [`as_into`] for the common case where the result only needs to be converted with
  `.into()`.
- Use [`as_self`] when the result should be discarded and `self` returned instead.

Reserve `#[as_expr]` for cases that require non-trivial transformations (like arrays, tuples, etc.).

# Syntax

```text
#[ndfwd::as_expr(CLOSURE)]
fn METHOD(…) -> ReturnType;
```

- **`CLOSURE`** — an inline Rust closure expression that receives the return value of the
  forwarded call and produces the final return value. The closure is applied immediately
  to the result of the inner method call.

The attribute must be placed on a method declaration inside a `#[ndfwd::decl]` trait. It
is a marker only at the declaration site and is erased from the trait definition; the
closure is read and inlined by [`def`] at each use site. It also **must** be specified
in a fully qualified path only.

# Effect

Without the modifier, [`def`] generates a forwarding body that returns the
inner call's result directly:

```rust,ignore
// without #[as_expr]
fn method(&self) -> ReturnType {
    self.forward_ref().method()
}
```

With `#[as_expr(|v| expr)]`, it applies the closure to the result:

```rust,ignore
// with #[as_expr(|v| expr)]
fn method(&self) -> ReturnType {
    (|v| expr)(self.forward_ref().method())
}
```

# Example

```rust
#[ndfwd::decl]
pub trait Measure {
    /// Returns the length, negated when the wrapper is inverted.
    #[ndfwd::as_expr(|v: usize| v.saturating_add(1))]
    fn len(&self) -> usize;
}

#[ndfwd::def(self.0 with Inner: Measure)]
struct Extended(Inner);

struct Inner(Vec<i32>);

impl Measure for Inner {
    fn len(&self) -> usize { self.0.len() }
}

assert_eq!(Extended(Inner(vec![1, 2, 3])).len(), 4);
```

# See also

- [`as_into`] — wraps the forwarded return value with `.into()`.
- [`as_self`] — discards the forwarded return value and returns `self`.
- [`decl`] — the trait-level macro that recognises this modifier.
- [`def`] — the type-level macro that generates the forwarding body.
