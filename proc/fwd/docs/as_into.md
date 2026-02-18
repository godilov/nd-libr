Wrap a forwarded method's return value with `.into()`.

# When to use

Use `#[ndfwd::as_into]` on a method inside a [`decl`] trait when the inner
type's method returns the inner type itself, but the forwarding impl should return the
outer (wrapper) type. The modifier instructs [`def`] to append `.into()` to
the forwarded call, converting the result automatically.

This requires the outer type to implement `From<Inner>` (or equivalently,
`Inner: Into<Outer>`).

- Use [`as_self`] instead when the method mutates in place and the outer type
  should be returned for chaining, without a conversion.
- Use [`as_expr`] for arbitrary transformations that neither
  `.into()` nor returning `self` can express.

# Syntax

```text
#[ndfwd::as_into]
fn METHOD(…) -> ReturnType;
```

The attribute takes no arguments and must be placed on a method declaration inside a
`#[ndfwd::decl]` trait. It is a marker only; it has no effect at the declaration site
and is erased from the trait definition. It also **must** be specified in a fully
qualified path only.

# Effect

Without the modifier, [`def`] generates a forwarding body that returns the
inner call's result directly:

```rust,ignore
// without #[as_into]
fn method(&self) -> ReturnType {
    self.forward_ref().method()
}
```

With `#[as_into]`, it appends `.into()`:

```rust,ignore
// with #[as_into]
fn method(&self) -> ReturnType {
    self.forward_ref().method().into()
}
```

# Example

```rust
#[ndfwd::decl]
pub trait Resetable: Sized {
    /// Returns a fresh default instance of the type.
    #[ndfwd::as_into]
    fn reset(&self) -> Self;
}

#[ndfwd::def(self.0 with Inner: Resetable)]
struct Outer(Inner);

impl From<Inner> for Outer {
    fn from(v: Inner) -> Self { Outer(v) }
}

#[derive(Default, Clone)]
struct Inner(i32);

impl Resetable for Inner {
    fn reset(&self) -> Self { Inner::default() }
}

assert_eq!(Outer(Inner(1337)).reset().0.0, 0);
```

# See also

- [`as_self`] — returns `self` after the forwarded call instead of the call's return value.
- [`as_expr`] — transforms the forwarded return value with an arbitrary closure.
- [`decl`] — the trait-level macro that recognises this modifier.
- [`def`] — the type-level macro that generates the forwarding body.
