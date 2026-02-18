Discard a forwarded method's return value and return `self` instead.

# When to use

Use `#[ndfwd::as_self]` on a method inside a [`decl`] trait when the
forwarding impl should return `self` for chaining, regardless of what the inner type's
method returns. The modifier instructs [`def`] to call the inner method for
its side effects and then return `self`.

This is the natural choice for fluent or builder-style APIs where the inner type's method
mutates state in place (or returns the inner type) but the caller expects to chain calls
on the outer wrapper type.

- Use [`as_into`] instead when the inner method returns a value that should be
  converted to the outer type with `.into()`.
- Use [`as_expr`] for arbitrary transformations that neither returning
  `self` nor `.into()` can express.

# Syntax

```text
#[ndfwd::as_self]
fn METHOD(...) -> ReturnType;
```

The attribute takes no arguments and must be placed on a method declaration inside a
`#[ndfwd::decl]` trait. It is a marker only; it has no effect at the declaration site
and is erased from the trait definition. It also **must** be specified in a fully
qualified path only.

# Effect

Without the modifier, [`def`] generates a forwarding body that returns the
inner call's result directly:

```rust,ignore
// without #[as_self]
fn method(&mut self) -> ReturnType {
    self.forward_mut().method()
}
```

With `#[as_self]`, it calls the inner method and then returns `self`:

```rust,ignore
// with #[as_self]
fn method(&mut self) -> ReturnType {
    self.forward_mut().method();
    self
}
```

# Example

```rust
#[ndfwd::decl]
pub trait Configure: Sized {
    /// Sets a label. Returns `self` for chaining.
    #[ndfwd::as_self]
    fn set_label(&mut self, label: &str) -> &mut Self;

    /// Sets a value. Returns `self` for chaining.
    #[ndfwd::as_self]
    fn set_value(&mut self, value: i32) -> &mut Self;
}

#[ndfwd::def(self.0 with Inner: Configure)]
struct Outer(Inner);

struct Inner {
    label: String,
    value: i32,
}

impl Configure for Inner {
    fn set_label(&mut self, label: &str) -> &mut Self {
        self.label = label.to_owned();
        self
    }

    fn set_value(&mut self, value: i32) -> &mut Self {
        self.value = value;
        self
    }
}

let mut cfg = Outer(Inner { label: String::new(), value: 0 });

cfg.set_label("example").set_value(42);
```

# See also

- [`as_into`] — wraps the forwarded return value with `.into()`.
- [`as_expr`] — transforms the forwarded return value with an arbitrary closure.
- [`decl`] — the trait-level macro that recognises this modifier.
- [`def`] — the type-level macro that generates the forwarding body.
