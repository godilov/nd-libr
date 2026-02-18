Forward formatting traits to an inner field.

# When to use

Use `#[ndfwd::fmt]` when a wrapper type should display and format itself by delegating
to the formatting behaviour of its inner field. The macro implements the full family of
standard formatting traits in one annotation.

- When you need dereferencing and conversion behaviour instead, use [`#[ndfwd::std]`].
- When you need comparison behaviour, use [`#[ndfwd::cmp]`].

# Syntax

```text
#[ndfwd::fmt(EXPR with TYPE)]
```

- **`EXPR`** — a Rust expression that evaluates to the inner field (e.g. `self.0` or
  `self.inner`). Used verbatim in every generated method body.
- **`TYPE`** — the type of the inner field. Used to form the bounds on the generated
  impls.

The macro can be applied to **structs**, **enums**, and **unions**.

# Implemented traits

All five impls are emitted unconditionally, but each carries its own conditional bound.

| Trait                | Format specifier | Bound required on `TYPE` |
| -------------------- | ---------------- | ------------------------ |
| `std::fmt::Display`  | `{}`             | `TYPE: Display`          |
| `std::fmt::Binary`   | `{:b}`           | `TYPE: Binary`           |
| `std::fmt::Octal`    | `{:o}`           | `TYPE: Octal`            |
| `std::fmt::LowerHex` | `{:x}`           | `TYPE: LowerHex`         |
| `std::fmt::UpperHex` | `{:X}`           | `TYPE: UpperHex`         |

# Generated impls

Given the annotation `#[ndfwd::fmt(EXPR with TYPE)]` on type `Outer`, the macro emits
the following impls (written here without generics for clarity):

```rust,ignore
impl std::fmt::Display for Outer where TYPE: std::fmt::Display {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { EXPR.fmt(f) }
}
impl std::fmt::Binary for Outer where TYPE: std::fmt::Binary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { EXPR.fmt(f) }
}
impl std::fmt::Octal for Outer where TYPE: std::fmt::Octal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { EXPR.fmt(f) }
}
impl std::fmt::LowerHex for Outer where TYPE: std::fmt::LowerHex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { EXPR.fmt(f) }
}
impl std::fmt::UpperHex for Outer where TYPE: std::fmt::UpperHex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { EXPR.fmt(f) }
}
```

# Examples

```rust
// ── Integer flags ────────────────────────────────────────────────────────────

#[ndfwd::fmt(self.0 with u32)]
#[derive(Clone, Copy)]
struct Flags(u32);

let f = Flags(0b1011_0100);
assert_eq!(format!("{f}"),    "180");
assert_eq!(format!("{f:b}"),  "10110100");
assert_eq!(format!("{f:o}"),  "264");
assert_eq!(format!("{f:x}"),  "b4");
assert_eq!(format!("{f:X}"),  "B4");

// ── Named-field struct ───────────────────────────────────────────────────────

#[ndfwd::fmt(self.value with f64)]
#[derive(Clone, Copy)]
struct Temperature {
    value: f64,
}

let t = Temperature { value: 36.6 };
assert_eq!(format!("{t}"), "36.6");

// ── Generic wrapper ──────────────────────────────────────────────────────────

#[ndfwd::fmt(self.0 with T)]
#[derive(Clone, Copy)]
struct Annotated<T>(T);

assert_eq!(format!("{}", Annotated(42u32)),     "42");
assert_eq!(format!("{:x}", Annotated(255u32)),  "ff");
assert_eq!(format!("{:X}", Annotated(255u32)),  "FF");
```

# See also

- [`std`] — forwards `Deref`, `DerefMut`, `AsRef`, `AsMut`, `FromIterator`.
- [`cmp`] — forwards `PartialEq`, `Eq`, `PartialOrd`, `Ord`.
