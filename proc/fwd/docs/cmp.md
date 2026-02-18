Forward comparison traits to an inner field.

# When to use

Use `#[ndfwd::cmp]` when a wrapper type should compare by delegating to the comparison
behaviour of its inner field. The macro implements the full family of standard comparison
traits in one annotation.

- When you need dereferencing and conversion behaviour instead, use [`#[ndfwd::std]`].
- When you need formatting behaviour, use [`#[ndfwd::fmt]`].

# Syntax

```text
#[ndfwd::cmp(EXPR with TYPE)]
```

- **`EXPR`** — a Rust expression that evaluates to the inner field (e.g. `self.0` or
  `self.inner`). Used verbatim in every generated method body.
- **`TYPE`** — the type of the inner field. Used to form the bounds on the generated
  impls.

The macro can be applied to **structs**, **enums**, and **unions**.

# Implemented traits

All four impls are emitted unconditionally, but each carries its own conditional bound.

| Trait        | Bound required on `TYPE` |
| ------------ | ------------------------ |
| `PartialEq`  | `TYPE: PartialEq`        |
| `Eq`         | `TYPE: Eq`               |
| `PartialOrd` | `TYPE: PartialOrd`       |
| `Ord`        | `TYPE: Ord`              |

# Generated impls

Given the annotation `#[ndfwd::cmp(EXPR with TYPE)]` on type `Outer`, the macro emits
the following impls (written here without generics for clarity):

```rust,ignore
impl Eq for Outer where TYPE: Eq {}

impl Ord for Outer where TYPE: Ord {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        EXPR.cmp(&other.FIELD)
    }
}

impl PartialEq for Outer where TYPE: PartialEq {
    fn eq(&self, other: &Self) -> bool {
        EXPR.eq(&other.FIELD)
    }
}

impl PartialOrd for Outer where TYPE: PartialOrd {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        EXPR.partial_cmp(&other.FIELD)
    }
}
```

# Examples

```rust
// ── Newtype ordering ─────────────────────────────────────────────────────────

#[ndfwd::cmp(self.0 with u32)]
#[derive(Clone, Copy)]
struct Version(u32);

assert!(Version(2) > Version(1));
assert!(Version(1) < Version(2));
assert_eq!(Version(3), Version(3));

let mut versions = [Version(3), Version(1), Version(2)];
versions.sort();
assert_eq!(versions, [Version(1), Version(2), Version(3)]);

// ── Named-field struct ───────────────────────────────────────────────────────

#[ndfwd::cmp(self.score with i32)]
#[derive(Clone, Copy)]
struct Player {
    score: i32,
    name: &'static str, // not involved in comparison
}

let a = Player { score: 10, name: "Alice" };
let b = Player { score: 20, name: "Bob" };
assert!(a < b);

// ── Generic wrapper ──────────────────────────────────────────────────────────

#[ndfwd::cmp(self.0 with T)]
#[derive(Clone, Copy)]
struct Ranked<T>(T);

assert!(Ranked(1.0f64) < Ranked(2.0f64));
assert_eq!(Ranked("alpha"), Ranked("alpha"));
```

# See also

- [`std`] — forwards `Deref`, `DerefMut`, `AsRef`, `AsMut`, `FromIterator`.
- [`fmt`] — forwards `Display`, `Binary`, `Octal`, `LowerHex`, `UpperHex`.
