Forward standard container and conversion traits to an inner field.

# When to use

Use `#[ndfwd::std]` when a wrapper type should behave transparently as its inner type for
dereferencing, reference conversion, and iteration. The macro implements the full family
of standard container and conversion traits in one annotation.

When you only need comparison or formatting behaviour, prefer [`cmp`] or [`fmt`] respectively,
which target those specific trait families.

# Syntax

```text
#[ndfwd::std(EXPR with TYPE)]
```

- **`EXPR`** — a Rust expression that evaluates to the inner field (e.g. `self.0` or
  `self.inner`). Used verbatim in every generated method body.
- **`TYPE`** — the type of the inner field. Used to form the bounds on the generated
  impls.

The macro can be applied to **structs**, **enums**, and **unions**.

# Implemented traits

All five impls are emitted unconditionally, but each carries its own conditional bound so
the compiler rejects uses only when the inner type does not satisfy that bound.

| Trait                  | Bound required on `TYPE`                    |
| ---------------------- | ------------------------------------------- |
| `Deref<Target = TYPE>` | _(none)_                                    |
| `DerefMut`             | _(none)_                                    |
| `AsRef<T>`             | `TYPE: AsRef<T>`                            |
| `AsMut<T>`             | `TYPE: AsMut<T>`                            |
| `FromIterator<E>`      | `TYPE: FromIterator<E>`, `Self: From<TYPE>` |

# Generated impls

Given the annotation `#[ndfwd::std(EXPR with TYPE)]` on type `Outer`, the macro emits
the following impls (written here without generics for clarity):

```rust,ignore
impl Deref for Outer {
    type Target = TYPE;
    fn deref(&self) -> &TYPE { &EXPR }
}

impl DerefMut for Outer {
    fn deref_mut(&mut self) -> &mut TYPE { &mut EXPR }
}

impl<T> AsRef<T> for Outer where TYPE: AsRef<T> {
    fn as_ref(&self) -> &T { EXPR.as_ref() }
}

impl<T> AsMut<T> for Outer where TYPE: AsMut<T> {
    fn as_mut(&mut self) -> &mut T { EXPR.as_mut() }
}

impl<E> FromIterator<E> for Outer where Self: From<TYPE>, TYPE: FromIterator<E> {
    fn from_iter<I: IntoIterator<Item = E>>(iter: I) -> Self {
        TYPE::from_iter(iter).into()
    }
}
```

# Examples

```rust
// ── Simple tuple struct ──────────────────────────────────────────────────────

#[ndfwd::std(self.0 with Vec<u8>)]
#[derive(Default)]
struct ByteVec(Vec<u8>);

impl From<Vec<u8>> for ByteVec {
    fn from(v: Vec<u8>) -> Self { ByteVec(v) }
}

// Deref / DerefMut
let mut buf = ByteVec::default();
buf.push(42);
assert_eq!(buf[0], 42);

// AsRef / AsMut
fn takes_slice(s: &[u8]) { let _ = s; }
takes_slice(&buf.as_ref());

// FromIterator
let doubled = buf.iter().map(|b| b * 2).collect::<ByteVec>();
assert_eq!(&*doubled, &[84u8]);

// ── Named-field struct ───────────────────────────────────────────────────────

#[ndfwd::std(self.data with String)]
#[derive(Default)]
struct Label {
    data: String,
}

impl From<String> for Label {
    fn from(s: String) -> Self { Label { data: s } }
}

let mut label = Label::default();
label.push_str("hello");           // via DerefMut → &mut String
assert_eq!(&*label, "hello");      // via Deref    → &String

// ── Generic wrapper ──────────────────────────────────────────────────────────

#[ndfwd::std(self.0 with Vec<T>)]
#[derive(Default)]
struct Bag<T>(Vec<T>);

impl<T> From<Vec<T>> for Bag<T> {
    fn from(v: Vec<T>) -> Self { Bag(v) }
}

let bag: Bag<i32> = (0..3).collect();
assert_eq!(&*bag, &[0, 1, 2]);
```

# See also

- [`cmp`] — forwards `PartialEq`, `Eq`, `PartialOrd`, `Ord`.
- [`fmt`] — forwards `Display`, `Binary`, `Octal`, `LowerHex`, `UpperHex`.
