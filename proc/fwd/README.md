# Nd Forward

Zero-boilerplate forwarding trait implementations for Rust.

`ndfwd` provides attribute macros that generate `impl` blocks delegating to an
inner field or expression, eliminating the repetitive glue code that wrapping
types otherwise require. It covers two complementary workflows:

- **Bundle macros** — [`macro@std`], [`cmp`], [`fmt`] — generate a fixed set of standard
  library trait implementations for a type in a single annotation.
- **Custom forwarding** — [`decl`] + [`def`] — let you declare any trait as
  forwardable and then implement it for any number of wrapping types, with full
  control over return-value adaptation via the [`as_into`], [`as_self`], and
  [`as_expr`] marker attributes.

## Quick start

```toml
[dependencies]
ndfwd = "*"
```

```rust
// Forward Deref, DerefMut, AsRef, AsMut, and FromIterator to the inner Vec<u8>
#[ndfwd::std(self.0 with Vec<u8>)]
struct Buffer(Vec<u8>);

impl From<Vec<u8>> for Buffer {
    fn from(v: Vec<u8>) -> Self { Buffer(v) }
}

// Forward PartialEq, Eq, PartialOrd, Ord to the inner i64
#[ndfwd::cmp(self.0 with i64)]
struct Meters(i64);

// Forward Display, Binary, Octal, LowerHex, UpperHex to the inner u32
#[ndfwd::fmt(self.0 with u32)]
struct Flags(u32);
```

## Bundle macros

These macros are self-contained: apply them to a struct, enum, or union together
with an `expr with Type` argument and they emit the corresponding `impl` blocks
immediately.

### `#[std(expr with Type)]`

Generates [`Deref`], [`DerefMut`], [`AsRef`], [`AsMut`], and [`FromIterator`].
`AsRef`, `AsMut`, and `FromIterator` carry blanket `where` bounds and are
available for any inner type that satisfies them. `FromIterator` requires
`Self: From<Type>`.

[`Deref`]: std::ops::Deref
[`DerefMut`]: std::ops::DerefMut
[`AsRef`]: std::convert::AsRef
[`AsMut`]: std::convert::AsMut
[`FromIterator`]: std::iter::FromIterator

```rust
#[ndfwd::std(self.0 with Vec<u8>)]
struct Buffer(Vec<u8>);
```

### `#[cmp(expr with Type)]`

Generates [`PartialEq`], [`Eq`], [`PartialOrd`], and [`Ord`], each conditioned
on the inner type satisfying the respective bound.

```rust
#[ndfwd::cmp(self.0 with i64)]
struct Meters(i64);

assert!(Meters(10) > Meters(5));
```

### `#[fmt(expr with Type)]`

Generates [`Display`], [`Binary`], [`Octal`], [`LowerHex`], and [`UpperHex`],
each conditioned on the inner type satisfying the respective bound.

[`Display`]: std::fmt::Display
[`Binary`]: std::fmt::Binary
[`Octal`]: std::fmt::Octal
[`LowerHex`]: std::fmt::LowerHex
[`UpperHex`]: std::fmt::UpperHex

```rust
#[ndfwd::fmt(self.0 with u32)]
struct Flags(u32);

println!("{:b}", Flags(0b1010));  // "1010"
```

## Custom forwarding

For your own traits use the two-step `decl` / `def` workflow.

### Step 1 — `#[ndfwd::decl]`

Annotate a trait with `#[ndfwd::decl]`. The trait is emitted unchanged; in
addition, a hidden `macro_rules!` helper is generated that [`def`] will use
internally to produce `impl` blocks.

```rust
#[ndfwd::decl]
pub trait Greet {
    fn hello(&self) -> String;
    fn goodbye(self) -> String;
}
```

Every method is forwarded automatically based on the `self` receiver:

- `&mut self` → `self.forward_mut().method(…)`
- `&self` → `self.forward_ref().method(…)`
- `self` → `self.forward().method(…)`

**Argument type support.** Plain `Self`, `&Self`, and `&mut Self` arguments are
transparently forwarded via the corresponding `forward` helper. `Self` appearing
as a tuple element is forwarded element-by-element. `Self` inside an array or
slice is **not supported** and will produce a compile error. `fn` pointers,
`impl Trait`, and `dyn Trait` arguments are always passed through unchanged.

**Return types** are not inspected — the raw return value is used as-is unless
a modifier attribute is applied (see below).

### Step 2 — `#[ndfwd::def(expr with Type: full::path::to::Trait [where …])]`

Annotate a concrete struct, enum, or union with `#[ndfwd::def]`. The macro
generates the full `impl Trait for Type` block, forwarding every item to the
inner expression.

> **The trait path must be fully qualified.** A bare trait name without a
> module path will not resolve the hidden forwarding macro and will produce a
> compile error.
>
> **Crate-local only.** `#[ndfwd::def]` can only forward traits declared with
> `#[ndfwd::decl]` within the same crate. Traits defined in external crates
> cannot be auto-implemented this way.

```rust
struct Inner;

impl Greet for Inner {
    fn hello(&self) -> String { "Hello!".into() }
    fn goodbye(self) -> String { "Goodbye!".into() }
}

#[ndfwd::def(self.0 with Inner: crate::greet::Greet)]
struct Wrapper(Inner);

assert_eq!(Wrapper(Inner).hello(), "Hello!");
```

An optional `where` clause can be appended to add extra bounds to the generated
`impl`:

```rust
#[ndfwd::def(self.0 with Inner: crate::some::Trait where Inner: Clone)]
struct Wrapper(Inner);
```

### Return-value adaptation

By default the forwarded call's return value is passed through unchanged. Three
marker attributes, placed on individual method signatures _inside_ the
`#[ndfwd::decl]`-annotated trait, let you control this. All three must be
written as full paths — bare names such as `#[as_into]` are not recognised.

#### `#[ndfwd::as_into]`

Wraps the return value with `.into()`. Use this when the inner method returns
the inner type and the outer type implements `From<Inner>`.

```rust
#[ndfwd::decl]
pub trait Builder {
    #[ndfwd::as_into]
    fn push(self, item: u8) -> Self;
}
```

Generated body: `self.forward().push(item).into()`

#### `#[ndfwd::as_self]`

Calls through for its side effects and returns `self`, discarding the inner
method's return value. Use this for fluent APIs where the outer type must
return `&mut Self` while the inner type returns `&mut Inner`.

```rust
#[ndfwd::decl]
pub trait Config {
    #[ndfwd::as_self]
    fn set_timeout(&mut self, ms: u64) -> &mut Self;
}
```

Generated body: `self.forward_mut().set_timeout(ms); self`

#### `#[ndfwd::as_expr(|val| expr)]`

Passes the return value through an arbitrary closure. The argument must be
a closure expression; it receives the raw return value of the inner call.

```rust
#[ndfwd::decl]
pub trait Container {
    #[ndfwd::as_expr(|v| v.map(Self::from))]
    fn first(&self) -> Option<Self>;
}
```

Generated body: `(|v| v.map(Self::from))(self.forward_ref().first())`

## Complete example

```rust
// ── Inner type ────────────────────────────────────────────────────────────────

#[derive(Clone)]
struct Inner(Vec<i32>);

impl Inner {
    fn sum(&self) -> i32 { self.0.iter().sum() }
    fn push(mut self, v: i32) -> Self { self.0.push(v); self }
}

// ── Declare a forwardable trait ───────────────────────────────────────────────

#[ndfwd::decl]
pub trait Stats {
    fn sum(&self) -> i32;

    #[ndfwd::as_into]
    fn push(self, v: i32) -> Self;
}

// ── Wrapping type ─────────────────────────────────────────────────────────────

#[ndfwd::def(self.0 with Inner: crate::Stats)]
#[ndfwd::std(self.0 with Inner)]
#[ndfwd::cmp(self.0 with Inner)]
struct Metrics(Inner);

impl From<Inner> for Metrics {
    fn from(inner: Inner) -> Self { Metrics(inner) }
}

// ── Usage ─────────────────────────────────────────────────────────────────────

let m = Metrics(Inner(vec![1, 2, 3]));
assert_eq!(m.sum(), 6);

let m = m.push(4);           // returns Metrics via ndfwd::as_into
assert_eq!(m.sum(), 10);
```

## License

Licensed under [MIT License](LICENSE-MIT).
