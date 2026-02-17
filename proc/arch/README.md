# Nd Arch

Architecture-dependent proc-macro attributes for Rust.

`ndarch` provides attribute macros that expand to architecture-conditional
`cfg_attr` annotations, letting you express platform-specific concerns — such as
cache-line alignment — without writing repetitive conditional attributes by hand.

## Quick start

Add the crate to your `Cargo.toml`:

```toml
[dependencies]
ndarch = "*"
```

Then annotate your types:

```rust
#[ndarch::align]
struct SimdBuffer([f32; 16]);
```

## Macros

### `#[align]`

Applies an architecture-appropriate cache-line alignment to a struct, enum, or union.

```rust
#[ndarch::align]
struct Foo(u8);
```

Expands to:

```rust
#[cfg_attr(target_arch = "x86",     repr(align(64)))]
#[cfg_attr(target_arch = "x86_64",  repr(align(64)))]
#[cfg_attr(target_arch = "arm",     repr(align(64)))]
#[cfg_attr(target_arch = "aarch64", repr(align(128)))]
struct Foo(u8);
```

Alignment values by architecture:

| Architecture | Alignment |
| ------------ | --------- |
| `x86`        | 64 bytes  |
| `x86_64`     | 64 bytes  |
| `arm`        | 64 bytes  |
| `aarch64`    | 128 bytes |

All other architectures are left unaffected — no alignment attribute is emitted for them.

The macro accepts no arguments and can be applied to structs, enums, and unions.
Applying it to any other item is a compile-time error.

## Examples

```rust
// Struct
#[ndarch::align]
struct Packet {
    header: u32,
    payload: [u8; 60],
}

// Enum
#[ndarch::align]
enum Message {
    Data([u8; 56]),
    Control(u32),
}

// Union
#[ndarch::align]
union RawSlot {
    integer: u64,
    bytes: [u8; 8],
}
```

## License

Licensed under [MIT License](LICENSE-MIT).
