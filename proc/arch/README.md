# NdArch

**Architecture-aware procedural macros**

## Start

```toml
[dependencies]
ndarch = "*"
```

## Examples

```rust
#[ndarch::align]
struct Any<T>(T);

#[cfg(target_arch = "x86")]
assert_eq!(std::mem::align_of::<Any::<usize>>(), 64);

#[cfg(target_arch = "x86_64")]
assert_eq!(std::mem::align_of::<Any::<usize>>(), 64);

#[cfg(target_arch = "arm")]
assert_eq!(std::mem::align_of::<Any::<usize>>(), 64);

#[cfg(target_arch = "aarch64")]
assert_eq!(std::mem::align_of::<Any::<usize>>(), 128);
```

## License

MIT License
