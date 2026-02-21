# NdArch

**Architecture-aware facilities**

## Syntax

#### [`ndarch::align`]([align])

```text
#[ndarch::align]
(STRUCT | ENUM | UNION)
```

The macro aligns struct, enum or union according to approximate architecture cacheline size.

| Architecture | Alignment |
| ------------ | --------- |
| x86          | 64 bytes  |
| x86_64       | 64 bytes  |
| arm          | 64 bytes  |
| aarch64      | 128 bytes |

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
