# NdLibr Library

**NdLibr meta-library**

## Start

```toml
[dependencies]
ndlibr = "*"
```

**Feature-flags:**

- `all` - enable all features.
- `assert` - include `ndassert` dependency.
- `fwd` - include `ndfwd` dependency.
- `ops` - include `ndops` dependency.
- `crypto` - include `ndcrypto` dependency (exposed via `ndlibr::crypto`).
- `ext` - include `ndext` dependency (exposed via `ndlibr::ext`).
- `mem` - include `ndmem` dependency (exposed via `ndlibr::mem`).
- `num` - include `ndnum` dependency (exposed via `ndlibr::num`).

## License

MIT License
