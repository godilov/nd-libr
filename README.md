# NdLibr

A Rust collection of numerical, cryptography, blockchain and memory-related libraries.

## Start

For entry-point, see [Libr README](/lib/libr/README.md).

## Requirements

- [Cargo Asm](https://github.com/pacak/cargo-show-asm) (`cargo asm`/`optional`)
- [Cargo Nextest](https://github.com/nextest-rs/nextest) (`cargo nextest`/`optional`)

## Commands

### Clone

```shell
git clone https://github.com/godilov/nd-libr.git
```

### Build

Compiles `cli`/`lib`/`proc` packages.

```shell
cargo build
```

### Verify

Executes all tests to verify correctness.

```shell
cargo test --all-features
```

```shell
cargo nextest run --all-features
```

Executes all benches to verify performance (report: `target/criterion/report/index.html`).

```shell
cargo bench
```

Emits Assembly for functions in specified package.

```shell
cargo asm
```

## License

MIT License
