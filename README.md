# nd-libr

## Requirements

- [Cargo Asm](https://github.com/pacak/cargo-show-asm) (`cargo asm`/`optional`)

## Commands

### Clone

```shell
git clone https://github.com/godilov/nd-libr.git
```

### Build

Compiles `ndcli`/`ndlib`/`ndproc` packages

```shell
cargo build
```

### Verify

Executes all tests to verify correctness

```shell
cargo test
```

Executes all benches to verify performance

```shell
cargo bench
```

Emits Assembly for functions in `ndlib` package. `asm` submodules contain monomorphized versions for generics

```shell
cargo asm -p ndlib --lib
```

### Run

Calculates primes by count - first 256

```shell
cargo run -- primes by-count 256
```

Calculates primes by limit - up-to 256

```shell
cargo run -- primes by-limit 256
```
