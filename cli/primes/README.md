# NdPrime CLI

## Run

**Intro:**

```shell
cargo run --bin ndprimes -- --help
```

**Generate primes with count:**

```shell
# Generates prime numbers with 256 as count
cargo run --bin ndprimes -- by-count 256
```

**Generate primes with limit:**

```shell
# Generates prime numbers with 1024 as limit
cargo run --bin ndprimes -- by-limit 1024
```

**Generate random primes of 60-bits length:**

```shell
# 60 - length in binary
# 1024 - amount
cargo run --bin ndprimes -- rand 60 1024
```

## License

MIT License
