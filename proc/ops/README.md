# NdOperations Procedural Macros

**Zero-boilerplate operations implementation procedural macros**

## Start

```toml
[dependencies]
ndops = "*"
ndext = "*" # Nd-kind operations
```

## Features

#### Kinds

The crate allows implementing operations in six **kinds**: `@stdmut`, `@stdbin`, `@stdun`, `@ndmut`, `@ndbin`, `@ndun`.
Each kind determines set of **operations** it supports, set of **traits** it supports and **signature** syntax.

| Kind      | Operations                                                     | Traits       |
| --------- | -------------------------------------------------------------- | ------------ |
| `@stdmut` | `+=`, `-=`, `\*=`, `/=`, `%=`, `\|=`, `&=`, `^=`, `<<=`, `>>=` | [`std::ops`] |
| `@ndmut`  | `+=`, `-=`, `\*=`, `/=`, `%=`, `\|=`, `&=`, `^=`, `<<=`, `>>=` | `ndext::ops` |
| `@stdbin` | `+`, `-`, `\*`, `/`, `%`, `\|`, `&`, `^`, `<<`, `>>`           | [`std::ops`] |
| `@ndbin`  | `+`, `-`, `\*`, `/`, `%`, `\|`, `&`, `^`, `<<`, `>>`           | `ndext::ops` |
| `@stdun`  | `!`, `-`                                                       | [`std::ops`] |
| `@ndun`   | `!`, `-`                                                       | `ndext::ops` |

#### Modes

The crate allows implementing operations in seven **modes**: `Default`, `Checked`, `Strict`, `Wrapping`, `Saturating`, `Overflowing`, `Unbounded`.
Each mode is used within specific operations set.

For more info, see `ndext::ops` documentation.

#### Generics

The crate allows implementing operations for **generic** types with **signature-level** and **operation-level**
conditions, merging them when implementing every specific operation.

#### Completeness

The crate allows implementing **complete** set of `Std-kind` operations with regard to **non-reference**/**reference** types.
The syntax supports **asterisk notation** before `lhs`/`rhs`/`value` patterns in signature to specify implementation types.

- For **non-reference** types, the asterisk before pattern implements operations for **non-reference** types.
- For **reference** types, the asterisk before pattern implements operation for **reference** and **non-reference** types.

| Kind      | Arguments                     | Types                                                      |
| --------- | ----------------------------- | ---------------------------------------------------------- |
| `@stdmut` | `(lhs: &mut Lhs, *rhs: &Rhs)` | `(Lhs, &Rhs)`, `(Lhs, Rhs)`                                |
| `@stdmut` | `(lhs: &mut Lhs, rhs: &Rhs)`  | `(Lhs, &Rhs)`                                              |
| `@stdbin` | `(*lhs: &Lhs, *rhs: &Rhs)`    | `(&Lhs, &Rhs)`, `(&Lhs, Rhs)`, `(Lhs, &Rhs)`, `(Lhs, Rhs)` |
| `@stdbin` | `(lhs: &Lhs, *rhs: &Rhs)`     | `(&Lhs, &Rhs)`, `(&Lhs, Rhs)`                              |
| `@stdbin` | `(*lhs: &Lhs, rhs: &Rhs)`     | `(&Lhs, &Rhs)`, `(Lhs, &Rhs)`                              |
| `@stdbin` | `(lhs: &Lhs, rhs: &Rhs)`      | `(&Lhs, &Rhs)`                                             |
| `@stdun`  | `(*value: &Value)`            | `(&Value)`, `(Value)`                                      |
| `@stdun`  | `(value: &Value)`             | `(&Value)`                                                 |

## License

MIT License
