# NdOps Procedural Macros

**Zero-boilerplate operations implementation procedural macros**

## Start

```toml
[dependencies]
ndops = "*"
ndcore = "*" # Nd-kind operations
```

## Features

#### Kinds

The crate allows implementing operations in six **kinds**: `@stdmut`, `@stdbin`, `@stdun`, `@ndmut`, `@ndbin`, `@ndun`.
Each kind determines set of **operations** it supports, set of **traits** it supports and **signature** syntax.

| Kind      | Operations                                                     | Traits        |
| --------- | -------------------------------------------------------------- | ------------- |
| `@stdmut` | `+=`, `-=`, `\*=`, `/=`, `%=`, `\|=`, `&=`, `^=`, `<<=`, `>>=` | [`std::ops`]  |
| `@ndmut`  | `+=`, `-=`, `\*=`, `/=`, `%=`, `\|=`, `&=`, `^=`, `<<=`, `>>=` | `ndcore::ops` |
| `@stdbin` | `+`, `-`, `\*`, `/`, `%`, `\|`, `&`, `^`, `<<`, `>>`           | [`std::ops`]  |
| `@ndbin`  | `+`, `-`, `\*`, `/`, `%`, `\|`, `&`, `^`, `<<`, `>>`           | `ndcore::ops` |
| `@stdun`  | `!`, `-`                                                       | [`std::ops`]  |
| `@ndun`   | `!`, `-`                                                       | `ndcore::ops` |

#### Modes

The crate allows implementing operations in seven **modes**: `Default`, `Checked`, `Strict`, `Wrapping`, `Saturating`, `Overflowing`, `Unbounded`.
Each mode is used within specific operations set.

For more info, see `ndcore::ops` and [syntax](#syntax) documentation.

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

## Syntax

```text
ndops::def! { <kind> <generics> <signature>, [
    (<operation> <expr> <conditions>?),*
] }

ndops::fwd! { <kind> <generics> <signature>, <impl> [
    (<operation> <conditions>?),*
] }

<kind> := @stdmut | @stdbin | @stdun | @ndmut | @ndbin | @ndun
<mode> := "" | @checked | @strict | @wrapping | @saturating | @overflowing | @unbounded

<operation> := <op> <mode>?

<generics> := <<param>,*> <conditions>?
<conditions> := where [<predicate>,*]

<signature> :=
    (<pat>: &mut <type>, (*)? <pat>: <type>)                    | // @stdmut
    ((*)? <pat>: <type>, (*)? <pat>: <type>) -> <type>          | // @stdbin
    ((*)? <pat>: <type>)                     -> <type>          | // @stdun
    (<pat>: &mut <type>, <pat>: &<type>)           <impl_type>? | // @ndmut
    (<pat>: &<type>,     <pat>: &<type>) -> <type> <impl_type>? | // @ndbin
    (<pat>: &<type>)                     -> <type> <impl_type>? | // @ndun

<impl_type> := for <type> | for [<type>,*]
<impl> :=
    (<type>) (<lhs_expr>) (<rhs_expr>) | // @stdmut, @stdbin, @ndmut, @ndbin
    (<type>) (<value_expr>)            | // @stdun, @ndun
```
