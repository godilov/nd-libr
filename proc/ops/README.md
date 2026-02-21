# NdOps

**Zero-boilerplate operations implementation procedural macros**

The crate allows to define complex and structured operations implementation in all combinations.

- [`ndops::all!`]([all]) implements `std::ops::*` and `ndcore::ops::*` operations with **explicitly** provided expressions.
- [`ndops::all_auto!`]([all_auto]) implements `std::ops::*` and `ndcore::ops::*` operations with **implicitly** derived expressions.

## Start

```toml
[dependencies]
ndops = "*"
ndcore = "*" # Optional: Nd-kind only
```

## Features

#### Kinds

The crate allows to implement operations in six **kinds**.
Each kind determines set of **operations** it supports, set of **traits** it supports and **signature** syntax.

| Kind      | Operations                                                     | Traits           |
| --------- | -------------------------------------------------------------- | ---------------- |
| `@stdmut` | `+=`, `-=`, `\*=`, `/=`, `%=`, `\|=`, `&=`, `^=`, `<<=`, `>>=` | `std::ops::*`    |
| `@ndmut`  | `+=`, `-=`, `\*=`, `/=`, `%=`, `\|=`, `&=`, `^=`, `<<=`, `>>=` | `ndcore::ops::*` |
| `@stdbin` | `+`, `-`, `\*`, `/`, `%`, `\|`, `&`, `^`, `<<`, `>>`           | `std::ops::*`    |
| `@ndbin`  | `+`, `-`, `\*`, `/`, `%`, `\|`, `&`, `^`, `<<`, `>>`           | `ndcore::ops::*` |
| `@stdun`  | `-`, `!`                                                       | `std::ops::*`    |
| `@ndun`   | `-`, `!`                                                       | `ndcore::ops::*` |

#### Completeness

The crate allows to implement **complete** set of `Std-kind` operations with regard to non-reference/reference types.
The syntax supports **asterisk notation** before `lhs`/`rhs`/`value` patterns in signature to specify implementation types.

- For reference types, the asterisk before pattern implements operation for **reference** and **non-reference** types.
- For non-reference types, the asterisk before pattern implements operations for **non-reference** types.

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

#### Generics

The crate allows to implement operations for **generic** types with **signature-level** and **operation-level** conditions for types,
merging them when implementing every specific operation.

#### Expressions

- [`ndops::all!`]([all]) implements operations with explicitly provided expressions.
- [`ndops::all_auto!`]([all_auto]) implements operations with implicitly derived expressions.

| Kind                    | Expression               |
| ----------------------- | ------------------------ |
| `ndops::all! *mut`      | `EXPR`                   |
| `ndops::all! *bin`      | `<TY>::from(EXPR)`       |
| `ndops::all! *un`       | `<TY>::from(EXPR)`       |
| `ndops::all_auto! *mut` | `EXPR`                   |
| `ndops::all_auto! *bin` | `<TY>::from(LHS OP RHS)` |
| `ndops::all_auto! *un`  | `<TY>::from(OP VALUE)`   |

## Syntax

### [`ndops::all!`]([all])

```text
ndops::all! { KIND SIGNATURE, [
    (OP EXPR OP_CONDITIONS?),*
] }

KIND := @stdmut | @stdbin | @stdun | @ndmut | @ndbin | @ndun
OP_CONDITIONS := where [(OP_PREDICATE),*]
```

`SIGNATURE` and `OP` depend on `KIND`.

- For `SIGNATURE` reference, see [section](#signatures).
- For `OP` reference, see [section](#kinds).

### [`ndops::all_auto!`]([all_auto])

```text
ndops::all_auto! { KIND SIGNATURE, [
    (OP OP_CONDITIONS?),*
] }

KIND := @stdmut | @stdbin | @stdun | @ndmut | @ndbin | @ndun
OP_CONDITIONS := where [(OP_PREDICATE),*]
```

`SIGNATURE` and `OP` depend on `KIND`.

- For `SIGNATURE` reference, see [section](#signatures).
- For `OP` reference, see [section](#kinds).

### Signatures

- `Std-kind` signatures allows to implement operations with **asterisk notation**.
- `Nd-kind` signatures allows to implement operations for multiple independent types.

#### `@stdmut`

```text
(<GENERICS> SIG_CONDITIONS?)? (LHS_PAT: &mut LHS_TY, (*)? RHS_PAT: RHS_TY)

SIG_CONDITIONS := where [(SIG_PREDICATE),*]
```

#### `@stdbin`

```text
(<GENERICS> SIG_CONDITIONS?)? ((*)? LHS_PAT: LHS_TY, (*)? RHS_PAT: RHS_TY) -> TY

SIG_CONDITIONS := where [(SIG_PREDICATE),*]
```

#### `@stdun`

```text
(<GENERICS> SIG_CONDITIONS?)? ((*)? VAL_PAT: VAL_TY) -> TY

SIG_CONDITIONS := where [(SIG_PREDICATE),*]
```

#### `@ndmut`

```text
(<GENERICS> SIG_CONDITIONS?)? (LHS_PAT: &mut LHS_TY, RHS_PAT: &RHS_TY) -> (for TY | for [(TY),*])?

SIG_CONDITIONS := where [(SIG_PREDICATE),*]
```

#### `@ndbin`

```text
(<GENERICS> SIG_CONDITIONS?)? (LHS_PAT: &LHS_TY, RHS_PAT: &RHS_TY) -> (for TY | for [(TY),*])?

SIG_CONDITIONS := where [(SIG_PREDICATE),*]
```

#### `@ndun`

```text
(<GENERICS> SIG_CONDITIONS?)? (VAL_PAT: &VAL_TY) -> (for TY | for [(TY),*])?

SIG_CONDITIONS := where [(SIG_PREDICATE),*]
```

## Examples

### All

```rust
struct Num(i64);

// Required (optionally) to construct operation result
impl From<i64> for Num {
    fn from(value: i64) -> Self {
        Num(value)
    }
}

// Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
ndops::all! { @stdmut (lhs: &mut Num, *rhs: &Num), [
    += lhs.0 += rhs.0,
    -= lhs.0 -= rhs.0,
    *= lhs.0 *= rhs.0,
    /= lhs.0 /= rhs.0,
    %= lhs.0 %= rhs.0,
    |= lhs.0 |= rhs.0,
    &= lhs.0 &= rhs.0,
    ^= lhs.0 ^= rhs.0,
] }

// Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
ndops::all! { @stdmut (lhs: &mut Num, *rhs: &Num), [
    <<= lhs.0 <<= rhs.0,
    >>= lhs.0 >>= rhs.0,
] }

// Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
ndops::all! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num, [
    + lhs.0 + rhs.0,
    - lhs.0 - rhs.0,
    * lhs.0 * rhs.0,
    / lhs.0 / rhs.0,
    % lhs.0 % rhs.0,
    | lhs.0 | rhs.0,
    & lhs.0 & rhs.0,
    ^ lhs.0 ^ rhs.0,
] }

// Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
ndops::all! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num, [
    << lhs.0 << rhs.0,
    >> lhs.0 >> rhs.0,
] }

// Implements corresponding std::ops::* for &Num, Num
ndops::all! { @stdun (*value: &Num) -> Num, [
    - -value.0,
    ! !value.0,
] }
```

### All Generic

```rust
use std::ops::*;

struct Any<N>(N);

// Required (optionally) to construct operation result
impl<N> From<N> for Any<N> {
    fn from(value: N) -> Self {
        Any(value)
    }
}

// Implements corresponding std::ops::* for (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all! { @stdmut <N: Copy> (lhs: &mut Any<N>, *rhs: &Any<N>), [
    += lhs.0 += rhs.0 where [N: AddAssign<N>],
    -= lhs.0 -= rhs.0 where [N: SubAssign<N>],
    *= lhs.0 *= rhs.0 where [N: MulAssign<N>],
    /= lhs.0 /= rhs.0 where [N: DivAssign<N>],
    %= lhs.0 %= rhs.0 where [N: RemAssign<N>],
    |= lhs.0 |= rhs.0 where [N: BitOrAssign<N>],
    &= lhs.0 &= rhs.0 where [N: BitAndAssign<N>],
    ^= lhs.0 ^= rhs.0 where [N: BitXorAssign<N>],
] }

// Implements corresponding std::ops::* for (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all! { @stdmut <N: Copy> (lhs: &mut Any<N>, *rhs: &Any<N>), [
    <<= lhs.0 <<= rhs.0 where [N: ShlAssign<N>],
    >>= lhs.0 >>= rhs.0 where [N: ShrAssign<N>],
] }

// Implements corresponding std::ops::* for (&Any, &Any), (&Any, Any), (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all! { @stdbin <N: Copy> (*lhs: &Any<N>, *rhs: &Any<N>) -> Any<N>, [
    + lhs.0 + rhs.0 where [N: Add<N, Output = N>],
    - lhs.0 - rhs.0 where [N: Sub<N, Output = N>],
    * lhs.0 * rhs.0 where [N: Mul<N, Output = N>],
    / lhs.0 / rhs.0 where [N: Div<N, Output = N>],
    % lhs.0 % rhs.0 where [N: Rem<N, Output = N>],
    | lhs.0 | rhs.0 where [N: BitOr<N, Output = N>],
    & lhs.0 & rhs.0 where [N: BitAnd<N, Output = N>],
    ^ lhs.0 ^ rhs.0 where [N: BitXor<N, Output = N>],
] }

// Implements corresponding std::ops::* for (&Any, &Any), (&Any, Any), (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all! { @stdbin <N: Copy> (*lhs: &Any<N>, *rhs: &Any<N>) -> Any<N>, [
    << lhs.0 << rhs.0 where [N: Shl<N, Output = N>],
    >> lhs.0 >> rhs.0 where [N: Shr<N, Output = N>],
] }

// Implements corresponding std::ops::* for &Any, Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all! { @stdun <N: Copy> (*value: &Any<N>) -> Any<N>, [
    - -value.0 where [N: Neg<Output = N>],
    ! !value.0 where [N: Not<Output = N>],
] }
```

### All Auto

```rust
struct Num(i64);

// Required to construct operation result
impl From<i64> for Num {
    fn from(value: i64) -> Self {
        Num(value)
    }
}

// Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
ndops::all_auto! { @stdmut (lhs: &mut Num, *rhs: &Num), (lhs.0) (rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=] }

// Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
ndops::all_auto! { @stdmut (lhs: &mut Num, *rhs: &Num), (lhs.0) (rhs.0) [<<=, >>=] }

// Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
ndops::all_auto! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num, (lhs.0) (rhs.0) [+, -, *, /, %, |, &, ^] }

// Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
ndops::all_auto! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num, (lhs.0) (rhs.0) [<<, >>] }

// Implements corresponding std::ops::* for &Num, Num
ndops::all_auto! { @stdun (*value: &Num) -> Num, (value.0) [-, !] }
```

### All Auto Generic

```rust
use std::ops::*;

struct Any<N>(N);

// Required to construct operation result
impl<N: Copy> From<N> for Any<N> {
    fn from(value: N) -> Self {
        Any(value)
    }
}

// Implements corresponding std::ops::* for (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all_auto! { @stdmut <N: Copy> (lhs: &mut Any<N>, *rhs: &Any<N>), (lhs.0) (rhs.0) [
    += where [N: AddAssign<N>],
    -= where [N: SubAssign<N>],
    *= where [N: MulAssign<N>],
    /= where [N: DivAssign<N>],
    %= where [N: RemAssign<N>],
    |= where [N: BitOrAssign<N>],
    &= where [N: BitAndAssign<N>],
    ^= where [N: BitXorAssign<N>],
] }

// Implements corresponding std::ops::* for (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all_auto! { @stdmut <N: Copy> (lhs: &mut Any<N>, *rhs: &Any<N>), (lhs.0) (rhs.0) [
    <<= where [N: ShlAssign<N>],
    >>= where [N: ShrAssign<N>],
] }

// Implements corresponding std::ops::* for (&Any, &Any), (&Any, Any), (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all_auto! { @stdbin <N: Copy> (*lhs: &Any<N>, *rhs: &Any<N>) -> Any<N>, (lhs.0) (rhs.0) [
    + where [N: Add<N, Output = N>],
    - where [N: Sub<N, Output = N>],
    * where [N: Mul<N, Output = N>],
    / where [N: Div<N, Output = N>],
    % where [N: Rem<N, Output = N>],
    | where [N: BitOr<N, Output = N>],
    & where [N: BitAnd<N, Output = N>],
    ^ where [N: BitXor<N, Output = N>],
] }

// Implements corresponding std::ops::* for (&Any, &Any), (&Any, Any), (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all_auto! { @stdbin <N: Copy> (*lhs: &Any<N>, *rhs: &Any<N>) -> Any<N>, (lhs.0) (rhs.0) [
    << where [N: Shl<N, Output = N>],
    >> where [N: Shr<N, Output = N>],
] }

// Implements corresponding std::ops::* for &Any, Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all_auto! { @stdun <N: Copy> (*value: &Any<N>) -> Any<N>, (value.0) [
    - where [N: Neg<Output = N>],
    ! where [N: Not<Output = N>],
] }
```
