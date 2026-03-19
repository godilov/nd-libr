//! # NdOperations Definition Generic Example

use std::ops::*;

struct Any<N>(N);

// Required (optionally) to construct operation result
impl<N> From<N> for Any<N> {
    fn from(value: N) -> Self {
        Any(value)
    }
}

// Implements corresponding ndext::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::def! { @ndmut <N: Copy> (lhs: &mut Any<N>, rhs: &Any<N>), [
    += lhs.0 += rhs.0 where [N: AddAssign<N>],
    -= lhs.0 -= rhs.0 where [N: SubAssign<N>],
    *= lhs.0 *= rhs.0 where [N: MulAssign<N>],
    /= lhs.0 /= rhs.0 where [N: DivAssign<N>],
    %= lhs.0 %= rhs.0 where [N: RemAssign<N>],
    |= lhs.0 |= rhs.0 where [N: BitOrAssign<N>],
    &= lhs.0 &= rhs.0 where [N: BitAndAssign<N>],
    ^= lhs.0 ^= rhs.0 where [N: BitXorAssign<N>],
] }

// Implements corresponding ndext::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::def! { @ndmut <N: Copy> (lhs: &mut Any<N>, rhs: usize), [
    <<= lhs.0 <<= rhs where [N: ShlAssign<usize>],
    >>= lhs.0 >>= rhs where [N: ShrAssign<usize>],
] }

// Implements corresponding ndext::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::def! { @ndbin <N: Copy> (lhs: &Any<N>, rhs: &Any<N>) -> Any<N>, [
    + lhs.0 + rhs.0 where [N: Add<N, Output = N>],
    - lhs.0 - rhs.0 where [N: Sub<N, Output = N>],
    * lhs.0 * rhs.0 where [N: Mul<N, Output = N>],
    / lhs.0 / rhs.0 where [N: Div<N, Output = N>],
    % lhs.0 % rhs.0 where [N: Rem<N, Output = N>],
    | lhs.0 | rhs.0 where [N: BitOr<N, Output = N>],
    & lhs.0 & rhs.0 where [N: BitAnd<N, Output = N>],
    ^ lhs.0 ^ rhs.0 where [N: BitXor<N, Output = N>],
] }

// Implements corresponding ndext::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::def! { @ndbin <N: Copy> (lhs: &Any<N>, rhs: usize) -> Any<N>, [
    << lhs.0 << rhs where [N: Shl<usize, Output = N>],
    >> lhs.0 >> rhs where [N: Shr<usize, Output = N>],
] }

// Implements corresponding ndext::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::def! { @ndun <N: Copy> (value: &Any<N>) -> Any<N>, [
    ! !value.0 where [N: Not<Output = N>],
    - -value.0 where [N: Neg<Output = N>],
] }

// Implements corresponding std::ops::* for (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::def! { @stdmut <N: Copy> (lhs: &mut Any<N>, *rhs: &Any<N>), [
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
ndops::def! { @stdmut <N: Copy> (lhs: &mut Any<N>, *rhs: &Any<N>), [
    <<= lhs.0 <<= rhs.0 where [N: ShlAssign<N>],
    >>= lhs.0 >>= rhs.0 where [N: ShrAssign<N>],
] }

// Implements corresponding std::ops::* for (&Any, &Any), (&Any, Any), (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::def! { @stdbin <N: Copy> (*lhs: &Any<N>, *rhs: &Any<N>) -> Any<N>, [
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
ndops::def! { @stdbin <N: Copy> (*lhs: &Any<N>, *rhs: &Any<N>) -> Any<N>, [
    << lhs.0 << rhs.0 where [N: Shl<N, Output = N>],
    >> lhs.0 >> rhs.0 where [N: Shr<N, Output = N>],
] }

// Implements corresponding std::ops::* for &Any, Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::def! { @stdun <N: Copy> (*value: &Any<N>) -> Any<N>, [
    ! !value.0 where [N: Not<Output = N>],
    - -value.0 where [N: Neg<Output = N>],
] }

fn main() {}
