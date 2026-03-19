//! # NdOperations Forward Generic Example

use ndext::ops::*;

struct Any<N>(N);

// Required to construct operation result
impl<N: Copy> From<N> for Any<N> {
    fn from(value: N) -> Self {
        Any(value)
    }
}

// Implements corresponding ndext::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::fwd! { @ndmut <N: Copy> (lhs: &mut Any<N>, rhs: &Any<N>), (N) (&mut lhs.0) (&rhs.0) [
    += where [N: NdAddAssign],
    -= where [N: NdSubAssign],
    *= where [N: NdMulAssign],
    /= where [N: NdDivAssign],
    %= where [N: NdRemAssign],
    |= where [N: NdBitOrAssign],
    &= where [N: NdBitAndAssign],
    ^= where [N: NdBitXorAssign],
] }

// Implements corresponding ndext::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::fwd! { @ndmut <N: Copy> (lhs: &mut Any<N>, rhs: usize), (N) (&mut lhs.0) (rhs) [
    <<= where [N: NdShlAssign],
    >>= where [N: NdShrAssign],
] }

// Implements corresponding ndext::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::fwd! { @ndbin <N: Copy> (lhs: &Any<N>, rhs: &Any<N>) -> Any<N>, (N) (&lhs.0) (&rhs.0) [
    + where [N: NdAdd<Type = N>],
    - where [N: NdSub<Type = N>],
    * where [N: NdMul<Type = N>],
    / where [N: NdDiv<Type = N>],
    % where [N: NdRem<Type = N>],
    | where [N: NdBitOr<Type = N>],
    & where [N: NdBitAnd<Type = N>],
    ^ where [N: NdBitXor<Type = N>],
] }

// Implements corresponding ndext::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::fwd! { @ndbin <N: Copy> (lhs: &Any<N>, rhs: usize) -> Any<N>, (N) (&lhs.0) (rhs) [
    << where [N: NdShl<Type = N>],
    >> where [N: NdShr<Type = N>],
] }

// Implements corresponding ndext::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::fwd! { @ndun <N: Copy> (value: &Any<N>) -> Any<N>, (N) (&value.0) [
    ! where [N: NdNot<Type = N>],
    - where [N: NdNeg<Type = N>],
] }

// Implements corresponding std::ops::* for (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::fwd! { @stdmut <N: Copy> (lhs: &mut Any<N>, *rhs: &Any<N>), (N) (&mut lhs.0) (&rhs.0) [
    += where [N: NdAddAssign],
    -= where [N: NdSubAssign],
    *= where [N: NdMulAssign],
    /= where [N: NdDivAssign],
    %= where [N: NdRemAssign],
    |= where [N: NdBitOrAssign],
    &= where [N: NdBitAndAssign],
    ^= where [N: NdBitXorAssign],
] }

// Implements corresponding std::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::fwd! { @stdmut <N: Copy> (lhs: &mut Any<N>, rhs: usize), (N) (&mut lhs.0) (rhs) [
    <<= where [N: NdShlAssign],
    >>= where [N: NdShrAssign],
] }

// Implements corresponding std::ops::* for (&Any, &Any), (&Any, Any), (Any, &Any), (Any, Any)
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::fwd! { @stdbin <N: Copy> (*lhs: &Any<N>, *rhs: &Any<N>) -> Any<N>, (N) (&lhs.0) (&rhs.0) [
    + where [N: NdAdd<Type = N>],
    - where [N: NdSub<Type = N>],
    * where [N: NdMul<Type = N>],
    / where [N: NdDiv<Type = N>],
    % where [N: NdRem<Type = N>],
    | where [N: NdBitOr<Type = N>],
    & where [N: NdBitAnd<Type = N>],
    ^ where [N: NdBitXor<Type = N>],
] }

// Implements corresponding std::ops::* for &Any, Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::fwd! { @stdbin <N: Copy> (*lhs: &Any<N>, rhs: usize) -> Any<N>, (N) (&lhs.0) (rhs) [
    << where [N: NdShl<Type = N>],
    >> where [N: NdShr<Type = N>],
] }

// Implements corresponding std::ops::* for &Any, Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::fwd! { @stdun <N: Copy> (*value: &Any<N>) -> Any<N>, (N) (&value.0) [
    ! where [N: NdNot<Type = N>],
    - where [N: NdNeg<Type = N>],
] }

fn main() {}
