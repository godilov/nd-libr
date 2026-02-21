use std::ops::*;

struct Any<N>(N);

// Required to construct operation result
impl<N: Copy> From<N> for Any<N> {
    fn from(value: N) -> Self {
        Any(value)
    }
}

// Implements corresponding ndcore::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all_auto! { @ndmut <N: Copy> (lhs: &mut Any<N>, rhs: &Any<N>), (lhs.0) (rhs.0) [
    += where [N: AddAssign<N>],
    -= where [N: SubAssign<N>],
    *= where [N: MulAssign<N>],
    /= where [N: DivAssign<N>],
    %= where [N: RemAssign<N>],
    |= where [N: BitOrAssign<N>],
    &= where [N: BitAndAssign<N>],
    ^= where [N: BitXorAssign<N>],
] }

// Implements corresponding ndcore::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all_auto! { @ndmut <N: Copy> (lhs: &mut Any<N>, rhs: usize), (lhs.0) (rhs) [
    <<= where [N: ShlAssign<usize>],
    >>= where [N: ShrAssign<usize>],
] }

// Implements corresponding ndcore::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all_auto! { @ndbin <N: Copy> (lhs: &Any<N>, rhs: &Any<N>) -> Any<N>, (lhs.0) (rhs.0) [
    + where [N: Add<N, Output = N>],
    - where [N: Sub<N, Output = N>],
    * where [N: Mul<N, Output = N>],
    / where [N: Div<N, Output = N>],
    % where [N: Rem<N, Output = N>],
    | where [N: BitOr<N, Output = N>],
    & where [N: BitAnd<N, Output = N>],
    ^ where [N: BitXor<N, Output = N>],
] }

// Implements corresponding ndcore::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all_auto! { @ndbin <N: Copy> (lhs: &Any<N>, rhs: usize) -> Any<N>, (lhs.0) (rhs) [
    << where [N: Shl<usize, Output = N>],
    >> where [N: Shr<usize, Output = N>],
] }

// Implements corresponding ndcore::ops::* for Any
// with signature-level condition N: Copy
// with operation-level conditions per operation
ndops::all_auto! { @ndun <N: Copy> (value: &Any<N>) -> Any<N>, (value.0) [
    - where [N: Neg<Output = N>],
    ! where [N: Not<Output = N>],
] }

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

fn main() {}
