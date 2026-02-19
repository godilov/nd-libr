use std::ops::*;

struct Num<N>(N);

// Required to construct operation result
impl<N: Copy> From<N> for Num<N> {
    fn from(value: N) -> Self {
        Num(value)
    }
}

// Implements corresponding ndcore::ops::* for Num
// with general condition N: Copy
// with special conditions per operation
ndops::all_auto! { @ndmut <N: Copy> (lhs: &mut Num<N>, rhs: &Num<N>), (lhs.0) (rhs.0) [
    += where [N: AddAssign<N>],
    -= where [N: SubAssign<N>],
    *= where [N: MulAssign<N>],
    /= where [N: DivAssign<N>],
    %= where [N: RemAssign<N>],
    |= where [N: BitOrAssign<N>],
    &= where [N: BitAndAssign<N>],
    ^= where [N: BitXorAssign<N>],
] }

// Implements corresponding ndcore::ops::* for Num
// with general condition N: Copy
// with special conditions per operation
ndops::all_auto! { @ndmut <N: Copy> (lhs: &mut Num<N>, rhs: usize), (lhs.0) (rhs) [
    <<= where [N: ShlAssign<usize>],
    >>= where [N: ShrAssign<usize>],
] }

// Implements corresponding ndcore::ops::* for Num
// with general condition N: Copy
// with special conditions per operation
ndops::all_auto! { @ndbin <N: Copy> (lhs: &Num<N>, rhs: &Num<N>) -> Num<N>, (lhs.0) (rhs.0) [
    + where [N: Add<N, Output = N>],
    - where [N: Sub<N, Output = N>],
    * where [N: Mul<N, Output = N>],
    / where [N: Div<N, Output = N>],
    % where [N: Rem<N, Output = N>],
    | where [N: BitOr<N, Output = N>],
    & where [N: BitAnd<N, Output = N>],
    ^ where [N: BitXor<N, Output = N>],
] }

// Implements corresponding ndcore::ops::* for Num
// with general condition N: Copy
// with special conditions per operation
ndops::all_auto! { @ndbin <N: Copy> (lhs: &Num<N>, rhs: usize) -> Num<N>, (lhs.0) (rhs) [
    << where [N: Shl<usize, Output = N>],
    >> where [N: Shr<usize, Output = N>],
] }

// Implements corresponding ndcore::ops::* for Num
// with general condition N: Copy
// with special conditions per operation
ndops::all_auto! { @ndun <N: Copy> (value: &Num<N>) -> Num<N>, (value.0) [
    - where [N: Neg<Output = N>],
    ! where [N: Not<Output = N>],
] }

// Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
// with general condition N: Copy
// with special conditions per operation
ndops::all_auto! { @stdmut <N: Copy> (lhs: &mut Num<N>, *rhs: &Num<N>), (lhs.0) (rhs.0) [
    += where [N: AddAssign<N>],
    -= where [N: SubAssign<N>],
    *= where [N: MulAssign<N>],
    /= where [N: DivAssign<N>],
    %= where [N: RemAssign<N>],
    |= where [N: BitOrAssign<N>],
    &= where [N: BitAndAssign<N>],
    ^= where [N: BitXorAssign<N>],
] }

// Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
// with general condition N: Copy
// with special conditions per operation
ndops::all_auto! { @stdmut <N: Copy> (lhs: &mut Num<N>, *rhs: usize), (lhs.0) (rhs) [
    <<= where [N: ShlAssign<usize>],
    >>= where [N: ShrAssign<usize>],
] }

// Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
// with general condition N: Copy
// with special conditions per operation
ndops::all_auto! { @stdbin <N: Copy> (*lhs: &Num<N>, *rhs: &Num<N>) -> Num<N>, (lhs.0) (rhs.0) [
    + where [N: Add<N, Output = N>],
    - where [N: Sub<N, Output = N>],
    * where [N: Mul<N, Output = N>],
    / where [N: Div<N, Output = N>],
    % where [N: Rem<N, Output = N>],
    | where [N: BitOr<N, Output = N>],
    & where [N: BitAnd<N, Output = N>],
    ^ where [N: BitXor<N, Output = N>],
] }

// Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
// with general condition N: Copy
// with special conditions per operation
ndops::all_auto! { @stdbin <N: Copy> (*lhs: &Num<N>, *rhs: usize) -> Num<N>, (lhs.0) (rhs) [
    << where [N: Shl<usize, Output = N>],
    >> where [N: Shr<usize, Output = N>],
] }

// Implements corresponding std::ops::* for &Num, Num
// with general condition N: Copy
// with special conditions per operation
ndops::all_auto! { @stdun <N: Copy> (*value: &Num<N>) -> Num<N>, (value.0) [
    - where [N: Neg<Output = N>],
    ! where [N: Not<Output = N>],
] }

fn main() {}
