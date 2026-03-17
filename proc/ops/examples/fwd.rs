//! # NdOps Fwd Example

struct Num(i64);

// Required to construct operation result
impl From<i64> for Num {
    fn from(value: i64) -> Self {
        Num(value)
    }
}

// Implements corresponding ndext::ops::* for Num
ndops::fwd! { @ndmut (lhs: &mut Num, rhs: &Num), (i64) (&mut lhs.0) (&rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=] }

// Implements corresponding ndext::ops::* for Num
ndops::fwd! { @ndmut (lhs: &mut Num, rhs: usize), (i64) (&mut lhs.0) (rhs) [<<=, >>=] }

// Implements corresponding ndext::ops::* for Num
ndops::fwd! { @ndbin (lhs: &Num, rhs: &Num) -> Num, (i64) (&lhs.0) (&rhs.0) [+, -, *, /, %, |, &, ^] }

// Implements corresponding ndext::ops::* for Num
ndops::fwd! { @ndbin (lhs: &Num, rhs: usize) -> Num, (i64) (&lhs.0) (rhs) [<<, >>] }

// Implements corresponding ndext::ops::* for Num
ndops::fwd! { @ndun (value: &Num) -> Num, (i64) (&value.0) [-, !] }

// Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
ndops::fwd! { @stdmut (lhs: &mut Num, *rhs: &Num), (i64) (&mut lhs.0) (&rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=] }

// Implements corresponding std::ops::* for Num
ndops::fwd! { @stdmut (lhs: &mut Num, rhs: usize), (i64) (&mut lhs.0) (rhs) [<<=, >>=] }

// Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
ndops::fwd! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num, (i64) (&lhs.0) (&rhs.0) [+, -, *, /, %, |, &, ^] }

// Implements corresponding std::ops::* for &Num, Num
ndops::fwd! { @stdbin (*lhs: &Num, rhs: usize) -> Num, (i64) (&lhs.0) (rhs) [<<, >>] }

// Implements corresponding std::ops::* for &Num, Num
ndops::fwd! { @stdun (*value: &Num) -> Num, (i64) (&value.0) [!, -] }

fn main() {}
