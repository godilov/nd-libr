use crate::ops::OpsRem;

pub fn gcd<X: OpsRem<Output = X> + PartialEq + Eq>(
    a: X,
    b: X,
) -> X {
    if b != 0 {
        gcd(b, a % b)
    } else {
        a
    }
}

fn _gcd(
    a: u64,
    b: u64,
) -> u64 {
    if b != 0 {
        gcd(b, a % b)
    } else {
        a
    }
}

fn _lcm(
    a: u64,
    b: u64,
) -> u64 {
    a / gcd(a, b) * b
}
