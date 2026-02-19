struct Num(i64);

// Required (optionally) to construct operation result
impl From<i64> for Num {
    fn from(value: i64) -> Self {
        Num(value)
    }
}

// Implements corresponding ndcore::ops::* for Num
ndops::all! { @ndmut (lhs: &mut Num, rhs: &Num),
    += lhs.0 += rhs.0,
    -= lhs.0 -= rhs.0,
    *= lhs.0 *= rhs.0,
    /= lhs.0 /= rhs.0,
    %= lhs.0 %= rhs.0,
    |= lhs.0 |= rhs.0,
    &= lhs.0 &= rhs.0,
    ^= lhs.0 ^= rhs.0,
}

// Implements corresponding ndcore::ops::* for Num
ndops::all! { @ndmut (lhs: &mut Num, rhs: usize),
    <<= lhs.0 <<= rhs,
    >>= lhs.0 >>= rhs,
}

// Implements corresponding ndcore::ops::* for Num
ndops::all! { @ndbin (lhs: &Num, rhs: &Num) -> Num,
    + lhs.0 + rhs.0,
    - lhs.0 - rhs.0,
    * lhs.0 * rhs.0,
    / lhs.0 / rhs.0,
    % lhs.0 % rhs.0,
    | lhs.0 | rhs.0,
    & lhs.0 & rhs.0,
    ^ lhs.0 ^ rhs.0,
}

// Implements corresponding ndcore::ops::* for Num
ndops::all! { @ndbin (lhs: &Num, rhs: usize) -> Num,
    << lhs.0 << rhs,
    >> lhs.0 >> rhs,
}

// Implements corresponding ndcore::ops::* for Num
ndops::all! { @ndun (value: &Num) -> Num,
    - -value.0,
    ! !value.0,
}

// Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
ndops::all! { @stdmut (lhs: &mut Num, *rhs: &Num),
    += lhs.0 += rhs.0,
    -= lhs.0 -= rhs.0,
    *= lhs.0 *= rhs.0,
    /= lhs.0 /= rhs.0,
    %= lhs.0 %= rhs.0,
    |= lhs.0 |= rhs.0,
    &= lhs.0 &= rhs.0,
    ^= lhs.0 ^= rhs.0,
}

// Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
ndops::all! { @stdmut (lhs: &mut Num, *rhs: usize),
    <<= lhs.0 <<= rhs,
    >>= lhs.0 >>= rhs,
}

// Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
ndops::all! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num,
    + lhs.0 + rhs.0,
    - lhs.0 - rhs.0,
    * lhs.0 * rhs.0,
    / lhs.0 / rhs.0,
    % lhs.0 % rhs.0,
    | lhs.0 | rhs.0,
    & lhs.0 & rhs.0,
    ^ lhs.0 ^ rhs.0,
}

// Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
ndops::all! { @stdbin (*lhs: &Num, *rhs: usize) -> Num,
    << lhs.0 << rhs,
    >> lhs.0 >> rhs,
}

// Implements corresponding std::ops::* for &Num, Num
ndops::all! { @stdun (*value: &Num) -> Num,
    - -value.0,
    ! !value.0,
}

fn main() {}
