use std::cmp::{max, Ordering};

use crate::{
    ops::{Ops, OpsAssign},
    ops_impl_bin,
    ops_impl_mut,
};

pub trait NumberLong: Sized + Default + Clone + Ops + OpsAssign + PartialEq + Eq + PartialOrd + Ord {
    const MAX: u64;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NumberSign {
    NEG = -1,
    POS = 1,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedLong(Vec<u32>, NumberSign);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsignedLong(Vec<u32>);

impl Default for SignedLong {
    fn default() -> Self {
        SignedLong(vec![0], NumberSign::POS)
    }
}

impl Default for UnsignedLong {
    fn default() -> Self {
        UnsignedLong(vec![0])
    }
}

fn cmp_long(a: &[u32], b: &[u32], sign: NumberSign) -> Ordering {
    match a.len().cmp(&b.len()) {
        | Ordering::Equal => {
            let len = a.len();

            let lhs = &a[..len];
            let rhs = &b[..len];

            for i in (0..len).rev() {
                match lhs[i].cmp(&rhs[i]) {
                    | Ordering::Less => {
                        if sign == NumberSign::POS {
                            return Ordering::Less;
                        }
                        else {
                            return Ordering::Greater;
                        }
                    },
                    | Ordering::Equal => (),
                    | Ordering::Greater => {
                        if sign == NumberSign::POS {
                            return Ordering::Greater;
                        }
                        else {
                            return Ordering::Less;
                        }
                    },
                }
            }

            Ordering::Equal
        },
        | order => order,
    }
}

impl Ord for SignedLong {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.1 != other.1 {
            return self.1.cmp(&other.1);
        }

        cmp_long(&self.0, &other.0, self.1)
    }
}

impl Ord for UnsignedLong {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_long(&self.0, &other.0, NumberSign::POS)
    }
}

impl PartialOrd for SignedLong {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd for UnsignedLong {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl NumberLong for SignedLong {
    const MAX: u64 = u32::MAX as u64;
}

impl NumberLong for UnsignedLong {
    const MAX: u64 = u32::MAX as u64;
}

ops_impl_bin!(|a: &UnsignedLong, b: &UnsignedLong| -> UnsignedLong,
+ {
    const MAX: u64 = <UnsignedLong as NumberLong>::MAX;

    let a_len = a.0.len();
    let b_len = b.0.len();

    let mut res = UnsignedLong(Vec::<u32>::with_capacity(max(a_len, b_len)));

    let mut index = 0;
    let mut carry = 0;

    while index < a_len || index < b_len || carry > 0 {
        let a_val = if index < a_len { a.0[index] } else { 0 };
        let b_val = if index < b_len { b.0[index] } else { 0 };

        let val = a_val as u64 + b_val as u64 + carry as u64;

        carry = (val / MAX) as u32;

        res.0.push((val - carry as u64 * MAX) as u32);

        index += 1;
    }

    res
}
- {
    const MAX: u64 = <UnsignedLong as NumberLong>::MAX;

    let a_len = a.0.len();
    let b_len = b.0.len();

    let mut res = UnsignedLong(Vec::<u32>::with_capacity(max(a_len, b_len)));

    let mut index = 0;
    let mut carry = 0;

    while index < a_len || index < b_len || carry > 0 {
        let a_val = if index < a_len { a.0[index] } else { 0 };
        let b_val = if index < b_len { b.0[index] } else { 0 };

        let val = a_val as u64 - b_val as u64 - carry as u64;

        carry = (val / MAX) as u32;

        res.0.push((val - carry as u64 * MAX) as u32);

        index += 1;
    }

    res
}
* {
    let mut res = UnsignedLong(Vec::<u32>::new());

    res
}
/ {
    let mut res = UnsignedLong(Vec::<u32>::new());

    res
});

ops_impl_mut!(|a: &mut UnsignedLong, b: &UnsignedLong|,
              += {}
              -= {}
              *= {}
              /= {});

ops_impl_bin!(|a: &SignedLong, b: &SignedLong| -> SignedLong,
+ {
    let mut res = SignedLong(Vec::<u32>::new(), NumberSign::POS);

    res
}
- {
    let mut res = SignedLong(Vec::<u32>::new(), NumberSign::POS);

    res
}
* {
    let mut res = SignedLong(Vec::<u32>::new(), NumberSign::POS);

    res
}
/ {
    let mut res = SignedLong(Vec::<u32>::new(), NumberSign::POS);

    res
});

ops_impl_mut!(|a: &mut SignedLong, b: &SignedLong|,
              += {}
              -= {}
              *= {}
              /= {});
