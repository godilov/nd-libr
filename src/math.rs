use crate::{num::Integer, ops::OpsAllFrom};

pub type Prime = u64;

pub struct Primes {}

impl Primes {
    pub fn iter(count: usize) -> impl Iterator<Item = Prime> {
        PrimesIter {
            data: Vec::with_capacity(count),
            next: 2,
            idx: 0,
            len: count,
        }
    }
}

struct PrimesIter {
    data: Vec<Prime>,
    next: Prime,
    idx: usize,
    len: usize,
}

impl Iterator for PrimesIter {
    type Item = Prime;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == self.idx {
            return None;
        }

        self.data.push(self.next);

        for n in self.next + 1..Prime::MAX {
            let mut is_prime = true;
            let mut idx = 0;

            while is_prime && self.data[idx] * self.data[idx] <= n {
                is_prime &= (n % self.data[idx]) != 0;
                idx += 1;
            }

            if is_prime {
                self.next = n;
                self.idx += 1;

                break;
            }
        }

        self.data.last().copied()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl ExactSizeIterator for PrimesIter {}

pub fn gcd_ext<I: Integer + OpsAllFrom>(a: I, b: I) -> (I, I, I) {
    if b == I::ZERO {
        return (a, I::ONE, I::ZERO);
    }

    let aop = a.clone();
    let bop = b.clone();
    let rem = I::from(aop % bop);

    let (g, x, y) = gcd_ext(b.clone(), rem);

    let xval = y.clone();
    let yval = I::from(a / b);
    let yval = I::from(yval * y);
    let yval = I::from(x - yval);

    (g, xval, yval)
}

pub fn gcd<I: Integer + OpsAllFrom>(mut a: I, mut b: I) -> I {
    while b > I::ZERO {
        let x = b.clone();

        b = I::from(a % b.clone());
        a = x;
    }

    a
}

pub fn lcm<I: Integer + OpsAllFrom>(a: I, b: I) -> I {
    let aop = a.clone();
    let bop = b.clone();
    let gop = gcd(aop, bop);

    I::from(I::from(a / gop) * b)
}
