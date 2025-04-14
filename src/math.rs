use crate::{num::Integer, ops::OpsAllFrom};

pub type Prime = u64;

pub struct Primes {}

impl Primes {
    pub fn by_count(len: usize) -> impl Iterator<Item = Prime> {
        PrimesIter {
            primes: Vec::with_capacity(len),
            next: 2,
        }
        .take(len)
    }

    pub fn by_limit(val: Prime) -> impl Iterator<Item = Prime> {
        let len = val as usize;
        let len = len / len.isqrt() + 1;

        PrimesIter {
            primes: Vec::with_capacity(len),
            next: 2,
        }
        .take_while(move |&x| x < val)
    }
}

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

struct PrimesIter {
    primes: Vec<Prime>,
    next: Prime,
}

impl Iterator for PrimesIter {
    type Item = Prime;

    fn next(&mut self) -> Option<Self::Item> {
        self.primes.push(self.next);

        self.next = (self.next + 1 + self.next % 2..)
            .step_by(2)
            .find(|&val| self.primes.iter().take_while(|&p| p * p <= val).all(|&p| val % p != 0))?;

        self.primes.last().copied()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.primes.capacity(), Some(self.primes.capacity()))
    }
}

impl ExactSizeIterator for PrimesIter {}
