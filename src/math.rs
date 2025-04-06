use crate::{num::Integer, ops::OpsAllFrom};

pub type Prime = u64;

pub struct Primes {}

impl Primes {
    pub fn by_count(val: usize) -> impl Iterator<Item = Prime> {
        PrimesCountIter {
            primes: Vec::with_capacity(val),
            next: 2,
            idx: 0,
            len: val,
        }
    }

    pub fn by_limit(val: usize) -> impl Iterator<Item = Prime> {
        PrimesLimitIter {
            primes: Vec::with_capacity(val.isqrt() + 1),
            next: 2,
            limit: val as Prime,
        }
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

fn get_next_prime(primes: &[Prime], limit: Prime) -> Option<Prime> {
    let last = *primes.last().unwrap_or(&0);

    (last + 1..=limit).find(|&val| primes.iter().filter(|&p| p * p <= val).all(|&p| val % p != 0))
}

struct PrimesCountIter {
    primes: Vec<Prime>,
    next: Prime,
    idx: usize,
    len: usize,
}

struct PrimesLimitIter {
    primes: Vec<Prime>,
    next: Prime,
    limit: Prime,
}

impl Iterator for PrimesCountIter {
    type Item = Prime;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == self.idx {
            return None;
        }

        self.primes.push(self.next);

        self.next = get_next_prime(&self.primes, Prime::MAX)?;
        self.idx += 1;

        self.primes.last().copied()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.primes.capacity(), Some(self.primes.capacity()))
    }
}

impl Iterator for PrimesLimitIter {
    type Item = Prime;

    fn next(&mut self) -> Option<Self::Item> {
        self.primes.push(self.next);

        self.next = get_next_prime(&self.primes, self.limit)?;

        self.primes.last().copied()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.primes.capacity(), Some(self.primes.capacity()))
    }
}

impl ExactSizeIterator for PrimesCountIter {}
impl ExactSizeIterator for PrimesLimitIter {}
