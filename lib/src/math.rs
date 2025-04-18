use crate::{num::FixedInt, ops::OpsAllFrom};

const PRIMES: [Prime; 50] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
    113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
];

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

    pub fn by_limit(val: u64) -> impl Iterator<Item = Prime> {
        let len = val as usize;
        let len = len / len.isqrt() + 1;

        PrimesIter {
            primes: Vec::with_capacity(len),
            next: 2,
        }
        .take_while(move |&x| x < val)
    }

    pub fn by_count_fast(len: usize) -> impl Iterator<Item = Prime> {
        (2..).filter(|&val| is_prime(val)).take(len)
    }

    pub fn by_limit_fast(val: u64) -> impl Iterator<Item = Prime> {
        (2..val).filter(|&val| is_prime(val))
    }
}

pub fn gcd_ext<I: FixedInt>(a: I, b: I) -> (I, I, I) {
    if b == I::ZERO {
        return (a, I::ONE, I::ZERO);
    }

    let rem = a % b;

    let (g, x, y) = gcd_ext(b, rem.into());

    let xval = y;
    let yval = I::from(a / b);
    let yval = I::from(yval * y);
    let yval = I::from(x - yval);

    (g, xval, yval)
}

pub fn gcd<I: FixedInt>(mut a: I, mut b: I) -> I {
    while b > I::ZERO {
        let x = b;

        b = I::from(a % b);
        a = x;
    }

    a
}

pub fn lcm<I: FixedInt + OpsAllFrom>(a: I, b: I) -> I {
    let g = gcd(a, b);

    I::from(I::from(a / g) * b)
}

fn is_prime(val: u64) -> bool {
    fn pow_fast(x: u64, p: u64, m: u64) -> u64 {
        if p == 0 {
            return 1;
        }

        match p % 2 {
            0 => {
                let pow = pow_fast(x, p / 2, m);

                (pow * pow) % m
            },
            1 => {
                let pow = pow_fast(x, p - 1, m);

                (x * pow) % m
            },
            _ => 0,
        }
    }

    PRIMES.iter().take(12).copied().take_while(|&p| p < val).all(|p| {
        let x = val - 1;
        let range = 2..x;

        let mut idx = 0;
        let mut pow = x >> (x ^ (x - 1)).ilog2();
        let mut exp = pow_fast(p, pow, val);

        while pow < x && range.contains(&exp) {
            let expn = (exp * exp) % val;

            idx += 1;
            pow *= 2;
            exp = expn;
        }

        idx == 0 && exp == 1 || exp == x
    })
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
