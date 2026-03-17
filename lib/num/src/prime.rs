#![doc = include_str!("../docs/prime.md")]

use std::mem::{replace, take};

use crate::{NumExt, NumUnsigned};

pub(super) const PRIMES: [u16; 128] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
    113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239,
    241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
    383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521,
    523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661,
    673, 677, 683, 691, 701, 709, 719,
];

/// Entry point for generating primes.
pub struct Primes;

impl Primes {
    /// Generates primes by count.
    ///
    /// Uses full-search.
    pub fn by_count_full<Prime: Primality>(count: usize) -> impl Iterator<Item = Prime> {
        PrimesFullIter {
            next: Prime::from(2),
            primes: Vec::with_capacity(count.as_count_check_estimate()),
            count: count.as_count_estimate(),
            limit: None,
        }
    }

    /// Generates primes by limit.
    ///
    /// Uses full-search.
    pub fn by_limit_full<Prime: Primality>(limit: Prime) -> impl Iterator<Item = Prime> {
        PrimesFullIter {
            next: Prime::from(2),
            primes: Vec::with_capacity(limit.as_limit_check_estimate()),
            count: limit.as_limit_estimate(),
            limit: Some(limit),
        }
    }

    /// Generates primes by count.
    ///
    /// Uses fast-search.
    pub fn by_count_fast<Prime: Primality>(count: usize) -> impl Iterator<Item = Prime> {
        PrimesFastIter {
            next: Prime::from(2),
            count: count.as_count_estimate(),
            limit: None,
        }
    }

    /// Generates primes by limit.
    ///
    /// Uses fast-search.
    pub fn by_limit_fast<Prime: Primality>(limit: Prime) -> impl Iterator<Item = Prime> {
        PrimesFastIter {
            next: Prime::from(2),
            count: limit.as_limit_estimate(),
            limit: Some(limit),
        }
    }
}

/// Primality test functions.
pub trait Primality: NumExt + NumUnsigned {
    /// Prime numbers iterator to use in `is_prime` implementation.
    fn primes() -> impl Iterator<Item = Self>;

    /// Prime numbers amount estimate depending on count.
    fn as_count_estimate(&self) -> usize;

    /// Prime numbers amount estimate depending on limit.
    fn as_limit_estimate(&self) -> usize;

    /// Prime numbers amount estimate depending on count (for check).
    fn as_count_check_estimate(&self) -> usize;

    /// Prime numbers amount estimate depending on limit (for check).
    fn as_limit_check_estimate(&self) -> usize;

    /// Primality test.
    ///
    /// Miller-Rabin by default.
    fn is_prime(&self) -> bool {
        let sqrt = self.sqrt();

        Self::primes().take_while(|p| p <= &sqrt).all(|p| {
            let one = Self::one();

            let x = Self::nd_sub(self, &one);

            let shr = Self::nd_sub(&x, &one);
            let shr = Self::nd_bitxor(&x, &shr);
            let shr = shr.order();

            let mut any = false;
            let mut pow = Self::nd_shr(&x, shr);
            let mut exp = p.powrem(pow.clone(), self);

            while pow < x && one < exp && exp < x {
                any |= true;

                let val = exp.clone();

                Self::nd_shl_assign(&mut pow, 1);
                Self::nd_mul_assign(&mut exp, &val);
                Self::nd_rem_assign(&mut exp, self);
            }

            !any && exp == one || exp == x
        })
    }
}

/// Primality test functions extensions.
pub trait PrimalityExt: Send + Primality {
    /// Generates random prime number.
    ///
    /// Order represents position of the most significant bit.
    #[cfg(feature = "rand")]
    fn rand_prime(order: usize) -> Self {
        let mut rng = rand::rng();
        let mut val = Self::rand(order, &mut rng).into_odd();

        while !val.is_prime() {
            val = Self::rand(order, &mut rng).into_odd();
        }

        val
    }

    /// Generates random prime numbers.
    ///
    /// Order represents position of the most significant bit.
    #[cfg(feature = "rand")]
    fn rand_primes(order: usize, count: usize) -> Vec<Self> {
        (0..count).map(|_| Self::rand_prime(order)).collect::<Vec<Self>>()
    }

    /// Generates random prime number in parallel.
    ///
    /// Order represents position of the most significant bit.
    #[cfg(all(feature = "rand", feature = "rayon"))]
    fn rand_prime_par(order: usize) -> Self {
        use rayon::iter::{IntoParallelIterator, ParallelIterator};

        let threads = std::thread::available_parallelism().map(|val| val.get()).unwrap_or(1);

        (0..threads)
            .into_par_iter()
            .find_map_first(|_| Some(Self::rand_prime(order)))
            .unwrap_or_default()
    }

    /// Generates random prime numbers in parallel.
    ///
    /// Order represents position of the most significant bit.
    #[cfg(all(feature = "rand", feature = "rayon"))]
    fn rand_primes_par(order: usize, count: usize) -> Vec<Self> {
        use rayon::iter::{IntoParallelIterator, ParallelIterator};

        (0..count)
            .into_par_iter()
            .map(|_| Self::rand_prime(order))
            .collect::<Vec<Self>>()
    }
}

struct PrimesFullIter<Prime: Primality> {
    next: Prime,
    primes: Vec<Prime>,
    count: usize,
    limit: Option<Prime>,
}

struct PrimesFastIter<Prime: Primality> {
    next: Prime,
    count: usize,
    limit: Option<Prime>,
}

impl<Prime: Primality> Iterator for PrimesFullIter<Prime> {
    type Item = Prime;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count == 0 || self.limit.as_ref().is_some_and(|limit| &self.next > limit) {
            return None;
        }

        if self.primes.len() < self.primes.capacity() {
            self.primes.push(self.next.clone());
        }

        let zero = Prime::from(0);
        let one = Prime::from(1);
        let two = Prime::from(2);

        let offset = Prime::nd_bitand(&self.next, &one);
        let offset = Prime::nd_add(&offset, &one);

        let mut val = Prime::nd_add(&self.next, &offset);

        while self
            .primes
            .iter()
            .take_while(|&p| Prime::nd_mul(p, p) <= val)
            .any(|p| Prime::nd_rem(&val, p) == zero)
        {
            Prime::nd_add_assign(&mut val, &two);

            if self.limit.as_ref().is_some_and(|limit| &val > limit) {
                self.count = 0;

                return Some(take(&mut self.next));
            }
        }

        self.count -= 1;

        Some(replace(&mut self.next, val))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<Prime: Primality> Iterator for PrimesFastIter<Prime> {
    type Item = Prime;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count == 0 || self.limit.as_ref().is_some_and(|limit| &self.next > limit) {
            return None;
        }

        let one = Prime::from(1);
        let two = Prime::from(2);

        let offset = Prime::nd_bitand(&self.next, &one);
        let offset = Prime::nd_add(&offset, &one);

        let mut val = Prime::nd_add(&self.next, &offset);

        while !val.is_prime() {
            Prime::nd_add_assign(&mut val, &two);

            if self.limit.as_ref().is_some_and(|limit| &val > limit) {
                self.count = 0;

                return Some(take(&mut self.next));
            }
        }

        self.count -= 1;

        Some(replace(&mut self.next, val))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<Prime: Primality> ExactSizeIterator for PrimesFullIter<Prime> {}
impl<Prime: Primality> ExactSizeIterator for PrimesFastIter<Prime> {}

impl<Any: Send + Primality + NumExt> PrimalityExt for Any {}
