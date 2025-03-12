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

pub fn gcd_ext(a: i64, b: i64) -> (i64, i64, i64) {
    if b == 0 {
        return (a, 1, 0);
    }

    let (g, x, y) = gcd_ext(b, a % b);

    (g, y, x - a / b * y)
}

pub fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b > 0 {
        let x = b;

        b = a % b;
        a = x;
    }

    a
}

pub fn lcm(a: i64, b: i64) -> i64 {
    a / gcd(a, b) * b
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
