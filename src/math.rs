pub type Prime = u64;

pub struct Primes {}

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
}

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

pub fn gcd() {
    todo!()
}

pub fn lcm() {
    todo!()
}
