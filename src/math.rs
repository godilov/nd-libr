fn gcd(a: u64, b: u64) -> u64 {
    if b != 0 {
        gcd(b, a % b)
    }
    else {
        a
    }
}

fn lcm(a: u64, b: u64) -> u64 {
    a / gcd(a, b) * b
}
