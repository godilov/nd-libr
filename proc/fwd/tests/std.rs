#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[derive(Debug, Clone, Copy)]
struct Struct<T>(T);

impl<T> From<T> for Struct<T> {
    fn from(value: T) -> Self {
        Struct(value)
    }
}

mod fwd {
    use std::ops::{Deref, DerefMut};

    use super::*;

    #[test]
    #[allow(unused_allocation)]
    fn std() {
        ndassert::check! { (ndassert::range!(i64, 60)) [
            |value: i64| *Struct(value) == value,
            |value: i64| Struct(value).deref() == &value,
            |value: i64| Struct(value).deref_mut() == &value,

            |value: i64| *Struct(Box::new(value)) == Box::new(value),
            |value: i64| Struct(Box::new(value)).as_ref() == &value,
            |value: i64| Struct(Box::new(value)).as_mut() == &value,

            |value: i64| Struct(vec![value]) == Struct::<Vec<i64>>::from_iter([value]),
        ] }
    }

    #[test]
    fn cmp() {
        ndassert::check! { (ndassert::range!(i64, 60, 0), ndassert::range!(i64, 60, 1)) [
            |lhs: i64, rhs: i64| (Struct(lhs) == Struct(rhs)) == (lhs == rhs),
            |lhs: i64, rhs: i64| (Struct(lhs) <  Struct(rhs)) == (lhs <  rhs),
            |lhs: i64, rhs: i64| (Struct(lhs) >  Struct(rhs)) == (lhs >  rhs),
            |lhs: i64, rhs: i64| (Struct(lhs) <= Struct(rhs)) == (lhs <= rhs),
            |lhs: i64, rhs: i64| (Struct(lhs) >= Struct(rhs)) == (lhs >= rhs),
        ] }
    }

    #[test]
    fn fmt() {
        ndassert::check! { (ndassert::range!(i64, 60)) [
            |value: i64| format!("{:}",   Struct(value)) == format!("{:}",   value),
            |value: i64| format!("{:b}",  Struct(value)) == format!("{:b}",  value),
            |value: i64| format!("{:o}",  Struct(value)) == format!("{:o}",  value),
            |value: i64| format!("{:x}",  Struct(value)) == format!("{:x}",  value),
            |value: i64| format!("{:X}",  Struct(value)) == format!("{:X}",  value),
            |value: i64| format!("{:#}",  Struct(value)) == format!("{:#}",  value),
            |value: i64| format!("{:#b}", Struct(value)) == format!("{:#b}", value),
            |value: i64| format!("{:#o}", Struct(value)) == format!("{:#o}", value),
            |value: i64| format!("{:#x}", Struct(value)) == format!("{:#x}", value),
            |value: i64| format!("{:#X}", Struct(value)) == format!("{:#X}", value),
        ] }
    }
}
