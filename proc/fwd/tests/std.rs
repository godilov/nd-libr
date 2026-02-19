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
    fn std() {
        assert_eq!(*Struct(0), 0);
        assert_eq!(Struct(0).deref(), &0);
        assert_eq!(Struct(0).deref_mut(), &0);

        assert_eq!(*Struct(Box::new(0)), Box::new(0));
        assert_eq!(Struct(Box::new(0)).as_ref(), &0);
        assert_eq!(Struct(Box::new(0)).as_mut(), &0);

        assert_eq!(Struct(vec![1, 2, 3]), Struct::<Vec<i32>>::from_iter([1, 2, 3]));
    }

    #[test]
    fn cmp() {
        assert!(Struct(0) == Struct(0));
        assert!(Struct(0) != Struct(1));

        assert!(Struct(0) <= Struct(0));
        assert!(Struct(0) < Struct(1));
        assert!(Struct(1) > Struct(0));
        assert!(Struct(1) >= Struct(1));
    }

    #[test]
    fn fmt() {
        assert_eq!(format!("{}", Struct(0)), format!("{}", 0));
        assert_eq!(format!("{:b}", Struct(0)), format!("{:b}", 0));
        assert_eq!(format!("{:o}", Struct(0)), format!("{:o}", 0));
        assert_eq!(format!("{:x}", Struct(0)), format!("{:x}", 0));
        assert_eq!(format!("{:X}", Struct(0)), format!("{:X}", 0));

        assert_eq!(format!("{:#}", Struct(0)), format!("{:#}", 0));
        assert_eq!(format!("{:#b}", Struct(0)), format!("{:#b}", 0));
        assert_eq!(format!("{:#o}", Struct(0)), format!("{:#o}", 0));
        assert_eq!(format!("{:#x}", Struct(0)), format!("{:#x}", 0));
        assert_eq!(format!("{:#X}", Struct(0)), format!("{:#X}", 0));
    }
}

