#[ndfwd::decl]
trait Greeter {
    type Type;

    const HELLO: Self::Type;
    const GOODBYE: Self::Type;

    fn hello() -> Self::Type;
    fn goodbye() -> Self::Type;
}

#[ndfwd::decl]
trait Builder: Sized {
    #[ndfwd::as_into]
    fn new() -> Self;

    #[ndfwd::as_self]
    fn set_x(&mut self, value: usize) -> &mut Self;

    #[ndfwd::as_self]
    fn set_y(&mut self, value: usize) -> &mut Self;

    #[ndfwd::as_self]
    fn set_z(&mut self, value: usize) -> &mut Self;

    #[ndfwd::as_into]
    fn with_x(self, value: usize) -> Self;

    #[ndfwd::as_into]
    fn with_y(self, value: usize) -> Self;

    #[ndfwd::as_into]
    fn with_z(self, value: usize) -> Self;
}

#[ndfwd::decl]
trait Num: Sized {
    #[ndfwd::as_expr(|(a, b)| (Self::from(a), Self::from(b)))]
    fn split(&self) -> (Self, Self);

    #[ndfwd::as_map(Self::from)]
    fn option(&self) -> Option<Self>;
}

#[ndfwd::std(self.0 with T)]
#[ndfwd::cmp(self.0 with T)]
#[ndfwd::fmt(self.0 with T)]
#[ndfwd::def(self.0 with T: Greeter)]
#[ndfwd::def(self.0 with T: Builder)]
#[ndfwd::def(self.0 with T: Num)]
#[derive(Debug, Clone, Copy)]
struct Any<T>(T);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BuilderImpl(usize, usize, usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct GreeterImpl;

impl<T> From<T> for Any<T> {
    fn from(value: T) -> Self {
        Any(value)
    }
}

#[rustfmt::skip]
impl Greeter for GreeterImpl {
    type Type = &'static str;

    const HELLO: Self::Type = "Hello!";
    const GOODBYE: Self::Type = "Goodbye!";

    fn hello() -> Self::Type {
        Self::HELLO
    }

    fn goodbye() -> Self::Type {
        Self::GOODBYE
    }
}

impl Builder for BuilderImpl {
    fn new() -> Self {
        Self(0, 0, 0)
    }

    fn set_x(&mut self, value: usize) -> &mut Self {
        self.0 = value;
        self
    }

    fn set_y(&mut self, value: usize) -> &mut Self {
        self.1 = value;
        self
    }

    fn set_z(&mut self, value: usize) -> &mut Self {
        self.2 = value;
        self
    }

    fn with_x(self, value: usize) -> Self {
        Self(value, self.1, self.2)
    }

    fn with_y(self, value: usize) -> Self {
        Self(self.0, value, self.2)
    }

    fn with_z(self, value: usize) -> Self {
        Self(self.0, self.1, value)
    }
}

impl Num for usize {
    fn split(&self) -> (Self, Self) {
        (self / 2, self - self / 2)
    }

    fn option(&self) -> Option<Self> {
        Some(*self)
    }
}

mod fwd {
    use std::ops::{Deref, DerefMut};

    use super::*;

    #[test]
    #[allow(unused_allocation)]
    fn std() {
        ndassert::check! { (val in ndassert::range!(i64, 60)) [
            *Any(val) == val,
            Any(val).deref() == &val,
            Any(val).deref_mut() == &val,

            *Any(Box::new(val)) == Box::new(val),
            Any(Box::new(val)).as_ref() == &val,
            Any(Box::new(val)).as_mut() == &val,

            Any(vec![val]) == Any::<Vec<i64>>::from_iter([val]),
        ] }
    }

    #[test]
    fn cmp() {
        ndassert::check! { @eq (
            lhs in ndassert::range!(i64, 60, 0),
            rhs in ndassert::range!(i64, 60, 1),
        ) [
            (Any(lhs) == Any(rhs), lhs == rhs),
            (Any(lhs) <  Any(rhs), lhs <  rhs),
            (Any(lhs) >  Any(rhs), lhs >  rhs),
            (Any(lhs) <= Any(rhs), lhs <= rhs),
            (Any(lhs) >= Any(rhs), lhs >= rhs),
        ] }
    }

    #[test]
    fn fmt() {
        ndassert::check! { (val in ndassert::range!(i64, 60)) [
            format!("{:}",   Any(val)) == format!("{:}",   val),
            format!("{:b}",  Any(val)) == format!("{:b}",  val),
            format!("{:o}",  Any(val)) == format!("{:o}",  val),
            format!("{:x}",  Any(val)) == format!("{:x}",  val),
            format!("{:X}",  Any(val)) == format!("{:X}",  val),
            format!("{:#}",  Any(val)) == format!("{:#}",  val),
            format!("{:#b}", Any(val)) == format!("{:#b}", val),
            format!("{:#o}", Any(val)) == format!("{:#o}", val),
            format!("{:#x}", Any(val)) == format!("{:#x}", val),
            format!("{:#X}", Any(val)) == format!("{:#X}", val),
        ] }
    }

    #[test]
    fn def() {
        let mut builder = Any::<BuilderImpl>::new();

        builder.set_x(1).set_y(2).set_z(3);

        assert_eq!(builder, Any::<BuilderImpl>::new().with_x(1).with_y(2).with_z(3));
        assert_ne!(builder, Any::<BuilderImpl>::new().with_x(3).with_y(2).with_z(1));

        assert_eq!(Any::<GreeterImpl>::HELLO, GreeterImpl::HELLO);
        assert_eq!(Any::<GreeterImpl>::GOODBYE, GreeterImpl::GOODBYE);

        assert_eq!(Any::<GreeterImpl>::hello(), GreeterImpl::hello());
        assert_eq!(Any::<GreeterImpl>::goodbye(), GreeterImpl::goodbye());

        assert_eq!(Any(4usize).split().0.0, 4.split().0);
        assert_eq!(Any(4usize).split().1.0, 4.split().1);
        assert_eq!(Any(4usize).option(), 4.option().map(Any::from));
    }
}
