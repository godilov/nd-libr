pub mod arch;
pub mod long;
pub mod num;
pub mod ops;

pub trait NdFrom<T>: Sized {
    fn nd_from(value: T) -> Self;
}

pub trait NdTryFrom<T>: Sized {
    type Error;

    fn nd_try_from(value: T) -> Result<Self, Self::Error>;
}

impl<U, V: From<U>> NdFrom<U> for V {
    fn nd_from(value: U) -> Self {
        V::from(value)
    }
}

impl<U, V: TryFrom<U>> NdTryFrom<U> for V {
    type Error = V::Error;

    fn nd_try_from(value: U) -> Result<Self, Self::Error> {
        V::try_from(value)
    }
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
    use ndproc::{forward_cmp, forward_decl, forward_fmt, forward_ops, forward_ops_assign, forward_std};

    #[forward_std(self.value with usize)]
    #[forward_cmp(self.value with usize)]
    #[forward_fmt(self.value with usize)]
    #[forward_ops(self.value with usize)]
    #[forward_ops_assign(self.value with usize)]
    struct Struct {
        value: usize,
    }

    #[forward_decl]
    trait Interface {
        type Type;

        const CONSTANT: usize;

        fn function(value: usize) -> usize;
    }

    impl From<usize> for Struct {
        fn from(value: usize) -> Self {
            Self { value }
        }
    }

    impl Interface for usize {
        type Type = usize;

        const CONSTANT: usize = 0;

        fn function(value: usize) -> usize {
            value
        }
    }
}
