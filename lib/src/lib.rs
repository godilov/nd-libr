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

pub trait IteratorExt: Iterator {
    fn collect_with<Collection>(&mut self, mut collection: Collection) -> Collection
    where
        Self: Sized,
        for<'item> &'item mut Collection: IntoIterator<Item = &'item mut Self::Item>,
    {
        collection.into_iter().zip(self).for_each(|(dst, src)| *dst = src);
        collection
    }
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

impl<Iter: Iterator> IteratorExt for Iter {}
