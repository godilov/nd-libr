pub trait TryFromIterator<A>: Sized {
    type Error;

    fn try_from_iter<T: IntoIterator<Item = A>>(iter: T) -> Result<Self, Self::Error>;
}
