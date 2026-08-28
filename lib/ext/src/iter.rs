#![doc = include_str!("../docs/iter.md")]

/// `Nd-kind` extension for [std::iter::Iterator].
///
/// For more info, see [module-level](crate::iter) and [crate-level](crate) documentation.
pub trait IteratorExt: Iterator {
    /// Collects iterator with pre-allocated destination collection taken and returned by value.
    ///
    /// Consumes at most `collection.len()` amount of elements.
    ///
    /// ```rust
    /// # use ndext::iter::IteratorExt;
    ///
    /// let mut iter = (0..3).into_iter();
    ///
    /// let dst = [0; 4];
    ///
    /// let val = iter.collect_with(dst);
    ///
    /// assert_eq!(val, [0, 1, 2, 0]);
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// ```rust
    /// # use ndext::iter::IteratorExt;
    ///
    /// let mut iter = (0..3).into_iter();
    ///
    /// let mut dst = [0; 4];
    ///
    /// let val = iter.collect_with(&mut dst);
    ///
    /// assert_eq!(val, &[0, 1, 2, 0]);
    /// assert_eq!(dst, [0, 1, 2, 0]);
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    fn collect_with<Collection: AsRef<[Self::Item]> + AsMut<[Self::Item]>>(
        &mut self,
        mut collection: Collection,
    ) -> Collection {
        let ptr = collection.as_mut();

        for (idx, val) in self.take(ptr.len()).enumerate() {
            ptr[idx] = val;
        }

        collection
    }

    /// Iterator length.
    #[inline]
    fn length(self, elem: Self::Item) -> usize
    where
        Self: Sized,
        Self::Item: PartialEq + Eq,
    {
        self.enumerate().fold(0, |acc, (idx, val)| match val == elem {
            false => idx + 1,
            true => acc,
        })
    }
}

impl<Iter: Iterator> IteratorExt for Iter {}
