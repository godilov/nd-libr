#![doc = include_str!("../docs/iter.md")]

/// `Nd-kind` extension for [std::iter::Iterator].
///
/// For more info, see [module-level](crate::iter) and [crate-level](crate) documentation.
pub trait IteratorExt: Iterator {
    /// Collects iterator with static array.
    ///
    /// Consumes at most `N` amount of elements.
    ///
    /// ```rust
    /// # use ndext::iter::IteratorExt;
    ///
    /// let mut iter = (0..3).into_iter();
    ///
    /// let arr = iter.collect_arr() as [i32; 4];
    ///
    /// assert_eq!(arr, [0, 1, 2, 0]);
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    fn collect_arr<const N: usize>(&mut self) -> [Self::Item; N]
    where
        Self::Item: Default + Copy,
    {
        let mut res = [Self::Item::default(); N];

        for (idx, val) in self.take(N).enumerate() {
            res[idx] = val;
        }

        res
    }

    /// Collects iterator with pre-allocated destination collection taken and returned by value.
    ///
    /// Consumes at most `dst.len()` amount of elements.
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
    #[inline]
    fn collect_with<const N: usize>(&mut self, mut dst: [Self::Item; N]) -> [Self::Item; N] {
        dst.iter_mut().zip(self).for_each(|(dst, src)| *dst = src);
        dst
    }

    /// Collects iterator with pre-allocated destination collection taken and returned by reference.
    ///
    /// Consumes at most `dst.len()` amount of elements.
    ///
    /// ```rust
    /// # use ndext::iter::IteratorExt;
    ///
    /// let mut iter = (0..3).into_iter();
    ///
    /// let mut dst = [0; 4];
    ///
    /// let val = iter.collect_with_mut(&mut dst);
    ///
    /// assert_eq!(val, &[0, 1, 2, 0]);
    /// assert_eq!(dst, [0, 1, 2, 0]);
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    fn collect_with_mut<'dst, const N: usize>(&mut self, dst: &'dst mut [Self::Item; N]) -> &'dst mut [Self::Item; N] {
        dst.iter_mut().zip(self).for_each(|(dst, src)| *dst = src);
        dst
    }
}

impl<Iter: Iterator> IteratorExt for Iter {}
