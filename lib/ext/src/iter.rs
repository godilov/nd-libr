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

    /// ASCII uppercase iterator.
    #[inline]
    fn ascii_uppercase(self) -> std::iter::Map<Self, impl FnMut(u8) -> u8>
    where
        Self: Sized + Iterator<Item = u8>,
    {
        #[repr(align(256))]
        struct Aligned<T>(T);

        static ASCII: Aligned<[u8; 256]> = Aligned({
            let mut res = [0; 256];
            let mut idx = 0;

            while idx < res.len() {
                res[idx] = (idx as u8 as char).to_ascii_uppercase() as u8;
                idx += 1;
            }

            res
        });

        self.map(|idx| ASCII.0[idx as usize])
    }

    /// ASCII lowercase iterator.
    #[inline]
    fn ascii_lowercase(self) -> std::iter::Map<Self, impl FnMut(u8) -> u8>
    where
        Self: Sized + Iterator<Item = u8>,
    {
        #[repr(align(256))]
        struct Aligned<T>(T);

        static ASCII: Aligned<[u8; 256]> = Aligned({
            let mut res = [0; 256];
            let mut idx = 0;

            while idx < res.len() {
                res[idx] = (idx as u8 as char).to_ascii_lowercase() as u8;
                idx += 1;
            }

            res
        });

        self.map(|idx| ASCII.0[idx as usize])
    }
}

impl<Iter: Iterator> IteratorExt for Iter {}
