pub fn as_arr_impl<T, const L: usize>(slice: &[T]) -> &[T; L] {
    let ptr = slice.as_ptr() as *const [T; L];

    unsafe { &*ptr }
}

pub fn as_arr_mut_impl<T, const L: usize>(slice: &mut [T]) -> &mut [T; L] {
    let ptr = slice.as_mut_ptr() as *mut [T; L];

    unsafe { &mut *ptr }
}

#[macro_export]
macro_rules! as_arr {
    ($slice:expr, $len:expr) => {
        $crate::as_arr_impl::<_, $len>(&$slice[0..$len])
    };
    ($slice:expr, $index:expr, $len:expr) => {
        $crate::as_arr_impl::<_, $len>(&$slice[$index..$index + $len])
    };
}

#[macro_export]
macro_rules! as_arr_mut {
    ($slice:expr, $len:expr) => {
        $crate::as_arr_mut_impl::<_, $len>(&mut $slice[0..$len])
    };
    ($slice:expr, $index:expr, $len:expr) => {
        $crate:as_arr_mut_impl::<_, $len>(&mut $slice[$index..$index + $len])
    };
}

#[cfg(test)]
mod tests {
    use super::{as_arr, as_arr_mut};

    fn as_array_impl<T, const L: usize>(value: &[T; L])
    where
        T: Clone + PartialEq, {
        let slice = &value[0..L];
        let arr = &as_arr!(slice, L).clone();

        assert_eq!(arr.len(), slice.len());

        let slice_iter = slice.iter();
        let arr_iter = arr.iter();

        assert!(arr_iter.zip(slice_iter).all(|pair| (*pair.0 == *pair.1)));
    }

    fn as_array_mut_impl<T, const L: usize>(value: &mut [T; L])
    where
        T: Clone + PartialEq, {
        let slice = &mut value[0..L];
        let arr = &as_arr_mut!(slice, L).clone();

        assert_eq!(arr.len(), slice.len());

        let slice_iter = slice.iter();
        let arr_iter = arr.iter();

        assert!(arr_iter.zip(slice_iter).all(|pair| (*pair.0 == *pair.1)));
    }

    #[test]
    fn as_array() {
        as_array_impl(&[0; 0]);
        as_array_impl(&[0]);
        as_array_impl(&[0, 1]);
        as_array_impl(&[0, 1, 2]);
        as_array_impl(&[0, 1, 2, 3]);
        as_array_impl(&[0, 1, 2, 3, 4]);
    }

    #[test]
    fn as_array_mut() {
        as_array_mut_impl(&mut [0; 0]);
        as_array_mut_impl(&mut [0]);
        as_array_mut_impl(&mut [0, 1]);
        as_array_mut_impl(&mut [0, 1, 2]);
        as_array_mut_impl(&mut [0, 1, 2, 3]);
        as_array_mut_impl(&mut [0, 1, 2, 3, 4]);
    }
}
