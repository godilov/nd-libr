use thiserror::Error;

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsArrError {
    #[error("Invalid slice length (actual: {act}, required: {req})")]
    InvalidLength { act: usize, req: usize },
}

pub fn as_arr<T, const L: usize>(slice: &[T]) -> Result<&[T; L], AsArrError> {
    if slice.len() < L {
        return Err(AsArrError::InvalidLength { act: slice.len(), req: L });
    }

    let ptr = slice.as_ptr() as *const [T; L];

    unsafe { Ok(&*ptr) }
}

pub fn as_arr_mut<T, const L: usize>(slice: &mut [T]) -> Result<&mut [T; L], AsArrError> {
    if slice.len() < L {
        return Err(AsArrError::InvalidLength { act: slice.len(), req: L });
    }

    let ptr = slice.as_mut_ptr() as *mut [T; L];

    unsafe { Ok(&mut *ptr) }
}

#[macro_export]
macro_rules! as_arr {
    ($slice:expr, $len:expr) => {
        $crate::arr::as_arr::<_, $len>(&$slice[0..$len])
    };
    ($slice:expr, $index:expr, $len:expr) => {
        $crate::arr::as_arr::<_, $len>(&$slice[$index..$index + $len])
    };
}

#[macro_export]
macro_rules! as_arr_mut {
    ($slice:expr, $len:expr) => {
        $crate::arr::as_arr_mut::<_, $len>(&mut $slice[0..$len])
    };
    ($slice:expr, $index:expr, $len:expr) => {
        $crate::arr::as_arr_mut::<_, $len>(&mut $slice[$index..$index + $len])
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{as_arr, as_arr_mut};

    fn as_arr_impl<T, const L: usize>(value: &[T; L]) -> Result<(), AsArrError>
    where
        T: Clone + PartialEq,
    {
        let slice = &value[0..L];
        let arr = as_arr!(slice, L)?;

        assert_eq!(arr.len(), slice.len());

        let slice_iter = slice.iter();
        let arr_iter = arr.iter();

        assert!(arr_iter.zip(slice_iter).all(|pair| (*pair.0 == *pair.1)));

        Ok(())
    }

    fn as_arr_mut_impl<T, const L: usize>(value: &mut [T; L]) -> Result<(), AsArrError>
    where
        T: Clone + PartialEq,
    {
        let slice = &mut value[0..L];
        let arr = as_arr_mut!(slice, L)?.clone();

        assert_eq!(arr.len(), slice.len());

        let slice_iter = slice.iter();
        let arr_iter = arr.iter();

        assert!(arr_iter.zip(slice_iter).all(|pair| (*pair.0 == *pair.1)));

        Ok(())
    }

    #[test]
    fn as_arr() -> anyhow::Result<()> {
        as_arr_impl(&[0; 0])?;
        as_arr_impl(&[0])?;
        as_arr_impl(&[0, 1])?;
        as_arr_impl(&[0, 1, 2])?;
        as_arr_impl(&[0, 1, 2, 3])?;
        as_arr_impl(&[0, 1, 2, 3, 4])?;

        Ok(())
    }

    #[test]
    fn as_arr_mut() -> anyhow::Result<()> {
        as_arr_mut_impl(&mut [0; 0])?;
        as_arr_mut_impl(&mut [0])?;
        as_arr_mut_impl(&mut [0, 1])?;
        as_arr_mut_impl(&mut [0, 1, 2])?;
        as_arr_mut_impl(&mut [0, 1, 2, 3])?;
        as_arr_mut_impl(&mut [0, 1, 2, 3, 4])?;

        Ok(())
    }
}
