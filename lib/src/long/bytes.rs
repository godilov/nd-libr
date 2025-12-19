use std::{
    fmt::{Binary, Debug, Formatter, LowerHex, UpperHex},
    str::FromStr,
};

use crate::long::*;

macro_rules! from_str_impl {
    ($str:expr) => {{
        let (s, radix) = get_radix_from_str($str, 16)?;

        if radix.is_pow2() {
            from_str(s, radix.order() as u8, Sign::POS)
        } else {
            Err(FromStrError::InvalidRadix { radix: radix as usize })
        }
    }};
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Bytes<const L: usize>(pub [Single; L]);

impl<const L: usize> Default for Bytes<L> {
    fn default() -> Self {
        Self([0; L])
    }
}

impl<const L: usize, W: Word> FromIterator<W> for Bytes<L> {
    fn from_iter<T: IntoIterator<Item = W>>(iter: T) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize> FromStr for Bytes<L> {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(from_str_impl!(s)?))
    }
}

from_primitive!(@bytes [u8, u16, u32, u64, u128, usize]);

impl<const L: usize> AsRef<[u8]> for Bytes<L> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const L: usize> AsMut<[u8]> for Bytes<L> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
    }
}

impl<const L: usize> Binary for Bytes<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Bin.into(), get_sign(&self.0, Sign::POS), write_bin)
    }
}

impl<const L: usize> LowerHex for Bytes<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_lhex)
    }
}

impl<const L: usize> UpperHex for Bytes<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_uhex)
    }
}

impl<const L: usize> Bytes<L> {
    from_primitive_const!(@bytes [
        (from_u8, u8),
        (from_u16, u16),
        (from_u32, u32),
        (from_u64, u64),
        (from_u128, u128),
        (from_usize, usize),
    ]);

    pub const fn from_bytes(bytes: &[u8]) -> Self {
        Self(from_bytes(bytes))
    }

    pub fn from_arr<const N: usize, W: Word>(arr: &[W; N]) -> Result<Self, FromArrError> {
        Ok(Self(from_arr(arr, 0)?))
    }

    pub fn from_slice<W: Word>(slice: &[W]) -> Result<Self, FromSliceError> {
        Ok(Self(from_slice(slice)?))
    }

    pub fn from_arr_trunc<const N: usize, W: Word>(arr: &[W; N]) -> Self {
        Self(from_arr_trunc(arr, 0))
    }

    pub fn from_slice_trunc<W: Word>(arr: &[W]) -> Self {
        Self(from_slice_trunc(arr))
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }
}
