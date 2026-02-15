use alloy::primitives::{Address, aliases::*};
use thiserror::Error;

macro_rules! abi_impl {
    ($type:ty, $align:expr, $fn:expr, $fn_default:expr $(,)?) => {
        impl Abi for $type {
            abi_fns_impl!($type, $align, $fn, $fn_default);

            fn len(&self) -> [usize; 2] {
                [(<$type>::BITS as usize).div_ceil(8).div_ceil(32), 0]
            }

            fn len_packed(&self) -> usize {
                (<$type>::BITS as usize).div_ceil(8)
            }
        }
    };
    ($type:ty, $align:expr, $len:expr, $len_packed:expr, $fn:expr, $fn_default:expr $(,)?) => {
        impl Abi for $type {
            abi_fns_impl!($type, $align, $fn, $fn_default);

            fn len(&self) -> [usize; 2] {
                [$len, 0]
            }

            fn len_packed(&self) -> usize {
                $len_packed
            }
        }
    };
}

macro_rules! abi_fns_impl {
    ($type:ty, $align:expr, $fn:expr, $fn_default:expr $(,)?) => {
        fn encode_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
            let [len, _] = encode_validate(&slice, self)?;

            let bytes = ($fn)(self);
            let length = bytes.len();

            match $align {
                Alignment::Left => {
                    slice.bytes[..length].copy_from_slice(&bytes);
                    slice.bytes[len - length..len].fill(($fn_default)(self));
                },
                Alignment::Right => {
                    slice.bytes[..length].fill(($fn_default)(self));
                    slice.bytes[len - length..len].copy_from_slice(&bytes);
                },
            }

            Ok(Slice {
                offset: slice.offset + len,
                offset_dyn: slice.offset_dyn,
                bytes: &mut slice.bytes[len..],
                bytes_dyn: slice.bytes_dyn,
            })
        }

        fn encode_packed_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
            let len = encode_packed_validate(&slice, self)?;

            let bytes = ($fn)(self);
            let length = bytes.len();

            slice.bytes[..length].copy_from_slice(&bytes);

            Ok(Slice {
                offset: slice.offset + len,
                offset_dyn: slice.offset_dyn,
                bytes: &mut slice.bytes[len..],
                bytes_dyn: slice.bytes_dyn,
            })
        }
    };
}

macro_rules! abi_alloy_impl {
    (@signed [$($type:ty),+ $(,)?]) => {
        $(abi_alloy_impl!(@signed $type);)+
    };
    (@unsigned [$($type:ty),+ $(,)?]) => {
        $(abi_alloy_impl!(@unsigned $type);)+
    };
    (@signed $type:ty) => {
        abi_impl!($type, Alignment::Right,
            |val: &Self| val.to_be_bytes::<{ <$type>::BYTES }>(),
            |val: &Self| if val >= &<$type>::ZERO { 0 } else { u8::MAX },
        );
    };
    (@unsigned $type:ty) => {
        abi_impl!($type, Alignment::Right, |val: &Self| val.to_be_bytes::<{ <$type>::BYTES }>(), |_: &Self| 0);
    };
}

macro_rules! abi_prod_impl {
    (($($a:ident),+) => ($($ax:expr),+ $(,)?)) => {
        impl<$($a: Abi),+> Abi for ($($a),+) {
            fn len<'elem>(&'elem self) -> [usize; 2] {
                [$(($ax)(self).len()),+]
                    .into_iter()
                    .fold([0, 0], |acc, x| [acc[0] + x[0], acc[1] + x[1]])
            }

            fn len_packed<'elem>(&'elem self) -> usize {
                [$(($ax)(self).len_packed()),+].into_iter().sum::<usize>()
            }

            fn encode_into<'bytes, 'elem>(&'elem self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
                encode_validate(&slice, self)?;

                $(let slice = ($ax)(self).encode_into(slice)?;)+

                Ok(slice)
            }

            fn encode_packed_into<'bytes, 'elem>(&'elem self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
                encode_packed_validate(&slice, self)?;

                $(let slice = ($ax)(self).encode_packed_into(slice)?;)+

                Ok(slice)
            }
        }
    };
}

macro_rules! abi_len {
    ($iter:expr) => {
        $iter
            .map(|elem| elem.len())
            .fold([0, 0], |acc, x| [acc[0] + x[0], acc[1] + x[1]])
    };
}

pub struct Slice<'bytes> {
    offset: usize,
    offset_dyn: usize,
    bytes: &'bytes mut [u8],
    bytes_dyn: &'bytes mut [u8],
}

pub struct AsBytes<'ref_>(pub &'ref_ [u8]);
pub struct AsRelative<'ref_, A: Abi>(pub &'ref_ A);
pub struct AsEncode<'ref_, A: Abi>(pub &'ref_ A);
pub struct AsEncodePacked<'ref_, A: Abi>(pub &'ref_ A);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Alignment {
    Left,
    Right,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum SliceError {
    #[error("Failed to split bytes: out of bounds")]
    Bounds,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum AbiError {
    #[error("Failed to encode value: out of static bounds")]
    EncodeBounds,
    #[error("Failed to encode value: out of dynamic bounds")]
    EncodeBoundsDyn,
    #[error("Failed to allocate memory")]
    Memory,
}

pub trait Memory {
    fn alloc() -> Self;

    fn as_bytes(&mut self) -> &mut [u8];
}

pub trait MemoryDyn {
    fn alloc(len: usize) -> Self;

    fn as_bytes(&mut self) -> &mut [u8];
}

#[allow(clippy::len_without_is_empty)]
pub trait Abi {
    fn len(&self) -> [usize; 2];

    fn len_packed(&self) -> usize;

    fn encode_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError>;

    fn encode_packed_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError>;

    fn encode<M: Memory>(&self) -> Result<M, AbiError> {
        let [len, _] = self.len();

        let mut memory = M::alloc();

        self.encode_into(Slice::new(memory.as_bytes(), len)?)?;

        Ok(memory)
    }

    fn encode_packed<M: Memory>(&self) -> Result<M, AbiError> {
        let mut memory = M::alloc();

        self.encode_into(Slice::new_packed(memory.as_bytes()))?;

        Ok(memory)
    }

    fn encode_dyn<M: MemoryDyn>(&self) -> Result<M, AbiError> {
        let [len, len_dyn] = self.len();

        let mut memory = M::alloc(len + len_dyn);

        self.encode_into(Slice::new(memory.as_bytes(), len)?)?;

        Ok(memory)
    }

    fn encode_packed_dyn<M: MemoryDyn>(&self) -> Result<M, AbiError> {
        let len = self.len_packed();

        let mut memory = M::alloc(len);

        self.encode_into(Slice::new_packed(memory.as_bytes()))?;

        Ok(memory)
    }
}

impl From<SliceError> for AbiError {
    fn from(value: SliceError) -> Self {
        match value {
            SliceError::Bounds => AbiError::Memory,
        }
    }
}

impl<const N: usize> Memory for [u8; N] {
    fn alloc() -> Self {
        [0; N]
    }

    fn as_bytes(&mut self) -> &mut [u8] {
        self
    }
}

impl MemoryDyn for Vec<u8> {
    fn alloc(len: usize) -> Self {
        vec![0; len]
    }

    fn as_bytes(&mut self) -> &mut [u8] {
        self
    }
}

impl<'bytes> Slice<'bytes> {
    pub fn new(bytes: &mut [u8], split: usize) -> Result<Slice<'_>, SliceError> {
        let (bytes, bytes_dyn) = bytes.split_at_mut_checked(split).ok_or(SliceError::Bounds)?;

        Ok(Slice {
            offset: 0,
            offset_dyn: split,
            bytes,
            bytes_dyn,
        })
    }

    pub fn new_packed(bytes: &mut [u8]) -> Slice<'_> {
        let len = bytes.len();
        let (bytes, bytes_dyn) = bytes.split_at_mut(len);

        Slice {
            offset: 0,
            offset_dyn: len,
            bytes,
            bytes_dyn,
        }
    }

    pub fn alloc(&mut self, split: usize) -> Result<Slice<'_>, SliceError> {
        let (bytes, bytes_dyn) = self.bytes.split_at_mut_checked(split).ok_or(SliceError::Bounds)?;

        Ok(Slice {
            offset: self.offset,
            offset_dyn: self.offset + split,
            bytes,
            bytes_dyn,
        })
    }

    pub fn alloc_dyn(&mut self, split: usize) -> Result<Slice<'_>, SliceError> {
        let (bytes, bytes_dyn) = self.bytes_dyn.split_at_mut_checked(split).ok_or(SliceError::Bounds)?;

        Ok(Slice {
            offset: self.offset_dyn,
            offset_dyn: self.offset_dyn + split,
            bytes,
            bytes_dyn,
        })
    }
}

#[rustfmt::skip]
mod _impl {
    use super::*;

    abi_impl!(bool, Alignment::Right, 32, 1, |val: &Self| { [*val as u8] }, |_: &Self| { 0 });

    abi_impl!(u8,    Alignment::Right, |val: &Self| val.to_be_bytes(), |_: &Self| 0);
    abi_impl!(u16,   Alignment::Right, |val: &Self| val.to_be_bytes(), |_: &Self| 0);
    abi_impl!(u32,   Alignment::Right, |val: &Self| val.to_be_bytes(), |_: &Self| 0);
    abi_impl!(u64,   Alignment::Right, |val: &Self| val.to_be_bytes(), |_: &Self| 0);
    abi_impl!(u128,  Alignment::Right, |val: &Self| val.to_be_bytes(), |_: &Self| 0);
    abi_impl!(usize, Alignment::Right, |val: &Self| val.to_be_bytes(), |_: &Self| 0);

    abi_impl!(i8,    Alignment::Right, |val: &Self| val.to_be_bytes(), |val: &Self| if val >= &0 { 0 } else { u8::MAX });
    abi_impl!(i16,   Alignment::Right, |val: &Self| val.to_be_bytes(), |val: &Self| if val >= &0 { 0 } else { u8::MAX });
    abi_impl!(i32,   Alignment::Right, |val: &Self| val.to_be_bytes(), |val: &Self| if val >= &0 { 0 } else { u8::MAX });
    abi_impl!(i64,   Alignment::Right, |val: &Self| val.to_be_bytes(), |val: &Self| if val >= &0 { 0 } else { u8::MAX });
    abi_impl!(i128,  Alignment::Right, |val: &Self| val.to_be_bytes(), |val: &Self| if val >= &0 { 0 } else { u8::MAX });
    abi_impl!(isize, Alignment::Right, |val: &Self| val.to_be_bytes(), |val: &Self| if val >= &0 { 0 } else { u8::MAX });

    abi_impl!(Address, Alignment::Right, 32, 20, |val: &Self| val.0.0, |_: &Self| 0);

    abi_impl!(B8,   Alignment::Left, 32, 1,  |val: &Self| val.0, |_: &Self| 0);
    abi_impl!(B16,  Alignment::Left, 32, 2,  |val: &Self| val.0, |_: &Self| 0);
    abi_impl!(B32,  Alignment::Left, 32, 4,  |val: &Self| val.0, |_: &Self| 0);
    abi_impl!(B64,  Alignment::Left, 32, 8,  |val: &Self| val.0, |_: &Self| 0);
    abi_impl!(B96,  Alignment::Left, 32, 12, |val: &Self| val.0, |_: &Self| 0);
    abi_impl!(B128, Alignment::Left, 32, 16, |val: &Self| val.0, |_: &Self| 0);
    abi_impl!(B160, Alignment::Left, 32, 20, |val: &Self| val.0, |_: &Self| 0);
    abi_impl!(B192, Alignment::Left, 32, 24, |val: &Self| val.0, |_: &Self| 0);
    abi_impl!(B224, Alignment::Left, 32, 28, |val: &Self| val.0, |_: &Self| 0);
    abi_impl!(B256, Alignment::Left, 32, 32, |val: &Self| val.0, |_: &Self| 0);

    abi_alloy_impl!(@signed [
        I8,  I16,  I24,  I32,  I40,  I48,  I56,  I64,
        I72,  I80,  I88,  I96, I104, I112, I120, I128,
        I136, I144, I152, I160, I168, I176, I184, I192,
        I200, I208, I216, I224, I232, I240, I248, I256,
    ]);

    abi_alloy_impl!(@unsigned [
        U8,  U16,  U24,  U32,  U40,  U48,  U56,  U64,
        U72,  U80,  U88,  U96, U104, U112, U120, U128,
        U136, U144, U152, U160, U168, U176, U184, U192,
        U200, U208, U216, U224, U232, U240, U248, U256,
    ]);
}

abi_prod_impl!((A0, A1) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
));

abi_prod_impl!((A0, A1, A2) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
));

abi_prod_impl!((A0, A1, A2, A3) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
));

abi_prod_impl!((A0, A1, A2, A3, A4) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5, A6) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
    |val: &'elem Self| &val.6,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5, A6, A7) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
    |val: &'elem Self| &val.6,
    |val: &'elem Self| &val.7,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5, A6, A7, A8) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
    |val: &'elem Self| &val.6,
    |val: &'elem Self| &val.7,
    |val: &'elem Self| &val.8,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5, A6, A7, A8, A9) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
    |val: &'elem Self| &val.6,
    |val: &'elem Self| &val.7,
    |val: &'elem Self| &val.8,
    |val: &'elem Self| &val.9,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
    |val: &'elem Self| &val.6,
    |val: &'elem Self| &val.7,
    |val: &'elem Self| &val.8,
    |val: &'elem Self| &val.9,
    |val: &'elem Self| &val.10,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
    |val: &'elem Self| &val.6,
    |val: &'elem Self| &val.7,
    |val: &'elem Self| &val.8,
    |val: &'elem Self| &val.9,
    |val: &'elem Self| &val.10,
    |val: &'elem Self| &val.11,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
    |val: &'elem Self| &val.6,
    |val: &'elem Self| &val.7,
    |val: &'elem Self| &val.8,
    |val: &'elem Self| &val.9,
    |val: &'elem Self| &val.10,
    |val: &'elem Self| &val.11,
    |val: &'elem Self| &val.12,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
    |val: &'elem Self| &val.6,
    |val: &'elem Self| &val.7,
    |val: &'elem Self| &val.8,
    |val: &'elem Self| &val.9,
    |val: &'elem Self| &val.10,
    |val: &'elem Self| &val.11,
    |val: &'elem Self| &val.12,
    |val: &'elem Self| &val.13,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
    |val: &'elem Self| &val.6,
    |val: &'elem Self| &val.7,
    |val: &'elem Self| &val.8,
    |val: &'elem Self| &val.9,
    |val: &'elem Self| &val.10,
    |val: &'elem Self| &val.11,
    |val: &'elem Self| &val.12,
    |val: &'elem Self| &val.13,
    |val: &'elem Self| &val.14,
));

abi_prod_impl!((A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15) => (
    |val: &'elem Self| &val.0,
    |val: &'elem Self| &val.1,
    |val: &'elem Self| &val.2,
    |val: &'elem Self| &val.3,
    |val: &'elem Self| &val.4,
    |val: &'elem Self| &val.5,
    |val: &'elem Self| &val.6,
    |val: &'elem Self| &val.7,
    |val: &'elem Self| &val.8,
    |val: &'elem Self| &val.9,
    |val: &'elem Self| &val.10,
    |val: &'elem Self| &val.11,
    |val: &'elem Self| &val.12,
    |val: &'elem Self| &val.13,
    |val: &'elem Self| &val.14,
    |val: &'elem Self| &val.15,
));

impl<A: Abi, const N: usize> Abi for &[A; N] {
    fn len(&self) -> [usize; 2] {
        abi_len!(self.iter())
    }

    fn len_packed(&self) -> usize {
        self.iter().map(|elem| elem.len_packed()).sum::<usize>()
    }

    fn encode_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        encode_validate(&slice, self)?;

        self.iter().try_fold(slice, |acc, x| x.encode_into(acc))
    }

    fn encode_packed_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        encode_packed_validate(&slice, self)?;

        self.iter().try_fold(slice, |acc, x| x.encode_packed_into(acc))
    }
}

impl<A: Abi> Abi for &[A] {
    fn len(&self) -> [usize; 2] {
        [32, 32 + abi_len!(self.iter()).iter().sum::<usize>()]
    }

    fn len_packed(&self) -> usize {
        self.iter().map(|elem| elem.len_packed()).sum::<usize>()
    }

    fn encode_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        let [_, len_dyn] = encode_validate(&slice, self)?;

        let [split, _] = abi_len!(self.iter());

        let mut mem = slice.offset_dyn.clone().encode_into(slice)?;

        let mem_dyn = mem.alloc_dyn(32 + split)?;

        let mem_dyn = (self as &[A]).len().encode_into(mem_dyn)?;

        let _ = self.iter().try_fold(mem_dyn, |acc, x| x.encode_into(acc))?;

        Ok(Slice {
            offset: mem.offset,
            offset_dyn: mem.offset_dyn + len_dyn,
            bytes: mem.bytes,
            bytes_dyn: &mut mem.bytes_dyn[len_dyn..],
        })
    }

    fn encode_packed_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        encode_packed_validate(&slice, self)?;

        self.iter().try_fold(slice, |acc, x| x.encode_packed_into(acc))
    }
}

impl Abi for AsBytes<'_> {
    fn len(&self) -> [usize; 2] {
        [32, 32 + self.0.len().div_ceil(32)]
    }

    fn len_packed(&self) -> usize {
        self.0.len()
    }

    fn encode_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        let [_, len_dyn] = encode_validate(&slice, self)?;

        let mem = slice.offset_dyn.clone().encode_into(slice)?;

        let bytes = self.0;
        let length = bytes.len();

        mem.bytes_dyn[..length].copy_from_slice(bytes);

        Ok(Slice {
            offset: mem.offset,
            offset_dyn: mem.offset_dyn,
            bytes: mem.bytes,
            bytes_dyn: &mut mem.bytes_dyn[len_dyn..],
        })
    }

    fn encode_packed_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        let len = encode_packed_validate(&slice, self)?;

        let bytes = self.0;
        let length = bytes.len();

        slice.bytes[..length].copy_from_slice(bytes);

        Ok(Slice {
            offset: slice.offset + len,
            offset_dyn: slice.offset_dyn,
            bytes: &mut slice.bytes[len..],
            bytes_dyn: slice.bytes_dyn,
        })
    }
}

impl<A: Abi> Abi for AsRelative<'_, A> {
    fn len(&self) -> [usize; 2] {
        self.0.len()
    }

    fn len_packed(&self) -> usize {
        self.0.len_packed()
    }

    fn encode_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        let [len, len_dyn] = encode_validate(&slice, self)?;

        let offset = slice.offset + len;
        let offset_dyn = slice.offset_dyn + len_dyn;

        let mem = self.0.encode_into(Slice {
            offset: 0,
            offset_dyn: len,
            bytes: slice.bytes,
            bytes_dyn: slice.bytes_dyn,
        })?;

        Ok(Slice {
            offset,
            offset_dyn,
            bytes: mem.bytes,
            bytes_dyn: mem.bytes_dyn,
        })
    }

    fn encode_packed_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        let len = encode_packed_validate(&slice, self)?;

        let offset = slice.offset + len;
        let offset_dyn = slice.offset_dyn;

        let mem = self.0.encode_packed_into(Slice {
            offset: 0,
            offset_dyn: len,
            bytes: slice.bytes,
            bytes_dyn: slice.bytes_dyn,
        })?;

        Ok(Slice {
            offset,
            offset_dyn,
            bytes: mem.bytes,
            bytes_dyn: mem.bytes_dyn,
        })
    }
}

impl<A: Abi> Abi for AsEncode<'_, A> {
    fn len(&self) -> [usize; 2] {
        self.0.len()
    }

    fn len_packed(&self) -> usize {
        self.0.len().iter().sum::<usize>()
    }

    fn encode_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        self.0.encode_into(slice)
    }

    fn encode_packed_into<'bytes>(&self, mut slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        let len = self.len_packed();

        let [split, _] = self.len();

        let mem = slice.alloc(split)?;

        let _ = self.0.encode_into(mem)?;

        Ok(Slice {
            offset: slice.offset + len,
            offset_dyn: slice.offset_dyn,
            bytes: &mut slice.bytes[len..],
            bytes_dyn: slice.bytes_dyn,
        })
    }
}

impl<A: Abi> Abi for AsEncodePacked<'_, A> {
    fn len(&self) -> [usize; 2] {
        [self.0.len_packed(), 0]
    }

    fn len_packed(&self) -> usize {
        self.0.len_packed()
    }

    fn encode_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        self.0.encode_packed_into(slice)
    }

    fn encode_packed_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        self.0.encode_packed_into(slice)
    }
}

impl Abi for str {
    fn len(&self) -> [usize; 2] {
        AsBytes(self.as_bytes()).len()
    }

    fn len_packed(&self) -> usize {
        AsBytes(self.as_bytes()).len_packed()
    }

    fn encode_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        AsBytes(self.as_bytes()).encode_into(slice)
    }

    fn encode_packed_into<'bytes>(&self, slice: Slice<'bytes>) -> Result<Slice<'bytes>, AbiError> {
        AsBytes(self.as_bytes()).encode_packed_into(slice)
    }
}

fn encode_validate<A: Abi>(slice: &Slice<'_>, abi: &A) -> Result<[usize; 2], AbiError> {
    let [len, len_dyn] = abi.len();

    if slice.bytes.len() < len {
        return Err(AbiError::EncodeBounds);
    }

    if slice.bytes_dyn.len() < len_dyn {
        return Err(AbiError::EncodeBoundsDyn);
    }

    Ok([len, len_dyn])
}

fn encode_packed_validate<A: Abi>(slice: &Slice<'_>, abi: &A) -> Result<usize, AbiError> {
    let len = abi.len_packed();

    if slice.bytes.len() < len {
        return Err(AbiError::EncodeBounds);
    }

    Ok(len)
}
