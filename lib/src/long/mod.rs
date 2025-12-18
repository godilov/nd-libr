pub mod bytes;
pub mod num;

macro_rules! signed {
    ($bits:expr) => {
        $crate::long::num::Signed<{ ($bits as usize).div_ceil($crate::word::BITS as usize) }>
    };
}

macro_rules! unsigned {
    ($bits:expr) => {
        $crate::long::num::Unsigned<{ ($bits as usize).div_ceil($crate::word::BITS as usize) }>
    };
}

pub type S8 = signed!(8);
pub type S12 = signed!(12);
pub type S16 = signed!(16);
pub type S24 = signed!(24);
pub type S32 = signed!(32);
pub type S48 = signed!(48);
pub type S64 = signed!(64);
pub type S96 = signed!(96);
pub type S128 = signed!(128);
pub type S192 = signed!(192);
pub type S256 = signed!(256);
pub type S384 = signed!(384);
pub type S512 = signed!(512);
pub type S768 = signed!(768);
pub type S1024 = signed!(1024);
pub type S1536 = signed!(1536);
pub type S2048 = signed!(2048);
pub type S3072 = signed!(3072);
pub type S4096 = signed!(4096);
pub type S6144 = signed!(6144);
pub type S8192 = signed!(8192);

pub type U8 = unsigned!(8);
pub type U12 = unsigned!(12);
pub type U16 = unsigned!(16);
pub type U24 = unsigned!(24);
pub type U32 = unsigned!(32);
pub type U48 = unsigned!(48);
pub type U64 = unsigned!(64);
pub type U96 = unsigned!(96);
pub type U128 = unsigned!(128);
pub type U192 = unsigned!(192);
pub type U256 = unsigned!(256);
pub type U384 = unsigned!(384);
pub type U512 = unsigned!(512);
pub type U768 = unsigned!(768);
pub type U1024 = unsigned!(1024);
pub type U1536 = unsigned!(1536);
pub type U2048 = unsigned!(2048);
pub type U3072 = unsigned!(3072);
pub type U4096 = unsigned!(4096);
pub type U6144 = unsigned!(6144);
pub type U8192 = unsigned!(8192);
