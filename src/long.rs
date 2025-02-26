use crate::num::Sign;
use digit::Single;

#[cfg(target_pointer_width = "64")]
mod digit {
    pub type Single = u32;
    pub type Double = u64;

    pub(super) const DEC_MAX: Single = 1_000_000_000;
    pub(super) const DEC_WIDTH: u8 = 9;

    pub(super) const OCT_MAX: Single = 1 << 30;
    pub(super) const OCT_WIDTH: u8 = 10;
}

#[cfg(target_pointer_width = "32")]
mod digit {
    pub type Single = u16;
    pub type Double = u32;

    pub(super) const DEC_MAX: Single = 10_000;
    pub(super) const DEC_WIDTH: u8 = 4;

    pub(super) const OCT_MAX: Single = 1 << 15;
    pub(super) const OCT_WIDTH: u8 = 5;
}

mod radix {
    use super::digit::{DEC_MAX, DEC_WIDTH, OCT_MAX, OCT_WIDTH};
    use super::Single;

    pub trait Radix {
        const MAX: Single;
        const WIDTH: u8;
    }

    pub struct Bin;
    pub struct Oct;
    pub struct Dec;
    pub struct Hex;

    impl Radix for Bin {
        const MAX: Single = 1 << (Single::BITS - 1);
        const WIDTH: u8 = Single::BITS as u8;
    }

    impl Radix for Oct {
        const MAX: Single = OCT_MAX;
        const WIDTH: u8 = OCT_WIDTH;
    }

    impl Radix for Dec {
        const MAX: Single = DEC_MAX;
        const WIDTH: u8 = DEC_WIDTH;
    }

    impl Radix for Hex {
        const MAX: Single = 1 << (Single::BITS - 1);
        const WIDTH: u8 = Single::BITS as u8 / 4;
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SignedLong(Vec<Single>, Sign);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnsignedLong(Vec<Single>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SignedFixed<const L: usize>([Single; L], Sign);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnsignedFixed<const L: usize>([Single; L]);

impl Default for SignedLong {
    fn default() -> Self {
        SignedLong(vec![0], Sign::POS)
    }
}

impl Default for UnsignedLong {
    fn default() -> Self {
        UnsignedLong(vec![0])
    }
}

type S128 = ();
type S256 = ();
type S512 = ();
type S1024 = ();
type S2048 = ();
type S4096 = ();

type U128 = ();
type U256 = ();
type U512 = ();
type U1024 = ();
type U2048 = ();
type U4096 = ();
