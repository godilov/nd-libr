#![allow(clippy::manual_div_ceil)]
use std::{
    cmp::Ordering,
    fmt::{Binary, Debug, Display, Formatter, LowerHex, Octal, UpperHex},
    io::{Cursor, Write},
    iter::{once, repeat},
    marker::PhantomData,
    str::FromStr,
};

use ndproc::ops_impl;
use thiserror::Error;
use zerocopy::{IntoBytes, transmute_mut};

use crate::{
    arch::*,
    long::{bytes::*, num::*, radix::*, uops::*},
    num::{Num, Sign, Signed as NumSigned, Static as NumStatic, Unsigned as NumUnsigned},
    ops::*,
    *,
};

macro_rules! signed {
    ($bits:expr) => {
        $crate::long::num::Signed<{ ($bits as usize).div_ceil($crate::arch::BITS as usize) }>
    };
}

macro_rules! unsigned {
    ($bits:expr) => {
        $crate::long::num::Unsigned<{ ($bits as usize).div_ceil($crate::arch::BITS as usize) }>
    };
}

macro_rules! bytes {
    ($bits:expr) => {
        $crate::long::bytes::Bytes<{ ($bits as usize).div_ceil($crate::arch::BITS as usize) }>
    };
}

macro_rules! from_primitive {
    (@signed [$($primitive:ty),+ $(,)?]) => {
        $(from_primitive!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty),+ $(,)?]) => {
        $(from_primitive!(@unsigned $primitive);)+
    };
    (@bytes [$($primitive:ty),+ $(,)?]) => {
        $(from_primitive!(@bytes $primitive);)+
    };
    (@signed $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Signed<L> {
            #[allow(unused_comparisons)]
            fn from(value: $primitive) -> Self {
                let bytes = value.to_le_bytes();
                let res = from_arr(&bytes, if value >= 0 { 0 } else { MAX });

                Self(res)
            }
        }
    };
    (@unsigned $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Unsigned<L> {
            fn from(value: $primitive) -> Self {
                let bytes = value.to_le_bytes();
                let res = from_arr(&bytes, 0);

                Self(res)
            }
        }
    };
    (@bytes $primitive:ty) => {
        impl<const L: usize> From<$primitive> for Bytes<L> {
            fn from(value: $primitive) -> Self {
                let bytes = value.to_le_bytes();
                let res = from_arr(&bytes, 0);

                Self(res)
            }
        }
    };
}

macro_rules! from_primitive_const {
    (@signed [$(($fn:ident, $primitive:ty) $(,)?),+]) => {
        $(from_primitive_const!(@signed $fn, $primitive);)+
    };
    (@unsigned [$(($fn:ident, $primitive:ty) $(,)?),+]) => {
        $(from_primitive_const!(@unsigned $fn, $primitive);)+
    };
    (@bytes [$(($fn:ident, $primitive:ty) $(,)?),+]) => {
        $(from_primitive_const!(@unsigned $fn, $primitive);)+
    };
    (@signed $fn:ident, $primitive:ty) => {
        pub const fn $fn(val: $primitive) -> Self {
            let default = if val >= 0 { 0 } else { MAX };

            let mut val = val.abs_diff(0);
            let mut idx = 0;
            let mut res = [default; L];

            while val > 0 {
                res[idx] = val as Single;
                idx += 1;
                val = val.unbounded_shr(BITS as u32);
            }

            Self(res)
        }
    };
    (@unsigned $fn:ident, $primitive:ty) => {
        pub const fn $fn(mut val: $primitive) -> Self {
            let mut idx = 0;
            let mut res = [0; L];

            while val > 0 {
                res[idx] = val as Single;
                idx += 1;
                val = val.unbounded_shr(BITS as u32);
            }

            Self(res)
        }
    };
    (@bytes $fn:ident, $primitive:ty) => {
        pub const fn $fn(mut val: $primitive) -> Self {
            let mut idx = 0;
            let mut res = [0; L];

            while val > 0 {
                res[idx] = val as Single;
                idx += 1;
                val = val.unbounded_shr(BITS as u32);
            }

            Self(res)
        }
    };
}

macro_rules! from_digits_impl {
    ($digits:expr, $len:expr, $exp:expr) => {{
        let bits = $exp as usize;
        let mask = (1 << BITS) - 1;

        let mut acc = 0;
        let mut shl = 0;
        let mut idx = 0;
        let mut res = [0; L];

        for digit in $digits {
            acc |= digit.as_double() << shl;
            shl += bits;
            res[idx] = (acc & mask) as Single;

            if shl >= BITS {
                if idx + 1 == L {
                    break;
                }

                acc >>= BITS;
                shl -= BITS;
                idx += 1;
                res[idx] = (acc & mask) as Single;
            }
        }

        res
    }};
}

macro_rules! from_digits_radix_impl {
    ($digits:expr, $radix:expr) => {{
        let mut idx = 0;
        let mut res = [0; L];

        for digit in $digits {
            let mut acc = digit.as_double();

            for ptr in res.iter_mut().take(idx + 1) {
                acc += *ptr as Double * $radix.as_double();

                *ptr = acc as Single;

                acc >>= BITS;
            }

            if idx < L && res[idx] > 0 {
                idx += 1;
            }
        }

        res
    }};
}

macro_rules! from_str_impl {
    (@long $str:expr) => {{
        let (s, sign) = get_sign_from_str($str)?;
        let (s, radix) = get_radix_from_str(s, 10)?;

        if radix.is_pow2() {
            from_str(s, radix.order() as u8, sign)
        } else {
            from_str_radix(s, radix, sign)
        }
    }};
    (@bytes $str:expr) => {{
        let (s, radix) = get_radix_from_str($str, 16)?;

        if radix.is_pow2() {
            from_str(s, radix.order() as u8, Sign::POS)
        } else {
            Err(FromStrError::InvalidRadix { radix: radix as usize })
        }
    }};
}

macro_rules! ops_primitive_native_impl {
    (@signed [$($primitive:ty $(,)?),+]) => {
        $(ops_primitive_native_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty $(,)?),+]) => {
        $(ops_primitive_native_impl!(@unsigned $primitive);)+
    };
    (@bytes [$($primitive:ty $(,)?),+]) => {
        $(ops_primitive_native_impl!(@bytes $primitive);)+
    };
    (@signed $primitive:ty) => {
        ops_impl!(@bin <const L: usize> |*a: &Signed<L>, b: $primitive| -> Signed::<L>,
            + Signed::<L>(add_signed(&a.0, (b.unsigned_abs() as Single, Sign::from(b)))),
            - Signed::<L>(sub_signed(&a.0, (b.unsigned_abs() as Single, Sign::from(b)))),
            * Signed::<L>(mul_signed(&a.0, (b.unsigned_abs() as Single, Sign::from(b)))),
            / Signed::<L>(div_single(&a.abs().0, b.unsigned_abs() as Single).0).signed(a.sign() * Sign::from(b)),
            % Signed::<L>(div_single(&a.abs().0, b.unsigned_abs() as Single).1).signed(a.sign()),
            | Signed::<L>(bit_single(&a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop | bop)),
            & Signed::<L>(bit_single(&a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop & bop)),
            ^ Signed::<L>(bit_single(&a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop ^ bop)));

        ops_impl!(@mut <const L: usize> |a: mut Signed<L>, b: $primitive|,
            += add_signed_mut(&mut a.0, (b.unsigned_abs() as Single, Sign::from(b))),
            -= sub_signed_mut(&mut a.0, (b.unsigned_abs() as Single, Sign::from(b))),
            *= mul_signed_mut(&mut a.0, (b.unsigned_abs() as Single, Sign::from(b))),
            /= { *a = Signed::<L>(div_single(&a.abs().0, b.unsigned_abs() as Single).0).signed(a.sign() * Sign::from(b)); },
            %= { *a = Signed::<L>(div_single(&a.abs().0, b.unsigned_abs() as Single).1).signed(a.sign()); },
            |= bit_single_mut(&mut a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop | bop),
            &= bit_single_mut(&mut a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop & bop),
            ^= bit_single_mut(&mut a.0, b as Single, if b >= 0 { 0 } else { MAX }, |aop, bop| aop ^ bop));
    };
    (@unsigned $primitive:ty) => {
        ops_impl!(@bin <const L: usize> |*a: &Unsigned<L>, b: $primitive| -> Unsigned::<L>,
            + Unsigned::<L>(add_single(&a.0, b as Single)),
            - Unsigned::<L>(sub_single(&a.0, b as Single)),
            * Unsigned::<L>(mul_single(&a.0, b as Single)),
            / Unsigned::<L>(div_single(&a.0, b as Single).0),
            % Unsigned::<L>(div_single(&a.0, b as Single).1),
            | Unsigned::<L>(bit_single(&a.0, b as Single, 0, |aop, bop| aop | bop)),
            & Unsigned::<L>(bit_single(&a.0, b as Single, 0, |aop, bop| aop & bop)),
            ^ Unsigned::<L>(bit_single(&a.0, b as Single, 0, |aop, bop| aop ^ bop)));

        ops_impl!(@mut <const L: usize> |a: mut Unsigned<L>, b: $primitive|,
            += add_single_mut(&mut a.0, b as Single),
            -= sub_single_mut(&mut a.0, b as Single),
            *= mul_single_mut(&mut a.0, b as Single),
            /= div_single_mut(&mut a.0, b as Single),
            %= rem_single_mut(&mut a.0, b as Single),
            |= bit_single_mut(&mut a.0, b as Single, 0, |aop, bop| aop | bop),
            &= bit_single_mut(&mut a.0, b as Single, 0, |aop, bop| aop & bop),
            ^= bit_single_mut(&mut a.0, b as Single, 0, |aop, bop| aop ^ bop));
    };
    (@bytes $primitive:ty) => {
        ops_impl!(@bin <const L: usize> |*a: &Bytes<L>, b: $primitive| -> Bytes::<L>,
            | Bytes::<L>(bit_single(&a.0, b as Single, 0, |aop, bop| aop | bop)),
            & Bytes::<L>(bit_single(&a.0, b as Single, 0, |aop, bop| aop & bop)),
            ^ Bytes::<L>(bit_single(&a.0, b as Single, 0, |aop, bop| aop ^ bop)));

        ops_impl!(@mut <const L: usize> |a: mut Bytes<L>, b: $primitive|,
            |= bit_single_mut(&mut a.0, b as Single, 0, |aop, bop| aop | bop),
            &= bit_single_mut(&mut a.0, b as Single, 0, |aop, bop| aop & bop),
            ^= bit_single_mut(&mut a.0, b as Single, 0, |aop, bop| aop ^ bop));
    };
}

macro_rules! ops_primitive_impl {
    (@signed [$($primitive:ty $(,)?),+]) => {
        $(ops_primitive_impl!(@signed $primitive);)+
    };
    (@unsigned [$($primitive:ty $(,)?),+]) => {
        $(ops_primitive_impl!(@unsigned $primitive);)+
    };
    (@bytes [$($primitive:ty $(,)?),+]) => {
        $(ops_primitive_impl!(@bytes $primitive);)+
    };
    (@signed $primitive:ty) => {
        ops_impl!(@bin <const L: usize> |*a: &Signed<L>, b: $primitive| -> Signed::<L>,
            + Signed::<L>(add_long(&a.0, &Signed::<L>::from(b).0)),
            - Signed::<L>(sub_long(&a.0, &Signed::<L>::from(b).0)),
            * Signed::<L>(mul_long(&a.0, &Signed::<L>::from(b).0)),
            / Signed::<L>(div_long(&a.abs().0, &Signed::<L>::from(b.abs()).0).0).signed(a.sign() * Sign::from(b)),
            % Signed::<L>(div_long(&a.abs().0, &Signed::<L>::from(b.abs()).0).1).signed(a.sign()),
            | Signed::<L>(bit_long(&a.0, &Signed::<L>::from(b).0, |aop, bop| aop | bop)),
            & Signed::<L>(bit_long(&a.0, &Signed::<L>::from(b).0, |aop, bop| aop & bop)),
            ^ Signed::<L>(bit_long(&a.0, &Signed::<L>::from(b).0, |aop, bop| aop ^ bop)));

        ops_impl!(@mut <const L: usize> |a: mut Signed<L>, b: $primitive|,
            += add_long_mut(&mut a.0, &Signed::<L>::from(b).0),
            -= sub_long_mut(&mut a.0, &Signed::<L>::from(b).0),
            *= mul_long_mut(&mut a.0, &Signed::<L>::from(b).0),
            /= { *a = Signed::<L>(div_long(&a.abs().0, &Signed::<L>::from(b.abs()).0).0).signed(a.sign() * Sign::from(b)); },
            %= { *a = Signed::<L>(div_long(&a.abs().0, &Signed::<L>::from(b.abs()).0).1).signed(a.sign()); },
            |= bit_long_mut(&mut a.0, &Signed::<L>::from(b).0, |aop, bop| aop | bop),
            &= bit_long_mut(&mut a.0, &Signed::<L>::from(b).0, |aop, bop| aop & bop),
            ^= bit_long_mut(&mut a.0, &Signed::<L>::from(b).0, |aop, bop| aop ^ bop));
    };
    (@unsigned $primitive:ty) => {
        ops_impl!(@bin <const L: usize> |*a: &Unsigned<L>, b: $primitive| -> Unsigned::<L>,
            + Unsigned::<L>(add_long(&a.0, &Unsigned::<L>::from(b).0)),
            - Unsigned::<L>(sub_long(&a.0, &Unsigned::<L>::from(b).0)),
            * Unsigned::<L>(mul_long(&a.0, &Unsigned::<L>::from(b).0)),
            / Unsigned::<L>(div_long(&a.0, &Unsigned::<L>::from(b).0).0),
            % Unsigned::<L>(div_long(&a.0, &Unsigned::<L>::from(b).0).1),
            | Unsigned::<L>(bit_long(&a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop | bop)),
            & Unsigned::<L>(bit_long(&a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop & bop)),
            ^ Unsigned::<L>(bit_long(&a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop ^ bop)));

        ops_impl!(@mut <const L: usize> |a: mut Unsigned<L>, b: $primitive|,
            += add_long_mut(&mut a.0, &Unsigned::<L>::from(b).0),
            -= sub_long_mut(&mut a.0, &Unsigned::<L>::from(b).0),
            *= mul_long_mut(&mut a.0, &Unsigned::<L>::from(b).0),
            /= div_long_mut(&mut a.0, &Unsigned::<L>::from(b).0),
            %= rem_long_mut(&mut a.0, &Unsigned::<L>::from(b).0),
            |= bit_long_mut(&mut a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop | bop),
            &= bit_long_mut(&mut a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop & bop),
            ^= bit_long_mut(&mut a.0, &Unsigned::<L>::from(b).0, |aop, bop| aop ^ bop));
    };
    (@bytes $primitive:ty) => {
        ops_impl!(@bin <const L: usize> |*a: &Bytes<L>, b: $primitive| -> Bytes::<L>,
            | Bytes::<L>(bit_long(&a.0, &Bytes::<L>::from(b).0, |aop, bop| aop | bop)),
            & Bytes::<L>(bit_long(&a.0, &Bytes::<L>::from(b).0, |aop, bop| aop & bop)),
            ^ Bytes::<L>(bit_long(&a.0, &Bytes::<L>::from(b).0, |aop, bop| aop ^ bop)));

        ops_impl!(@mut <const L: usize> |a: mut Bytes<L>, b: $primitive|,
            |= bit_long_mut(&mut a.0, &Bytes::<L>::from(b).0, |aop, bop| aop | bop),
            &= bit_long_mut(&mut a.0, &Bytes::<L>::from(b).0, |aop, bop| aop & bop),
            ^= bit_long_mut(&mut a.0, &Bytes::<L>::from(b).0, |aop, bop| aop ^ bop));
    };
}

macro_rules! inc_impl {
    ($words:expr) => {{
        #[allow(unused_mut)]
        let mut words = $words;
        let mut acc = 1;

        for ptr in words.iter_mut() {
            let word = *ptr as Double + acc as Double;

            *ptr = word as Single;

            acc = word / RADIX;

            if acc == 0 {
                break;
            }
        }

        words
    }};
}

macro_rules! dec_impl {
    ($words:expr) => {{
        #[allow(unused_mut)]
        let mut words = $words;
        let mut acc = 1;

        for ptr in words.iter_mut() {
            let word = RADIX + *ptr as Double - acc as Double;

            *ptr = word as Single;

            acc = (word < RADIX) as Double;

            if acc == 0 {
                break;
            }
        }

        words
    }};
}

macro_rules! shl_impl {
    ($words:expr, $words_ret:expr, $shift:expr, $default:expr, $fn:expr) => {{
        let shift = $shift;
        let offset = shift / BITS;
        let shl = shift % BITS;
        let shr = BITS - shl;

        if offset >= L {
            return ($fn)($words_ret);
        }

        #[allow(unused_mut)]
        let mut res = $words;

        for idx in ((offset + 1).min(L)..L).rev() {
            let idx_h = idx - offset;
            let idx_l = idx - offset - 1;

            let val_h = res[idx_h].checked_shl(shl as u32).unwrap_or(0);
            let val_l = res[idx_l].checked_shr(shr as u32).unwrap_or(0);

            res[idx] = val_h | val_l;
        }

        let val_h = res[0].checked_shl(shl as u32).unwrap_or(0);
        let val_l = $default.checked_shr(shr as u32).unwrap_or(0);

        res[offset] = val_h | val_l;

        res.iter_mut().take(offset).for_each(|ptr| *ptr = $default);
        res
    }};
}

macro_rules! shr_impl {
    ($words:expr, $words_ret:expr, $shift:expr, $default:expr, $fn:expr) => {{
        let shift = $shift;
        let offset = shift / BITS;
        let shr = shift % BITS;
        let shl = BITS - shr;

        if offset >= L {
            return ($fn)($words_ret);
        }

        #[allow(unused_mut)]
        let mut res = $words;

        for idx in 0..(L - offset).saturating_sub(1) {
            let idx_h = idx + offset + 1;
            let idx_l = idx + offset;

            let val_h = res[idx_h].checked_shl(shl as u32).unwrap_or(0);
            let val_l = res[idx_l].checked_shr(shr as u32).unwrap_or(0);

            res[idx] = val_h | val_l;
        }

        let val_h = $default.checked_shl(shl as u32).unwrap_or(0);
        let val_l = res[L - 1].checked_shr(shr as u32).unwrap_or(0);

        res[L - offset - 1] = val_h | val_l;

        res.iter_mut().skip(L - offset).for_each(|ptr| *ptr = $default);
        res
    }};
}

macro_rules! add_long_impl {
    ($a:expr, $b:expr) => {
        $a.zip($b).scan(0, |acc, (a, b)| {
            let val = a as Double + b as Double + *acc;

            *acc = val / RADIX;

            Some(val as Single)
        })
    };
}

macro_rules! sub_long_impl {
    ($a:expr, $b:expr) => {
        $a.zip($b).scan(0, |acc, (a, b)| {
            let val = RADIX + a as Double - b as Double - *acc;

            *acc = (val < RADIX) as Double;

            Some(val as Single)
        })
    };
}

macro_rules! add_single_impl {
    ($a:expr, $b:expr) => {
        $a.scan($b as Double, |acc, a| {
            let val = a as Double + *acc;

            *acc = val / RADIX;

            Some(val as Single)
        })
    };
    (@overflow $a:expr, $b:expr, $acc:expr) => {
        $a.scan($b as Double, |_, a| {
            let val = a as Double + $acc;

            $acc = val / RADIX;

            Some(val as Single)
        })
    };
}

macro_rules! sub_single_impl {
    ($a:expr, $b:expr) => {
        $a.scan($b as Double, |acc, a| {
            let val = RADIX + a as Double - *acc;

            *acc = (val < RADIX) as Double;

            Some(val as Single)
        })
    };
}

macro_rules! mul_single_impl {
    ($a:expr, $b:expr) => {
        $a.scan(0, |acc, a| {
            let val = a as Double * $b as Double + *acc;

            *acc = val / RADIX;

            Some(val as Single)
        })
    };
    (@overflow $a:expr, $b:expr, $acc:expr) => {{
        $a.scan(0, |_, a| {
            let val = a as Double * $b as Double + $acc;

            $acc = val / RADIX;

            Some(val as Single)
        })
    }};
}

macro_rules! add_long_mut_impl {
    ($a:expr, $b:expr) => {
        $a.zip($b).fold(0, |acc, (ptr, val)| {
            let v = *ptr as Double + val as Double + acc;

            *ptr = v as Single;

            v / RADIX
        });
    };
}

macro_rules! sub_long_mut_impl {
    ($a:expr, $b:expr) => {
        $a.zip($b).fold(0, |acc, (ptr, val)| {
            let v = RADIX + *ptr as Double - val as Double - acc;

            *ptr = v as Single;

            (v < RADIX) as Double
        });
    };
}

macro_rules! add_single_mut_impl {
    ($a:expr, $b:expr) => {
        $a.fold($b as Double, |acc, ptr| {
            let v = *ptr as Double + acc;

            *ptr = v as Single;

            v / RADIX
        });
    };
}

macro_rules! sub_single_mut_impl {
    ($a:expr, $b:expr) => {
        $a.fold($b as Double, |acc, ptr| {
            let v = RADIX + *ptr as Double - acc;

            *ptr = v as Single;

            (v < RADIX) as Double
        });
    };
}

macro_rules! mul_single_mut_impl {
    ($a:expr, $b:expr) => {
        $a.fold(0, |acc, ptr| {
            let v = *ptr as Double * $b as Double + acc;

            *ptr = v as Single;

            v / RADIX
        });
    };
}

macro_rules! div_long_impl {
    ($a:expr, $b:expr) => {{
        #[allow(unused_mut)]
        let mut div = $a;
        let mut rem = [0; L];

        for val in div.iter_mut().rev() {
            cycle!(rem, *val);

            let digit = search!(@upper 0, RADIX, |m: Double| {
                let mut acc = 0;

                let mul = mul_single_impl!(@overflow $b, m, acc).collect_with([0; L]);

                if acc > 0 {
                    return Ordering::Greater;
                }

                mul.iter().rev().cmp(rem.iter().rev())
            });

            let digit = digit.saturating_sub(1) as Single;

            *val = digit;

            if digit > 0 {
                let rem_iter = rem.iter_mut();
                let mul_iter = mul_single_impl!($b, digit);

                sub_long_mut_impl!(rem_iter, mul_iter);
            }
        }

        (div, rem)
    }};
}

macro_rules! div_single_impl {
    ($a:expr, $b:expr) => {{
        #[allow(unused_mut)]
        let mut div = $a;
        let mut rem = 0 as Double;

        for val in div.iter_mut().rev() {
            rem <<= BITS;
            rem |= *val as Double;

            let digit = search!(@upper 0, RADIX, |m: Double| { (m * $b as Double).cmp(&rem) });
            let digit = digit.saturating_sub(1) as Single;

            *val = digit;
            rem -= digit as Double * $b as Double;
        }

        (div, rem)
    }};
}

macro_rules! cycle {
    ($arr:expr, $val:expr) => {{
        for i in (1..$arr.len()).rev() {
            $arr[i] = $arr[i - 1];
        }

        $arr[0] = $val;
    }};
}

macro_rules! search {
    (@lower $l:expr, $r:expr, $fn:expr) => {{
        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            match ($fn)(m) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => r = m,
                Ordering::Greater => r = m,
            }
        }

        l
    }};
    (@upper $l:expr, $r:expr, $fn:expr) => {{
        let mut l = 0;
        let mut r = RADIX;

        while l < r {
            let m = l + (r - l) / 2;

            match ($fn)(m) {
                Ordering::Less => l = m + 1,
                Ordering::Equal => l = m + 1,
                Ordering::Greater => r = m,
            }
        }

        l
    }};
}

pub mod radix {
    use super::*;

    pub struct Dec;
    pub struct Bin;
    pub struct Oct;
    pub struct Hex;

    pub struct Radix {
        pub prefix: &'static str,
        pub value: Double,
        pub width: u8,
    }

    impl Dec {
        pub const PREFIX: &str = "";
        pub const RADIX: Double = DEC_RADIX;
        pub const WIDTH: u8 = DEC_WIDTH;
    }

    impl Bin {
        pub const EXP: u8 = RADIX.ilog2() as u8;
        pub const PREFIX: &str = "0b";
        pub const RADIX: Double = RADIX;
        pub const WIDTH: u8 = BITS as u8;
    }

    impl Oct {
        pub const EXP: u8 = OCT_RADIX.ilog2() as u8;
        pub const PREFIX: &str = "0o";
        pub const RADIX: Double = OCT_RADIX;
        pub const WIDTH: u8 = OCT_WIDTH;
    }

    impl Hex {
        pub const EXP: u8 = RADIX.ilog2() as u8;
        pub const PREFIX: &str = "0x";
        pub const RADIX: Double = RADIX;
        pub const WIDTH: u8 = BITS as u8 / 4;
    }

    impl From<Dec> for Radix {
        fn from(_: Dec) -> Self {
            Self {
                prefix: Dec::PREFIX,
                value: Dec::RADIX,
                width: Dec::WIDTH,
            }
        }
    }

    impl From<Bin> for Radix {
        fn from(_: Bin) -> Self {
            Self {
                prefix: Bin::PREFIX,
                value: Bin::RADIX,
                width: Bin::WIDTH,
            }
        }
    }

    impl From<Oct> for Radix {
        fn from(_: Oct) -> Self {
            Self {
                prefix: Oct::PREFIX,
                value: Oct::RADIX,
                width: Oct::WIDTH,
            }
        }
    }

    impl From<Hex> for Radix {
        fn from(_: Hex) -> Self {
            Self {
                prefix: Hex::PREFIX,
                value: Hex::RADIX,
                width: Hex::WIDTH,
            }
        }
    }
}

pub mod num {
    use super::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Signed<const L: usize>(pub [Single; L]);

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Unsigned<const L: usize>(pub [Single; L]);

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct SignedFixed<const L: usize>(pub [Single; L], pub usize);

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct UnsignedFixed<const L: usize>(pub [Single; L], pub usize);

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct SignedDyn(Vec<Single>, Sign);

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct UnsignedDyn(Vec<Single>);

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct SignedFixedDyn(Vec<Single>, Sign, usize);

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct UnsignedFixedDyn(Vec<Single>, usize);
}

pub mod bytes {
    use super::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Bytes<const L: usize>(pub [Single; L]);
}

#[allow(unused)]
mod uops {
    use super::*;

    pub(super) fn pos<const L: usize>(words: &[Single; L]) -> [Single; L] {
        *words
    }

    pub(super) fn pos_mut<const L: usize>(words: &mut [Single; L]) -> &mut [Single; L] {
        words
    }

    pub(super) fn neg<const L: usize>(words: &[Single; L]) -> [Single; L] {
        let mut words = *words;

        not_mut(&mut words);
        inc_mut(&mut words);

        words
    }

    pub(super) fn neg_mut<const L: usize>(words: &mut [Single; L]) -> &mut [Single; L] {
        not_mut(words);
        inc_mut(words);

        words
    }

    pub(super) fn not<const L: usize>(words: &[Single; L]) -> [Single; L] {
        words.iter().map(|&word| !word).collect_with([0; L])
    }

    pub(super) fn not_mut<const L: usize>(words: &mut [Single; L]) -> &mut [Single; L] {
        words.iter_mut().for_each(|word| *word = !*word);
        words
    }

    pub(super) fn inc<const L: usize>(words: &[Single; L]) -> [Single; L] {
        inc_impl!(*words)
    }

    pub(super) fn inc_mut<const L: usize>(words: &mut [Single; L]) -> &mut [Single; L] {
        inc_impl!(words)
    }

    pub(super) fn dec<const L: usize>(words: &[Single; L]) -> [Single; L] {
        dec_impl!(*words)
    }

    pub(super) fn dec_mut<const L: usize>(words: &mut [Single; L]) -> &mut [Single; L] {
        dec_impl!(words)
    }

    #[allow(unused_variables)]
    pub(super) fn shl<const L: usize>(words: &[Single; L], shift: usize, default: Single) -> [Single; L] {
        shl_impl!(*words, words, shift, default, |words: &[Single; L]| { [default; L] })
    }

    #[allow(unused_variables)]
    pub(super) fn shr<const L: usize>(words: &[Single; L], shift: usize, default: Single) -> [Single; L] {
        shr_impl!(*words, words, shift, default, |words: &[Single; L]| { [default; L] })
    }

    pub(super) fn shl_mut<'words, const L: usize>(
        words: &'words mut [Single; L],
        shift: usize,
        default: Single,
    ) -> &'words mut [Single; L] {
        shl_impl!(words, words, shift, default, |words: &'words mut [Single; L]| {
            *words = [default; L];
            words
        })
    }

    pub(super) fn shr_mut<'words, const L: usize>(
        words: &'words mut [Single; L],
        shift: usize,
        default: Single,
    ) -> &'words mut [Single; L] {
        shr_impl!(words, words, shift, default, |words: &'words mut [Single; L]| {
            *words = [default; L];
            words
        })
    }

    pub(super) fn shl_signed<const L: usize>(words: &[Single; L], shift: usize) -> [Single; L] {
        shl(words, shift, 0)
    }

    pub(super) fn shr_signed<const L: usize>(words: &[Single; L], shift: usize) -> [Single; L] {
        let default = match sign(words, Sign::POS, Sign::NEG) {
            Sign::ZERO => 0,
            Sign::NEG => MAX,
            Sign::POS => 0,
        };

        shr(words, shift, default)
    }

    pub(super) fn shl_signed_mut<const L: usize>(words: &mut [Single; L], shift: usize) -> &mut [Single; L] {
        shl_mut(words, shift, 0)
    }

    pub(super) fn shr_signed_mut<const L: usize>(words: &mut [Single; L], shift: usize) -> &mut [Single; L] {
        let default = match sign(words, Sign::POS, Sign::NEG) {
            Sign::ZERO => 0,
            Sign::NEG => MAX,
            Sign::POS => 0,
        };

        shr_mut(words, shift, default)
    }

    pub(super) fn sign<const L: usize>(words: &[Single; L], pos: Sign, neg: Sign) -> Sign {
        if words == &[0; L] {
            return Sign::ZERO;
        }

        match words[L - 1] >> (BITS - 1) {
            0 => pos,
            _ => neg,
        }
    }
}

#[cfg(all(target_pointer_width = "64", not(test)))]
mod _impl {
    use super::*;

    ops_primitive_native_impl!(@signed [i8, i16, i32, i64]);
    ops_primitive_native_impl!(@unsigned [u8, u16, u32, u64]);
    ops_primitive_native_impl!(@bytes [u8, u16, u32, u64]);

    ops_primitive_impl!(@signed [i128]);
    ops_primitive_impl!(@unsigned [u128]);
    ops_primitive_impl!(@bytes [u128]);
}

#[cfg(all(target_pointer_width = "32", not(test)))]
mod _impl {
    use super::*;

    ops_primitive_native_impl!(@signed [i8, i16, i32]);
    ops_primitive_native_impl!(@unsigned [u8, u16, u32]);
    ops_primitive_native_impl!(@bytes [u8, u16, u32]);

    ops_primitive_impl!(@signed [i64, i128]);
    ops_primitive_impl!(@unsigned [u64, u128]);
    ops_primitive_impl!(@bytes [u64, u128]);
}

#[cfg(test)]
mod _impl {
    use super::*;

    ops_primitive_native_impl!(@signed [i8]);
    ops_primitive_native_impl!(@unsigned [u8]);
    ops_primitive_native_impl!(@bytes [u8]);

    ops_primitive_impl!(@signed [i16, i32, i64, i128]);
    ops_primitive_impl!(@unsigned [u16, u32, u64, u128]);
    ops_primitive_impl!(@bytes [u16, u32, u64, u128]);
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

pub type B8 = bytes!(8);
pub type B12 = bytes!(12);
pub type B16 = bytes!(16);
pub type B24 = bytes!(24);
pub type B32 = bytes!(32);
pub type B48 = bytes!(48);
pub type B64 = bytes!(64);
pub type B96 = bytes!(96);
pub type B128 = bytes!(128);
pub type B192 = bytes!(192);
pub type B256 = bytes!(256);
pub type B384 = bytes!(384);
pub type B512 = bytes!(512);
pub type B768 = bytes!(768);
pub type B1024 = bytes!(1024);
pub type B1536 = bytes!(1536);
pub type B2048 = bytes!(2048);
pub type B3072 = bytes!(3072);
pub type B4096 = bytes!(4096);
pub type B6144 = bytes!(6144);
pub type B8192 = bytes!(8192);

#[derive(Debug, Clone)]
pub struct DigitsIter<'words, const L: usize, W: Word> {
    words: &'words [Single; L],
    bits: usize,
    mask: Double,
    cnt: usize,
    len: usize,
    acc: Double,
    shl: usize,
    idx: usize,
    _phantom: PhantomData<W>,
}

#[derive(Debug, Clone)]
pub struct DigitsRadixIter<const L: usize, W: Word> {
    words: [Single; L],
    radix: W,
    len: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryFromArrError {
    #[error("Found invalid length during initializing from array")]
    InvalidLength,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum TryFromSliceError {
    #[error("Found invalid length during initializing from slice")]
    InvalidLength,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum FromDigitsError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: usize },
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent { exp: u8 },
    #[error("Found invalid digit '{digit}' during parsing from slice of radix '{radix}'")]
    InvalidDigit { digit: usize, radix: usize },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum FromStrError {
    #[error("Found empty during parsing from string")]
    InvalidLength,
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: usize },
    #[error("Found invalid symbol '{ch}' during parsing from string of radix '{radix}'")]
    InvalidSymbol { ch: char, radix: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum ToDigitsError {
    #[error("Found invalid exp '{exp}'")]
    InvalidExponent { exp: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum IntoDigitsError {
    #[error("Found invalid radix '{radix}'")]
    InvalidRadix { radix: usize },
}

pub struct ExpImpl {
    pub exp: u8,
}

pub struct RadixImpl<W: Word> {
    pub radix: W,
}

pub trait DigitsImpl<W: Word> {}

pub trait FromDigits<W: Word, Impl: DigitsImpl<W>>: Sized {
    fn from_digits(digits: impl AsRef<[W]>, arg: Impl) -> Result<Self, FromDigitsError>;
}

pub trait FromDigitsIter<W: Word, Impl: DigitsImpl<W>>: Sized {
    fn from_digits_iter<Words>(digits: Words, arg: Impl) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W> + DoubleEndedIterator;
}

pub trait ToDigits<'words>: Sized {
    fn to_digits<W: Word>(&'words self, arg: ExpImpl) -> Result<Vec<W>, ToDigitsError>;
}

pub trait ToDigitsIter<'words>: Sized {
    type Iter<W: Word>: WordsIterator<Item = W> + ExactSizeIterator
    where
        Self: 'words;

    fn to_digits_iter<W: Word>(&'words self, arg: ExpImpl) -> Result<Self::Iter<W>, ToDigitsError>;
}

pub trait IntoDigits: Sized {
    fn into_digits<W: Word>(self, arg: RadixImpl<W>) -> Result<Vec<W>, IntoDigitsError>;
}

pub trait IntoDigitsIter: Sized {
    type Iter<W: Word>: WordsIterator<Item = W> + ExactSizeIterator;

    fn into_digits_iter<W: Word>(self, arg: RadixImpl<W>) -> Result<Self::Iter<W>, IntoDigitsError>;
}

impl<W: Word> DigitsImpl<W> for ExpImpl {}
impl<W: Word> DigitsImpl<W> for RadixImpl<W> {}

impl From<ToDigitsError> for IntoDigitsError {
    fn from(value: ToDigitsError) -> Self {
        match value {
            ToDigitsError::InvalidExponent { exp } => Self::InvalidRadix { radix: exp.order() },
        }
    }
}

impl<const L: usize> Default for Signed<L> {
    fn default() -> Self {
        Self([0; L])
    }
}

impl<const L: usize> Default for Unsigned<L> {
    fn default() -> Self {
        Self([0; L])
    }
}

impl<const L: usize> Default for Bytes<L> {
    fn default() -> Self {
        Self([0; L])
    }
}

impl<const L: usize> From<bool> for Signed<L> {
    fn from(value: bool) -> Self {
        Self::from(value as i8)
    }
}

impl<const L: usize> From<bool> for Unsigned<L> {
    fn from(value: bool) -> Self {
        Self::from(value as u8)
    }
}

impl<const L: usize> From<bool> for Bytes<L> {
    fn from(value: bool) -> Self {
        Self::from(value as u8)
    }
}

from_primitive!(@signed [i8, i16, i32, i64, i128, isize]);
from_primitive!(@unsigned [u8, u16, u32, u64, u128, usize]);
from_primitive!(@bytes [u8, u16, u32, u64, u128, usize]);

impl<const L: usize, W: Word, const N: usize> NdFrom<&[W; N]> for Signed<L> {
    fn nd_from(value: &[W; N]) -> Self {
        Self(from_arr(value, 0))
    }
}

impl<const L: usize, W: Word, const N: usize> NdFrom<&[W; N]> for Unsigned<L> {
    fn nd_from(value: &[W; N]) -> Self {
        Self(from_arr(value, 0))
    }
}

impl<const L: usize, W: Word, const N: usize> NdFrom<&[W; N]> for Bytes<L> {
    fn nd_from(value: &[W; N]) -> Self {
        Self(from_arr(value, 0))
    }
}

impl<const L: usize, W: Word> NdFrom<&[W]> for Signed<L> {
    fn nd_from(value: &[W]) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, W: Word> NdFrom<&[W]> for Unsigned<L> {
    fn nd_from(value: &[W]) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, W: Word> NdFrom<&[W]> for Bytes<L> {
    fn nd_from(value: &[W]) -> Self {
        Self(from_slice(value))
    }
}

impl<const L: usize, W: Word, const N: usize> NdTryFrom<&[W; N]> for Signed<L> {
    type Error = TryFromArrError;

    fn nd_try_from(value: &[W; N]) -> Result<Self, Self::Error> {
        try_from_arr(value, 0).map(Self)
    }
}

impl<const L: usize, W: Word, const N: usize> NdTryFrom<&[W; N]> for Unsigned<L> {
    type Error = TryFromArrError;

    fn nd_try_from(value: &[W; N]) -> Result<Self, Self::Error> {
        try_from_arr(value, 0).map(Self)
    }
}

impl<const L: usize, W: Word, const N: usize> NdTryFrom<&[W; N]> for Bytes<L> {
    type Error = TryFromArrError;

    fn nd_try_from(value: &[W; N]) -> Result<Self, Self::Error> {
        try_from_arr(value, 0).map(Self)
    }
}

impl<const L: usize, W: Word> NdTryFrom<&[W]> for Signed<L> {
    type Error = TryFromSliceError;

    fn nd_try_from(value: &[W]) -> Result<Self, Self::Error> {
        try_from_slice(value).map(Self)
    }
}

impl<const L: usize, W: Word> NdTryFrom<&[W]> for Unsigned<L> {
    type Error = TryFromSliceError;

    fn nd_try_from(value: &[W]) -> Result<Self, Self::Error> {
        try_from_slice(value).map(Self)
    }
}

impl<const L: usize, W: Word> NdTryFrom<&[W]> for Bytes<L> {
    type Error = TryFromSliceError;

    fn nd_try_from(value: &[W]) -> Result<Self, Self::Error> {
        try_from_slice(value).map(Self)
    }
}

impl<const L: usize, W: Word> FromIterator<W> for Signed<L> {
    fn from_iter<T: IntoIterator<Item = W>>(iter: T) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize, W: Word> FromIterator<W> for Unsigned<L> {
    fn from_iter<T: IntoIterator<Item = W>>(iter: T) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize, W: Word> FromIterator<W> for Bytes<L> {
    fn from_iter<T: IntoIterator<Item = W>>(iter: T) -> Self {
        Self(from_iter(iter.into_iter()))
    }
}

impl<const L: usize> FromStr for Signed<L> {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_impl!(@long s).map(Self)
    }
}

impl<const L: usize> FromStr for Unsigned<L> {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_impl!(@long s).map(Self)
    }
}

impl<const L: usize> FromStr for Bytes<L> {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_impl!(@bytes s).map(Self)
    }
}

impl<const L: usize> AsRef<[u8]> for Signed<L> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const L: usize> AsRef<[u8]> for Unsigned<L> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const L: usize> AsRef<[u8]> for Bytes<L> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const L: usize> AsMut<[u8]> for Signed<L> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
    }
}

impl<const L: usize> AsMut<[u8]> for Unsigned<L> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
    }
}

impl<const L: usize> AsMut<[u8]> for Bytes<L> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
    }
}

impl<const L: usize> PartialOrd for Signed<L> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const L: usize> PartialOrd for Unsigned<L> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const L: usize> Ord for Signed<L> {
    fn cmp(&self, other: &Self) -> Ordering {
        let x = self.sign();
        let y = other.sign();

        if x != y {
            return x.cmp(&y);
        }

        let ord = self.0.iter().rev().cmp(other.0.iter().rev());

        match x {
            Sign::ZERO => ord,
            Sign::NEG => match ord {
                Ordering::Less => Ordering::Greater,
                Ordering::Equal => Ordering::Equal,
                Ordering::Greater => Ordering::Less,
            },
            Sign::POS => ord,
        }
    }
}

impl<const L: usize> Ord for Unsigned<L> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.iter().rev().cmp(other.0.iter().rev())
    }
}

impl<const L: usize> Display for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self
            .signed(Sign::POS)
            .into_digits_iter(RadixImpl { radix: Dec::RADIX as Single })
        {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Dec.into(), self.sign(), write_dec)
    }
}

impl<const L: usize> Display for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.into_digits_iter(RadixImpl { radix: Dec::RADIX as Single }) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Dec.into(), self.sign(), write_dec)
    }
}

impl<const L: usize> Display for Bytes<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), Sign::POS, write_uhex)
    }
}

impl<const L: usize> Binary for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Bin.into(), get_sign(&self.0, Sign::POS), write_bin)
    }
}

impl<const L: usize> Binary for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Bin.into(), get_sign(&self.0, Sign::POS), write_bin)
    }
}

impl<const L: usize> Binary for Bytes<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Bin.into(), Sign::POS, write_bin)
    }
}

impl<const L: usize> Octal for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.to_digits_iter::<Single>(ExpImpl { exp: Oct::EXP }) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Oct.into(), get_sign(&self.0, Sign::POS), write_oct)
    }
}

impl<const L: usize> Octal for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.to_digits_iter::<Single>(ExpImpl { exp: Oct::EXP }) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Oct.into(), get_sign(&self.0, Sign::POS), write_oct)
    }
}

impl<const L: usize> Octal for Bytes<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let iter = match self.to_digits_iter::<Single>(ExpImpl { exp: Oct::EXP }) {
            Ok(val) => val,
            Err(_) => unreachable!(),
        };

        write_iter(f, iter, Oct.into(), Sign::POS, write_oct)
    }
}

impl<const L: usize> LowerHex for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_lhex)
    }
}

impl<const L: usize> LowerHex for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_lhex)
    }
}

impl<const L: usize> LowerHex for Bytes<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), Sign::POS, write_lhex)
    }
}

impl<const L: usize> UpperHex for Signed<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_uhex)
    }
}

impl<const L: usize> UpperHex for Unsigned<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), get_sign(&self.0, Sign::POS), write_uhex)
    }
}

impl<const L: usize> UpperHex for Bytes<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write(f, &self.0, Hex.into(), Sign::POS, write_uhex)
    }
}

ops_impl!(@un <const L: usize> |a: &Signed<L>| -> Signed::<L>,
    - Signed::<L>(neg(&a.0)),
    ! Signed::<L>(not(&a.0)),
);

ops_impl!(@un <const L: usize> |a: &Unsigned<L>| -> Unsigned::<L>,
    ! Unsigned::<L>(not(&a.0)),
);

ops_impl!(@un <const L: usize> |mut a: Signed<L>| -> Signed::<L>,
    - { neg_mut(&mut a.0); a },
    ! { not_mut(&mut a.0); a },
);

ops_impl!(@un <const L: usize> |mut a: Unsigned<L>| -> Unsigned::<L>,
    ! { not_mut(&mut a.0); a },
);

ops_impl!(@bin |a: Sign, b: Sign| -> Sign, * Sign::from((a as i8) * (b as i8)));

ops_impl!(@bin <const L: usize> |*a: &Signed<L>, *b: &Signed<L>| -> Signed::<L>,
    + Signed::<L>(add_long(&a.0, &b.0)),
    - Signed::<L>(sub_long(&a.0, &b.0)),
    * Signed::<L>(mul_long(&a.0, &b.0)),
    / Signed::<L>(div_long(&a.abs().0, &b.abs().0).0).signed(a.sign() * b.sign()),
    % Signed::<L>(div_long(&a.abs().0, &b.abs().0).1).signed(a.sign()),
    | Signed::<L>(bit_long(&a.0, &b.0, |aop, bop| aop | bop)),
    & Signed::<L>(bit_long(&a.0, &b.0, |aop, bop| aop & bop)),
    ^ Signed::<L>(bit_long(&a.0, &b.0, |aop, bop| aop ^ bop)));

ops_impl!(@bin <const L: usize> |*a: &Unsigned<L>, *b: &Unsigned<L>| -> Unsigned::<L>,
    + Unsigned::<L>(add_long(&a.0, &b.0)),
    - Unsigned::<L>(sub_long(&a.0, &b.0)),
    * Unsigned::<L>(mul_long(&a.0, &b.0)),
    / Unsigned::<L>(div_long(&a.0, &b.0).0),
    % Unsigned::<L>(div_long(&a.0, &b.0).1),
    | Unsigned::<L>(bit_long(&a.0, &b.0, |aop, bop| aop | bop)),
    & Unsigned::<L>(bit_long(&a.0, &b.0, |aop, bop| aop & bop)),
    ^ Unsigned::<L>(bit_long(&a.0, &b.0, |aop, bop| aop ^ bop)));

ops_impl!(@bin <const L: usize> |*a: &Bytes<L>, *b: &Bytes<L>| -> Bytes::<L>,
    | Bytes::<L>(bit_long(&a.0, &b.0, |aop, bop| aop | bop)),
    & Bytes::<L>(bit_long(&a.0, &b.0, |aop, bop| aop & bop)),
    ^ Bytes::<L>(bit_long(&a.0, &b.0, |aop, bop| aop ^ bop)));

ops_impl!(@mut <const L: usize> |a: mut Signed<L>, *b: &Signed<L>|,
    += add_long_mut(&mut a.0, &b.0),
    -= sub_long_mut(&mut a.0, &b.0),
    *= mul_long_mut(&mut a.0, &b.0),
    /= { *a = Signed::<L>(div_long(&a.abs().0, &b.abs().0).0).signed(a.sign() * b.sign()); },
    %= { *a = Signed::<L>(div_long(&a.abs().0, &b.abs().0).1).signed(a.sign()); },
    |= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop | bop),
    &= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop & bop),
    ^= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: mut Unsigned<L>, *b: &Unsigned<L>|,
    += add_long_mut(&mut a.0, &b.0),
    -= sub_long_mut(&mut a.0, &b.0),
    *= mul_long_mut(&mut a.0, &b.0),
    /= div_long_mut(&mut a.0, &b.0),
    %= rem_long_mut(&mut a.0, &b.0),
    |= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop | bop),
    &= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop & bop),
    ^= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop ^ bop));

ops_impl!(@mut <const L: usize> |a: mut Bytes<L>, *b: &Bytes<L>|,
    |= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop | bop),
    &= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop & bop),
    ^= bit_long_mut(&mut a.0, &b.0, |aop, bop| aop ^ bop));

ops_impl!(@bin <const L: usize> |*a: &Signed<L>, b: usize| -> Signed::<L>,
    << Signed::<L>(shl_signed(&a.0, b)),
    >> Signed::<L>(shr_signed(&a.0, b)));

ops_impl!(@bin <const L: usize> |*a: &Unsigned<L>, b: usize| -> Unsigned::<L>,
    << Unsigned::<L>(shl(&a.0, b, 0)),
    >> Unsigned::<L>(shr(&a.0, b, 0)));

ops_impl!(@bin <const L: usize> |*a: &Bytes<L>, b: usize| -> Bytes::<L>,
    << Bytes::<L>(shl(&a.0, b, 0)),
    >> Bytes::<L>(shr(&a.0, b, 0)));

ops_impl!(@mut <const L: usize> |a: mut Signed<L>, b: usize|,
    <<= { shl_signed_mut(&mut a.0, b); },
    >>= { shr_signed_mut(&mut a.0, b); });

ops_impl!(@mut <const L: usize> |a: mut Unsigned<L>, b: usize|,
    <<= { shl_mut(&mut a.0, b, 0); },
    >>= { shr_mut(&mut a.0, b, 0); });

ops_impl!(@mut <const L: usize> |a: mut Bytes<L>, b: usize|,
    <<= { shl_mut(&mut a.0, b, 0); },
    >>= { shr_mut(&mut a.0, b, 0); });

impl<const L: usize> Signed<L> {
    from_primitive_const!(@signed [
        (from_i8, i8),
        (from_i16, i16),
        (from_i32, i32),
        (from_i64, i64),
        (from_i128, i128),
        (from_isize, isize),
    ]);

    pub const fn from_bytes(bytes: &[u8]) -> Self {
        Self(from_bytes(bytes))
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    pub fn sign(&self) -> Sign {
        sign(&self.0, Sign::POS, Sign::NEG)
    }

    pub fn abs(&self) -> Signed<L> {
        match self.sign() {
            Sign::ZERO => Signed::<L>(self.0),
            Sign::NEG => Signed::<L>(neg(&self.0)),
            Sign::POS => Signed::<L>(self.0),
        }
    }

    pub fn signed(mut self, sign: Sign) -> Self {
        match self.sign() * sign {
            Sign::ZERO => return Self::default(),
            Sign::NEG => neg_mut(&mut self.0),
            Sign::POS => pos_mut(&mut self.0),
        };

        self
    }

    pub fn unsigned(self) -> Unsigned<L> {
        Unsigned::<L>(self.0)
    }
}

impl<const L: usize> Unsigned<L> {
    from_primitive_const!(@unsigned [
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

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }

    pub fn sign(&self) -> Sign {
        sign(&self.0, Sign::POS, Sign::POS)
    }

    pub fn signed(mut self, sign: Sign) -> Signed<L> {
        match self.sign() * sign {
            Sign::ZERO => return Signed::<L>::default(),
            Sign::NEG => neg_mut(&mut self.0),
            Sign::POS => pos_mut(&mut self.0),
        };

        Signed::<L>(self.0)
    }

    pub fn unsigned(self) -> Self {
        Self(self.0)
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

    pub fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_bytes()
    }
}

impl<const L: usize, W: Word> FromDigits<W, ExpImpl> for Signed<L> {
    fn from_digits(digits: impl AsRef<[W]>, arg: ExpImpl) -> Result<Self, FromDigitsError> {
        from_digits(digits.as_ref(), arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigits<W, ExpImpl> for Unsigned<L> {
    fn from_digits(digits: impl AsRef<[W]>, arg: ExpImpl) -> Result<Self, FromDigitsError> {
        from_digits(digits.as_ref(), arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigits<W, ExpImpl> for Bytes<L> {
    fn from_digits(digits: impl AsRef<[W]>, arg: ExpImpl) -> Result<Self, FromDigitsError> {
        from_digits(digits.as_ref(), arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigitsIter<W, ExpImpl> for Signed<L> {
    fn from_digits_iter<Words>(digits: Words, arg: ExpImpl) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W>,
    {
        from_digits_iter(digits, arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigitsIter<W, ExpImpl> for Unsigned<L> {
    fn from_digits_iter<Words>(digits: Words, arg: ExpImpl) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W>,
    {
        from_digits_iter(digits, arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigitsIter<W, ExpImpl> for Bytes<L> {
    fn from_digits_iter<Words>(digits: Words, arg: ExpImpl) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W>,
    {
        from_digits_iter(digits, arg.exp).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigits<W, RadixImpl<W>> for Signed<L> {
    fn from_digits(digits: impl AsRef<[W]>, arg: RadixImpl<W>) -> Result<Self, FromDigitsError> {
        from_digits_radix(digits.as_ref(), arg.radix).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigits<W, RadixImpl<W>> for Unsigned<L> {
    fn from_digits(digits: impl AsRef<[W]>, arg: RadixImpl<W>) -> Result<Self, FromDigitsError> {
        from_digits_radix(digits.as_ref(), arg.radix).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigitsIter<W, RadixImpl<W>> for Signed<L> {
    fn from_digits_iter<Words>(digits: Words, arg: RadixImpl<W>) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W> + DoubleEndedIterator,
    {
        from_digits_radix_iter(digits, arg.radix).map(Self)
    }
}

impl<const L: usize, W: Word> FromDigitsIter<W, RadixImpl<W>> for Unsigned<L> {
    fn from_digits_iter<Words>(digits: Words, arg: RadixImpl<W>) -> Result<Self, FromDigitsError>
    where
        Words: WordsIterator<Item = W> + DoubleEndedIterator,
    {
        from_digits_radix_iter(digits, arg.radix).map(Self)
    }
}

impl<'words, const L: usize> ToDigits<'words> for Signed<L> {
    fn to_digits<W: Word>(&'words self, arg: ExpImpl) -> Result<Vec<W>, ToDigitsError> {
        to_digits(&self.0, arg.exp)
    }
}

impl<'words, const L: usize> ToDigits<'words> for Unsigned<L> {
    fn to_digits<W: Word>(&'words self, arg: ExpImpl) -> Result<Vec<W>, ToDigitsError> {
        to_digits(&self.0, arg.exp)
    }
}

impl<'words, const L: usize> ToDigits<'words> for Bytes<L> {
    fn to_digits<W: Word>(&'words self, arg: ExpImpl) -> Result<Vec<W>, ToDigitsError> {
        to_digits(&self.0, arg.exp)
    }
}

impl<'words, const L: usize> ToDigitsIter<'words> for Signed<L> {
    type Iter<W: Word> = DigitsIter<'words, L, W>;

    fn to_digits_iter<W: Word>(&'words self, arg: ExpImpl) -> Result<Self::Iter<W>, ToDigitsError> {
        to_digits_iter(&self.0, arg.exp)
    }
}

impl<'words, const L: usize> ToDigitsIter<'words> for Unsigned<L> {
    type Iter<W: Word> = DigitsIter<'words, L, W>;

    fn to_digits_iter<W: Word>(&'words self, arg: ExpImpl) -> Result<Self::Iter<W>, ToDigitsError> {
        to_digits_iter(&self.0, arg.exp)
    }
}

impl<'words, const L: usize> ToDigitsIter<'words> for Bytes<L> {
    type Iter<W: Word> = DigitsIter<'words, L, W>;

    fn to_digits_iter<W: Word>(&'words self, arg: ExpImpl) -> Result<Self::Iter<W>, ToDigitsError> {
        to_digits_iter(&self.0, arg.exp)
    }
}

impl<const L: usize> IntoDigits for Signed<L> {
    fn into_digits<W: Word>(self, arg: RadixImpl<W>) -> Result<Vec<W>, IntoDigitsError> {
        into_digits(self.0, arg.radix)
    }
}

impl<const L: usize> IntoDigits for Unsigned<L> {
    fn into_digits<W: Word>(self, arg: RadixImpl<W>) -> Result<Vec<W>, IntoDigitsError> {
        into_digits(self.0, arg.radix)
    }
}

impl<const L: usize> IntoDigitsIter for Signed<L> {
    type Iter<W: Word> = DigitsRadixIter<L, W>;

    fn into_digits_iter<W: Word>(self, arg: RadixImpl<W>) -> Result<Self::Iter<W>, IntoDigitsError> {
        into_digits_iter(self.0, arg.radix)
    }
}

impl<const L: usize> IntoDigitsIter for Unsigned<L> {
    type Iter<W: Word> = DigitsRadixIter<L, W>;

    fn into_digits_iter<W: Word>(self, arg: RadixImpl<W>) -> Result<Self::Iter<W>, IntoDigitsError> {
        into_digits_iter(self.0, arg.radix)
    }
}

impl<'words, const L: usize, W: Word> ExactSizeIterator for DigitsIter<'words, L, W> {}
impl<'words, const L: usize, W: Word> Iterator for DigitsIter<'words, L, W> {
    type Item = W;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == self.cnt {
            if self.acc == 0 {
                return None;
            }

            let val = self.acc;

            self.acc >>= self.bits;
            self.shl = self.shl.saturating_sub(self.bits);

            return Some(W::from_double(val & self.mask));
        }

        if self.shl < self.bits {
            self.acc |= (self.words[self.idx] as Double) << self.shl;
            self.shl += BITS;
            self.idx += 1;
        }

        let val = self.acc;

        self.acc >>= self.bits;
        self.shl -= self.bits;

        Some(W::from_double(val & self.mask))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<const L: usize, W: Word> ExactSizeIterator for DigitsRadixIter<L, W> {}
impl<const L: usize, W: Word> Iterator for DigitsRadixIter<L, W> {
    type Item = W;

    fn next(&mut self) -> Option<Self::Item> {
        let radix = self.radix.as_double();

        let mut any = 0;
        let mut acc = 0;

        for word in self.words.iter_mut().rev() {
            any |= *word;
            acc = (acc << BITS) | *word as Double;

            *word = (acc / radix) as Single;

            acc %= radix;
        }

        if any == 0 {
            return None;
        }

        Some(W::from_double(acc))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<const L: usize> Num for Signed<L> {
    fn bits(&self) -> usize {
        L * BITS
    }

    fn is_even(&self) -> bool {
        self.0[0].is_multiple_of(2)
    }
}

impl<const L: usize> Num for Unsigned<L> {
    fn bits(&self) -> usize {
        L * BITS
    }

    fn is_even(&self) -> bool {
        self.0[0].is_multiple_of(2)
    }
}

impl<const L: usize> NumSigned for Signed<L> {}

impl<const L: usize> NumUnsigned for Unsigned<L> {
    fn order(&self) -> usize {
        let len = get_len_arr(&self.0);

        match len {
            0 => 0,
            l => (l - 1) * BITS + self.0[l - 1].order(),
        }
    }

    fn log(&self) -> Self {
        let len = get_len_arr(&self.0);

        match len {
            0 => Self::ZERO,
            l => Self::from((l - 1) * BITS + self.0[l - 1].order()),
        }
    }

    fn sqrt(&self) -> Self {
        todo!()
    }
}

impl<const L: usize> NumStatic for Signed<L> {
    const BITS: usize = L * BITS;
    const BYTES: usize = L * BYTES;
    const MAX: Self = Self({
        let mut res = [MAX; L];

        res[L - 1] = MAX >> 1;
        res
    });
    const MIN: Self = Self({
        let mut res = [MIN; L];

        res[L - 1] = 1 << (BITS - 1);
        res
    });
    const ONE: Self = Self::from_isize(0);
    const ZERO: Self = Self::from_isize(0);
}

impl<const L: usize> NumStatic for Unsigned<L> {
    const BITS: usize = BITS;
    const BYTES: usize = BYTES;
    const MAX: Self = Self([MAX; L]);
    const MIN: Self = Self([MIN; L]);
    const ONE: Self = Self::from_usize(0);
    const ZERO: Self = Self::from_usize(0);
}

const fn from_bytes<const L: usize>(bytes: &[u8]) -> [Single; L] {
    let (bytes, bytes_) = bytes.as_chunks::<BYTES>();

    let mut idx = 0;
    let mut idx_ = 0;
    let mut res = [0; L];

    #[allow(clippy::modulo_one)]
    while idx < bytes.len() && idx < L * BYTES {
        let offset = idx / BYTES;
        let shift = idx % BYTES;
        let byte = bytes[offset][shift] as Single;

        idx += 1;
        res[offset] |= byte << shift;
    }

    #[allow(clippy::modulo_one)]
    while idx_ < bytes_.len() && idx < L * BYTES {
        let offset = idx / BYTES;
        let shift = idx % BYTES;
        let shift_ = idx_ % BYTES;
        let byte = bytes_[shift_] as Single;

        idx += 1;
        idx_ += 1;
        res[offset] |= byte << shift;
    }

    res
}

fn try_from_arr<const L: usize, const N: usize, W: Word>(
    arr: &[W; N],
    default: Single,
) -> Result<[Single; L], TryFromArrError> {
    match (N * W::BYTES).cmp(&(L * BYTES)) {
        Ordering::Less => Ok(from_arr(arr, default)),
        Ordering::Equal => Ok(from_arr(arr, default)),
        Ordering::Greater => Err(TryFromArrError::InvalidLength),
    }
}

fn try_from_slice<const L: usize, W: Word>(slice: &[W]) -> Result<[Single; L], TryFromSliceError> {
    match (slice.len() * W::BYTES).cmp(&(L * BYTES)) {
        Ordering::Less => Ok(from_slice(slice)),
        Ordering::Equal => Ok(from_slice(slice)),
        Ordering::Greater => Err(TryFromSliceError::InvalidLength),
    }
}

fn from_arr<const L: usize, const N: usize, W: Word>(arr: &[W; N], default: Single) -> [Single; L] {
    let len = N.min(L * BYTES / W::BYTES);

    let mut res = [default; L];

    (transmute_mut!(res.as_mut_bytes()) as &mut [W])[..len].copy_from_slice(&arr[..len]);

    #[cfg(target_endian = "big")]
    res.iter_mut().for_each(|ptr| {
        (transmute_mut!(ptr.as_mut_bytes()) as &mut [W]).reverse();
    });

    res
}

fn from_slice<const L: usize, W: Word>(slice: &[W]) -> [Single; L] {
    let len = slice.len().min(L * BYTES / W::BYTES);

    let mut res = [0; L];

    (transmute_mut!(res.as_mut_bytes()) as &mut [W])[..len].copy_from_slice(&slice[..len]);

    #[cfg(target_endian = "big")]
    res.iter_mut().for_each(|ptr| {
        (transmute_mut!(ptr.as_mut_bytes()) as &mut [W]).reverse();
    });

    res
}

fn from_iter<const L: usize, W: Word, Iter: Iterator<Item = W>>(iter: Iter) -> [Single; L] {
    let mut res = [0; L];

    (transmute_mut!(res.as_mut_bytes()) as &mut [W])
        .iter_mut()
        .zip(iter)
        .for_each(|(ptr, val)| *ptr = val);

    #[cfg(target_endian = "big")]
    res.iter_mut().for_each(|ptr| {
        (transmute_mut!(ptr.as_mut_bytes()) as &mut [W]).reverse();
    });

    res
}

fn from_digits_validate<W: Word, Words>(mut digits: Words, radix: W) -> Result<(), FromDigitsError>
where
    Words: WordsIterator<Item = W>,
{
    if radix.as_single() < 2 {
        return Err(FromDigitsError::InvalidRadix {
            radix: radix.as_single() as usize,
        });
    }

    if let Some(digit) = digits.find(|&digit| digit >= radix) {
        return Err(FromDigitsError::InvalidDigit {
            digit: digit.as_single() as usize,
            radix: radix.as_single() as usize,
        });
    }

    Ok(())
}

fn from_str_validate(s: &str, radix: u8) -> Result<(), FromStrError> {
    if let Some(ch) = s.chars().find(|&ch| {
        let byte = ch as u8;

        match ch {
            '0'..='9' => byte - b'0' >= radix,
            'a'..='f' => byte - b'a' + 10 >= radix,
            'A'..='F' => byte - b'A' + 10 >= radix,
            '_' => false,
            _ => false,
        }
    }) {
        return Err(FromStrError::InvalidSymbol { ch, radix });
    }

    Ok(())
}

fn to_digits_validate<W: Word>(exp: u8) -> Result<(), ToDigitsError> {
    if exp == 0 || exp >= W::BITS as u8 {
        return Err(ToDigitsError::InvalidExponent { exp });
    }

    Ok(())
}

fn into_digits_validate<W: Word>(radix: W) -> Result<(), IntoDigitsError> {
    let radix = radix.as_single() as usize;

    if radix < 2 {
        return Err(IntoDigitsError::InvalidRadix { radix });
    }

    Ok(())
}

fn from_digits<const L: usize, W: Word>(digits: &[W], exp: u8) -> Result<[Single; L], FromDigitsError> {
    if exp >= W::BITS as u8 {
        return Err(FromDigitsError::InvalidExponent { exp });
    }

    from_digits_validate(digits.iter().copied(), W::from_single(1 << exp))?;

    let res = from_digits_impl!(digits, digits.len(), exp);

    Ok(res)
}

fn from_digits_iter<const L: usize, W: Word, Words>(digits: Words, exp: u8) -> Result<[Single; L], FromDigitsError>
where
    Words: WordsIterator<Item = W>,
{
    if exp >= W::BITS as u8 {
        return Err(FromDigitsError::InvalidExponent { exp });
    }

    from_digits_validate(digits.clone(), W::from_single(1 << exp))?;

    let res = from_digits_impl!(digits, digits.len(), exp);

    Ok(res)
}

fn from_str<const L: usize>(s: &str, exp: u8, sign: Sign) -> Result<[Single; L], FromStrError> {
    from_str_validate(s, 1 << exp)?;

    let mut res = from_digits_impl!(s.bytes().rev().filter_map(get_digit_from_byte), s.len(), exp);

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

fn from_digits_radix<const L: usize, W: Word>(digits: &[W], radix: W) -> Result<[Single; L], FromDigitsError> {
    if radix.is_pow2() {
        return from_digits(digits, radix.order() as u8);
    }

    from_digits_validate(digits.iter().copied(), radix)?;

    let res = from_digits_radix_impl!(digits.iter().rev(), radix);

    Ok(res)
}

fn from_digits_radix_iter<const L: usize, W: Word, Words>(
    digits: Words,
    radix: W,
) -> Result<[Single; L], FromDigitsError>
where
    Words: WordsIterator<Item = W> + DoubleEndedIterator,
{
    if radix.is_pow2() {
        return from_digits_iter(digits, radix.order() as u8);
    }

    from_digits_validate(digits.clone(), radix)?;

    let res = from_digits_radix_impl!(digits.rev(), radix);

    Ok(res)
}

fn from_str_radix<const L: usize>(s: &str, radix: u8, sign: Sign) -> Result<[Single; L], FromStrError> {
    if radix.is_pow2() {
        return from_str(s, radix.order() as u8, sign);
    }

    from_str_validate(s, radix)?;

    let mut res = from_digits_radix_impl!(s.bytes().filter_map(get_digit_from_byte), radix);

    if sign == Sign::NEG {
        neg_mut(&mut res);
    }

    Ok(res)
}

fn to_digits<const L: usize, W: Word>(words: &[Single; L], exp: u8) -> Result<Vec<W>, ToDigitsError> {
    to_digits_validate::<W>(exp)?;

    let bits = exp as usize;
    let mask = (1 << bits) - 1;
    let len = (words.len() * BITS + bits - 1) / bits;

    let mut acc = 0;
    let mut shl = 0;
    let mut idx = 0;
    let mut res = vec![W::ZERO; len + 1];

    for &digit in words {
        acc |= (digit as Double) << shl;
        shl += BITS;
        res[idx] = W::from_double(acc & mask);

        while shl >= bits {
            acc >>= bits;
            shl -= bits;
            idx += 1;
            res[idx] = W::from_double(acc & mask);
        }
    }

    res.truncate(get_len_slice(&res));

    Ok(res)
}

fn to_digits_iter<const L: usize, W: Word>(
    words: &[Single; L],
    exp: u8,
) -> Result<DigitsIter<'_, L, W>, ToDigitsError> {
    to_digits_validate::<W>(exp)?;

    let bits = exp as usize;
    let mask = (1 << bits) - 1;
    let cnt = get_len_arr(words);
    let len = (cnt * BITS + bits - 1) / bits;

    Ok(DigitsIter {
        words,
        bits,
        mask,
        cnt,
        len,
        acc: 0,
        shl: 0,
        idx: 0,
        _phantom: PhantomData,
    })
}

fn into_digits<const L: usize, W: Word>(mut words: [Single; L], radix: W) -> Result<Vec<W>, IntoDigitsError> {
    if radix.is_pow2() {
        return Ok(to_digits(&words, radix.order() as u8)?);
    }

    into_digits_validate(radix)?;

    let bits = radix.order();
    let len = (words.len() * BITS + bits - 1) / bits;

    let mut idx = 0;
    let mut res = vec![W::ZERO; len + 1];

    loop {
        let mut any = 0;
        let mut acc = 0;

        for digit in words.iter_mut().rev() {
            any |= *digit;
            acc = (acc << BITS) | *digit as Double;

            *digit = (acc / radix.as_double()) as Single;

            acc %= radix.as_double();
        }

        if any == 0 {
            break;
        }

        res[idx] = W::from_double(acc);
        idx += 1;
    }

    res.truncate(get_len_slice(&res));

    Ok(res)
}

fn into_digits_iter<const L: usize, W: Word>(
    words: [Single; L],
    radix: W,
) -> Result<DigitsRadixIter<L, W>, IntoDigitsError> {
    into_digits_validate(radix)?;

    let bits = radix.order();
    let cnt = get_len_arr(&words);
    let len = (cnt * BITS + bits - 1) / bits;

    Ok(DigitsRadixIter { words, radix, len })
}

fn write_dec(mut cursor: Cursor<&mut [u8]>, word: Single, width: usize) -> std::fmt::Result {
    match cursor.write_fmt(format_args!("{word:0width$}")) {
        Ok(()) => (),
        Err(_) => return Err(std::fmt::Error),
    }

    Ok(())
}

fn write_bin(cursor: Cursor<&mut [u8]>, mut word: Single, width: usize) -> std::fmt::Result {
    let buf = cursor.into_inner();

    #[allow(clippy::unnecessary_cast)]
    for byte in buf[..width].iter_mut().rev() {
        *byte = b'0' + (word % 2) as u8;
        word /= 2;
    }

    Ok(())
}

fn write_oct(cursor: Cursor<&mut [u8]>, mut word: Single, width: usize) -> std::fmt::Result {
    let buf = cursor.into_inner();

    #[allow(clippy::unnecessary_cast)]
    for byte in buf[..width].iter_mut().rev() {
        *byte = b'0' + (word % 8) as u8;
        word /= 8;
    }

    Ok(())
}

fn write_lhex(cursor: Cursor<&mut [u8]>, mut word: Single, width: usize) -> std::fmt::Result {
    const HEX: [u8; 16] = [
        b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'a', b'b', b'c', b'd', b'e', b'f',
    ];

    let buf = cursor.into_inner();

    for byte in buf[..width].iter_mut().rev() {
        *byte = HEX[(word % 16) as usize];
        word /= 16;
    }

    Ok(())
}

fn write_uhex(cursor: Cursor<&mut [u8]>, mut word: Single, width: usize) -> std::fmt::Result {
    const HEX: [u8; 16] = [
        b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'A', b'B', b'C', b'D', b'E', b'F',
    ];

    let buf = cursor.into_inner();

    for byte in buf[..width].iter_mut().rev() {
        *byte = HEX[(word % 16) as usize];
        word /= 16;
    }

    Ok(())
}

fn write<const L: usize, F: Fn(Cursor<&mut [u8]>, Single, usize) -> std::fmt::Result>(
    fmt: &mut Formatter<'_>,
    words: &[Single; L],
    radix: Radix,
    sign: Sign,
    func: F,
) -> std::fmt::Result {
    let sign = match sign {
        Sign::ZERO => {
            return write!(fmt, "{}0", radix.prefix);
        },
        Sign::NEG => "-",
        Sign::POS => "",
    };

    let prefix = radix.prefix;
    let width = radix.width as usize;
    let len = get_len_arr(words);

    let mut buf = vec![b'0'; len * width];

    for (i, &word) in words[..len].iter().enumerate() {
        let offset = (len - i - 1) * width;

        func(Cursor::new(&mut buf[offset..]), word, width)?;
    }

    let offset = buf.iter().take_while(|&byte| byte == &b'0').count();
    let str = match str::from_utf8(&buf[offset..]) {
        Ok(val) => val,
        Err(_) => unreachable!(),
    };

    write!(fmt, "{}{}{}", sign, prefix, str)
}

fn write_iter<W: Word, Words, F: Fn(Cursor<&mut [u8]>, Single, usize) -> std::fmt::Result>(
    fmt: &mut Formatter<'_>,
    words: Words,
    radix: Radix,
    sign: Sign,
    func: F,
) -> std::fmt::Result
where
    Words: WordsIterator<Item = W>,
{
    let sign = match sign {
        Sign::ZERO => {
            return write!(fmt, "{}0", radix.prefix);
        },
        Sign::NEG => "-",
        Sign::POS => "",
    };

    let prefix = radix.prefix;
    let width = radix.width as usize;
    let len = words.len();

    let mut buf = vec![b'0'; len * width];

    for (i, word) in words.enumerate() {
        let offset = (len - i - 1) * width;

        func(Cursor::new(&mut buf[offset..]), word.as_single(), width)?;
    }

    let offset = buf.iter().take_while(|&byte| byte == &b'0').count();
    let str = match str::from_utf8(&buf[offset..]) {
        Ok(val) => val,
        Err(_) => unreachable!(),
    };

    write!(fmt, "{}{}{}", sign, prefix, str)
}

fn add_long<const L: usize>(a: &[Single; L], b: &[Single; L]) -> [Single; L] {
    add_long_impl!(a.iter().copied(), b.iter().copied()).collect_with([0; L])
}

fn sub_long<const L: usize>(a: &[Single; L], b: &[Single; L]) -> [Single; L] {
    sub_long_impl!(a.iter().copied(), b.iter().copied()).collect_with([0; L])
}

fn mul_long<const L: usize>(a: &[Single; L], b: &[Single; L]) -> [Single; L] {
    let mut res = [0; L];

    for (idx, x) in b.iter().enumerate() {
        let res_iter = res.iter_mut().skip(idx);
        let mul_iter = mul_single_impl!(a.iter().copied(), *x);

        add_long_mut_impl!(res_iter, mul_iter);
    }

    res
}

fn div_long<const L: usize>(a: &[Single; L], b: &[Single; L]) -> ([Single; L], [Single; L]) {
    div_long_impl!(*a, b.iter().copied())
}

fn bit_long<const L: usize, F>(a: &[Single; L], b: &[Single; L], f: F) -> [Single; L]
where
    F: Fn(Single, Single) -> Single,
{
    a.iter()
        .copied()
        .zip(b.iter().copied())
        .map(|(a, b)| f(a, b))
        .collect_with([0; L])
}

fn add_single<const L: usize>(a: &[Single; L], b: Single) -> [Single; L] {
    add_single_impl!(a.iter().copied(), b).collect_with([0; L])
}

fn sub_single<const L: usize>(a: &[Single; L], b: Single) -> [Single; L] {
    sub_single_impl!(a.iter().copied(), b).collect_with([0; L])
}

fn mul_single<const L: usize>(a: &[Single; L], b: Single) -> [Single; L] {
    mul_single_impl!(a.iter().copied(), b).collect_with([0; L])
}

fn div_single<const L: usize>(a: &[Single; L], b: Single) -> ([Single; L], [Single; L]) {
    let (div, rem) = div_single_impl!(*a, b);

    (div, from_arr(&rem.to_le_bytes(), 0))
}

fn bit_single<const L: usize, F>(a: &[Single; L], b: Single, default: Single, f: F) -> [Single; L]
where
    F: Fn(Single, Single) -> Single,
{
    a.iter()
        .copied()
        .zip(once(b).chain(repeat(default)))
        .map(|(a, b)| f(a, b))
        .collect_with([0; L])
}

fn add_signed<const L: usize>(a: &[Single; L], (b, sign): (Single, Sign)) -> [Single; L] {
    match sign {
        Sign::ZERO => sub_single(a, b),
        Sign::NEG => sub_single(a, b),
        Sign::POS => add_single(a, b),
    }
}

fn sub_signed<const L: usize>(a: &[Single; L], (b, sign): (Single, Sign)) -> [Single; L] {
    match sign {
        Sign::ZERO => add_single(a, b),
        Sign::NEG => add_single(a, b),
        Sign::POS => sub_single(a, b),
    }
}

fn mul_signed<const L: usize>(a: &[Single; L], (b, sign): (Single, Sign)) -> [Single; L] {
    let mut mul = mul_single(a, b);

    if sign == Sign::NEG {
        neg_mut(&mut mul);
    }

    mul
}

fn add_long_mut<const L: usize>(a: &mut [Single; L], b: &[Single; L]) {
    add_long_mut_impl!(a.iter_mut(), b.iter().copied());
}

fn sub_long_mut<const L: usize>(a: &mut [Single; L], b: &[Single; L]) {
    sub_long_mut_impl!(a.iter_mut(), b.iter().copied());
}

fn mul_long_mut<const L: usize>(a: &mut [Single; L], b: &[Single; L]) {
    *a = mul_long(a, b);
}

fn div_long_mut<const L: usize>(a: &mut [Single; L], b: &[Single; L]) {
    div_long_impl!(a, b.iter().copied());
}

fn rem_long_mut<const L: usize>(a: &mut [Single; L], b: &[Single; L]) {
    let (_, rem) = div_long_impl!(*a, b.iter().copied());

    *a = rem;
}

fn bit_long_mut<const L: usize, F>(a: &mut [Single; L], b: &[Single; L], f: F)
where
    F: Fn(Single, Single) -> Single,
{
    a.iter_mut().zip(b.iter().copied()).for_each(|(ptr, val)| *ptr = f(*ptr, val));
}

fn add_single_mut<const L: usize>(a: &mut [Single; L], b: Single) {
    add_single_mut_impl!(a.iter_mut(), b);
}

fn sub_single_mut<const L: usize>(a: &mut [Single; L], b: Single) {
    sub_single_mut_impl!(a.iter_mut(), b);
}

fn mul_single_mut<const L: usize>(a: &mut [Single; L], b: Single) {
    mul_single_mut_impl!(a.iter_mut(), b);
}

fn div_single_mut<const L: usize>(a: &mut [Single; L], b: Single) {
    div_single_impl!(a, b);
}

fn rem_single_mut<const L: usize>(a: &mut [Single; L], b: Single) {
    let (_, rem) = div_single_impl!(*a, b);

    *a = from_arr(&rem.to_le_bytes(), 0);
}

fn bit_single_mut<const L: usize, F>(a: &mut [Single; L], b: Single, default: Single, f: F)
where
    F: Fn(Single, Single) -> Single,
{
    a.iter_mut()
        .zip(once(b).chain(repeat(default)))
        .for_each(|(ptr, val)| *ptr = f(*ptr, val));
}

fn add_signed_mut<const L: usize>(a: &mut [Single; L], (b, sign): (Single, Sign)) {
    match sign {
        Sign::ZERO => sub_single_mut(a, b),
        Sign::NEG => sub_single_mut(a, b),
        Sign::POS => add_single_mut(a, b),
    }
}

fn sub_signed_mut<const L: usize>(a: &mut [Single; L], (b, sign): (Single, Sign)) {
    match sign {
        Sign::ZERO => add_single_mut(a, b),
        Sign::NEG => add_single_mut(a, b),
        Sign::POS => sub_single_mut(a, b),
    }
}

fn mul_signed_mut<const L: usize>(a: &mut [Single; L], (b, sign): (Single, Sign)) {
    mul_single_mut(a, b);

    if sign == Sign::NEG {
        neg_mut(a);
    }
}

fn get_sign_from_str(s: &str) -> Result<(&str, Sign), FromStrError> {
    if s.is_empty() {
        return Err(FromStrError::InvalidLength);
    }

    Ok(match &s[..1] {
        "+" => (&s[1..], Sign::POS),
        "-" => (&s[1..], Sign::NEG),
        _ => (s, Sign::POS),
    })
}

fn get_radix_from_str(s: &str, default: u8) -> Result<(&str, u8), FromStrError> {
    if s.is_empty() {
        return Err(FromStrError::InvalidLength);
    }

    if s.len() < 2 {
        return Ok((s, 10));
    }

    Ok(match &s[..2] {
        "0x" | "0X" => (&s[2..], 16),
        "0o" | "0O" => (&s[2..], 8),
        "0b" | "0B" => (&s[2..], 2),
        _ => (s, default),
    })
}

fn get_digit_from_byte(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn get_len_arr<W: Word, const L: usize>(words: &[W; L]) -> usize {
    for (i, word) in words.iter().enumerate().rev() {
        if word != &W::ZERO {
            return i + 1;
        }
    }

    0
}

fn get_len_slice<W: Word>(words: &[W]) -> usize {
    for (i, word) in words.iter().enumerate().rev() {
        if word != &W::ZERO {
            return i + 1;
        }
    }

    0
}

fn get_sign<W: Word, const L: usize>(words: &[W; L], sign: Sign) -> Sign {
    if words != &[W::ZERO; L] { sign } else { Sign::ZERO }
}

#[cfg(test)]
mod tests {
    use std::iter::repeat;

    use anyhow::Result;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    use super::*;
    use crate::long::{S64, U64};

    const PRIMES_48BIT: [usize; 2] = [281_415_416_265_077, 281_397_419_487_323];
    const PRIMES_56BIT: [usize; 2] = [72_057_582_686_044_051, 72_051_998_136_909_223];

    macro_rules! assert_ops {
        ($type:ty, $iter_a:expr, $iter_b:expr, [$(($fn_lval:expr) ($fn_rval:expr)),+ $(,)?]) => {
            for a in $iter_a {
                for b in $iter_b {
                    let along = <$type>::from(a);
                    let blong = <$type>::from(b);

                    $({
                        let lval = ($fn_lval)(along, blong);
                        let rval = ($fn_rval)(a, b);

                        assert_eq!(lval, rval);
                    })+
                }
            }
        };
    }

    macro_rules! assert_ops_primitive {
        ($type:ty, $iter_a:expr, $iter_b:expr, [$(($fn_lval:expr) ($fn_rval:expr)),+ $(,)?]) => {
            for a in $iter_a {
                for b in $iter_b {
                    let long = <$type>::from(a);

                    $({
                        let lval = ($fn_lval)(long, b);
                        let rval = ($fn_rval)(a, b);

                        assert_eq!(lval, rval);
                    })+
                }
            }
        };
    }

    macro_rules! assert_ops_shift {
        ($type:ty, $iter_val:expr, $iter_shift:expr, [$(($fn_lval:expr) ($fn_rval:expr)),+ $(,)?]) => {
            for val in $iter_val {
                for shift in $iter_shift {
                    let long = <$type>::from(val);

                    $({
                        let lval = ($fn_lval)(long, shift);
                        let rval = ($fn_rval)(val, shift);

                        assert_eq!(lval, rval);
                    })+
                }
            }
        };
    }

    #[test]
    fn from_std() {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            let pval = val as i128;
            let nval = -pval;

            assert_eq!(S64::from(pval), S64 { 0: pos(&bytes) });
            assert_eq!(S64::from(nval), S64 { 0: neg(&bytes) });
            assert_eq!(U64::from(val), U64 { 0: pos(&bytes) });
        }
    }

    #[test]
    fn from_bytes() {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            assert_eq!(S64::from_bytes(&bytes), S64 { 0: pos(&bytes) });
            assert_eq!(U64::from_bytes(&bytes), U64 { 0: pos(&bytes) });
        }
    }

    #[test]
    fn from_arr() -> Result<()> {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            assert_eq!(S64::nd_try_from(&bytes)?, S64 { 0: pos(&bytes) });
            assert_eq!(U64::nd_try_from(&bytes)?, U64 { 0: pos(&bytes) });
        }

        Ok(())
    }

    #[test]
    fn from_slice() -> Result<()> {
        let empty = &[] as &[u8];

        assert_eq!(S64::nd_try_from(empty)?, S64::default());
        assert_eq!(U64::nd_try_from(empty)?, U64::default());

        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();
            let slice = bytes.as_slice();

            assert_eq!(S64::nd_try_from(slice)?, S64 { 0: pos(&bytes) });
            assert_eq!(U64::nd_try_from(slice)?, U64 { 0: pos(&bytes) });
        }

        Ok(())
    }

    #[test]
    fn from_iter() {
        let empty = (&[] as &[u8]).iter().copied();

        assert_eq!(empty.clone().collect::<S64>(), S64::default());
        assert_eq!(empty.clone().collect::<U64>(), U64::default());

        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();
            let iter = bytes.iter().copied();

            assert_eq!(iter.clone().collect::<S64>(), S64 { 0: pos(&bytes) });
            assert_eq!(iter.clone().collect::<U64>(), U64 { 0: pos(&bytes) });
        }
    }

    #[test]
    fn from_digits() -> Result<()> {
        let empty = &[] as &[u8];

        assert_eq!(S64::from_digits(empty, ExpImpl { exp: 7 })?, S64::default());
        assert_eq!(U64::from_digits(empty, ExpImpl { exp: 7 })?, U64::default());
        assert_eq!(S64::from_digits(empty, RadixImpl { radix: 251u8 })?, S64::default());
        assert_eq!(U64::from_digits(empty, RadixImpl { radix: 251u8 })?, U64::default());

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for radix in 2..=u8::MAX {
            for _ in 0..=u8::MAX {
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                let bytes = digits
                    .iter()
                    .rev()
                    .fold(0, |acc, &x| acc * radix as u64 + x as u64)
                    .to_le_bytes();

                assert_eq!(S64::from_digits(digits, RadixImpl { radix })?, S64 { 0: pos(&bytes) });
                assert_eq!(U64::from_digits(digits, RadixImpl { radix })?, U64 { 0: pos(&bytes) });
            }
        }

        Ok(())
    }

    #[test]
    fn from_digits_iter() -> Result<()> {
        let empty = (&[] as &[u8]).iter().copied();

        assert_eq!(S64::from_digits_iter(empty.clone(), ExpImpl { exp: 7 })?, S64::default());
        assert_eq!(U64::from_digits_iter(empty.clone(), ExpImpl { exp: 7 })?, U64::default());
        assert_eq!(
            S64::from_digits_iter(empty.clone(), RadixImpl { radix: 251u8 })?,
            S64::default()
        );
        assert_eq!(
            U64::from_digits_iter(empty.clone(), RadixImpl { radix: 251u8 })?,
            U64::default()
        );

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for radix in 2..=u8::MAX {
            for _ in 0..=u8::MAX {
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                let bytes = digits
                    .iter()
                    .rev()
                    .fold(0, |acc, &x| acc * radix as u64 + x as u64)
                    .to_le_bytes();

                assert_eq!(
                    S64::from_digits_iter(digits.iter().copied(), RadixImpl { radix })?,
                    S64 { 0: pos(&bytes) }
                );

                assert_eq!(
                    U64::from_digits_iter(digits.iter().copied(), RadixImpl { radix })?,
                    U64 { 0: pos(&bytes) }
                );
            }
        }

        Ok(())
    }

    #[test]
    fn to_digits() -> Result<()> {
        assert_eq!(S64::from(0i8).to_digits::<u8>(ExpImpl { exp: 7 })?, vec![]);
        assert_eq!(U64::from(0u8).to_digits::<u8>(ExpImpl { exp: 7 })?, vec![]);

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for exp in 1..u8::BITS as u8 {
            for _ in 0..=u8::MAX {
                let radix = 1u8 << exp;
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                assert!(
                    S64::from_digits(digits, ExpImpl { exp })?
                        .to_digits(ExpImpl { exp })?
                        .iter()
                        .chain(repeat(&0))
                        .zip(digits.iter())
                        .all(|(lhs, rhs)| lhs == rhs)
                );

                assert!(
                    U64::from_digits(digits, ExpImpl { exp })?
                        .to_digits(ExpImpl { exp })?
                        .iter()
                        .chain(repeat(&0))
                        .zip(digits.iter())
                        .all(|(lhs, rhs)| lhs == rhs)
                );
            }
        }

        Ok(())
    }

    #[test]
    fn to_digits_iter() -> Result<()> {
        assert_eq!(S64::from(0i8).to_digits_iter::<u8>(ExpImpl { exp: 7 })?.len(), 0);
        assert_eq!(U64::from(0u8).to_digits_iter::<u8>(ExpImpl { exp: 7 })?.len(), 0);

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for exp in 1..u8::BITS as u8 {
            for _ in 0..=u8::MAX {
                let radix = 1u8 << exp;
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                assert!(
                    S64::from_digits(digits, ExpImpl { exp })?
                        .to_digits_iter(ExpImpl { exp })?
                        .chain(repeat(0))
                        .zip(digits.iter())
                        .all(|(lhs, &rhs)| lhs == rhs)
                );

                assert!(
                    U64::from_digits(digits, ExpImpl { exp })?
                        .to_digits_iter(ExpImpl { exp })?
                        .chain(repeat(0))
                        .zip(digits.iter())
                        .all(|(lhs, &rhs)| lhs == rhs)
                );
            }
        }

        Ok(())
    }

    #[test]
    fn into_digits() -> Result<()> {
        assert_eq!(S64::from(0i8).into_digits(RadixImpl { radix: 251 })?, vec![]);
        assert_eq!(U64::from(0u8).into_digits(RadixImpl { radix: 251 })?, vec![]);

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for radix in 2..=u8::MAX {
            for _ in 0..=u8::MAX {
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                assert!(
                    S64::from_digits(digits, RadixImpl { radix })?
                        .into_digits(RadixImpl { radix })?
                        .iter()
                        .chain(repeat(&0))
                        .zip(digits.iter())
                        .all(|(lhs, rhs)| lhs == rhs)
                );

                assert!(
                    U64::from_digits(digits, RadixImpl { radix })?
                        .into_digits(RadixImpl { radix })?
                        .iter()
                        .chain(repeat(&0))
                        .zip(digits.iter())
                        .all(|(lhs, rhs)| lhs == rhs)
                );
            }
        }

        Ok(())
    }

    #[test]
    fn into_digits_iter() -> Result<()> {
        assert_eq!(S64::from(0i8).into_digits_iter(RadixImpl { radix: 251 })?.len(), 0);
        assert_eq!(U64::from(0u8).into_digits_iter(RadixImpl { radix: 251 })?.len(), 0);

        let mut rng = StdRng::seed_from_u64(PRIMES_48BIT[0] as u64);

        for radix in 2..=u8::MAX {
            for _ in 0..=u8::MAX {
                let digits = (0..8).map(|_| rng.random_range(..radix)).collect_with([0; 8]);

                assert!(
                    S64::from_digits(digits, RadixImpl { radix })?
                        .into_digits_iter(RadixImpl { radix })?
                        .chain(repeat(0))
                        .zip(digits.iter())
                        .all(|(lhs, &rhs)| lhs == rhs)
                );

                assert!(
                    U64::from_digits(digits, RadixImpl { radix })?
                        .into_digits_iter(RadixImpl { radix })?
                        .chain(repeat(0))
                        .zip(digits.iter())
                        .all(|(lhs, &rhs)| lhs == rhs)
                );
            }
        }

        Ok(())
    }

    #[test]
    fn from_str() -> Result<()> {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            let pval = val as i64;
            let nval = -(val as i64);

            let pos_dec = format!("{pval:#}");
            let pos_bin = format!("{pval:#b}");
            let pos_oct = format!("{pval:#o}");
            let pos_hex = format!("{pval:#x}");

            let neg_dec = format!("{nval:#}");
            let neg_bin = format!("{nval:#b}");
            let neg_oct = format!("{nval:#o}");
            let neg_hex = format!("{nval:#x}");

            let dec = format!("{val:#}");
            let bin = format!("{val:#b}");
            let oct = format!("{val:#o}");
            let hex = format!("{val:#x}");

            assert_eq!(pos_dec.parse::<S64>()?, S64 { 0: pos(&bytes) });
            assert_eq!(pos_bin.parse::<S64>()?, S64 { 0: pos(&bytes) });
            assert_eq!(pos_oct.parse::<S64>()?, S64 { 0: pos(&bytes) });
            assert_eq!(pos_hex.parse::<S64>()?, S64 { 0: pos(&bytes) });

            assert_eq!(neg_dec.parse::<S64>()?, S64 { 0: neg(&bytes) });
            assert_eq!(neg_bin.parse::<S64>()?, S64 { 0: neg(&bytes) });
            assert_eq!(neg_oct.parse::<S64>()?, S64 { 0: neg(&bytes) });
            assert_eq!(neg_hex.parse::<S64>()?, S64 { 0: neg(&bytes) });

            assert_eq!(dec.parse::<U64>()?, U64 { 0: pos(&bytes) });
            assert_eq!(bin.parse::<U64>()?, U64 { 0: pos(&bytes) });
            assert_eq!(oct.parse::<U64>()?, U64 { 0: pos(&bytes) });
            assert_eq!(hex.parse::<U64>()?, U64 { 0: pos(&bytes) });
        }

        Ok(())
    }

    #[test]
    fn to_str() {
        for val in (u64::MIN..u64::MAX).step_by(PRIMES_48BIT[0]) {
            let bytes = val.to_le_bytes();

            let pval = val as i64;
            let nval = -(val as i64);

            let pos_dec = format!("{pval:#}");
            let pos_bin = format!("{pval:#b}");
            let pos_oct = format!("{pval:#o}");
            let pos_hex = format!("{pval:#x}");

            let neg_dec = format!("{nval:#}");
            let neg_bin = format!("{nval:#b}");
            let neg_oct = format!("{nval:#o}");
            let neg_hex = format!("{nval:#x}");

            let dec = format!("{val:#}");
            let bin = format!("{val:#b}");
            let oct = format!("{val:#o}");
            let hex = format!("{val:#x}");

            assert_eq!(format!("{:#}", S64 { 0: pos(&bytes) }), pos_dec);
            assert_eq!(format!("{:#b}", S64 { 0: pos(&bytes) }), pos_bin);
            assert_eq!(format!("{:#o}", S64 { 0: pos(&bytes) }), pos_oct);
            assert_eq!(format!("{:#x}", S64 { 0: pos(&bytes) }), pos_hex);

            assert_eq!(format!("{:#}", S64 { 0: neg(&bytes) }), neg_dec);
            assert_eq!(format!("{:#b}", S64 { 0: neg(&bytes) }), neg_bin);
            assert_eq!(format!("{:#o}", S64 { 0: neg(&bytes) }), neg_oct);
            assert_eq!(format!("{:#x}", S64 { 0: neg(&bytes) }), neg_hex);

            assert_eq!(format!("{:#}", U64 { 0: pos(&bytes) }), dec);
            assert_eq!(format!("{:#b}", U64 { 0: pos(&bytes) }), bin);
            assert_eq!(format!("{:#o}", U64 { 0: pos(&bytes) }), oct);
            assert_eq!(format!("{:#x}", U64 { 0: pos(&bytes) }), hex);
        }
    }

    #[test]
    fn signed_ops() {
        assert_ops!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|a: S64, b: S64| { a + b })(|a: i64, b: i64| { S64::from(a.wrapping_add(b)) }),
                (|a: S64, b: S64| { a - b })(|a: i64, b: i64| { S64::from(a.wrapping_sub(b)) }),
                (|a: S64, b: S64| { a * b })(|a: i64, b: i64| { S64::from(a.wrapping_mul(b)) }),
                (|a: S64, b: S64| { a / b })(|a: i64, b: i64| { S64::from(a / b) }),
                (|a: S64, b: S64| { a % b })(|a: i64, b: i64| { S64::from(a % b) }),
                (|a: S64, b: S64| { a | b })(|a: i64, b: i64| { S64::from(a | b) }),
                (|a: S64, b: S64| { a & b })(|a: i64, b: i64| { S64::from(a & b) }),
                (|a: S64, b: S64| { a ^ b })(|a: i64, b: i64| { S64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    fn unsigned_ops() {
        assert_ops!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            (1..u64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|a: U64, b: U64| { a + b })(|a: u64, b: u64| { U64::from(a.wrapping_add(b)) }),
                (|a: U64, b: U64| { a - b })(|a: u64, b: u64| { U64::from(a.wrapping_sub(b)) }),
                (|a: U64, b: U64| { a * b })(|a: u64, b: u64| { U64::from(a.wrapping_mul(b)) }),
                (|a: U64, b: U64| { a / b })(|a: u64, b: u64| { U64::from(a / b) }),
                (|a: U64, b: U64| { a % b })(|a: u64, b: u64| { U64::from(a % b) }),
                (|a: U64, b: U64| { a | b })(|a: u64, b: u64| { U64::from(a | b) }),
                (|a: U64, b: U64| { a & b })(|a: u64, b: u64| { U64::from(a & b) }),
                (|a: U64, b: U64| { a ^ b })(|a: u64, b: u64| { U64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    fn signed_ops_primitive_native() {
        assert_ops_primitive!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i8::MIN..i8::MAX).filter(|&x| x != 0),
            [
                (|a: S64, b: i8| { a + b })(|a: i64, b: i8| { S64::from(a.wrapping_add(b as i64)) }),
                (|a: S64, b: i8| { a - b })(|a: i64, b: i8| { S64::from(a.wrapping_sub(b as i64)) }),
                (|a: S64, b: i8| { a * b })(|a: i64, b: i8| { S64::from(a.wrapping_mul(b as i64)) }),
                (|a: S64, b: i8| { a / b })(|a: i64, b: i8| { S64::from(a / b as i64) }),
                (|a: S64, b: i8| { a % b })(|a: i64, b: i8| { S64::from(a % b as i64) }),
                (|a: S64, b: i8| { a | b })(|a: i64, b: i8| { S64::from(a | b as i64) }),
                (|a: S64, b: i8| { a & b })(|a: i64, b: i8| { S64::from(a & b as i64) }),
                (|a: S64, b: i8| { a ^ b })(|a: i64, b: i8| { S64::from(a ^ b as i64) }),
            ]
        );
    }

    #[test]
    fn unsigned_ops_primitive_native() {
        assert_ops_primitive!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            1..u8::MAX,
            [
                (|a: U64, b: u8| { a + b })(|a: u64, b: u8| { U64::from(a.wrapping_add(b as u64)) }),
                (|a: U64, b: u8| { a - b })(|a: u64, b: u8| { U64::from(a.wrapping_sub(b as u64)) }),
                (|a: U64, b: u8| { a * b })(|a: u64, b: u8| { U64::from(a.wrapping_mul(b as u64)) }),
                (|a: U64, b: u8| { a / b })(|a: u64, b: u8| { U64::from(a / b as u64) }),
                (|a: U64, b: u8| { a % b })(|a: u64, b: u8| { U64::from(a % b as u64) }),
                (|a: U64, b: u8| { a | b })(|a: u64, b: u8| { U64::from(a | b as u64) }),
                (|a: U64, b: u8| { a & b })(|a: u64, b: u8| { U64::from(a & b as u64) }),
                (|a: U64, b: u8| { a ^ b })(|a: u64, b: u8| { U64::from(a ^ b as u64) }),
            ]
        );
    }

    #[test]
    fn signed_ops_primitive() {
        assert_ops_primitive!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|a: S64, b: i64| { a + b })(|a: i64, b: i64| { S64::from(a.wrapping_add(b)) }),
                (|a: S64, b: i64| { a - b })(|a: i64, b: i64| { S64::from(a.wrapping_sub(b)) }),
                (|a: S64, b: i64| { a * b })(|a: i64, b: i64| { S64::from(a.wrapping_mul(b)) }),
                (|a: S64, b: i64| { a / b })(|a: i64, b: i64| { S64::from(a / b) }),
                (|a: S64, b: i64| { a % b })(|a: i64, b: i64| { S64::from(a % b) }),
                (|a: S64, b: i64| { a | b })(|a: i64, b: i64| { S64::from(a | b) }),
                (|a: S64, b: i64| { a & b })(|a: i64, b: i64| { S64::from(a & b) }),
                (|a: S64, b: i64| { a ^ b })(|a: i64, b: i64| { S64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    fn unsigned_ops_primitive() {
        assert_ops_primitive!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            (1..u64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|a: U64, b: u64| { a + b })(|a: u64, b: u64| { U64::from(a.wrapping_add(b)) }),
                (|a: U64, b: u64| { a - b })(|a: u64, b: u64| { U64::from(a.wrapping_sub(b)) }),
                (|a: U64, b: u64| { a * b })(|a: u64, b: u64| { U64::from(a.wrapping_mul(b)) }),
                (|a: U64, b: u64| { a / b })(|a: u64, b: u64| { U64::from(a / b) }),
                (|a: U64, b: u64| { a % b })(|a: u64, b: u64| { U64::from(a % b) }),
                (|a: U64, b: u64| { a | b })(|a: u64, b: u64| { U64::from(a | b) }),
                (|a: U64, b: u64| { a & b })(|a: u64, b: u64| { U64::from(a & b) }),
                (|a: U64, b: u64| { a ^ b })(|a: u64, b: u64| { U64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn signed_ops_mut() {
        assert_ops!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|mut a: S64, b: S64| { a += b; a })(|a: i64, b: i64| { S64::from(a.wrapping_add(b)) }),
                (|mut a: S64, b: S64| { a -= b; a })(|a: i64, b: i64| { S64::from(a.wrapping_sub(b)) }),
                (|mut a: S64, b: S64| { a *= b; a })(|a: i64, b: i64| { S64::from(a.wrapping_mul(b)) }),
                (|mut a: S64, b: S64| { a /= b; a })(|a: i64, b: i64| { S64::from(a / b) }),
                (|mut a: S64, b: S64| { a %= b; a })(|a: i64, b: i64| { S64::from(a % b) }),
                (|mut a: S64, b: S64| { a |= b; a })(|a: i64, b: i64| { S64::from(a | b) }),
                (|mut a: S64, b: S64| { a &= b; a })(|a: i64, b: i64| { S64::from(a & b) }),
                (|mut a: S64, b: S64| { a ^= b; a })(|a: i64, b: i64| { S64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn unsigned_ops_mut() {
        assert_ops!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            (1..u64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|mut a: U64, b: U64| { a += b; a })(|a: u64, b: u64| { U64::from(a.wrapping_add(b)) }),
                (|mut a: U64, b: U64| { a -= b; a })(|a: u64, b: u64| { U64::from(a.wrapping_sub(b)) }),
                (|mut a: U64, b: U64| { a *= b; a })(|a: u64, b: u64| { U64::from(a.wrapping_mul(b)) }),
                (|mut a: U64, b: U64| { a /= b; a })(|a: u64, b: u64| { U64::from(a / b) }),
                (|mut a: U64, b: U64| { a %= b; a })(|a: u64, b: u64| { U64::from(a % b) }),
                (|mut a: U64, b: U64| { a |= b; a })(|a: u64, b: u64| { U64::from(a | b) }),
                (|mut a: U64, b: U64| { a &= b; a })(|a: u64, b: u64| { U64::from(a & b) }),
                (|mut a: U64, b: U64| { a ^= b; a })(|a: u64, b: u64| { U64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn signed_ops_primitive_native_mut() {
        assert_ops_primitive!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i8::MIN..i8::MAX).filter(|&x| x != 0),
            [
                (|mut a: S64, b: i8| { a += b; a })(|a: i64, b: i8| { S64::from(a.wrapping_add(b as i64)) }),
                (|mut a: S64, b: i8| { a -= b; a })(|a: i64, b: i8| { S64::from(a.wrapping_sub(b as i64)) }),
                (|mut a: S64, b: i8| { a *= b; a })(|a: i64, b: i8| { S64::from(a.wrapping_mul(b as i64)) }),
                (|mut a: S64, b: i8| { a /= b; a })(|a: i64, b: i8| { S64::from(a / b as i64) }),
                (|mut a: S64, b: i8| { a %= b; a })(|a: i64, b: i8| { S64::from(a % b as i64) }),
                (|mut a: S64, b: i8| { a |= b; a })(|a: i64, b: i8| { S64::from(a | b as i64) }),
                (|mut a: S64, b: i8| { a &= b; a })(|a: i64, b: i8| { S64::from(a & b as i64) }),
                (|mut a: S64, b: i8| { a ^= b; a })(|a: i64, b: i8| { S64::from(a ^ b as i64) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn unsigned_ops_primitive_native_mut() {
        assert_ops_primitive!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            1..u8::MAX,
            [
                (|mut a: U64, b: u8| { a += b; a })(|a: u64, b: u8| { U64::from(a.wrapping_add(b as u64)) }),
                (|mut a: U64, b: u8| { a -= b; a })(|a: u64, b: u8| { U64::from(a.wrapping_sub(b as u64)) }),
                (|mut a: U64, b: u8| { a *= b; a })(|a: u64, b: u8| { U64::from(a.wrapping_mul(b as u64)) }),
                (|mut a: U64, b: u8| { a /= b; a })(|a: u64, b: u8| { U64::from(a / b as u64) }),
                (|mut a: U64, b: u8| { a %= b; a })(|a: u64, b: u8| { U64::from(a % b as u64) }),
                (|mut a: U64, b: u8| { a |= b; a })(|a: u64, b: u8| { U64::from(a | b as u64) }),
                (|mut a: U64, b: u8| { a &= b; a })(|a: u64, b: u8| { U64::from(a & b as u64) }),
                (|mut a: U64, b: u8| { a ^= b; a })(|a: u64, b: u8| { U64::from(a ^ b as u64) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn signed_ops_primitive_mut() {
        assert_ops_primitive!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[0]),
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|mut a: S64, b: i64| { a += b; a })(|a: i64, b: i64| { S64::from(a.wrapping_add(b)) }),
                (|mut a: S64, b: i64| { a -= b; a })(|a: i64, b: i64| { S64::from(a.wrapping_sub(b)) }),
                (|mut a: S64, b: i64| { a *= b; a })(|a: i64, b: i64| { S64::from(a.wrapping_mul(b)) }),
                (|mut a: S64, b: i64| { a /= b; a })(|a: i64, b: i64| { S64::from(a / b) }),
                (|mut a: S64, b: i64| { a %= b; a })(|a: i64, b: i64| { S64::from(a % b) }),
                (|mut a: S64, b: i64| { a |= b; a })(|a: i64, b: i64| { S64::from(a | b) }),
                (|mut a: S64, b: i64| { a &= b; a })(|a: i64, b: i64| { S64::from(a & b) }),
                (|mut a: S64, b: i64| { a ^= b; a })(|a: i64, b: i64| { S64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn unsigned_ops_primitive_mut() {
        assert_ops_primitive!(
            U64,
            (1..u64::MAX).step_by(PRIMES_56BIT[0]),
            (1..u64::MAX).step_by(PRIMES_56BIT[1]),
            [
                (|mut a: U64, b: u64| { a += b; a })(|a: u64, b: u64| { U64::from(a.wrapping_add(b)) }),
                (|mut a: U64, b: u64| { a -= b; a })(|a: u64, b: u64| { U64::from(a.wrapping_sub(b)) }),
                (|mut a: U64, b: u64| { a *= b; a })(|a: u64, b: u64| { U64::from(a.wrapping_mul(b)) }),
                (|mut a: U64, b: u64| { a /= b; a })(|a: u64, b: u64| { U64::from(a / b) }),
                (|mut a: U64, b: u64| { a %= b; a })(|a: u64, b: u64| { U64::from(a % b) }),
                (|mut a: U64, b: u64| { a |= b; a })(|a: u64, b: u64| { U64::from(a | b) }),
                (|mut a: U64, b: u64| { a &= b; a })(|a: u64, b: u64| { U64::from(a & b) }),
                (|mut a: U64, b: u64| { a ^= b; a })(|a: u64, b: u64| { U64::from(a ^ b) }),
            ]
        );
    }

    #[test]
    fn signed_ops_shift() {
        assert_ops_shift!(
            S64,
            (i64::MIN + 1..i64::MAX).step_by(PRIMES_48BIT[0]),
            0..64,
            [
                (|val: S64, shift: usize| { val << shift })(|val: i64, shift: usize| { S64::from(val << shift) }),
                (|val: S64, shift: usize| { val >> shift })(|val: i64, shift: usize| { S64::from(val >> shift) }),
            ]
        );
    }

    #[test]
    fn unsigned_ops_shift() {
        assert_ops_shift!(
            U64,
            (1..u64::MAX).step_by(PRIMES_48BIT[0]),
            0..64,
            [
                (|val: U64, shift: usize| { val << shift })(|val: u64, shift: usize| { U64::from(val << shift) }),
                (|val: U64, shift: usize| { val >> shift })(|val: u64, shift: usize| { U64::from(val >> shift) }),
            ]
        );
    }

    #[test]
    #[rustfmt::skip]
    fn signed_ops_shift_mut() {
        assert_ops_shift!(S64, (i64::MIN + 1..i64::MAX).step_by(PRIMES_48BIT[0]), 0..64, [
            (|mut val: S64, shift: usize| { val <<= shift; val })(|val: i64, shift: usize| { S64::from(val << shift) }),
            (|mut val: S64, shift: usize| { val >>= shift; val })(|val: i64, shift: usize| { S64::from(val >> shift) }),
        ]);
    }

    #[test]
    #[rustfmt::skip]
    fn unsigned_ops_shift_mut() {
        assert_ops_shift!(U64, (1..u64::MAX).step_by(PRIMES_48BIT[0]), 0..64, [
            (|mut val: U64, shift: usize| { val <<= shift; val })(|val: u64, shift: usize| { U64::from(val << shift) }),
            (|mut val: U64, shift: usize| { val >>= shift; val })(|val: u64, shift: usize| { U64::from(val >> shift) }),
        ]);
    }
}
