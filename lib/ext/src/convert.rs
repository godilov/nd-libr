#![doc = include_str!("../docs/convert.md")]

use std::str::FromStr;

/// `Nd-kind` extension for [`std::convert::From`].
///
/// Allows to implement [`NdFrom`] and [`NdTryFrom`] at the same time.
///
/// Auto-implemented for all `V: From<U>`.
///
/// For more info, see [module-level](crate::convert) and [crate-level](crate) documentation.
pub trait NdFrom<T>: Sized {
    /// Convert from value in non-failable way.
    fn nd_from(value: T) -> Self;
}

/// `Nd-kind` extension for [`std::convert::TryFrom`].
///
/// Allows to implement [`NdFrom`] and [`NdTryFrom`] at the same time.
///
/// Auto-implemented for all `V: TryFrom<U>`.
///
/// For more info, see [module-level](crate::convert) and [crate-level](crate) documentation.
pub trait NdTryFrom<T>: Sized {
    /// Conversion error type.
    type Error;

    /// Convert from value in failable way.
    fn nd_try_from(value: T) -> Result<Self, Self::Error>;
}

/// `Nd-kind` extension for [`std::str::FromStr`].
///
/// Allows to implement [`NdFromStr`] parsing with additional context or interpretation.
///
/// Auto-implemented for all `V: FromStr` with `Ctx = ()`.
///
/// For more info, see [module-level](crate::convert) and [crate-level](crate) documentation.
pub trait NdFromStr<Ctx>: Sized {
    /// Parsing error type.
    type Err;

    /// Parse from string and context.
    fn nd_from_str(s: &str, ctx: Ctx) -> Result<Self, Self::Err>;
}

impl<U, V: From<U>> NdFrom<U> for V {
    #[inline]
    fn nd_from(value: U) -> Self {
        V::from(value)
    }
}

impl<U, V: TryFrom<U>> NdTryFrom<U> for V {
    type Error = V::Error;

    #[inline]
    fn nd_try_from(value: U) -> Result<Self, Self::Error> {
        V::try_from(value)
    }
}

impl<T: FromStr> NdFromStr<()> for T {
    type Err = T::Err;

    #[inline]
    fn nd_from_str(s: &str, _: ()) -> Result<Self, Self::Err> {
        T::from_str(s)
    }
}
