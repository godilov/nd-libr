#![doc = include_str!("../README.md")]

use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::TokenStream;
use quote::{ToTokens, quote};
use syn::{
    Error, Expr, Ident, LitInt, Result, Token, Type, bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token::{Bracket, Paren},
};

mod kw {
    syn::custom_keyword!(eq);
    syn::custom_keyword!(ne);
}

/// Creates structured assertions.
///
/// # Syntax
///
/// ```text
/// ndassert::check! { <kind>
///     (<arg_expr>,*)
///     [<check_expr>,*]
/// }
///
/// <kind> := "" | "@eq" | "@ne"
/// <arg_expr> := <ident> in <expr> | <ident> as <expr>
/// <check_expr> := <expr>
/// ```
///
/// **Kinds**:
///
/// - None - checks as `assert!()`, `<check_expr>` **must** return bool.
/// - `@eq` - checks as `assert_eq!()`, `<check_expr>` **must** return tuple of 2 elems.
/// - `@ne` - checks as `assert_ne!()`, `<check_expr>` **must** return tuple of 2 elems.
///
/// **Args**:
///
/// - `<ident> in <expr>` - creates `for <ident> in <expr> { ... }`.
/// - `<ident> as <expr>` - creates `let <ident> = <expr>; ...`.
///
/// # Examples
///
/// ```rust
/// // Checks for all combinations of lhs and rhs
/// ndassert::check! { (
///     lhs in (i8::MIN / 4..i8::MAX / 4),
///     rhs in (i8::MIN / 4..i8::MAX / 4),
///     sum as lhs + rhs,
/// ) [
///     sum == lhs + rhs, // Direct
///     sum == rhs + lhs, // Inverse
/// ] }
/// ```
///
/// ```rust
/// // Checks for all combinations of lhs and rhs
/// ndassert::check! { @eq (
///     lhs in (i8::MIN / 4..i8::MAX / 4),
///     rhs in (i8::MIN / 4..i8::MAX / 4),
///     sum as lhs + rhs,
/// ) [
///     (sum, lhs + rhs), // Direct
///     (sum, rhs + lhs), // Inverse
/// ] }
/// ```
///
/// ```rust
/// // Checks for all combinations of lhs and rhs
/// ndassert::check! { @ne (
///     lhs in (i8::MIN / 4..i8::MAX / 4),
///     rhs in (i8::MIN / 4..i8::MAX / 4),
///     sum as lhs + rhs,
/// ) [
///     (sum, lhs + rhs + 1), // Direct
///     (sum, rhs + lhs + 1), // Inverse
/// ] }
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro]
pub fn check(stream: TokenStreamStd) -> TokenStreamStd {
    let assert = parse_macro_input!(stream as AssertCheck);

    quote! {
        #assert
    }
    .into()
}

/// Creates prime number.
///
/// # Syntax
///
/// ```text
/// ndassert::prime!(<len>, <class>);
///
/// <len> := <num>
/// <class> := <num>?
/// ```
///
/// - `<len>` **must** be `4 * N`, where `N in [1; 15]`.
/// - `<class>` **must** be non-negative.
///
/// `<len>` is approximate binary length of prime numbers.
/// `<class>` is cyclic index in predetermined prime numbers sequence.
///
/// # Examples
///
/// ```rust
/// assert_eq!(ndassert::prime!(4).ilog2(), 3);
/// assert_eq!(ndassert::prime!(8).ilog2(), 7);
/// assert_eq!(ndassert::prime!(12).ilog2(), 11);
/// assert_eq!(ndassert::prime!(16).ilog2(), 15);
///
/// assert_ne!(ndassert::prime!(60, 0), ndassert::prime!(60, 1));
/// assert_ne!(ndassert::prime!(60, 1), ndassert::prime!(60, 2));
/// assert_ne!(ndassert::prime!(60, 2), ndassert::prime!(60, 3));
/// assert_ne!(ndassert::prime!(60, 3), ndassert::prime!(60, 4));
///
/// assert_eq!(ndassert::prime!(60, 0), ndassert::prime!(60, 4));
/// assert_eq!(ndassert::prime!(60, 1), ndassert::prime!(60, 5));
/// assert_eq!(ndassert::prime!(60, 2), ndassert::prime!(60, 6));
/// assert_eq!(ndassert::prime!(60, 3), ndassert::prime!(60, 7));
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro]
pub fn prime(stream: TokenStreamStd) -> TokenStreamStd {
    let prime = parse_macro_input!(stream as AssertPrime);

    quote! {
        #prime
    }
    .into()
}

/// Creates random number generator.
///
/// # Syntax
///
/// ```text
/// ndassert::rand!(<type>, <len>, <class>);
///
/// <len> := <num>
/// <class> := <num>?
/// ```
///
/// - `<type>` **must** contain `<type>::seed_from_u64()`.
/// - `<len>` **must** be as in [`prime`].
/// - `<class>` **must** be as in [`prime`].
///
/// `<len>` and `<class>` determine prime number to be used as seed in generator.
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro]
pub fn rand(stream: TokenStreamStd) -> TokenStreamStd {
    let rand = parse_macro_input!(stream as AssertRand);

    quote! {
        #rand
    }
    .into()
}

/// Creates range.
///
/// Allows producing single or multiple uniform ranges over the type `(MIN..MAX)`
/// with relative variety of combinations for [`ndassert::check!`](check) args expressions.
///
/// # Syntax
///
/// ```text
/// ndassert::range!(<type>, <len>, <class>);
///
/// <len> := <num>
/// <class> := <num>?
/// ```
///
/// - `<type>` **must** be standard Rust primitive type.
/// - `<len>` **must** be as in [`prime`].
/// - `<class>` **must** be as in [`prime`].
///
/// `<len>` and `<class>` determine prime number to be used as step in range.
///
/// # Examples
///
/// ```rust
/// // Lhs takes approximately 16 different uniformly distributed values in (i64::MIN..i64::MAX)
/// // Rhs takes approximately 16 different uniformly distributed values in (i64::MIN..i64::MAX)
/// ndassert::check! { @eq (
///     lhs in ndassert::range!(i64, 60, 0),
///     rhs in ndassert::range!(i64, 60, 1),
///     sum as lhs.wrapping_add(rhs),
/// ) [
///     (sum, lhs.wrapping_add(rhs)), // Direct
///     (sum, rhs.wrapping_add(lhs)), // Inverse
/// ] }
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro]
pub fn range(stream: TokenStreamStd) -> TokenStreamStd {
    let range = parse_macro_input!(stream as AssertRange);

    quote! {
        #range
    }
    .into()
}

/// Creates catch.
///
/// Allows catching panics for [`ndassert::check!`](check) check expressions.
///
/// # Examples
///
/// ```rust
/// // Add operations panics on first iteration with overflow, but catched with macro
/// ndassert::check! { @eq (
///     lhs in ndassert::range!(i64, 60, 0),
///     rhs in ndassert::range!(i64, 60, 1),
///     sum as ndassert::catch!(lhs + rhs),
/// ) [
///     ndassert::catch!(lhs + rhs, rhs + lhs),
///
///     (sum, ndassert::catch!(lhs + rhs)), // Direct
///     (sum, ndassert::catch!(rhs + lhs)), // Inverse
/// ] }
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro]
pub fn catch(stream: TokenStreamStd) -> TokenStreamStd {
    let catch = parse_macro_input!(stream as AssertCatch);

    quote! {
        #catch
    }
    .into()
}

#[rustfmt::skip]
const PRIMES: [[u64; 4]; 15] = [
    [            13,             11,              7,              5],
    [           251,            241,            239,            233],
    [         4_093,          4_091,          4_079,          4_073],
    [        65_521,         65_519,         65_497,         65_479],
    [     1_048_573,      1_048_571,      1_048_559,      1_048_549],
    [    16_777_213,     16_777_199,     16_777_153,     16_777_141],
    [   268_435_273,    268_435_091,    268_434_961,    268_434_941],
    [ 4_294_961_623,  4_294_960_883,  4_294_957_207,  4_294_956_461],
    [68_719_440_701, 68_719_423_037, 68_719_419_037, 68_719_404_931],
    [
        1_099_510_850_981,
        1_099_509_640_783,
        1_099_508_899_219,
        1_099_508_677_453,
    ],
    [
        17_592_181_425_547,
        17_592_180_344_983,
        17_592_168_578_183,
        17_592_166_738_889,
    ],
    [
        281_474_919_759_889,
        281_474_854_044_589,
        281_474_838_022_123,
        281_474_404_239_029,
    ],
    [
        4_503_599_539_849_933,
        4_503_597_730_049_837,
        4_503_596_355_552_149,
        4_503_596_318_916_671,
    ],
    [
        72_057_588_543_547_877,
        72_057_567_830_793_901,
        72_057_544_403_510_693,
        72_057_531_892_930_823,
    ],
    [
        1_152_920_950_656_862_133,
        1_152_920_243_723_361_439,
        1_152_919_710_129_785_861,
        1_152_918_570_102_243_433,
    ],
];

enum AssertKind {
    Eq,
    EqNot,
    Default,
}

#[allow(unused)]
struct AssertCheck {
    kind: AssertKind,
    args_paren: Paren,
    args: Punctuated<AssertArg, Token![,]>,
    exprs_bracket: Bracket,
    exprs: Punctuated<Expr, Token![,]>,
}

#[allow(unused)]
enum AssertArg {
    Single(Ident, Token![as], Expr),
    Multiple(Ident, Token![in], Expr),
}

struct AssertPrime {
    len: usize,
    class: usize,
}

struct AssertRand {
    ty: Type,
    prime: AssertPrime,
}

struct AssertRange {
    ty: Type,
    prime: AssertPrime,
}

struct AssertCatch {
    elems: Punctuated<Expr, Token![,]>,
}

impl Parse for AssertKind {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(Token![@]) {
            return Ok(Self::Default);
        }

        input.parse::<Token![@]>()?;

        let lookahead = input.lookahead1();

        if lookahead.peek(kw::eq) {
            input.parse::<kw::eq>()?;

            Ok(Self::Eq)
        } else if lookahead.peek(kw::ne) {
            input.parse::<kw::ne>()?;

            Ok(Self::EqNot)
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for AssertCheck {
    fn parse(input: ParseStream) -> Result<Self> {
        let args;
        let exprs;

        Ok(Self {
            kind: input.parse()?,
            args_paren: parenthesized!(args in input),
            args: args.parse_terminated(AssertArg::parse, Token![,])?,
            exprs_bracket: bracketed!(exprs in input),
            exprs: exprs.parse_terminated(Expr::parse, Token![,])?,
        })
    }
}

impl Parse for AssertArg {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident = input.parse()?;

        let lookahead = input.lookahead1();

        if lookahead.peek(Token![as]) {
            let token = input.parse()?;
            let expr = input.parse()?;

            Ok(Self::Single(ident, token, expr))
        } else if lookahead.peek(Token![in]) {
            let token = input.parse()?;
            let expr = input.parse()?;

            Ok(Self::Multiple(ident, token, expr))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for AssertPrime {
    fn parse(input: ParseStream) -> Result<Self> {
        let len = input.parse::<LitInt>()?;

        let class = if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;

            input.parse::<LitInt>()?.base10_parse::<usize>()?
        } else {
            0
        };

        let len = match len.base10_parse::<usize>()? {
            val if val % 4 == 0 && (4..=60).contains(&val) => val / 4 - 1,
            _ => {
                return Err(Error::new_spanned(
                    len,
                    "Failed to parse assert range, expected len to be 4 * N, where N in [1; 15]",
                ));
            },
        };

        Ok(Self { len, class })
    }
}

impl Parse for AssertRand {
    fn parse(input: ParseStream) -> Result<Self> {
        let ty = input.parse()?;
        let _ = input.parse::<Token![,]>()?;
        let prime = input.parse()?;

        Ok(Self { ty, prime })
    }
}

impl Parse for AssertRange {
    fn parse(input: ParseStream) -> Result<Self> {
        let ty = input.parse()?;
        let _ = input.parse::<Token![,]>()?;
        let prime = input.parse()?;

        Ok(Self { ty, prime })
    }
}

impl Parse for AssertCatch {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            elems: input.parse_terminated(Expr::parse, Token![,])?,
        })
    }
}

impl ToTokens for AssertCheck {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let args = self.args.iter().fold(quote! {}, |acc, arg| match arg {
            AssertArg::Single(ident, _, _) => quote! { #acc #ident, },
            AssertArg::Multiple(ident, _, _) => quote! { #acc #ident, },
        });

        let args_msg = self
            .args
            .iter()
            .map(|arg| match arg {
                AssertArg::Single(ident, _, _) => format!("{}: {{:?}}\n", ident),
                AssertArg::Multiple(ident, _, _) => format!("{}: {{:?}}\n", ident),
            })
            .fold(quote! {}, |acc, msg| quote! { #acc #msg, });

        let exprs_call = self.exprs.iter().fold(quote! {}, |acc, expr| {
            let assert = match self.kind {
                AssertKind::Eq => quote! {{
                    let res = (#expr);

                    assert_eq!(res.0, res.1, concat!("Expression: {}\n", #args_msg), stringify!(#expr), #args);
                }},
                AssertKind::EqNot => quote! {{
                    let res = (#expr);

                    assert_ne!(res.0, res.1, concat!("Expression: {}\n", #args_msg), stringify!(#expr), #args);
                }},
                AssertKind::Default => quote! {
                    assert!((#expr), concat!("Expression: {}\n", #args_msg), stringify!(#expr), #args);
                },
            };

            quote! {
                #acc
                #assert
            }
        });

        let quote = self.args.iter().rev().fold(exprs_call, |acc, arg| match arg {
            AssertArg::Single(ident, _, expr) => quote! {
                let #ident = (#expr);

                #acc
            },
            AssertArg::Multiple(ident, _, expr) => quote! {
                for #ident in #expr {
                    #acc
                }
            },
        });

        tokens.extend(quote);
    }
}

impl ToTokens for AssertPrime {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let len = self.len;
        let class = self.class;
        let primes = PRIMES[len];
        let prime = primes[class % primes.len()];

        tokens.extend(quote! { #prime });
    }
}

impl ToTokens for AssertRand {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ty = &self.ty;
        let prime = &self.prime;

        tokens.extend(quote! { <#ty>::seed_from_u64(#prime) });
    }
}

impl ToTokens for AssertRange {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ty = &self.ty;
        let prime = &self.prime;

        tokens.extend(quote! { (#ty::MIN..=#ty::MAX).step_by(#prime as usize) });
    }
}

impl ToTokens for AssertCatch {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let elems = self.elems.iter();

        tokens.extend(quote! { (#(std::panic::catch_unwind(|| #elems).ok()),*) })
    }
}
