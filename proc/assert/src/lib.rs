use std::collections::HashMap;

use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{
    Error, Expr, LitInt, Result, Token, Type, bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token::{Bracket, Paren},
};

mod kw {
    syn::custom_keyword!(eq);
    syn::custom_keyword!(ne);

    syn::custom_keyword!(range);
    syn::custom_keyword!(step);
    syn::custom_keyword!(bits);
}

#[proc_macro]
pub fn check(stream: TokenStreamStd) -> TokenStreamStd {
    let assert = parse_macro_input!(stream as Assert<AssertKindCheck>);

    quote! {
        #assert
    }
    .into()
}

#[proc_macro]
pub fn compare(stream: TokenStreamStd) -> TokenStreamStd {
    let assert = parse_macro_input!(stream as Assert<AssertKindCompare>);

    quote! {
        #assert
    }
    .into()
}

#[allow(unused)]
struct Assert<Kind: AssertKind> {
    kind: Kind,
    args_paren: Paren,
    args: Punctuated<AssertArg, Token![,]>,
    exprs_bracket: Bracket,
    exprs: Punctuated<Expr, Token![,]>,
}

enum AssertKindCheck {
    Default,
}

enum AssertKindCompare {
    Eq,
    EqNot,
}

enum AssertArg {
    Expr(Expr),
    Range(AssertRange),
}

#[allow(unused)]
struct AssertRange {
    ty: Type,
    step: kw::step,
    len: LitInt,
    bits: kw::bits,
    idx: usize,
}

trait AssertKind: Parse {
    fn assert(&self, expr: &Expr, args: &TokenStream) -> TokenStream;
}

impl AssertKind for AssertKindCheck {
    fn assert(&self, expr: &Expr, args: &TokenStream) -> TokenStream {
        quote! { assert!((#expr)(#args)); }
    }
}

impl AssertKind for AssertKindCompare {
    fn assert(&self, expr: &Expr, args: &TokenStream) -> TokenStream {
        match self {
            AssertKindCompare::Eq => quote! {{ let val = (#expr)(#args); assert_eq!(val.0, val.1); }},
            AssertKindCompare::EqNot => quote! {{ let val = (#expr)(#args); assert_ne!(val.0, val.1); }},
        }
    }
}

impl<Kind: AssertKind> Parse for Assert<Kind> {
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

impl Parse for AssertKindCheck {
    fn parse(_: ParseStream) -> Result<Self> {
        Ok(Self::Default)
    }
}

impl Parse for AssertKindCompare {
    fn parse(input: ParseStream) -> Result<Self> {
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

impl Parse for AssertArg {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![@]) {
            input.parse::<Token![@]>()?;
            input.parse::<kw::range>()?;

            let content;

            let _ = parenthesized!(content in input);
            let ty = content.parse()?;
            let step = content.parse()?;
            let len = content.parse::<LitInt>()?;
            let bits = content.parse()?;

            let idx = match len.base10_parse::<usize>()? {
                val if val % 4 == 0 && (4..=60).contains(&val) => val / 4 - 1,
                _ => {
                    return Err(Error::new(
                        len.span(),
                        "Failed to parse assert argument, expected len to be 4 * N, where N in [1; 15]",
                    ));
                },
            };

            return Ok(Self::Range(AssertRange { ty, step, len, bits, idx }));
        }

        input.parse::<Expr>().map(Self::Expr)
    }
}

impl<Kind: AssertKind> ToTokens for Assert<Kind> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[rustfmt::skip]
        const PRIMES: [[usize; 4]; 15] = [
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

        let args = &self.args;
        let exprs = &self.exprs;

        let args_call = (0..args.len())
            .map(|idx| format_ident!("arg{}", idx))
            .fold(quote! {}, |acc, arg| quote! { #acc #arg, });

        let exprs_call = exprs.iter().fold(quote! {}, |acc, expr| {
            let assert = self.kind.assert(expr, &args_call);

            quote! { #acc #assert }
        });

        let mut counter = HashMap::<(&Type, usize), usize>::new();

        let quote = args
            .iter()
            .enumerate()
            .rev()
            .map(|(idx, arg)| (format_ident!("arg{}", idx), arg))
            .fold(exprs_call, |acc, (ident, arg)| match arg {
                AssertArg::Expr(val) => quote! {
                    for #ident in #val {
                        #acc
                    }
                },
                AssertArg::Range(val) => {
                    let ty = &val.ty;

                    let idx = *counter.entry((ty, val.idx)).and_modify(|idx| *idx += 1).or_default();

                    let primes = PRIMES[val.idx];
                    let prime = primes[idx % primes.len()];

                    quote! {
                        for #ident in (#ty::MIN..#ty::MAX).step_by(#prime) {
                            #acc
                        }
                    }
                },
            });

        tokens.extend(quote);
    }
}
