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
}

#[proc_macro]
pub fn check(stream: TokenStreamStd) -> TokenStreamStd {
    let assert = parse_macro_input!(stream as AssertCheck);

    quote! {
        #assert
    }
    .into()
}

#[proc_macro]
pub fn range(stream: TokenStreamStd) -> TokenStreamStd {
    let range = parse_macro_input!(stream as AssertRange);

    quote! {
        #range
    }
    .into()
}

#[allow(unused)]
struct AssertCheck {
    kind: AssertKind,
    args_paren: Paren,
    args: Punctuated<Expr, Token![,]>,
    exprs_bracket: Bracket,
    exprs: Punctuated<Expr, Token![,]>,
}

enum AssertKind {
    Eq,
    EqNot,
    Default,
}

#[allow(unused)]
struct AssertRange {
    ty: Type,
    len: usize,
    class: usize,
}

impl Parse for AssertCheck {
    fn parse(input: ParseStream) -> Result<Self> {
        let args;
        let exprs;

        Ok(Self {
            kind: input.parse()?,
            args_paren: parenthesized!(args in input),
            args: args.parse_terminated(Expr::parse, Token![,])?,
            exprs_bracket: bracketed!(exprs in input),
            exprs: exprs.parse_terminated(Expr::parse, Token![,])?,
        })
    }
}

impl Parse for AssertKind {
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
            Ok(Self::Default)
        }
    }
}

impl Parse for AssertRange {
    fn parse(input: ParseStream) -> Result<Self> {
        let ty = input.parse()?;
        let _ = input.parse::<Token![,]>()?;
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
                return Err(Error::new(
                    len.span(),
                    "Failed to parse assert range, expected len to be 4 * N, where N in [1; 15]",
                ));
            },
        };

        Ok(Self { ty, len, class })
    }
}

impl ToTokens for AssertCheck {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let args_call = (0..self.args.len())
            .map(|idx| format_ident!("arg{}", idx))
            .fold(quote! {}, |acc, arg| quote! { #acc #arg, });

        let args_msg = (0..self.args.len())
            .map(|idx| format!("Arg #{}: {}\n", idx, "{}"))
            .fold(quote! {}, |acc, arg| quote! { #acc #arg, });

        let exprs_call = self.exprs.iter().fold(quote! {}, |acc, expr| {
            let value = self.kind.value(expr, &args_call);

            quote! {
                #acc

                assert!(#value, concat!("Expression: {}\n", #args_msg), stringify!(#expr), #args_call);
            }
        });

        let quote = self
            .args
            .iter()
            .enumerate()
            .rev()
            .map(|(idx, expr)| (format_ident!("arg{}", idx), expr))
            .fold(exprs_call, |acc, (ident, expr)| {
                quote! {
                    for #ident in #expr {
                        #acc
                    }
                }
            });

        tokens.extend(quote);
    }
}

impl ToTokens for AssertRange {
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

        let ty = &self.ty;
        let len = self.len;
        let class = self.class;
        let primes = PRIMES[len];
        let prime = primes[class % primes.len()];

        tokens.extend(quote! { (#ty::MIN..#ty::MAX).step_by(#prime) });
    }
}

impl AssertKind {
    fn value(&self, expr: &Expr, args: &TokenStream) -> TokenStream {
        match self {
            AssertKind::Eq => quote! {{ let val = (#expr)(#args); val.0 == val.1 }},
            AssertKind::EqNot => quote! {{ let val = (#expr)(#args); val.0 != val.1 }},
            AssertKind::Default => quote! { (#expr)(#args) },
        }
    }
}
