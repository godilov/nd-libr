use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{
    Expr, Result, Token, bracketed, parenthesized,
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
    args: Punctuated<Expr, Token![,]>,
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

trait AssertKind: Parse {
    fn assert(&self, stream: TokenStream) -> TokenStream;
}

impl AssertKind for AssertKindCheck {
    fn assert(&self, call: TokenStream) -> TokenStream {
        quote! { assert!(#call); }
    }
}

impl AssertKind for AssertKindCompare {
    fn assert(&self, call: TokenStream) -> TokenStream {
        match self {
            AssertKindCompare::Eq => quote! {{ let val = #call; assert_eq!(val.0, val.1); }},
            AssertKindCompare::EqNot => quote! {{ let val = #call; assert_ne!(val.0, val.1); }},
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
            args: args.parse_terminated(Expr::parse, Token![,])?,
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
            input.parse::<kw::eq>()?;

            Ok(Self::EqNot)
        } else {
            Err(lookahead.error())
        }
    }
}

impl<Kind: AssertKind> ToTokens for Assert<Kind> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let args = &self.args;
        let exprs = &self.exprs;

        let args_call = (0..args.len())
            .map(|idx| format_ident!("arg{}", idx))
            .fold(quote! {}, |acc, arg| quote! { #acc #arg, });

        let exprs_call = exprs.iter().fold(quote! {}, |acc, expr| {
            let assert = self.kind.assert(quote! { (#expr)(#args_call) });

            quote! { #acc #assert }
        });

        let quote = args
            .iter()
            .enumerate()
            .rev()
            .map(|(idx, expr)| (format_ident!("arg{}", idx), expr))
            .fold(exprs_call, |acc, (arg, iter)| {
                quote! {
                    for #arg in #iter {
                        #acc
                    }
                }
            });

        tokens.extend(quote);
    }
}
