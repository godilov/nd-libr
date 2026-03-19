#![doc = include_str!("../README.md")]

use std::hash::{DefaultHasher, Hash, Hasher};

use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{
    Expr, FnArg, Ident, ItemFn, Result, Token, Type,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
};

/// Creates function monomorphization.
///
/// Allows emitting asm output of generic function for verifying with `cargo asm`.
///
/// # Examples
///
/// ```rust,ignore
/// // Asm contains monomorphization for sum::<16>, sum::<32>, sum::<64> functions
/// #[ndasm::emit(const N: usize = 16)]
/// #[ndasm::emit(const N: usize = 32)]
/// #[ndasm::emit(const N: usize = 64)]
/// fn sum<const N: usize>(arr: &[u64; N]) -> u64 {
///     arr.iter().copied().sum::<u64>()
/// }
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro_attribute]
pub fn emit(attr: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    let func = parse_macro_input!(item as AsmFunc);
    let args = parse_macro_input!(attr as AsmArgs);

    let asm = Asm { func: &func, args: &args };

    quote! {
        #func

        #asm
    }
    .into()
}

struct Asm<'x> {
    func: &'x AsmFunc,
    args: &'x AsmArgs,
}

struct AsmFunc {
    elem: ItemFn,
}

struct AsmArgs {
    elems: Punctuated<AsmArgument, Token![,]>,
}

enum AsmArgument {
    Type(AsmType),
    Const(AsmConst),
}

#[allow(unused)]
struct AsmType {
    token: Token![type],
    ident: Ident,
    eq: Token![=],
    ty: Type,
}

#[allow(unused)]
struct AsmConst {
    token: Token![const],
    ident: Ident,
    colon: Token![:],
    ty: Type,
    eq: Token![=],
    expr: Expr,
}

impl Parse for AsmFunc {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self { elem: input.parse()? })
    }
}

impl Parse for AsmArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            elems: input.parse_terminated(AsmArgument::parse, Token![,])?,
        })
    }
}

impl Parse for AsmArgument {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(Token![type]) {
            Ok(Self::Type(AsmType {
                token: input.parse()?,
                ident: input.parse()?,
                eq: input.parse()?,
                ty: input.parse()?,
            }))
        } else if lookahead.peek(Token![const]) {
            Ok(Self::Const(AsmConst {
                token: input.parse()?,
                ident: input.parse()?,
                colon: input.parse()?,
                ty: input.parse()?,
                eq: input.parse()?,
                expr: input.parse()?,
            }))
        } else {
            Err(lookahead.error())
        }
    }
}

impl<'x> ToTokens for Asm<'x> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Asm {
            func: AsmFunc { elem: func },
            args,
        } = self;

        let module = format_ident!("__{}_asm_{}", &func.sig.ident, args.hash());

        let ident = &func.sig.ident;
        let generics = &func.sig.generics;
        let inputs = &func.sig.inputs;
        let output = &func.sig.output;

        let function = if !generics.params.is_empty() {
            let (_, gen_ty, _) = generics.split_for_impl();

            quote! { #ident::#gen_ty }
        } else {
            quote! { #ident }
        };

        let inputs = inputs.iter().filter_map(|arg| match arg {
            FnArg::Receiver(_) => None,
            FnArg::Typed(val) => Some(&*val.ty),
        });

        let args = args.elems.iter();

        tokens.extend(quote! {
            mod #module {
                use super::*;

                #(#args)*

                #[used]
                static FN: fn(#(#inputs),*) #output = #function;
            }
        });
    }
}

impl ToTokens for AsmFunc {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let val = &self.elem;

        tokens.extend(quote! { #val });
    }
}

impl ToTokens for AsmArgument {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            AsmArgument::Type(val) => {
                let ident = &val.ident;
                let ty = &val.ty;

                tokens.extend(quote! { type #ident = #ty; });
            },
            AsmArgument::Const(val) => {
                let ident = &val.ident;
                let ty = &val.ty;
                let expr = &val.expr;

                tokens.extend(quote! { const #ident: #ty = #expr; });
            },
        }
    }
}

impl AsmArgs {
    fn hash(&self) -> u64 {
        let mut hasher = DefaultHasher::default();

        self.elems.iter().for_each(|arg| match arg {
            AsmArgument::Type(val) => {
                val.ident.hash(&mut hasher);
                val.ty.hash(&mut hasher);
            },
            AsmArgument::Const(val) => {
                val.ident.hash(&mut hasher);
                val.ty.hash(&mut hasher);
                val.expr.hash(&mut hasher);
            },
        });

        hasher.finish()
    }
}
