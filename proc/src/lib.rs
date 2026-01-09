use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::{
    BinOp, Error, Expr, ExprField, GenericParam, Generics, Ident, Item, Path, Result, Token, TraitItem, Type, UnOp,
    WhereClause, bracketed,
    ext::IdentExt,
    parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input, parse_quote, parse_str, parse2,
    punctuated::Punctuated,
    token::{Bracket, Paren},
};

enum Ops {
    Mutable(TokenStream),
    Binary(TokenStream),
    Unary(TokenStream),
}

#[allow(dead_code)]
struct OpsSignatureMutable {
    lhs_token: Token![|],
    lhs_vmut: Option<Token![mut]>,
    lhs_star: Option<Token![*]>,
    lhs_ident: Ident,
    lhs_colon: Token![:],
    lhs_ref: Option<Token![&]>,
    lhs_mut: Token![mut],
    lhs_type: Type,
    delim: Token![,],
    rhs_vmut: Option<Token![mut]>,
    rhs_star: Option<Token![*]>,
    rhs_ident: Ident,
    rhs_colon: Token![:],
    rhs_ref: Option<Token![&]>,
    rhs_type: Type,
    rhs_token: Token![|],
}

#[allow(dead_code)]
struct OpsSignatureBinary {
    lhs_token: Token![|],
    lhs_vmut: Option<Token![mut]>,
    lhs_star: Option<Token![*]>,
    lhs_ident: Ident,
    lhs_colon: Token![:],
    lhs_ref: Option<Token![&]>,
    lhs_type: Type,
    delim: Token![,],
    rhs_vmut: Option<Token![mut]>,
    rhs_star: Option<Token![*]>,
    rhs_ident: Ident,
    rhs_colon: Token![:],
    rhs_ref: Option<Token![&]>,
    rhs_type: Type,
    rhs_token: Token![|],
    arrow: Token![->],
    op_type: Type,
}

#[allow(dead_code)]
struct OpsSignatureUnary {
    lhs_token: Token![|],
    lhs_vmut: Option<Token![mut]>,
    lhs_star: Option<Token![*]>,
    lhs_ident: Ident,
    lhs_colon: Token![:],
    lhs_ref: Option<Token![&]>,
    lhs_type: Type,
    rhs_token: Token![|],
    arrow: Token![->],
    op_type: Type,
}

#[allow(dead_code)]
struct OpsImplEntry<Op: Parse> {
    op: Op,
    expr: Expr,
}

#[allow(dead_code)]
struct OpsImpl<OpsSignature: Parse, Op: Parse> {
    generics: Generics,
    signature: OpsSignature,
    colon: Token![,],
    entries: Punctuated<OpsImplEntry<Op>, Token![,]>,
}

#[allow(dead_code)]
struct OpsImplAutoBin<OpsSignature: Parse, Op: Parse> {
    generics: Generics,
    signature: OpsSignature,
    colon: Token![,],
    lhs_paren: Paren,
    lhs_expr: Expr,
    rhs_paren: Paren,
    rhs_expr: Expr,
    ops_bracket: Bracket,
    ops: Punctuated<Op, Token![,]>,
}

#[allow(dead_code)]
struct OpsImplAutoUn<OpsSignature: Parse, Op: Parse> {
    generics: Generics,
    signature: OpsSignature,
    colon: Token![,],
    lhs_paren: Paren,
    lhs_expr: Expr,
    ops_bracket: Bracket,
    ops: Punctuated<Op, Token![,]>,
}

#[allow(dead_code)]
struct ForwardImpl {
    expr: Expr,
    comma: Token![,],
    idents: Punctuated<Ident, Token![,]>,
}

type OpsImplMutable = OpsImpl<OpsSignatureMutable, BinOp>;
type OpsImplBinary = OpsImpl<OpsSignatureBinary, BinOp>;
type OpsImplUnary = OpsImpl<OpsSignatureUnary, UnOp>;

type OpsImplAutoMutable = OpsImplAutoBin<OpsSignatureMutable, BinOp>;
type OpsImplAutoBinary = OpsImplAutoBin<OpsSignatureBinary, BinOp>;
type OpsImplAutoUnary = OpsImplAutoUn<OpsSignatureUnary, UnOp>;

impl Parse for Ops {
    fn parse(input: ParseStream) -> Result<Self> {
        let _ = input.parse::<Token![@]>();

        let ident = input.call(Ident::parse_any)?;
        let tokens = input.parse::<TokenStream>()?;

        if ident == "mut" {
            return Ok(Ops::Mutable(tokens));
        }

        if ident == "bin" {
            return Ok(Ops::Binary(tokens));
        }

        if ident == "un" {
            return Ok(Ops::Unary(tokens));
        }

        Err(input.error("Failed to parse ops identifier, expected @mut, @bin or @un"))
    }
}

impl Parse for OpsSignatureMutable {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            lhs_token: input.parse()?,
            lhs_vmut: input.parse().ok(),
            lhs_star: input.parse().ok(),
            lhs_ident: input.parse()?,
            lhs_colon: input.parse()?,
            lhs_ref: input.parse().ok(),
            lhs_mut: input.parse()?,
            lhs_type: input.parse()?,
            delim: input.parse()?,
            rhs_vmut: input.parse().ok(),
            rhs_star: input.parse().ok(),
            rhs_ident: input.parse()?,
            rhs_colon: input.parse()?,
            rhs_ref: input.parse().ok(),
            rhs_type: input.parse()?,
            rhs_token: input.parse()?,
        })
    }
}

impl Parse for OpsSignatureBinary {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            lhs_token: input.parse()?,
            lhs_vmut: input.parse().ok(),
            lhs_star: input.parse().ok(),
            lhs_ident: input.parse()?,
            lhs_colon: input.parse()?,
            lhs_ref: input.parse().ok(),
            lhs_type: input.parse()?,
            delim: input.parse()?,
            rhs_vmut: input.parse().ok(),
            rhs_star: input.parse().ok(),
            rhs_ident: input.parse()?,
            rhs_colon: input.parse()?,
            rhs_ref: input.parse().ok(),
            rhs_type: input.parse()?,
            rhs_token: input.parse()?,
            arrow: input.parse()?,
            op_type: input.parse()?,
        })
    }
}

impl Parse for OpsSignatureUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            lhs_token: input.parse()?,
            lhs_vmut: input.parse().ok(),
            lhs_star: input.parse().ok(),
            lhs_ident: input.parse()?,
            lhs_colon: input.parse()?,
            lhs_ref: input.parse().ok(),
            lhs_type: input.parse()?,
            rhs_token: input.parse()?,
            arrow: input.parse()?,
            op_type: input.parse()?,
        })
    }
}

impl<Op: Parse> Parse for OpsImplEntry<Op> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            op: input.parse()?,
            expr: input.parse()?,
        })
    }
}

impl<OpsSinature: Parse, Op: Parse> Parse for OpsImpl<OpsSinature, Op> {
    fn parse(input: ParseStream) -> Result<Self> {
        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;

        Ok(Self {
            generics: Generics {
                where_clause: gen_where,
                ..gen_
            },
            signature: input.parse()?,
            colon: input.parse()?,
            entries: input.parse_terminated(OpsImplEntry::parse, Token![,])?,
        })
    }
}

impl<OpsSinature: Parse, Op: Parse> Parse for OpsImplAutoBin<OpsSinature, Op> {
    fn parse(input: ParseStream) -> Result<Self> {
        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;

        let lhs_content;
        let rhs_content;
        let ops_content;

        Ok(Self {
            generics: Generics {
                where_clause: gen_where,
                ..gen_
            },
            signature: input.parse()?,
            colon: input.parse()?,
            lhs_paren: parenthesized!(lhs_content in input),
            lhs_expr: lhs_content.parse()?,
            rhs_paren: parenthesized!(rhs_content in input),
            rhs_expr: rhs_content.parse()?,
            ops_bracket: bracketed!(ops_content in input),
            ops: ops_content.parse_terminated(Op::parse, Token![,])?,
        })
    }
}

impl<OpsSinature: Parse, Op: Parse> Parse for OpsImplAutoUn<OpsSinature, Op> {
    fn parse(input: ParseStream) -> Result<Self> {
        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;

        let lhs_content;
        let ops_content;

        Ok(Self {
            generics: Generics {
                where_clause: gen_where,
                ..gen_
            },
            signature: input.parse()?,
            colon: input.parse()?,
            lhs_paren: parenthesized!(lhs_content in input),
            lhs_expr: lhs_content.parse()?,
            ops_bracket: bracketed!(ops_content in input),
            ops: ops_content.parse_terminated(Op::parse, Token![,])?,
        })
    }
}

impl Parse for ForwardImpl {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            expr: input.parse()?,
            comma: input.parse()?,
            idents: input.parse_terminated(Ident::parse, Token![,])?,
        })
    }
}

impl ToTokens for OpsImplMutable {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            op: &'ops BinOp,
            generics: &'ops Generics,
            signature: &'ops OpsSignatureMutable,
            expr: &'ops Expr,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>, rhs_ref: Option<Token![&]>) -> TokenStream {
            let (ident, path) = match get_std_path_mut(spec.op) {
                Ok(val) => val,
                Err(err) => {
                    return err.into_compile_error();
                },
            };

            let (gen_impl, _, gen_where) = spec.generics.split_for_impl();

            let lhs_mut = &spec.signature.lhs_vmut;
            let lhs_ident = &spec.signature.lhs_ident;
            let lhs_type = &spec.signature.lhs_type;
            let rhs_mut = &spec.signature.rhs_vmut;
            let rhs_ident = &spec.signature.rhs_ident;
            let rhs_type = &spec.signature.rhs_type;

            let expr = &spec.expr;

            let lhs_ref = lhs_ref.map(|_| quote! { &mut });

            quote! {
                impl #gen_impl #path<#rhs_ref #rhs_type> for #lhs_ref #lhs_type #gen_where {
                    fn #ident(&mut self, rhs: #rhs_ref #rhs_type ) {
                        (|#lhs_mut #lhs_ident: &mut #lhs_type, #rhs_mut #rhs_ident: #rhs_ref #rhs_type| { #expr })(self, rhs);
                    }
                }
            }
        }

        let lstar = self.signature.lhs_star.is_some();
        let rstar = self.signature.rhs_star.is_some();

        let lhs = self.signature.lhs_ref.is_some();
        let rhs = self.signature.rhs_ref.is_some();

        let some = Some(Default::default());
        let none = None;

        for entry in &self.entries {
            let spec = OpsSpec {
                op: &entry.op,
                generics: &self.generics,
                signature: &self.signature,
                expr: &entry.expr,
            };

            match (lhs, rhs) {
                (true, true) => match (lstar, rstar) {
                    (true, true) => {
                        tokens.extend(get_impl(spec, some, some));
                        tokens.extend(get_impl(spec, some, none));
                        tokens.extend(get_impl(spec, none, some));
                        tokens.extend(get_impl(spec, none, none));
                    },
                    (true, false) => {
                        tokens.extend(get_impl(spec, some, some));
                        tokens.extend(get_impl(spec, none, some));
                    },
                    (false, true) => {
                        tokens.extend(get_impl(spec, some, some));
                        tokens.extend(get_impl(spec, some, none));
                    },
                    (false, false) => {
                        tokens.extend(get_impl(spec, some, some));
                    },
                },
                (true, false) => match lstar {
                    true => {
                        tokens.extend(get_impl(spec, some, none));
                        tokens.extend(get_impl(spec, none, none));
                    },
                    false => {
                        tokens.extend(get_impl(spec, some, none));
                    },
                },
                (false, true) => match rstar {
                    true => {
                        tokens.extend(get_impl(spec, none, some));
                        tokens.extend(get_impl(spec, none, none));
                    },
                    false => {
                        tokens.extend(get_impl(spec, none, some));
                    },
                },
                (false, false) => {
                    tokens.extend(get_impl(spec, none, none));
                },
            }
        }
    }
}

impl ToTokens for OpsImplBinary {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            op: &'ops BinOp,
            generics: &'ops Generics,
            signature: &'ops OpsSignatureBinary,
            expr: &'ops Expr,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>, rhs_ref: Option<Token![&]>) -> TokenStream {
            let (ident, path) = match get_std_path_binary(spec.op) {
                Ok(val) => val,
                Err(err) => {
                    return err.into_compile_error();
                },
            };

            let (gen_impl, _, gen_where) = spec.generics.split_for_impl();

            let lhs_mut = &spec.signature.lhs_vmut;
            let lhs_ident = &spec.signature.lhs_ident;
            let lhs_type = &spec.signature.lhs_type;
            let rhs_mut = &spec.signature.rhs_vmut;
            let rhs_ident = &spec.signature.rhs_ident;
            let rhs_type = &spec.signature.rhs_type;
            let op_type = &spec.signature.op_type;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path<#rhs_ref #rhs_type> for #lhs_ref #lhs_type #gen_where {
                    type Output = #op_type;

                    fn #ident(self, rhs: #rhs_ref #rhs_type) -> Self::Output {
                        (|#lhs_mut #lhs_ident: #lhs_ref #lhs_type, #rhs_mut #rhs_ident: #rhs_ref #rhs_type| { #op_type::from(#expr) })(self, rhs)
                    }
                }
            }
        }

        let lstar = self.signature.lhs_star.is_some();
        let rstar = self.signature.lhs_star.is_some();

        let lhs = self.signature.lhs_ref.is_some();
        let rhs = self.signature.rhs_ref.is_some();

        let some = Some(Default::default());
        let none = None;

        for entry in &self.entries {
            let spec = OpsSpec {
                op: &entry.op,
                generics: &self.generics,
                signature: &self.signature,
                expr: &entry.expr,
            };

            match (lhs, rhs) {
                (true, true) => match (lstar, rstar) {
                    (true, true) => {
                        tokens.extend(get_impl(spec, some, some));
                        tokens.extend(get_impl(spec, some, none));
                        tokens.extend(get_impl(spec, none, some));
                        tokens.extend(get_impl(spec, none, none));
                    },
                    (true, false) => {
                        tokens.extend(get_impl(spec, some, some));
                        tokens.extend(get_impl(spec, none, some));
                    },
                    (false, true) => {
                        tokens.extend(get_impl(spec, some, some));
                        tokens.extend(get_impl(spec, some, none));
                    },
                    (false, false) => {
                        tokens.extend(get_impl(spec, some, some));
                    },
                },
                (true, false) => match lstar {
                    true => {
                        tokens.extend(get_impl(spec, some, none));
                        tokens.extend(get_impl(spec, none, none));
                    },
                    false => {
                        tokens.extend(get_impl(spec, some, none));
                    },
                },
                (false, true) => match rstar {
                    true => {
                        tokens.extend(get_impl(spec, none, some));
                        tokens.extend(get_impl(spec, none, none));
                    },
                    false => {
                        tokens.extend(get_impl(spec, none, some));
                    },
                },
                (false, false) => {
                    tokens.extend(get_impl(spec, none, none));
                },
            }
        }
    }
}

impl ToTokens for OpsImplUnary {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            op: &'ops UnOp,
            generics: &'ops Generics,
            signature: &'ops OpsSignatureUnary,
            expr: &'ops Expr,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>) -> TokenStream {
            let (ident, path) = match get_std_path_unary(spec.op) {
                Ok(val) => val,
                Err(err) => {
                    return err.into_compile_error();
                },
            };

            let (gen_impl, _, gen_where) = spec.generics.split_for_impl();

            let lhs_mut = &spec.signature.lhs_vmut;
            let lhs_ident = &spec.signature.lhs_ident;
            let lhs_type = &spec.signature.lhs_type;
            let op_type = &spec.signature.op_type;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path for #lhs_ref #lhs_type #gen_where {
                    type Output = #op_type;

                    fn #ident(self) -> Self::Output {
                        (|#lhs_mut #lhs_ident: #lhs_ref #lhs_type| { (#expr).into() })(self)
                    }
                }
            }
        }

        let lstar = self.signature.lhs_star.is_some();
        let lhs = self.signature.lhs_ref.is_some();

        let some = Some(Default::default());
        let none = None;

        for entry in &self.entries {
            let spec = OpsSpec {
                op: &entry.op,
                generics: &self.generics,
                signature: &self.signature,
                expr: &entry.expr,
            };

            match lhs {
                true => match lstar {
                    true => {
                        tokens.extend(get_impl(spec, some));
                        tokens.extend(get_impl(spec, none));
                    },
                    false => {
                        tokens.extend(get_impl(spec, some));
                    },
                },
                false => {
                    tokens.extend(get_impl(spec, none));
                },
            }
        }
    }
}

#[proc_macro]
pub fn ops_impl(stream: TokenStreamStd) -> TokenStreamStd {
    let ops = parse_macro_input!(stream as Ops);

    match ops {
        Ops::Mutable(tokens) => {
            let ops = parse2::<OpsImplMutable>(tokens);

            match ops {
                Ok(val) => quote! { #val }.into(),
                Err(err) => err.into_compile_error().into(),
            }
        },
        Ops::Binary(tokens) => {
            let ops = parse2::<OpsImplBinary>(tokens);

            match ops {
                Ok(val) => quote! { #val }.into(),
                Err(err) => err.into_compile_error().into(),
            }
        },
        Ops::Unary(tokens) => {
            let ops = parse2::<OpsImplUnary>(tokens);

            match ops {
                Ok(val) => quote! { #val }.into(),
                Err(err) => err.into_compile_error().into(),
            }
        },
    }
}

#[proc_macro]
pub fn ops_impl_auto(stream: TokenStreamStd) -> TokenStreamStd {
    let ops = parse_macro_input!(stream as Ops);

    match ops {
        Ops::Mutable(tokens) => {
            let ops = parse2::<OpsImplAutoMutable>(tokens).map(|val| OpsImplMutable {
                generics: val.generics,
                signature: val.signature,
                colon: Default::default(),
                entries: val
                    .ops
                    .into_iter()
                    .map(|op| {
                        let lhs = &val.lhs_expr;
                        let rhs = &val.rhs_expr;

                        OpsImplEntry::<BinOp> {
                            op,
                            expr: parse_quote! {{ #lhs #op #rhs; }},
                        }
                    })
                    .collect::<Punctuated<OpsImplEntry<BinOp>, Token![,]>>(),
            });

            match ops {
                Ok(val) => quote! { #val }.into(),
                Err(err) => err.into_compile_error().into(),
            }
        },
        Ops::Binary(tokens) => {
            let ops = parse2::<OpsImplAutoBinary>(tokens).map(|val| OpsImplBinary {
                generics: val.generics,
                signature: val.signature,
                colon: Default::default(),
                entries: val
                    .ops
                    .into_iter()
                    .map(|op| {
                        let lhs = &val.lhs_expr;
                        let rhs = &val.rhs_expr;

                        OpsImplEntry::<BinOp> {
                            op,
                            expr: parse_quote! {{ #lhs #op #rhs }},
                        }
                    })
                    .collect::<Punctuated<OpsImplEntry<BinOp>, Token![,]>>(),
            });

            match ops {
                Ok(val) => quote! { #val }.into(),
                Err(err) => err.into_compile_error().into(),
            }
        },
        Ops::Unary(tokens) => {
            let ops = parse2::<OpsImplAutoUnary>(tokens).map(|val| OpsImplUnary {
                generics: val.generics,
                signature: val.signature,
                colon: Default::default(),
                entries: val
                    .ops
                    .into_iter()
                    .map(|op| {
                        let lhs = &val.lhs_expr;

                        OpsImplEntry::<UnOp> {
                            op,
                            expr: parse_quote! {{ #op #lhs }},
                        }
                    })
                    .collect::<Punctuated<OpsImplEntry<UnOp>, Token![,]>>(),
            });

            match ops {
                Ok(val) => quote! { #val }.into(),
                Err(err) => err.into_compile_error().into(),
            }
        },
    }
}

#[proc_macro_attribute]
pub fn align(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    let item = parse_macro_input!(item as Item);

    match item {
        Item::Struct(item) => quote! {
            #[cfg_attr(target_arch = "x86",     repr(align(64)))]
            #[cfg_attr(target_arch = "x86_64",  repr(align(64)))]
            #[cfg_attr(target_arch = "arm",     repr(align(64)))]
            #[cfg_attr(target_arch = "aarch64", repr(align(128)))]
            #item
        }
        .into(),
        Item::Enum(item) => quote! {
            #[cfg_attr(target_arch = "x86",     repr(align(64)))]
            #[cfg_attr(target_arch = "x86_64",  repr(align(64)))]
            #[cfg_attr(target_arch = "arm",     repr(align(64)))]
            #[cfg_attr(target_arch = "aarch64", repr(align(128)))]
            #item
        }
        .into(),
        Item::Union(item) => quote! {
            #[cfg_attr(target_arch = "x86",     repr(align(64)))]
            #[cfg_attr(target_arch = "x86_64",  repr(align(64)))]
            #[cfg_attr(target_arch = "arm",     repr(align(64)))]
            #[cfg_attr(target_arch = "aarch64", repr(align(128)))]
            #item
        }
        .into(),
        _ => Error::new(Span::call_site(), "Failed to align, expected struct, enum or union")
            .into_compile_error()
            .into(),
    }
}

#[proc_macro_attribute]
pub fn forward_std(attr: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    let item = parse_macro_input!(item as Item);
    let expr = parse_macro_input!(attr as Expr);

    let item = get_normalized_item(item);

    let (ident, generics, field, ty) = match get_forward_args(&item, &expr) {
        Ok(val) => val,
        Err(err) => return err.into_compile_error().into(),
    };

    let gen_params = &generics.params;

    let (gen_impl, gen_type, gen_where) = generics.split_for_impl();

    let as_ref: WhereClause = match gen_where {
        Some(val) => parse_quote! { #val, #ty: std::convert::AsRef<AsRefRet> },
        None => parse_quote! { where #ty: std::convert::AsRef<AsRefRet> },
    };

    let as_mut: WhereClause = match gen_where {
        Some(val) => parse_quote! { #val, #ty: std::convert::AsMut<AsMutRet> },
        None => parse_quote! { where #ty: std::convert::AsMut<AsMutRet> },
    };

    let from_iter: WhereClause = match gen_where {
        Some(val) => parse_quote! { #val, #ty: std::iter::FromIterator<Elem> },
        None => parse_quote! { where #ty: std::iter::FromIterator<Elem> },
    };

    quote! {
        #item

        impl #gen_impl std::ops::Deref for #ident #gen_type #gen_where {
            type Target = #ty;

            fn deref(&self) -> &Self::Target {
                &#field
            }
        }

        impl #gen_impl std::ops::DerefMut for #ident #gen_type #gen_where {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut #field
            }
        }

        impl<AsRefRet, #gen_params> std::convert::AsRef<AsRefRet> for #ident #gen_type #as_ref {
            fn as_ref(&self) -> &AsRefRet {
                #field.as_ref()
            }
        }

        impl<AsMutRet, #gen_params> std::convert::AsMut<AsMutRet> for #ident #gen_type #as_mut {
            fn as_mut(&mut self) -> &mut AsMutRet {
                #field.as_mut()
            }
        }

        impl<Elem, #gen_params> std::iter::FromIterator<Elem> for #ident #gen_type #from_iter {
            fn from_iter<Iter: IntoIterator<Item = Elem>>(iter: Iter) -> Self {
                Self::from(#ty::from_iter(iter))
            }
        }
    }
    .into()
}

#[proc_macro_attribute]
pub fn forward_fmt(attr: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    fn forward_fmt_impl(
        ident: &Ident,
        generics: &Generics,
        field: &ExprField,
        display: Path,
        display_where: WhereClause,
    ) -> TokenStream {
        let (gen_impl, gen_type, _) = generics.split_for_impl();

        quote! {
            impl #gen_impl #display for #ident #gen_type #display_where {
                fn fmt(&self,f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    #field.fmt(f)
                }
            }
        }
    }

    let item = parse_macro_input!(item as Item);
    let expr = parse_macro_input!(attr as Expr);

    let item = get_normalized_item(item);

    let (ident, generics, field, ty) = match get_forward_args(&item, &expr) {
        Ok(val) => val,
        Err(err) => return err.into_compile_error().into(),
    };

    let (_, _, gen_where) = generics.split_for_impl();

    let display = forward_fmt_impl(
        ident,
        generics,
        field,
        parse_quote! { std::fmt::Display },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::fmt::Display },
            None => parse_quote! { where #ty: std::fmt::Display },
        },
    );

    let binary = forward_fmt_impl(
        ident,
        generics,
        field,
        parse_quote! { std::fmt::Binary },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::fmt::Binary },
            None => parse_quote! { where #ty: std::fmt::Binary },
        },
    );

    let octal = forward_fmt_impl(
        ident,
        generics,
        field,
        parse_quote! { std::fmt::Octal },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::fmt::Octal },
            None => parse_quote! { where #ty: std::fmt::Octal },
        },
    );

    let lhex = forward_fmt_impl(
        ident,
        generics,
        field,
        parse_quote! { std::fmt::LowerHex },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::fmt::LowerHex },
            None => parse_quote! { where #ty: std::fmt::LowerHex },
        },
    );

    let uhex = forward_fmt_impl(
        ident,
        generics,
        field,
        parse_quote! { std::fmt::UpperHex },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::fmt::UpperHex },
            None => parse_quote! { where #ty: std::fmt::UpperHex },
        },
    );

    quote! {
        #item
        #display
        #binary
        #octal
        #lhex
        #uhex
    }
    .into()
}

#[proc_macro_attribute]
pub fn forward_ops(attr: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    fn forward_ops_impl(
        ident: &Ident,
        generics: &Generics,
        field: &ExprField,
        op: Path,
        op_fn: Ident,
        op_where: WhereClause,
    ) -> TokenStream {
        let gen_params = &generics.params;

        let (_, gen_type, _) = generics.split_for_impl();

        quote! {
            impl<Rhs, #gen_params> #op for #ident #gen_type #op_where {
                type Output = Self;

                fn #op_fn(self, rhs: Rhs) -> Self::Output {
                    Self::from(#field.#op_fn(rhs))
                }
            }
        }
    }

    let item = parse_macro_input!(item as Item);
    let expr = parse_macro_input!(attr as Expr);

    let item = get_normalized_item(item);

    let (ident, generics, field, ty) = match get_forward_args(&item, &expr) {
        Ok(val) => val,
        Err(err) => return err.into_compile_error().into(),
    };

    let (_, _, gen_where) = generics.split_for_impl();

    let add = forward_ops_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::Add<Rhs> },
        parse_quote! { add },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::Add<Rhs, Output = #ty> },
            None => parse_quote! { where #ty: std::ops::Add<Rhs, Output = #ty> },
        },
    );

    let sub = forward_ops_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::Sub<Rhs> },
        parse_quote! { sub },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::Sub<Rhs, Output = #ty> },
            None => parse_quote! { where #ty: std::ops::Sub<Rhs, Output = #ty> },
        },
    );

    let mul = forward_ops_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::Mul<Rhs> },
        parse_quote! { mul },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::Mul<Rhs, Output = #ty> },
            None => parse_quote! { where #ty: std::ops::Mul<Rhs, Output = #ty> },
        },
    );

    let div = forward_ops_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::Div<Rhs> },
        parse_quote! { div },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::Div<Rhs, Output = #ty> },
            None => parse_quote! { where #ty: std::ops::Div<Rhs, Output = #ty> },
        },
    );

    let rem = forward_ops_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::Rem<Rhs> },
        parse_quote! { rem },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::Rem<Rhs, Output = #ty> },
            None => parse_quote! { where #ty: std::ops::Rem<Rhs, Output = #ty> },
        },
    );

    let bitor = forward_ops_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::BitOr<Rhs> },
        parse_quote! { bitor },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::BitOr<Rhs, Output = #ty> },
            None => parse_quote! { where #ty: std::ops::BitOr<Rhs, Output = #ty> },
        },
    );

    let bitand = forward_ops_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::BitAnd<Rhs> },
        parse_quote! { bitand },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::BitAnd<Rhs, Output = #ty> },
            None => parse_quote! { where #ty: std::ops::BitAnd<Rhs, Output = #ty> },
        },
    );

    let bitxor = forward_ops_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::BitXor<Rhs> },
        parse_quote! { bitxor },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::BitXor<Rhs, Output = #ty> },
            None => parse_quote! { where #ty: std::ops::BitXor<Rhs, Output = #ty> },
        },
    );

    quote! {
        #item
        #add
        #sub
        #mul
        #div
        #rem
        #bitor
        #bitand
        #bitxor
    }
    .into()
}

#[proc_macro_attribute]
pub fn forward_ops_assign(attr: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    fn forward_ops_assign_impl(
        ident: &Ident,
        generics: &Generics,
        field: &ExprField,
        op: Path,
        op_fn: Ident,
        op_where: WhereClause,
    ) -> TokenStream {
        let gen_params = &generics.params;

        let (_, gen_type, _) = generics.split_for_impl();

        quote! {
            impl<Rhs, #gen_params> #op for #ident #gen_type #op_where {
                fn #op_fn(&mut self, rhs: Rhs) {
                    #field.#op_fn(rhs);
                }
            }
        }
    }

    let item = parse_macro_input!(item as Item);
    let expr = parse_macro_input!(attr as Expr);

    let item = get_normalized_item(item);

    let (ident, generics, field, ty) = match get_forward_args(&item, &expr) {
        Ok(val) => val,
        Err(err) => return err.into_compile_error().into(),
    };

    let (_, _, gen_where) = generics.split_for_impl();

    let add = forward_ops_assign_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::AddAssign<Rhs> },
        parse_quote! { add_assign },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::AddAssign<Rhs> },
            None => parse_quote! { where #ty: std::ops::AddAssign<Rhs> },
        },
    );

    let sub = forward_ops_assign_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::SubAssign<Rhs> },
        parse_quote! { sub_assign },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::SubAssign<Rhs> },
            None => parse_quote! { where #ty: std::ops::SubAssign<Rhs> },
        },
    );

    let mul = forward_ops_assign_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::MulAssign<Rhs> },
        parse_quote! { mul_assign },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::MulAssign<Rhs> },
            None => parse_quote! { where #ty: std::ops::MulAssign<Rhs> },
        },
    );

    let div = forward_ops_assign_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::DivAssign<Rhs> },
        parse_quote! { div_assign },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::DivAssign<Rhs> },
            None => parse_quote! { where #ty: std::ops::DivAssign<Rhs> },
        },
    );

    let rem = forward_ops_assign_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::RemAssign<Rhs> },
        parse_quote! { rem_assign },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::RemAssign<Rhs> },
            None => parse_quote! { where #ty: std::ops::RemAssign<Rhs> },
        },
    );

    let bitor = forward_ops_assign_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::BitOrAssign<Rhs> },
        parse_quote! { bitor_assign },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::BitOrAssign<Rhs> },
            None => parse_quote! { where #ty: std::ops::BitOrAssign<Rhs> },
        },
    );

    let bitand = forward_ops_assign_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::BitAndAssign<Rhs> },
        parse_quote! { bitand_assign },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::BitAndAssign<Rhs> },
            None => parse_quote! { where #ty: std::ops::BitAndAssign<Rhs> },
        },
    );

    let bitxor = forward_ops_assign_impl(
        ident,
        generics,
        field,
        parse_quote! { std::ops::BitXorAssign<Rhs> },
        parse_quote! { bitxor_assign },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::ops::BitXorAssign<Rhs> },
            None => parse_quote! { where #ty: std::ops::BitXorAssign<Rhs> },
        },
    );

    quote! {
        #item
        #add
        #sub
        #mul
        #div
        #rem
        #bitor
        #bitand
        #bitxor
    }
    .into()
}

#[proc_macro_attribute]
pub fn forward_decl(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    let item = parse_macro_input!(item as Item);

    let item = match get_normalized_item(item) {
        Item::Trait(item) => item,
        _ => {
            return Error::new(Span::call_site(), "Failed to forward declaration, expected trait")
                .into_compile_error()
                .into();
        },
    };

    let ident = &item.ident;
    let ident_macros = format_ident!("forward_impl_{}", ident);

    let gen_params = &item.generics.params;
    let (_, gen_type, gen_where) = item.generics.split_for_impl();

    let gen_params: Punctuated<GenericParam, Token![,]> = match gen_params.is_empty() {
        true => parse_quote! {},
        false => parse_quote! { #gen_params, },
    };

    let gen_where: WhereClause = match gen_where {
        Some(val) => parse_quote! { #val, },
        None => parse_quote! { where },
    };

    let types = item
        .items
        .iter()
        .filter_map(|item| match item {
            TraitItem::Type(item) => Some(item),
            _ => None,
        })
        .map(|item| {
            let attrs = &item.attrs;
            let ident = &item.ident;

            let (gen_impl, gen_type, _) = item.generics.split_for_impl();

            quote! {
                #(#attrs)*
                type #ident #gen_impl = <$ty_field>::#ident #gen_type;
            }
        });

    let consts = item
        .items
        .iter()
        .filter_map(|item| match item {
            TraitItem::Const(item) => Some(item),
            _ => None,
        })
        .map(|item| {
            let attrs = &item.attrs;
            let ident = &item.ident;
            let ty = &item.ty;

            quote! {
                #(#attrs)*
                const #ident: #ty = <$ty_field>::#ident;
            }
        });

    let fns = item
        .items
        .iter()
        .filter_map(|item| match item {
            TraitItem::Fn(item) => Some(item),
            _ => None,
        })
        .map(|item| quote! { #item });

    quote! {
        #item

        #[doc(hidden)]
        #[allow(unused_macros)]
        macro_rules! #ident_macros {
            () => {};
            ($ty:ty, $ty_field:ty, $field:expr, $field_ref:expr, $field_mut:expr, ($($gen_params:tt)+), ($($gen_where:tt)+),) => {
                impl <#gen_params $gen_params> #ident #gen_type for $ty #gen_where $gen_where {
                    #(#types)*
                    #(#consts)*
                    #(#fns)*
                }
            };
        }

        #[allow(unused_imports)]
        pub(crate) use #ident_macros;
    }
    .into()
}

#[proc_macro_attribute]
pub fn forward_def(attr: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    let item = parse_macro_input!(item as Item);
    let forward = parse_macro_input!(attr as ForwardImpl);

    let (_ident, _generics, _field, _ty) = match get_forward_args(&item, &forward.expr) {
        Ok(val) => val,
        Err(err) => return err.into_compile_error().into(),
    };

    let item = match get_normalized_item(item) {
        Item::Struct(item) => Item::from(item),
        Item::Enum(item) => Item::from(item),
        Item::Union(item) => Item::from(item),
        _ => {
            return Error::new(
                Span::call_site(),
                "Failed to forward definition, expected struct, enum or union",
            )
            .into_compile_error()
            .into();
        },
    };

    let quotes =
        forward
            .idents
            .iter()
            .map(|ident| format_ident!("forward_impl_{}", ident))
            .fold(quote! {}, |acc, ident| {
                quote! {
                    #acc

                    #ident!();
                }
            });

    quote! {
        #item

        #quotes
    }
    .into()
}

fn get_std_path_mut(op: &BinOp) -> Result<(Ident, Path)> {
    let (ident, path) = match op {
        BinOp::AddAssign(_) => Ok(("add_assign", "std::ops::AddAssign")),
        BinOp::SubAssign(_) => Ok(("sub_assign", "std::ops::SubAssign")),
        BinOp::MulAssign(_) => Ok(("mul_assign", "std::ops::MulAssign")),
        BinOp::DivAssign(_) => Ok(("div_assign", "std::ops::DivAssign")),
        BinOp::RemAssign(_) => Ok(("rem_assign", "std::ops::RemAssign")),
        BinOp::BitOrAssign(_) => Ok(("bitor_assign", "std::ops::BitOrAssign")),
        BinOp::BitAndAssign(_) => Ok(("bitand_assign", "std::ops::BitAndAssign")),
        BinOp::BitXorAssign(_) => Ok(("bitxor_assign", "std::ops::BitXorAssign")),
        BinOp::ShlAssign(_) => Ok(("shl_assign", "std::ops::ShlAssign")),
        BinOp::ShrAssign(_) => Ok(("shr_assign", "std::ops::ShrAssign")),
        _ => Err(Error::new(
            Span::call_site(),
            format!(
                "Failed to find valid op for operation: '{:?}'. Expected: +=, -=, *=, /=, %=, |=, &=, ^=, <<=, >>=",
                op
            ),
        )),
    }?;

    Ok((parse_str::<Ident>(ident)?, parse_str::<Path>(path)?))
}

fn get_std_path_binary(op: &BinOp) -> Result<(Ident, Path)> {
    let (ident, path) = match op {
        BinOp::Add(_) => Ok(("add", "std::ops::Add")),
        BinOp::Sub(_) => Ok(("sub", "std::ops::Sub")),
        BinOp::Mul(_) => Ok(("mul", "std::ops::Mul")),
        BinOp::Div(_) => Ok(("div", "std::ops::Div")),
        BinOp::Rem(_) => Ok(("rem", "std::ops::Rem")),
        BinOp::BitOr(_) => Ok(("bitor", "std::ops::BitOr")),
        BinOp::BitAnd(_) => Ok(("bitand", "std::ops::BitAnd")),
        BinOp::BitXor(_) => Ok(("bitxor", "std::ops::BitXor")),
        BinOp::Shl(_) => Ok(("shl", "std::ops::Shl")),
        BinOp::Shr(_) => Ok(("shr", "std::ops::Shr")),
        _ => Err(Error::new(
            Span::call_site(),
            format!(
                "Failed to find valid op for operation: '{:?}'. Expected: +, -, *, /, %, |, &, ^, <<, >>",
                op
            ),
        )),
    }?;

    Ok((parse_str::<Ident>(ident)?, parse_str::<Path>(path)?))
}

fn get_std_path_unary(op: &UnOp) -> Result<(Ident, Path)> {
    let (ident, path) = match op {
        UnOp::Not(_) => Ok(("not", "std::ops::Not")),
        UnOp::Neg(_) => Ok(("neg", "std::ops::Neg")),
        _ => Err(Error::new(
            Span::call_site(),
            format!("Failed to find valid op for operation: '{:?}'. Expected: -, !", op),
        )),
    }?;

    Ok((parse_str::<Ident>(ident)?, parse_str::<Path>(path)?))
}

fn get_normalized_generics(mut generics: Generics) -> Generics {
    generics.params.pop_punct();
    generics.where_clause.as_mut().map(|clause| clause.predicates.pop_punct());
    generics
}

fn get_normalized_item(item: Item) -> Item {
    match item {
        Item::Struct(mut item) => {
            item.generics = get_normalized_generics(item.generics);

            item.into()
        },
        Item::Enum(mut item) => {
            item.generics = get_normalized_generics(item.generics);

            item.into()
        },
        Item::Union(mut item) => {
            item.generics = get_normalized_generics(item.generics);

            item.into()
        },
        Item::Trait(mut item) => {
            item.generics = get_normalized_generics(item.generics);

            item.into()
        },
        _ => todo!(),
    }
}

fn get_forward_args<'item, 'expr>(
    item: &'item Item,
    expr: &'expr Expr,
) -> Result<(&'item Ident, &'item Generics, &'expr ExprField, &'expr Type)> {
    let (ident, generics) = match item {
        Item::Struct(item) => (&item.ident, &item.generics),
        Item::Enum(item) => (&item.ident, &item.generics),
        Item::Union(item) => (&item.ident, &item.generics),
        _ => {
            return Err(Error::new(
                Span::call_site(),
                "Failed to forward, expected struct, enum or union",
            ));
        },
    };

    let (expr, ty) = match expr {
        Expr::Cast(cast) => (cast.expr.as_ref(), cast.ty.as_ref()),
        _ => {
            return Err(Error::new(Span::call_site(), "Failed to forward, excpected cast expression"));
        },
    };

    let field = match expr {
        Expr::Field(field) => field,
        _ => {
            return Err(Error::new(Span::call_site(), "Failed to forward, excpected field expression"));
        },
    };

    Ok((ident, generics, field, ty))
}
