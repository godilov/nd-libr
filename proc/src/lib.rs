use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::{
    BinOp, Error, Expr, ExprClosure, FnArg, Generics, Ident, Item, ItemEnum, ItemImpl, ItemStruct, ItemTrait,
    ItemUnion, Meta, Path, Result, Signature, Token, TraitItem, TraitItemConst, TraitItemFn, TraitItemType, Type, UnOp,
    WhereClause, bracketed,
    ext::IdentExt,
    parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input, parse_quote, parse_str, parse2,
    punctuated::Punctuated,
    token::{Bracket, Paren},
};

mod kw {
    syn::custom_keyword!(with);
    syn::custom_keyword!(pre);
    syn::custom_keyword!(post);
}

enum Ops {
    Mutable(TokenStream),
    Binary(TokenStream),
    Unary(TokenStream),
}

struct OpsImpl<OpsSignature: Parse, Op: Parse> {
    generics: Generics,
    signature: OpsSignature,
    #[allow(unused)]
    colon: Token![,],
    entries: Punctuated<OpsImplEntry<Op>, Token![,]>,
}

struct OpsSignatureMutable {
    #[allow(unused)]
    lhs_token: Token![|],
    lhs_vmut: Option<Token![mut]>,
    lhs_star: Option<Token![*]>,
    lhs_ident: Ident,
    #[allow(unused)]
    lhs_colon: Token![:],
    lhs_ref: Option<Token![&]>,
    #[allow(unused)]
    lhs_mut: Token![mut],
    lhs_type: Type,
    #[allow(unused)]
    delim: Token![,],
    rhs_vmut: Option<Token![mut]>,
    rhs_star: Option<Token![*]>,
    rhs_ident: Ident,
    #[allow(unused)]
    rhs_colon: Token![:],
    rhs_ref: Option<Token![&]>,
    rhs_type: Type,
    #[allow(unused)]
    rhs_token: Token![|],
}

struct OpsSignatureBinary {
    #[allow(unused)]
    lhs_token: Token![|],
    lhs_vmut: Option<Token![mut]>,
    lhs_star: Option<Token![*]>,
    lhs_ident: Ident,
    #[allow(unused)]
    lhs_colon: Token![:],
    lhs_ref: Option<Token![&]>,
    lhs_type: Type,
    #[allow(unused)]
    delim: Token![,],
    rhs_vmut: Option<Token![mut]>,
    #[allow(unused)]
    rhs_star: Option<Token![*]>,
    rhs_ident: Ident,
    #[allow(unused)]
    rhs_colon: Token![:],
    rhs_ref: Option<Token![&]>,
    rhs_type: Type,
    #[allow(unused)]
    rhs_token: Token![|],
    #[allow(unused)]
    arrow: Token![->],
    ty: Type,
}

struct OpsSignatureUnary {
    #[allow(unused)]
    lhs_token: Token![|],
    lhs_vmut: Option<Token![mut]>,
    lhs_star: Option<Token![*]>,
    lhs_ident: Ident,
    #[allow(unused)]
    lhs_colon: Token![:],
    lhs_ref: Option<Token![&]>,
    lhs_type: Type,
    #[allow(unused)]
    rhs_token: Token![|],
    #[allow(unused)]
    arrow: Token![->],
    ty: Type,
}

struct OpsImplEntry<Op: Parse> {
    op: Op,
    expr: Expr,
}

struct OpsImplAutoBin<OpsSignature: Parse, Op: Parse> {
    generics: Generics,
    signature: OpsSignature,
    #[allow(unused)]
    colon: Token![,],
    #[allow(unused)]
    lhs_paren: Paren,
    lhs_expr: Expr,
    #[allow(unused)]
    rhs_paren: Paren,
    rhs_expr: Expr,
    #[allow(unused)]
    ops_bracket: Bracket,
    ops: Punctuated<Op, Token![,]>,
}

struct OpsImplAutoUn<OpsSignature: Parse, Op: Parse> {
    generics: Generics,
    signature: OpsSignature,
    #[allow(unused)]
    colon: Token![,],
    #[allow(unused)]
    lhs_paren: Paren,
    lhs_expr: Expr,
    #[allow(unused)]
    ops_bracket: Bracket,
    ops: Punctuated<Op, Token![,]>,
}

struct Forward {
    expr: Expr,
    #[allow(unused)]
    with: kw::with,
    ty: Type,
}

enum ForwardDataItem {
    Struct(ItemStruct),
    Enum(ItemEnum),
    Union(ItemUnion),
}

enum ForwardDeclItem {
    Trait(ItemTrait),
}

enum ForwardDefItem {
    Struct(ItemStruct),
    Enum(ItemEnum),
    Union(ItemUnion),
    Impl(ItemImpl),
}

struct ForwardDataDef {
    fwd: Forward,
    #[allow(unused)]
    colon: Token![:],
    path: Path,
    conditions: Option<WhereClause>,
}

struct ForwardImplDef {
    #[allow(unused)]
    fwd: Forward,
    #[allow(unused)]
    idents: Option<ForwardIdents>,
}

struct ForwardIdents {
    #[allow(unused)]
    colon: Token![:],
    #[allow(unused)]
    elems: Punctuated<Ident, Token![,]>,
}

#[derive(Debug, Clone)]
enum ForwardExpression {
    Raw(TokenStream),
    Ref(TokenStream),
    Mut(TokenStream),
}

#[derive(Debug, Clone)]
enum ForwardArgument {
    Raw(TokenStream),
    Alt(TokenStream),
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
            ty: input.parse()?,
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
            ty: input.parse()?,
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

impl Parse for Forward {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            expr: input.parse()?,
            with: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl Parse for ForwardDataItem {
    fn parse(input: ParseStream) -> Result<Self> {
        let item = input.parse::<Item>()?;

        match item {
            Item::Struct(mut val) => {
                val.generics = get_normalized_generics(val.generics);

                Ok(Self::Struct(val))
            },
            Item::Enum(mut val) => {
                val.generics = get_normalized_generics(val.generics);

                Ok(Self::Enum(val))
            },
            Item::Union(mut val) => {
                val.generics = get_normalized_generics(val.generics);

                Ok(Self::Union(val))
            },
            _ => Err(input.error("Failed to find correct item, expected struct, enum or union")),
        }
    }
}

impl Parse for ForwardDeclItem {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut item = input.parse::<ItemTrait>()?;

        item.generics = get_normalized_generics(item.generics);
        item.supertraits.pop_punct();

        Ok(Self::Trait(item))
    }
}

impl Parse for ForwardDefItem {
    fn parse(input: ParseStream) -> Result<Self> {
        let item = input.parse::<Item>()?;

        match item {
            Item::Struct(mut val) => {
                val.generics = get_normalized_generics(val.generics);

                Ok(Self::Struct(val))
            },
            Item::Enum(mut val) => {
                val.generics = get_normalized_generics(val.generics);

                Ok(Self::Enum(val))
            },
            Item::Union(mut val) => {
                val.generics = get_normalized_generics(val.generics);

                Ok(Self::Union(val))
            },
            Item::Impl(mut val) => {
                val.generics = get_normalized_generics(val.generics);

                if val.trait_.is_none() {
                    return Err(input.error("Failed to find correct item, expected impl for trait"));
                }

                Ok(Self::Impl(val))
            },
            _ => Err(input.error("Failed to find correct item, expected struct, enum, union or impl")),
        }
    }
}

impl Parse for ForwardDataDef {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            fwd: input.parse()?,
            colon: input.parse()?,
            path: input.parse()?,
            conditions: input.parse()?,
        })
    }
}

impl Parse for ForwardImplDef {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            fwd: input.parse()?,
            idents: input.parse().ok(),
        })
    }
}

impl Parse for ForwardIdents {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            colon: input.parse()?,
            elems: input.parse_terminated(Ident::parse, Token![,])?,
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
                    fn #ident(&mut self, rhs: #rhs_ref #rhs_type) {
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
            let op_type = &spec.signature.ty;

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
            let op_type = &spec.signature.ty;

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

impl ToTokens for ForwardDataItem {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            ForwardDataItem::Struct(val) => val.to_tokens(tokens),
            ForwardDataItem::Enum(val) => val.to_tokens(tokens),
            ForwardDataItem::Union(val) => val.to_tokens(tokens),
        }
    }
}

impl ToTokens for ForwardDefItem {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            ForwardDefItem::Struct(val) => val.to_tokens(tokens),
            ForwardDefItem::Enum(val) => val.to_tokens(tokens),
            ForwardDefItem::Union(val) => val.to_tokens(tokens),
            ForwardDefItem::Impl(val) => val.to_tokens(tokens),
        }
    }
}

impl ToTokens for ForwardExpression {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            ForwardExpression::Raw(val) => val.to_tokens(tokens),
            ForwardExpression::Ref(val) => val.to_tokens(tokens),
            ForwardExpression::Mut(val) => val.to_tokens(tokens),
        }
    }
}

impl Forward {
    fn forward_args(&self) -> (&Expr, &Type) {
        (&self.expr, &self.ty)
    }
}

impl ForwardDataItem {
    fn forward_args(&self) -> (&Ident, &Generics) {
        match self {
            ForwardDataItem::Struct(val) => (&val.ident, &val.generics),
            ForwardDataItem::Enum(val) => (&val.ident, &val.generics),
            ForwardDataItem::Union(val) => (&val.ident, &val.generics),
        }
    }
}

impl ForwardExpression {
    fn stream(self) -> TokenStream {
        match self {
            ForwardExpression::Raw(val) => val,
            ForwardExpression::Ref(val) => val,
            ForwardExpression::Mut(val) => val,
        }
    }
}

impl ForwardArgument {
    fn stream(self) -> TokenStream {
        match self {
            ForwardArgument::Raw(val) => val,
            ForwardArgument::Alt(val) => val,
        }
    }
}

#[proc_macro]
pub fn ops_impl(stream: TokenStreamStd) -> TokenStreamStd {
    match parse_macro_input!(stream as Ops) {
        Ops::Mutable(tokens) => match parse2::<OpsImplMutable>(tokens) {
            Ok(val) => quote! { #val }.into(),
            Err(err) => err.into_compile_error().into(),
        },
        Ops::Binary(tokens) => match parse2::<OpsImplBinary>(tokens) {
            Ok(val) => quote! { #val }.into(),
            Err(err) => err.into_compile_error().into(),
        },
        Ops::Unary(tokens) => match parse2::<OpsImplUnary>(tokens) {
            Ok(val) => quote! { #val }.into(),
            Err(err) => err.into_compile_error().into(),
        },
    }
}

#[proc_macro]
pub fn ops_impl_auto(stream: TokenStreamStd) -> TokenStreamStd {
    let ops = parse_macro_input!(stream as Ops);

    match ops {
        Ops::Mutable(tokens) => {
            let auto = match parse2::<OpsImplAutoMutable>(tokens) {
                Ok(val) => val,
                Err(err) => return err.into_compile_error().into(),
            };

            let ops = OpsImplMutable {
                generics: auto.generics,
                signature: auto.signature,
                colon: Default::default(),
                entries: auto
                    .ops
                    .into_iter()
                    .map(|op| {
                        let lhs = &auto.lhs_expr;
                        let rhs = &auto.rhs_expr;

                        OpsImplEntry::<BinOp> {
                            op,
                            expr: parse_quote! {{ #lhs #op #rhs; }},
                        }
                    })
                    .collect::<Punctuated<OpsImplEntry<BinOp>, Token![,]>>(),
            };

            quote! { #ops }.into()
        },
        Ops::Binary(tokens) => {
            let auto = match parse2::<OpsImplAutoBinary>(tokens) {
                Ok(val) => val,
                Err(err) => return err.into_compile_error().into(),
            };

            let ops = OpsImplBinary {
                generics: auto.generics,
                signature: auto.signature,
                colon: Default::default(),
                entries: auto
                    .ops
                    .into_iter()
                    .map(|op| {
                        let lhs = &auto.lhs_expr;
                        let rhs = &auto.rhs_expr;

                        OpsImplEntry::<BinOp> {
                            op,
                            expr: parse_quote! {{ #lhs #op #rhs }},
                        }
                    })
                    .collect::<Punctuated<OpsImplEntry<BinOp>, Token![,]>>(),
            };

            quote! { #ops }.into()
        },
        Ops::Unary(tokens) => {
            let auto = match parse2::<OpsImplAutoUnary>(tokens) {
                Ok(val) => val,
                Err(err) => return err.into_compile_error().into(),
            };

            let ops = OpsImplUnary {
                generics: auto.generics,
                signature: auto.signature,
                colon: Default::default(),
                entries: auto
                    .ops
                    .into_iter()
                    .map(|op| {
                        let lhs = &auto.lhs_expr;

                        OpsImplEntry::<UnOp> {
                            op,
                            expr: parse_quote! {{ #op #lhs }},
                        }
                    })
                    .collect::<Punctuated<OpsImplEntry<UnOp>, Token![,]>>(),
            };

            quote! { #ops }.into()
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
    let item = parse_macro_input!(item as ForwardDataItem);
    let fwd = parse_macro_input!(attr as Forward);

    let (ident, generics) = item.forward_args();
    let (expr, ty) = fwd.forward_args();

    let gen_params = &generics.params;
    let (gen_impl, gen_type, gen_where) = generics.split_for_impl();

    let as_ref = match gen_where {
        Some(val) => quote! { #val, #ty: std::convert::AsRef<AsRefRet> },
        None => quote! { where #ty: std::convert::AsRef<AsRefRet> },
    };

    let as_mut = match gen_where {
        Some(val) => quote! { #val, #ty: std::convert::AsMut<AsMutRet> },
        None => quote! { where #ty: std::convert::AsMut<AsMutRet> },
    };

    let from_iter = match gen_where {
        Some(val) => quote! { #val, #ty: std::iter::FromIterator<Elem> },
        None => quote! { where #ty: std::iter::FromIterator<Elem> },
    };

    quote! {
        #item

        impl #gen_impl std::ops::Deref for #ident #gen_type #gen_where {
            type Target = #ty;

            fn deref(&self) -> &Self::Target {
                &#expr
            }
        }

        impl #gen_impl std::ops::DerefMut for #ident #gen_type #gen_where {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut #expr
            }
        }

        impl<AsRefRet, #gen_params> std::convert::AsRef<AsRefRet> for #ident #gen_type #as_ref {
            fn as_ref(&self) -> &AsRefRet {
                #expr.as_ref()
            }
        }

        impl<AsMutRet, #gen_params> std::convert::AsMut<AsMutRet> for #ident #gen_type #as_mut {
            fn as_mut(&mut self) -> &mut AsMutRet {
                #expr.as_mut()
            }
        }

        impl<Elem, #gen_params> std::iter::FromIterator<Elem> for #ident #gen_type #from_iter {
            fn from_iter<Iter: IntoIterator<Item = Elem>>(iter: Iter) -> Self {
                <#ty>::from_iter(iter).into()
            }
        }
    }
    .into()
}

#[proc_macro_attribute]
pub fn forward_cmp(attr: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    let item = parse_macro_input!(item as ForwardDataItem);
    let fwd = parse_macro_input!(attr as Forward);

    let (ident, generics) = item.forward_args();
    let (expr, ty) = fwd.forward_args();

    let (gen_impl, gen_type, gen_where) = generics.split_for_impl();

    let partial_ord = match gen_where {
        Some(val) => quote! { #val, #ty: std::cmp::PartialOrd },
        None => quote! { where #ty: std::cmp::PartialOrd },
    };

    let partial_eq = match gen_where {
        Some(val) => quote! { #val, #ty: std::cmp::PartialEq },
        None => quote! { where #ty: std::cmp::PartialEq },
    };

    let ord = match gen_where {
        Some(val) => quote! { #val, #ty: std::cmp::Ord },
        None => quote! { where #ty: std::cmp::Ord },
    };

    let eq = match gen_where {
        Some(val) => quote! { #val, #ty: std::cmp::Eq },
        None => quote! { where #ty: std::cmp::Eq },
    };

    let forward_impl = get_forward_impl(ident, generics, expr, ty);

    quote! {
        #item

        impl #gen_impl std::cmp::Eq for #ident #gen_type #eq {}

        impl #gen_impl std::cmp::Ord for #ident #gen_type #ord {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                #forward_impl

                self.forward_ref().cmp(other.forward_ref())
            }
        }

        impl #gen_impl std::cmp::PartialEq for #ident #gen_type #partial_eq {
            fn eq(&self, other: &Self) -> bool {
                #forward_impl

                self.forward_ref().eq(other.forward_ref())
            }
        }

        impl #gen_impl std::cmp::PartialOrd for #ident #gen_type #partial_ord {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                #forward_impl

                self.forward_ref().partial_cmp(other.forward_ref())
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
        expr: &Expr,
        display: Path,
        display_where: WhereClause,
    ) -> TokenStream {
        let (gen_impl, gen_type, _) = generics.split_for_impl();

        quote! {
            impl #gen_impl #display for #ident #gen_type #display_where {
                fn fmt(&self,f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    #expr.fmt(f)
                }
            }
        }
    }

    let item = parse_macro_input!(item as ForwardDataItem);
    let fwd = parse_macro_input!(attr as Forward);

    let (ident, generics) = item.forward_args();
    let (expr, ty) = fwd.forward_args();

    let (_, _, gen_where) = generics.split_for_impl();

    let display = forward_fmt_impl(
        ident,
        generics,
        expr,
        parse_quote! { std::fmt::Display },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::fmt::Display },
            None => parse_quote! { where #ty: std::fmt::Display },
        },
    );

    let binary = forward_fmt_impl(
        ident,
        generics,
        expr,
        parse_quote! { std::fmt::Binary },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::fmt::Binary },
            None => parse_quote! { where #ty: std::fmt::Binary },
        },
    );

    let octal = forward_fmt_impl(
        ident,
        generics,
        expr,
        parse_quote! { std::fmt::Octal },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::fmt::Octal },
            None => parse_quote! { where #ty: std::fmt::Octal },
        },
    );

    let lhex = forward_fmt_impl(
        ident,
        generics,
        expr,
        parse_quote! { std::fmt::LowerHex },
        match gen_where {
            Some(val) => parse_quote! { #val, #ty: std::fmt::LowerHex },
            None => parse_quote! { where #ty: std::fmt::LowerHex },
        },
    );

    let uhex = forward_fmt_impl(
        ident,
        generics,
        expr,
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
pub fn forward_decl(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    let ForwardDeclItem::Trait(interface) = parse_macro_input!(item as ForwardDeclItem);

    let ident = &interface.ident;
    let macros = format_ident!("__forward_impl_{}", ident);

    let gen_params = &interface.generics.params;
    let (_, gen_type, gen_where) = &interface.generics.split_for_impl();

    let supertraits = &interface.supertraits;
    let supertraits = match interface.supertraits.len() {
        0 => quote! {},
        _ => quote! { Self: #supertraits, },
    };

    let gen_params = match gen_params.is_empty() {
        true => quote! {},
        false => quote! { #gen_params, },
    };

    let gen_where = match gen_where {
        Some(val) => quote! { #val, #supertraits },
        None => quote! { where #supertraits },
    };

    let idents = interface.items.iter().filter_map(|item| match item {
        TraitItem::Type(val) => Some(&val.ident),
        TraitItem::Const(val) => Some(&val.ident),
        TraitItem::Fn(val) => Some(&val.sig.ident),
        _ => None,
    });

    let forwards = interface
        .items
        .iter()
        .filter_map(|item| match item {
            TraitItem::Type(val) => Some(Ok(get_forward_type(&interface, val))),
            TraitItem::Const(val) => Some(Ok(get_forward_const(&interface, val))),
            TraitItem::Fn(val) => Some(get_forward_fn(&interface, val)),
            _ => None,
        })
        .collect::<Result<Vec<(&Ident, TokenStream)>>>();

    let forwards = match forwards {
        Ok(val) => val,
        Err(err) => return err.into_compile_error().into(),
    };

    let streams = forwards.iter().map(|(_, stream)| stream);
    let cases = forwards.iter().map(|(ident, stream)| {
        quote! {
            (#ident $ty:ty) => {
                #stream
            };
        }
    });

    quote! {
        #interface

        #[doc(hidden)]
        #[allow(unused_macros)]
        macro_rules! #macros {
            (@ $self:ty, $ty:ty, ($($gen_params:tt)*), ($($gen_where:tt)*)) => {
                impl <#gen_params $($gen_params)*> #ident #gen_type for $self #gen_where $($gen_where)* {
                    #(#streams)*
                }
            };

            (* $ty:ty) => {
                #(#macros!(#idents $ty);)*
            };

            #(#cases)*
        }

        #[allow(unused_imports)]
        pub(crate) use #macros;
    }
    .into()
}

#[proc_macro_attribute]
pub fn forward_def(attr: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    macro_rules! forward {
        ($item:expr, $def:expr) => {{
            let item = $item;
            let def = $def;

            let ident = &item.ident;
            let generics = &item.generics;
            let gen_params = &item.generics.params;
            let (_, gen_type, gen_where) = item.generics.split_for_impl();

            let expr = &def.fwd.expr;
            let ty = &def.fwd.ty;
            let path = &def.path;
            let predicates = def.conditions.as_ref().map(|conditions| &conditions.predicates);

            let gen_where = match gen_where {
                Some(val) => {
                    let preds = &val.predicates;

                    quote! { #preds, #predicates }
                },
                None => quote! { #predicates },
            };

            let segs = path.segments.iter().take(path.segments.len().saturating_sub(1));
            let id = match path.segments.last() {
                Some(val) => &val.ident,
                None => {
                    return Error::new(Span::call_site(), "Failed to forward definition, path is empty")
                        .into_compile_error()
                        .into();
                },
            };

            let forward = get_forward_impl(ident, generics, expr, ty);
            let module = format_ident!("__forward_impl_{}_{}", &id, &ident);
            let macros = format_ident!("__forward_impl_{}", &id);

            quote! {
                #item

                #[doc(hidden)]
                #[allow(non_snake_case)]
                mod #module {
                    #forward

                    #macros!(@ #ident #gen_type, #ty, (#gen_params), (#gen_where));

                    use super::*;
                    use #(#segs::)*#macros;
                    use #path;
                }
            }
            .into()
        }};
    }

    let item = parse_macro_input!(item as ForwardDefItem);

    match item {
        ForwardDefItem::Struct(val) => forward!(val, parse_macro_input!(attr as ForwardDataDef)),
        ForwardDefItem::Enum(val) => forward!(val, parse_macro_input!(attr as ForwardDataDef)),
        ForwardDefItem::Union(val) => forward!(val, parse_macro_input!(attr as ForwardDataDef)),
        ForwardDefItem::Impl(val) => {
            let ForwardImplDef { fwd: _, idents: _ } = parse_macro_input!(attr as ForwardImplDef);

            let attrs = &val.attrs;
            let default = &val.defaultness;
            let unsafety = &val.unsafety;
            let generics = &val.generics;
            let interface = &val.trait_;
            let ty = &val.self_ty;
            let items = &val.items;

            let (gen_impl, gen_type, gen_where) = generics.split_for_impl();

            let interface = match interface {
                Some(val) => {
                    let x = &val.0;
                    let y = &val.1;
                    let z = &val.2;

                    quote! { #x #y #z }
                },
                None => quote! {},
            };

            quote! {
                #(#attrs)*
                #default #unsafety impl #gen_impl #interface #gen_type #ty #gen_where {
                    #(#items)*
                }
            }
            .into()
        },
    }
}

#[proc_macro_attribute]
pub fn forward_into(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    item
}

#[proc_macro_attribute]
pub fn forward_self(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    item
}

#[proc_macro_attribute]
pub fn forward_with(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    item
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

fn get_forward_impl(ident: &Ident, generics: &Generics, expr: &Expr, ty: &Type) -> TokenStream {
    let (gen_impl, gen_type, gen_where) = generics.split_for_impl();

    quote! {
        pub trait Forward {
            type Type;

            fn forward(self) -> Self::Type;

            fn forward_ref(&self) -> &Self::Type;

            fn forward_mut(&mut self) -> &mut Self::Type;
        }

        impl #gen_impl Forward for #ident #gen_type #gen_where {
            type Type = #ty;

            fn forward(self) -> Self::Type {
                #expr
            }

            fn forward_ref(&self) -> &Self::Type {
                &#expr
            }

            fn forward_mut(&mut self) -> &mut Self::Type {
                &mut #expr
            }
        }
    }
}

fn get_forward_type<'item>(interface: &ItemTrait, item: &'item TraitItemType) -> (&'item Ident, TokenStream) {
    let attrs = &item.attrs;
    let ident = &item.ident;

    let (gen_impl, gen_type, _) = item.generics.split_for_impl();

    let id = &interface.ident;
    let (_, gen_type_id, _) = interface.generics.split_for_impl();

    (
        ident,
        quote! {
            #(#attrs)*
            type #ident #gen_impl = <$ty as #id #gen_type_id>::#ident #gen_type;
        },
    )
}

fn get_forward_const<'item>(interface: &ItemTrait, item: &'item TraitItemConst) -> (&'item Ident, TokenStream) {
    let attrs = &item.attrs;
    let ident = &item.ident;
    let ty = &item.ty;

    let id = &interface.ident;
    let (_, gen_type_id, _) = interface.generics.split_for_impl();

    (
        ident,
        quote! {
            #(#attrs)*
            const #ident: #ty = <$ty as #id #gen_type_id>::#ident;
        },
    )
}

fn get_forward_fn<'item>(_: &ItemTrait, item: &'item TraitItemFn) -> Result<(&'item Ident, TokenStream)> {
    let TraitItemFn {
        attrs,
        sig,
        default: _,
        semi_token: _,
    } = &item;

    let Signature {
        constness,
        asyncness,
        unsafety,
        abi,
        fn_token: _,
        ident,
        generics,
        paren_token: _,
        inputs,
        variadic: _,
        output,
    } = sig;

    let recv = inputs.iter().find_map(|arg| match arg {
        FnArg::Receiver(val) => Some(val),
        FnArg::Typed(_) => None,
    });

    let decl = inputs
        .iter()
        .filter_map(|arg| match arg {
            FnArg::Receiver(_) => None,
            FnArg::Typed(val) => Some(val),
        })
        .enumerate()
        .map(|(idx, val)| {
            let attrs = &val.attrs;
            let ty = &val.ty;

            let ident = format_ident!("arg{}", idx);

            quote! { #(#attrs)* #ident: #ty }
        });

    let def = inputs
        .iter()
        .filter_map(|arg| match arg {
            FnArg::Receiver(_) => None,
            FnArg::Typed(val) => Some(val),
        })
        .enumerate()
        .map(|(idx, val)| {
            let ident = format_ident!("arg{}", idx);
            let expr = quote! { #ident };

            let arg = get_forward_argument(ForwardExpression::Raw(expr), &val.ty);

            Ok(arg?.stream())
        })
        .collect::<Result<Vec<TokenStream>>>()?;

    let forward_into = attrs.iter().any(|attr| attr.path().is_ident("forward_into"));
    let forward_self = attrs.iter().any(|attr| attr.path().is_ident("forward_self"));
    let forward_with = attrs.iter().find(|attr| attr.path().is_ident("forward_with"));

    let expr = match recv {
        Some(val) if val.reference.is_some() && val.mutability.is_some() => {
            if forward_into {
                quote! {
                    self.forward_mut().#ident(#(#def),*).into()
                }
            } else if forward_self {
                quote! {
                    self.forward_mut().#ident(#(#def),*);
                    self
                }
            } else if let Some(forward_with) = forward_with {
                let ExprClosure {
                    attrs: _,
                    lifetimes,
                    constness,
                    movability,
                    asyncness,
                    capture,
                    or1_token: _,
                    inputs,
                    or2_token: _,
                    output,
                    body,
                } = get_forward_with_closure(&forward_with.meta)?;

                quote! {
                    (#lifetimes #constness #movability #asyncness #capture |#inputs| #output #body)
                    (self.forward_mut().#ident(#(#def),*))
                }
            } else {
                quote! {
                    self.forward_mut().#ident(#(#def),*)
                }
            }
        },
        Some(val) if val.reference.is_some() => {
            if forward_into {
                quote! {
                    self.forward_ref().#ident(#(#def),*).into()
                }
            } else if forward_self {
                quote! {
                    self.forward_ref().#ident(#(#def),*);
                    self
                }
            } else if let Some(forward_with) = forward_with {
                let ExprClosure {
                    attrs: _,
                    lifetimes,
                    constness,
                    movability,
                    asyncness,
                    capture,
                    or1_token: _,
                    inputs,
                    or2_token: _,
                    output,
                    body,
                } = get_forward_with_closure(&forward_with.meta)?;

                quote! {
                    (#lifetimes #constness #movability #asyncness #capture |#inputs| #output #body)
                    (self.forward_ref().#ident(#(#def),*))
                }
            } else {
                quote! {
                    self.forward_ref().#ident(#(#def),*)
                }
            }
        },
        Some(_) => {
            if forward_into {
                quote! {
                    self.forward().#ident(#(#def),*).into()
                }
            } else if forward_self {
                quote! {
                    self.forward().#ident(#(#def),*);
                    self
                }
            } else if let Some(forward_with) = forward_with {
                let ExprClosure {
                    attrs: _,
                    lifetimes,
                    constness,
                    movability,
                    asyncness,
                    capture,
                    or1_token: _,
                    inputs,
                    or2_token: _,
                    output,
                    body,
                } = get_forward_with_closure(&forward_with.meta)?;

                quote! {
                    (#lifetimes #constness #movability #asyncness #capture |#inputs| #output #body)
                    (self.forward().#ident(#(#def),*))
                }
            } else {
                quote! {
                    self.forward().#ident(#(#def),*)
                }
            }
        },
        None => quote! {
            <$ty>::#ident(#(#def),*).into()
        },
    };

    let recv = match recv {
        Some(val) => quote! { #val, },
        None => quote! {},
    };

    Ok((
        ident,
        quote! {
            #[allow(unused_mut)]
            #(#attrs)*
            #constness #asyncness #unsafety #abi fn #ident #generics (#recv #(#decl),*) #output {
                #expr
            }
        },
    ))
}

fn get_forward_with_closure(meta: &Meta) -> Result<ExprClosure> {
    match meta {
        Meta::Path(_) => Err(Error::new(
            Span::call_site(),
            "Failed to forward with, expected closure expression",
        )),
        Meta::List(val) => syn::parse2::<ExprClosure>(val.tokens.clone()),
        Meta::NameValue(_) => Err(Error::new(
            Span::call_site(),
            "Failed to forward with, expected closure expression",
        )),
    }
}

fn get_forward_argument(expr: ForwardExpression, ty: &Type) -> Result<ForwardArgument> {
    match ty {
        Type::Path(val) => {
            if val.path.segments.last().is_some_and(|seg| seg.ident == "Self") {
                return Ok(match expr {
                    ForwardExpression::Raw(val) => ForwardArgument::Alt(quote! { #val.forward() }),
                    ForwardExpression::Ref(val) => ForwardArgument::Alt(quote! { #val.forward_ref() }),
                    ForwardExpression::Mut(val) => ForwardArgument::Alt(quote! { #val.forward_mut() }),
                });
            }

            if val.path.segments.first().is_some_and(|seg| seg.ident == "Self") {
                return Ok(ForwardArgument::Alt(quote! { #expr.into() }));
            }

            Ok(ForwardArgument::Raw(expr.stream()))
        },
        Type::Array(val) => match get_forward_argument(expr, &val.elem)? {
            ForwardArgument::Raw(val) => Ok(ForwardArgument::Raw(val)),
            ForwardArgument::Alt(_) => Err(Error::new(
                Span::call_site(),
                "Failed to forward argument, alternating in array is unsupported",
            )),
        },
        Type::Slice(val) => match get_forward_argument(expr, &val.elem)? {
            ForwardArgument::Raw(val) => Ok(ForwardArgument::Raw(val)),
            ForwardArgument::Alt(_) => Err(Error::new(
                Span::call_site(),
                "Failed to forward argument, alternating in slice is unsupported",
            )),
        },
        Type::Tuple(val) => {
            let args = val
                .elems
                .iter()
                .enumerate()
                .map(|(idx, elem)| get_forward_argument(ForwardExpression::Raw(quote! { #expr.#idx }), elem))
                .collect::<Result<Vec<ForwardArgument>>>()?;

            if args.iter().all(|arg| match arg {
                ForwardArgument::Raw(_) => true,
                ForwardArgument::Alt(_) => false,
            }) {
                return Ok(ForwardArgument::Raw(expr.stream()));
            }

            let args = args.iter().map(|arg| match arg {
                ForwardArgument::Raw(val) => quote! { #val },
                ForwardArgument::Alt(val) => quote! { #val },
            });

            Ok(ForwardArgument::Alt(quote! { #(#args),* }))
        },
        Type::Group(val) => get_forward_argument(ForwardExpression::Raw(expr.stream()), &val.elem),
        Type::Paren(val) => get_forward_argument(ForwardExpression::Raw(expr.stream()), &val.elem),
        Type::Ptr(val) => get_forward_argument(
            match val.mutability {
                Some(_) => ForwardExpression::Mut(expr.stream()),
                None => ForwardExpression::Ref(expr.stream()),
            },
            &val.elem,
        ),
        Type::Reference(val) => get_forward_argument(
            match val.mutability {
                Some(_) => ForwardExpression::Mut(expr.stream()),
                None => ForwardExpression::Ref(expr.stream()),
            },
            &val.elem,
        ),
        Type::Never(_) => Err(Error::new(
            Span::call_site(),
            "Failed to forward argument, never type is unsupported",
        )),
        Type::Macro(_) => Err(Error::new(
            Span::call_site(),
            "Failed to forward argument, macro type is unsupported",
        )),
        Type::BareFn(_) => Ok(ForwardArgument::Raw(expr.stream())),
        Type::ImplTrait(_) => Ok(ForwardArgument::Raw(expr.stream())),
        Type::TraitObject(_) => Ok(ForwardArgument::Raw(expr.stream())),
        Type::Verbatim(_) => Err(Error::new(Span::call_site(), "Failed to forward argument, verbatim was found")),
        _ => todo!(),
    }
}
