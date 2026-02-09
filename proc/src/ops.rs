use proc_macro2::TokenStream;
use quote::{ToTokens, quote};
use syn::{
    Expr, Generics, Ident, Path, Result, Token, Type, WhereClause, braced, bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse_quote,
    punctuated::Punctuated,
    token::{Brace, Bracket, Paren},
};

use crate::get_normalized_generics;

mod kw {
    syn::custom_keyword!(stdmut);
    syn::custom_keyword!(stdbin);
    syn::custom_keyword!(stdun);

    syn::custom_keyword!(ndmut);
    syn::custom_keyword!(ndbin);
    syn::custom_keyword!(ndun);

    syn::custom_keyword!(ext);
}

#[allow(clippy::large_enum_variant)]
pub enum Ops {
    StdMutable(OpsImpl<OpsKindMutable>),
    StdBinary(OpsImpl<OpsKindBinary>),
    StdUnary(OpsImpl<OpsKindUnary>),
    NdMutable,
    NdBinary,
    NdUnary,
}

#[allow(clippy::large_enum_variant)]
#[allow(clippy::enum_variant_names)]
pub enum OpsAuto {
    StdMutable(OpsImplAuto<OpsKindMutable>),
    StdBinary(OpsImplAuto<OpsKindBinary>),
    StdUnary(OpsImplAuto<OpsKindUnary>),
}

pub struct OpsKindMutable;
pub struct OpsKindBinary;
pub struct OpsKindUnary;

#[allow(unused)]
pub struct OpsImpl<Kind: OpsKind> {
    pub generics: Generics,
    pub signature: Kind::Signature,
    pub colon: Token![,],
    pub definitions: Punctuated<OpsDefinition<Kind>, Token![,]>,
}

#[allow(unused)]
pub struct OpsImplAuto<Kind: OpsKind> {
    pub generics: Generics,
    pub signature: Kind::Signature,
    pub colon: Token![,],
    pub expression: Kind::Expression,
    pub ops_bracket: Bracket,
    pub ops: Punctuated<Kind::Operation, Token![,]>,
}

#[allow(unused)]
pub struct OpsSignatureMutable {
    pub paren: Paren,
    pub lhs_vmut: Option<Token![mut]>,
    pub lhs_ident: Ident,
    pub lhs_colon: Token![:],
    pub lhs_ref: Token![&],
    pub lhs_mut: Token![mut],
    pub lhs_type: Type,
    pub delim: Token![,],
    pub rhs_vmut: Option<Token![mut]>,
    pub rhs_star: Option<Token![*]>,
    pub rhs_ident: Ident,
    pub rhs_colon: Token![:],
    pub rhs_ref: Option<Token![&]>,
    pub rhs_type: Type,
}

#[allow(unused)]
pub struct OpsSignatureBinary {
    pub paren: Paren,
    pub lhs_vmut: Option<Token![mut]>,
    pub lhs_star: Option<Token![*]>,
    pub lhs_ident: Ident,
    pub lhs_colon: Token![:],
    pub lhs_ref: Option<Token![&]>,
    pub lhs_type: Type,
    pub delim: Token![,],
    pub rhs_vmut: Option<Token![mut]>,
    pub rhs_star: Option<Token![*]>,
    pub rhs_ident: Ident,
    pub rhs_colon: Token![:],
    pub rhs_ref: Option<Token![&]>,
    pub rhs_type: Type,
    pub arrow: Token![->],
    pub ty: Type,
}

#[allow(unused)]
pub struct OpsSignatureUnary {
    pub paren: Paren,
    pub lhs_vmut: Option<Token![mut]>,
    pub lhs_star: Option<Token![*]>,
    pub lhs_ident: Ident,
    pub lhs_colon: Token![:],
    pub lhs_ref: Option<Token![&]>,
    pub lhs_type: Type,
    pub arrow: Token![->],
    pub ty: Type,
}

#[allow(unused)]
pub struct OpsExpressionMutable {
    pub lhs_paren: Paren,
    pub lhs_expr: Expr,
    pub rhs_paren: Paren,
    pub rhs_expr: Expr,
}

#[allow(unused)]
pub struct OpsExpressionBinary {
    pub lhs_paren: Paren,
    pub lhs_expr: Expr,
    pub rhs_paren: Paren,
    pub rhs_expr: Expr,
}

#[allow(unused)]
pub struct OpsExpressionUnary {
    pub self_paren: Paren,
    pub self_expr: Expr,
}

pub enum OpsDefinition<Kind: OpsKind> {
    Standard(OpsDefinitionStandard<Kind>),
    Extended(OpsDefinitionExtended<Kind>),
}

#[allow(unused)]
pub struct OpsDefinitionStandard<Kind: OpsKind> {
    pub op: Kind::Operation,
    pub expr: Expr,
}

#[allow(unused)]
pub struct OpsDefinitionExtended<Kind: OpsKind> {
    pub op: Kind::Operation,
    pub ext: kw::ext,
    pub brace: Brace,
    pub elems: Punctuated<OpsDefinitionExtendedElem<Kind>, Token![;]>,
}

#[allow(unused)]
pub struct OpsDefinitionExtendedElem<Kind: OpsKind> {
    pub qualifier: Kind::Qualifier,
    pub expr: Expr,
    pub conditions: WhereClause,
}

#[allow(unused)]
pub struct OpsQualifierMutable {
    pub paren: Paren,
    pub lhs: Token![&],
    pub rhs: OpsQualifier,
}

#[allow(unused)]
pub struct OpsQualifierBinary {
    pub paren: Paren,
    pub lhs: OpsQualifier,
    pub rhs: OpsQualifier,
}

#[allow(unused)]
pub struct OpsQualifierUnary {
    pub paren: Paren,
    pub value: OpsQualifier,
}

#[derive(Clone, Copy)]
pub enum OpsQualifier {
    Raw,
    Ref,
}

#[derive(Clone, Copy)]
pub enum OpsMutable {
    Add(Token![+=]),
    Sub(Token![-=]),
    Mul(Token![*=]),
    Div(Token![/=]),
    Rem(Token![%=]),
    BitOr(Token![|=]),
    BitAnd(Token![&=]),
    BitXor(Token![^=]),
    Shl(Token![<<=]),
    Shr(Token![>>=]),
}

#[derive(Clone, Copy)]
pub enum OpsBinary {
    Add(Token![+]),
    Sub(Token![-]),
    Mul(Token![*]),
    Div(Token![/]),
    Rem(Token![%]),
    BitOr(Token![|]),
    BitAnd(Token![&]),
    BitXor(Token![^]),
    Shl(Token![<<]),
    Shr(Token![>>]),
}

#[derive(Clone, Copy)]
pub enum OpsUnary {
    Neg(Token![-]),
    Not(Token![!]),
}

pub trait OpsKind {
    type Operation: Parse;
    type Signature: Parse;
    type Expression: Parse;
    type Qualifier: Parse;
}

#[rustfmt::skip]
impl OpsKind for OpsKindMutable {
    type Operation = OpsMutable;
    type Signature = OpsSignatureMutable;
    type Expression = OpsExpressionMutable;
    type Qualifier = OpsQualifierMutable;
}

#[rustfmt::skip]
impl OpsKind for OpsKindBinary {
    type Operation = OpsBinary;
    type Signature = OpsSignatureBinary;
    type Expression = OpsExpressionBinary;
    type Qualifier = OpsQualifierBinary;
}

#[rustfmt::skip]
impl OpsKind for OpsKindUnary {
    type Operation = OpsUnary;
    type Signature = OpsSignatureUnary;
    type Expression = OpsExpressionUnary;
    type Qualifier = OpsQualifierUnary;
}

impl Parse for Ops {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<Token![@]>()?;

        let lookahead = input.lookahead1();

        if lookahead.peek(kw::stdmut) {
            input.parse::<kw::stdmut>()?;
            input.parse::<OpsImpl<OpsKindMutable>>().map(Self::StdMutable)
        } else if lookahead.peek(kw::stdbin) {
            input.parse::<kw::stdbin>()?;
            input.parse::<OpsImpl<OpsKindBinary>>().map(Self::StdBinary)
        } else if lookahead.peek(kw::stdun) {
            input.parse::<kw::stdun>()?;
            input.parse::<OpsImpl<OpsKindUnary>>().map(Self::StdUnary)
        } else if lookahead.peek(kw::ndmut) {
            input.parse::<kw::ndmut>()?;

            Ok(Self::NdMutable)
        } else if lookahead.peek(kw::ndbin) {
            input.parse::<kw::ndbin>()?;

            Ok(Self::NdBinary)
        } else if lookahead.peek(kw::ndun) {
            input.parse::<kw::ndun>()?;

            Ok(Self::NdUnary)
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsAuto {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<Token![@]>()?;

        let lookahead = input.lookahead1();

        if lookahead.peek(kw::stdmut) {
            input.parse::<kw::stdmut>()?;
            input.parse::<OpsImplAuto<OpsKindMutable>>().map(Self::StdMutable)
        } else if lookahead.peek(kw::stdbin) {
            input.parse::<kw::stdbin>()?;
            input.parse::<OpsImplAuto<OpsKindBinary>>().map(Self::StdBinary)
        } else if lookahead.peek(kw::stdun) {
            input.parse::<kw::stdun>()?;
            input.parse::<OpsImplAuto<OpsKindUnary>>().map(Self::StdUnary)
        } else {
            Err(lookahead.error())
        }
    }
}

impl<Kind: OpsKind> Parse for OpsImpl<Kind> {
    fn parse(input: ParseStream) -> Result<Self> {
        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;

        Ok(Self {
            generics: get_normalized_generics(Generics {
                where_clause: gen_where,
                ..gen_
            }),
            signature: input.parse()?,
            colon: input.parse()?,
            definitions: input.parse_terminated(OpsDefinition::parse, Token![,])?,
        })
    }
}

impl<Kind: OpsKind> Parse for OpsImplAuto<Kind> {
    fn parse(input: ParseStream) -> Result<Self> {
        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;

        let content;

        Ok(Self {
            generics: Generics {
                where_clause: gen_where,
                ..gen_
            },
            signature: input.parse()?,
            colon: input.parse()?,
            expression: input.parse()?,
            ops_bracket: bracketed!(content in input),
            ops: content.parse_terminated(Kind::Operation::parse, Token![,])?,
        })
    }
}

impl Parse for OpsSignatureMutable {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            paren: parenthesized!(content in input),
            lhs_vmut: content.parse().ok(),
            lhs_ident: content.parse()?,
            lhs_colon: content.parse()?,
            lhs_ref: content.parse()?,
            lhs_mut: content.parse()?,
            lhs_type: content.parse()?,
            delim: content.parse()?,
            rhs_vmut: content.parse().ok(),
            rhs_star: content.parse().ok(),
            rhs_ident: content.parse()?,
            rhs_colon: content.parse()?,
            rhs_ref: content.parse().ok(),
            rhs_type: content.parse()?,
        })
    }
}

impl Parse for OpsSignatureBinary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            paren: parenthesized!(content in input),
            lhs_vmut: content.parse().ok(),
            lhs_star: content.parse().ok(),
            lhs_ident: content.parse()?,
            lhs_colon: content.parse()?,
            lhs_ref: content.parse().ok(),
            lhs_type: content.parse()?,
            delim: content.parse()?,
            rhs_vmut: content.parse().ok(),
            rhs_star: content.parse().ok(),
            rhs_ident: content.parse()?,
            rhs_colon: content.parse()?,
            rhs_ref: content.parse().ok(),
            rhs_type: content.parse()?,
            arrow: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl Parse for OpsSignatureUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            paren: parenthesized!(content in input),
            lhs_vmut: content.parse().ok(),
            lhs_star: content.parse().ok(),
            lhs_ident: content.parse()?,
            lhs_colon: content.parse()?,
            lhs_ref: content.parse().ok(),
            lhs_type: content.parse()?,
            arrow: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl Parse for OpsExpressionMutable {
    fn parse(input: ParseStream) -> Result<Self> {
        let lhs_content;
        let rhs_content;

        Ok(Self {
            lhs_paren: parenthesized!(lhs_content in input),
            lhs_expr: lhs_content.parse()?,
            rhs_paren: parenthesized!(rhs_content in input),
            rhs_expr: rhs_content.parse()?,
        })
    }
}

impl Parse for OpsExpressionBinary {
    fn parse(input: ParseStream) -> Result<Self> {
        let lhs_content;
        let rhs_content;

        Ok(Self {
            lhs_paren: parenthesized!(lhs_content in input),
            lhs_expr: lhs_content.parse()?,
            rhs_paren: parenthesized!(rhs_content in input),
            rhs_expr: rhs_content.parse()?,
        })
    }
}

impl Parse for OpsExpressionUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            self_paren: parenthesized!(content in input),
            self_expr: content.parse()?,
        })
    }
}

impl<Kind: OpsKind> Parse for OpsDefinition<Kind> {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek2(kw::ext) {
            Ok(Self::Standard(input.parse()?))
        } else {
            Ok(Self::Extended(input.parse()?))
        }
    }
}

impl<Kind: OpsKind> Parse for OpsDefinitionStandard<Kind> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            op: input.parse()?,
            expr: input.parse()?,
        })
    }
}

impl<Kind: OpsKind> Parse for OpsDefinitionExtended<Kind> {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            op: input.parse()?,
            ext: input.parse()?,
            brace: braced!(content in input),
            elems: content.parse_terminated(OpsDefinitionExtendedElem::<Kind>::parse, Token![;])?,
        })
    }
}

impl<Kind: OpsKind> Parse for OpsDefinitionExtendedElem<Kind> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            qualifier: input.parse()?,
            expr: input.parse()?,
            conditions: input.parse()?,
        })
    }
}

impl Parse for OpsQualifierMutable {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            paren: parenthesized!(content in input),
            lhs: content.parse()?,
            rhs: content.parse()?,
        })
    }
}

impl Parse for OpsQualifierBinary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            paren: parenthesized!(content in input),
            lhs: content.parse()?,
            rhs: content.parse()?,
        })
    }
}

impl Parse for OpsQualifierUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            paren: parenthesized!(content in input),
            value: content.parse()?,
        })
    }
}

impl Parse for OpsQualifier {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(Token![^]) {
            input.parse::<Token![^]>()?;
            input.parse::<Token![^]>().map(|_| OpsQualifier::Raw)
        } else if lookahead.peek(Token![&]) {
            input.parse::<Token![&]>()?;
            input.parse::<Token![&]>().map(|_| OpsQualifier::Ref)
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsMutable {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(Token![+=]) {
            input.parse::<Token![+=]>().map(Self::Add)
        } else if lookahead.peek(Token![-=]) {
            input.parse::<Token![-=]>().map(Self::Sub)
        } else if lookahead.peek(Token![*=]) {
            input.parse::<Token![*=]>().map(Self::Mul)
        } else if lookahead.peek(Token![/=]) {
            input.parse::<Token![/=]>().map(Self::Div)
        } else if lookahead.peek(Token![%=]) {
            input.parse::<Token![%=]>().map(Self::Rem)
        } else if lookahead.peek(Token![|=]) {
            input.parse::<Token![|=]>().map(Self::BitOr)
        } else if lookahead.peek(Token![&=]) {
            input.parse::<Token![&=]>().map(Self::BitAnd)
        } else if lookahead.peek(Token![^=]) {
            input.parse::<Token![^=]>().map(Self::BitXor)
        } else if lookahead.peek(Token![<<=]) {
            input.parse::<Token![<<=]>().map(Self::Shl)
        } else if lookahead.peek(Token![>>=]) {
            input.parse::<Token![>>=]>().map(Self::Shr)
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsBinary {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(Token![+]) {
            input.parse::<Token![+]>().map(Self::Add)
        } else if lookahead.peek(Token![-]) {
            input.parse::<Token![-]>().map(Self::Sub)
        } else if lookahead.peek(Token![*]) {
            input.parse::<Token![*]>().map(Self::Mul)
        } else if lookahead.peek(Token![/]) {
            input.parse::<Token![/]>().map(Self::Div)
        } else if lookahead.peek(Token![%]) {
            input.parse::<Token![%]>().map(Self::Rem)
        } else if lookahead.peek(Token![|]) {
            input.parse::<Token![|]>().map(Self::BitOr)
        } else if lookahead.peek(Token![&]) {
            input.parse::<Token![&]>().map(Self::BitAnd)
        } else if lookahead.peek(Token![^]) {
            input.parse::<Token![^]>().map(Self::BitXor)
        } else if lookahead.peek(Token![<<]) {
            input.parse::<Token![<<]>().map(Self::Shl)
        } else if lookahead.peek(Token![>>]) {
            input.parse::<Token![>>]>().map(Self::Shr)
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(Token![-]) {
            input.parse::<Token![-]>().map(Self::Neg)
        } else if lookahead.peek(Token![!]) {
            input.parse::<Token![!]>().map(Self::Not)
        } else {
            Err(lookahead.error())
        }
    }
}

impl ToTokens for OpsImpl<OpsKindMutable> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            op: &'ops OpsMutable,
            generics: &'ops Generics,
            signature: &'ops OpsSignatureMutable,
            expr: &'ops Expr,
            conditions: Option<&'ops WhereClause>,
        }

        fn get_impl(spec: OpsSpec, rhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.get_ident();
            let path = spec.op.get_path();

            let (gen_impl, _, gen_where) = spec.generics.split_for_impl();

            let predicates = match spec.conditions {
                Some(val) => {
                    let predicates = &val.predicates;

                    quote! { #predicates }
                },
                None => quote! {},
            };

            let gen_where = match gen_where {
                Some(val) => quote! { #val, #predicates },
                None => quote! { where #predicates },
            };

            let lhs_mut = &spec.signature.lhs_vmut;
            let lhs_ident = &spec.signature.lhs_ident;
            let lhs_type = &spec.signature.lhs_type;
            let rhs_mut = &spec.signature.rhs_vmut;
            let rhs_ident = &spec.signature.rhs_ident;
            let rhs_type = &spec.signature.rhs_type;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path<#rhs_ref #rhs_type> for #lhs_type #gen_where {
                    fn #ident(&mut self, rhs: #rhs_ref #rhs_type) {
                        (|#lhs_mut #lhs_ident: &mut #lhs_type, #rhs_mut #rhs_ident: #rhs_ref #rhs_type| { #expr })(self, rhs);
                    }
                }
            }
        }

        let rhs_star = self.signature.rhs_star.is_some();
        let rhs_ref = self.signature.rhs_ref.is_some();

        let some = Some(Default::default());
        let none = None;

        for definition in self.definitions.iter().filter_map(|elem| match elem {
            OpsDefinition::Standard(val) => Some(val),
            OpsDefinition::Extended(_) => None,
        }) {
            let spec = OpsSpec {
                op: &definition.op,
                generics: &self.generics,
                signature: &self.signature,
                expr: &definition.expr,
                conditions: None,
            };

            match rhs_ref {
                true => match rhs_star {
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

        for definition in self.definitions.iter().filter_map(|elem| match elem {
            OpsDefinition::Standard(_) => None,
            OpsDefinition::Extended(val) => Some(val),
        }) {
            for elem in &definition.elems {
                let spec = OpsSpec {
                    op: &definition.op,
                    generics: &self.generics,
                    signature: &self.signature,
                    expr: &elem.expr,
                    conditions: Some(&elem.conditions),
                };

                match elem.qualifier.rhs {
                    OpsQualifier::Raw => {
                        tokens.extend(get_impl(spec, none));
                    },
                    OpsQualifier::Ref => {
                        tokens.extend(get_impl(spec, some));
                    },
                }
            }
        }
    }
}

impl ToTokens for OpsImpl<OpsKindBinary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            op: &'ops OpsBinary,
            generics: &'ops Generics,
            signature: &'ops OpsSignatureBinary,
            expr: &'ops Expr,
            conditions: Option<&'ops WhereClause>,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>, rhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.get_ident();
            let path = spec.op.get_path();

            let (gen_impl, _, gen_where) = spec.generics.split_for_impl();

            let predicates = match spec.conditions {
                Some(val) => {
                    let predicates = &val.predicates;

                    quote! { #predicates }
                },
                None => quote! {},
            };

            let gen_where = match gen_where {
                Some(val) => quote! { #val, #predicates },
                None => quote! { where #predicates },
            };

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

        let lhs_star = self.signature.lhs_star.is_some();
        let rhs_star = self.signature.lhs_star.is_some();

        let lhs_ref = self.signature.lhs_ref.is_some();
        let rhs_ref = self.signature.rhs_ref.is_some();

        let some = Some(Default::default());
        let none = None;

        for definition in self.definitions.iter().filter_map(|elem| match elem {
            OpsDefinition::Standard(val) => Some(val),
            OpsDefinition::Extended(_) => None,
        }) {
            let spec = OpsSpec {
                op: &definition.op,
                generics: &self.generics,
                signature: &self.signature,
                expr: &definition.expr,
                conditions: None,
            };

            match (lhs_ref, rhs_ref) {
                (true, true) => match (lhs_star, rhs_star) {
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
                (true, false) => match lhs_star {
                    true => {
                        tokens.extend(get_impl(spec, some, none));
                        tokens.extend(get_impl(spec, none, none));
                    },
                    false => {
                        tokens.extend(get_impl(spec, some, none));
                    },
                },
                (false, true) => match rhs_star {
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

        for definition in self.definitions.iter().filter_map(|elem| match elem {
            OpsDefinition::Standard(_) => None,
            OpsDefinition::Extended(val) => Some(val),
        }) {
            for elem in &definition.elems {
                let spec = OpsSpec {
                    op: &definition.op,
                    generics: &self.generics,
                    signature: &self.signature,
                    expr: &elem.expr,
                    conditions: Some(&elem.conditions),
                };

                match (elem.qualifier.lhs, elem.qualifier.rhs) {
                    (OpsQualifier::Raw, OpsQualifier::Raw) => {
                        tokens.extend(get_impl(spec, none, none));
                    },
                    (OpsQualifier::Raw, OpsQualifier::Ref) => {
                        tokens.extend(get_impl(spec, none, some));
                    },
                    (OpsQualifier::Ref, OpsQualifier::Raw) => {
                        tokens.extend(get_impl(spec, some, none));
                    },
                    (OpsQualifier::Ref, OpsQualifier::Ref) => {
                        tokens.extend(get_impl(spec, some, some));
                    },
                }
            }
        }
    }
}

impl ToTokens for OpsImpl<OpsKindUnary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            op: &'ops OpsUnary,
            generics: &'ops Generics,
            signature: &'ops OpsSignatureUnary,
            expr: &'ops Expr,
            conditions: Option<&'ops WhereClause>,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.get_ident();
            let path = spec.op.get_path();

            let (gen_impl, _, gen_where) = spec.generics.split_for_impl();

            let predicates = match spec.conditions {
                Some(val) => {
                    let predicates = &val.predicates;

                    quote! { #predicates }
                },
                None => quote! {},
            };

            let gen_where = match gen_where {
                Some(val) => quote! { #val, #predicates },
                None => quote! { where #predicates },
            };

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

        let lhs_star = self.signature.lhs_star.is_some();
        let lhs_ref = self.signature.lhs_ref.is_some();

        let some = Some(Default::default());
        let none = None;

        for definition in self.definitions.iter().filter_map(|elem| match elem {
            OpsDefinition::Standard(val) => Some(val),
            OpsDefinition::Extended(_) => None,
        }) {
            let spec = OpsSpec {
                op: &definition.op,
                generics: &self.generics,
                signature: &self.signature,
                expr: &definition.expr,
                conditions: None,
            };

            match lhs_ref {
                true => match lhs_star {
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

        for definition in self.definitions.iter().filter_map(|elem| match elem {
            OpsDefinition::Standard(_) => None,
            OpsDefinition::Extended(val) => Some(val),
        }) {
            for elem in &definition.elems {
                let spec = OpsSpec {
                    op: &definition.op,
                    generics: &self.generics,
                    signature: &self.signature,
                    expr: &elem.expr,
                    conditions: Some(&elem.conditions),
                };

                match elem.qualifier.value {
                    OpsQualifier::Raw => {
                        tokens.extend(get_impl(spec, none));
                    },
                    OpsQualifier::Ref => {
                        tokens.extend(get_impl(spec, some));
                    },
                }
            }
        }
    }
}

impl ToTokens for OpsMutable {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            OpsMutable::Add(op) => tokens.extend(quote! { #op }),
            OpsMutable::Sub(op) => tokens.extend(quote! { #op }),
            OpsMutable::Mul(op) => tokens.extend(quote! { #op }),
            OpsMutable::Div(op) => tokens.extend(quote! { #op }),
            OpsMutable::Rem(op) => tokens.extend(quote! { #op }),
            OpsMutable::BitOr(op) => tokens.extend(quote! { #op }),
            OpsMutable::BitXor(op) => tokens.extend(quote! { #op }),
            OpsMutable::BitAnd(op) => tokens.extend(quote! { #op }),
            OpsMutable::Shl(op) => tokens.extend(quote! { #op }),
            OpsMutable::Shr(op) => tokens.extend(quote! { #op }),
        }
    }
}

impl ToTokens for OpsBinary {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            OpsBinary::Add(op) => tokens.extend(quote! { #op }),
            OpsBinary::Sub(op) => tokens.extend(quote! { #op }),
            OpsBinary::Mul(op) => tokens.extend(quote! { #op }),
            OpsBinary::Div(op) => tokens.extend(quote! { #op }),
            OpsBinary::Rem(op) => tokens.extend(quote! { #op }),
            OpsBinary::BitOr(op) => tokens.extend(quote! { #op }),
            OpsBinary::BitXor(op) => tokens.extend(quote! { #op }),
            OpsBinary::BitAnd(op) => tokens.extend(quote! { #op }),
            OpsBinary::Shl(op) => tokens.extend(quote! { #op }),
            OpsBinary::Shr(op) => tokens.extend(quote! { #op }),
        }
    }
}

impl ToTokens for OpsUnary {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            OpsUnary::Neg(op) => tokens.extend(quote! { #op }),
            OpsUnary::Not(op) => tokens.extend(quote! { #op }),
        }
    }
}

impl OpsMutable {
    fn get_ident(&self) -> Ident {
        match self {
            OpsMutable::Add(_) => parse_quote! { add_assign },
            OpsMutable::Sub(_) => parse_quote! { sub_assign },
            OpsMutable::Mul(_) => parse_quote! { mul_assign },
            OpsMutable::Div(_) => parse_quote! { div_assign },
            OpsMutable::Rem(_) => parse_quote! { rem_assign },
            OpsMutable::BitOr(_) => parse_quote! { bitor_assign },
            OpsMutable::BitAnd(_) => parse_quote! { bitand_assign },
            OpsMutable::BitXor(_) => parse_quote! { bitxor_assign },
            OpsMutable::Shl(_) => parse_quote! { shl_assign },
            OpsMutable::Shr(_) => parse_quote! { shr_assign },
        }
    }

    fn get_path(&self) -> Path {
        match self {
            OpsMutable::Add(_) => parse_quote! { std::ops::AddAssign },
            OpsMutable::Sub(_) => parse_quote! { std::ops::SubAssign },
            OpsMutable::Mul(_) => parse_quote! { std::ops::MulAssign },
            OpsMutable::Div(_) => parse_quote! { std::ops::DivAssign },
            OpsMutable::Rem(_) => parse_quote! { std::ops::RemAssign },
            OpsMutable::BitOr(_) => parse_quote! { std::ops::BitOrAssign },
            OpsMutable::BitAnd(_) => parse_quote! { std::ops::BitAndAssign },
            OpsMutable::BitXor(_) => parse_quote! { std::ops::BitXorAssign },
            OpsMutable::Shl(_) => parse_quote! { std::ops::ShlAssign },
            OpsMutable::Shr(_) => parse_quote! { std::ops::ShrAssign },
        }
    }
}

impl OpsBinary {
    fn get_ident(&self) -> Ident {
        match self {
            OpsBinary::Add(_) => parse_quote! { add },
            OpsBinary::Sub(_) => parse_quote! { sub },
            OpsBinary::Mul(_) => parse_quote! { mul },
            OpsBinary::Div(_) => parse_quote! { div },
            OpsBinary::Rem(_) => parse_quote! { rem },
            OpsBinary::BitOr(_) => parse_quote! { bitor },
            OpsBinary::BitAnd(_) => parse_quote! { bitand },
            OpsBinary::BitXor(_) => parse_quote! { bitxor },
            OpsBinary::Shl(_) => parse_quote! { shl },
            OpsBinary::Shr(_) => parse_quote! { shr },
        }
    }

    fn get_path(&self) -> Path {
        match self {
            OpsBinary::Add(_) => parse_quote! { std::ops::Add },
            OpsBinary::Sub(_) => parse_quote! { std::ops::Sub },
            OpsBinary::Mul(_) => parse_quote! { std::ops::Mul },
            OpsBinary::Div(_) => parse_quote! { std::ops::Div },
            OpsBinary::Rem(_) => parse_quote! { std::ops::Rem },
            OpsBinary::BitOr(_) => parse_quote! { std::ops::BitOr },
            OpsBinary::BitAnd(_) => parse_quote! { std::ops::BitAnd },
            OpsBinary::BitXor(_) => parse_quote! { std::ops::BitXor },
            OpsBinary::Shl(_) => parse_quote! { std::ops::Shl },
            OpsBinary::Shr(_) => parse_quote! { std::ops::Shr },
        }
    }
}

impl OpsUnary {
    fn get_ident(&self) -> Ident {
        match self {
            OpsUnary::Neg(_) => parse_quote! { neg },
            OpsUnary::Not(_) => parse_quote! { not },
        }
    }

    fn get_path(&self) -> Path {
        match self {
            OpsUnary::Neg(_) => parse_quote! { std::ops::Neg },
            OpsUnary::Not(_) => parse_quote! { std::ops::Not },
        }
    }
}
