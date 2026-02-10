use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, quote};
use syn::{
    Error, Expr, Generics, Ident, PatType, Path, Result, Token, Type, WhereClause, braced, bracketed, parenthesized,
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
    StdMutable(OpsImpl<OpsStdKindMutable>),
    StdBinary(OpsImpl<OpsStdKindBinary>),
    StdUnary(OpsImpl<OpsStdKindUnary>),
    NdMutable(OpsImpl<OpsNdKindMutable>),
    NdBinary(OpsImpl<OpsNdKindBinary>),
    NdUnary(OpsImpl<OpsNdKindUnary>),
}

#[allow(clippy::large_enum_variant)]
#[allow(clippy::enum_variant_names)]
pub enum OpsAuto {
    StdMutable(OpsImplAuto<OpsStdKindMutable>),
    StdBinary(OpsImplAuto<OpsStdKindBinary>),
    StdUnary(OpsImplAuto<OpsStdKindUnary>),
    NdMutable(OpsImplAuto<OpsNdKindMutable>),
    NdBinary(OpsImplAuto<OpsNdKindBinary>),
    NdUnary(OpsImplAuto<OpsNdKindUnary>),
}

pub struct OpsStdKindMutable;
pub struct OpsStdKindBinary;
pub struct OpsStdKindUnary;
pub struct OpsNdKindMutable;
pub struct OpsNdKindBinary;
pub struct OpsNdKindUnary;

#[allow(unused)]
pub struct OpsImpl<Kind: OpsKind> {
    pub generics: Generics,
    pub signature: Kind::Signature,
    pub colon: Token![,],
    pub definitions: Punctuated<Kind::Definition, Token![,]>,
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
pub struct OpsStdSignatureMutable {
    pub paren: Paren,
    pub lhs_vmut: Option<Token![mut]>,
    pub lhs_ident: Ident,
    pub lhs_colon: Token![:],
    pub lhs_ref: Token![&],
    pub lhs_mut: Token![mut],
    pub lhs_type: Type,
    pub comma: Token![,],
    pub rhs_star: Option<Token![*]>,
    pub rhs_vmut: Option<Token![mut]>,
    pub rhs_ident: Ident,
    pub rhs_colon: Token![:],
    pub rhs_ref: Option<Token![&]>,
    pub rhs_type: Type,
}

#[allow(unused)]
pub struct OpsStdSignatureBinary {
    pub paren: Paren,
    pub lhs_star: Option<Token![*]>,
    pub lhs_vmut: Option<Token![mut]>,
    pub lhs_ident: Ident,
    pub lhs_colon: Token![:],
    pub lhs_ref: Option<Token![&]>,
    pub lhs_type: Type,
    pub comma: Token![,],
    pub rhs_star: Option<Token![*]>,
    pub rhs_vmut: Option<Token![mut]>,
    pub rhs_ident: Ident,
    pub rhs_colon: Token![:],
    pub rhs_ref: Option<Token![&]>,
    pub rhs_type: Type,
    pub arrow: Token![->],
    pub ty: Type,
}

#[allow(unused)]
pub struct OpsStdSignatureUnary {
    pub paren: Paren,
    pub self_star: Option<Token![*]>,
    pub self_vmut: Option<Token![mut]>,
    pub self_ident: Ident,
    pub self_colon: Token![:],
    pub self_ref: Option<Token![&]>,
    pub self_type: Type,
    pub arrow: Token![->],
    pub ty: Type,
}

#[allow(unused)]
pub struct OpsNdSignatureMutable {
    pub paren: Paren,
    pub lhs_pat: PatType,
    pub lhs_ty: Type,
    pub comma: Token![,],
    pub rhs_pat: PatType,
    pub rhs_ty: Type,
}

#[allow(unused)]
pub struct OpsNdSignatureBinary {
    pub paren: Paren,
    pub lhs_pat: PatType,
    pub lhs_ty: Type,
    pub comma: Token![,],
    pub rhs_pat: PatType,
    pub rhs_ty: Type,
    pub arrow: Token![->],
    pub ty: Type,
}

#[allow(unused)]
pub struct OpsNdSignatureUnary {
    pub paren: Paren,
    pub self_pat: PatType,
    pub self_ty: Type,
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

pub enum OpsDefinition<Operation: Parse, Qualifier: Parse> {
    Standard(OpsDefinitionStandard<Operation>),
    Extended(OpsDefinitionExtended<Operation, Qualifier>),
}

#[allow(unused)]
pub struct OpsDefinitionStandard<Operation: Parse> {
    pub op: Operation,
    pub expr: Expr,
}

#[allow(unused)]
pub struct OpsDefinitionExtended<Operation: Parse, Qualifier: Parse> {
    pub op: Operation,
    pub ext: kw::ext,
    pub brace: Brace,
    pub elems: Punctuated<OpsDefinitionExtendedElem<Qualifier>, Token![;]>,
}

#[allow(unused)]
pub struct OpsDefinitionExtendedElem<Qualifier: Parse> {
    pub qualifier: Qualifier,
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
    type Definition: Parse;
    type Expression: Parse;
    type Operation: Parse;
    type Signature: Parse;
}

impl OpsKind for OpsStdKindMutable {
    type Definition = OpsDefinition<Self::Operation, OpsQualifierMutable>;
    type Expression = OpsExpressionMutable;
    type Operation = OpsMutable;
    type Signature = OpsStdSignatureMutable;
}

impl OpsKind for OpsStdKindBinary {
    type Definition = OpsDefinition<Self::Operation, OpsQualifierBinary>;
    type Expression = OpsExpressionBinary;
    type Operation = OpsBinary;
    type Signature = OpsStdSignatureBinary;
}

impl OpsKind for OpsStdKindUnary {
    type Definition = OpsDefinition<Self::Operation, OpsQualifierUnary>;
    type Expression = OpsExpressionUnary;
    type Operation = OpsUnary;
    type Signature = OpsStdSignatureUnary;
}

impl OpsKind for OpsNdKindMutable {
    type Definition = OpsDefinitionStandard<Self::Operation>;
    type Expression = OpsExpressionMutable;
    type Operation = OpsMutable;
    type Signature = OpsNdSignatureMutable;
}

impl OpsKind for OpsNdKindBinary {
    type Definition = OpsDefinitionStandard<Self::Operation>;
    type Expression = OpsExpressionBinary;
    type Operation = OpsBinary;
    type Signature = OpsNdSignatureBinary;
}

impl OpsKind for OpsNdKindUnary {
    type Definition = OpsDefinitionStandard<Self::Operation>;
    type Expression = OpsExpressionUnary;
    type Operation = OpsUnary;
    type Signature = OpsNdSignatureUnary;
}

impl Parse for Ops {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<Token![@]>()?;

        let lookahead = input.lookahead1();

        if lookahead.peek(kw::stdmut) {
            input.parse::<kw::stdmut>()?;
            input.parse::<OpsImpl<OpsStdKindMutable>>().map(Self::StdMutable)
        } else if lookahead.peek(kw::stdbin) {
            input.parse::<kw::stdbin>()?;
            input.parse::<OpsImpl<OpsStdKindBinary>>().map(Self::StdBinary)
        } else if lookahead.peek(kw::stdun) {
            input.parse::<kw::stdun>()?;
            input.parse::<OpsImpl<OpsStdKindUnary>>().map(Self::StdUnary)
        } else if lookahead.peek(kw::ndmut) {
            input.parse::<kw::ndmut>()?;
            input.parse::<OpsImpl<OpsNdKindMutable>>().map(Self::NdMutable)
        } else if lookahead.peek(kw::ndbin) {
            input.parse::<kw::ndbin>()?;
            input.parse::<OpsImpl<OpsNdKindBinary>>().map(Self::NdBinary)
        } else if lookahead.peek(kw::ndun) {
            input.parse::<kw::ndun>()?;
            input.parse::<OpsImpl<OpsNdKindUnary>>().map(Self::NdUnary)
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
            input.parse::<OpsImplAuto<OpsStdKindMutable>>().map(Self::StdMutable)
        } else if lookahead.peek(kw::stdbin) {
            input.parse::<kw::stdbin>()?;
            input.parse::<OpsImplAuto<OpsStdKindBinary>>().map(Self::StdBinary)
        } else if lookahead.peek(kw::stdun) {
            input.parse::<kw::stdun>()?;
            input.parse::<OpsImplAuto<OpsStdKindUnary>>().map(Self::StdUnary)
        } else if lookahead.peek(kw::ndmut) {
            input.parse::<kw::ndmut>()?;
            input.parse::<OpsImplAuto<OpsNdKindMutable>>().map(Self::NdMutable)
        } else if lookahead.peek(kw::ndbin) {
            input.parse::<kw::ndbin>()?;
            input.parse::<OpsImplAuto<OpsNdKindBinary>>().map(Self::NdBinary)
        } else if lookahead.peek(kw::ndun) {
            input.parse::<kw::ndun>()?;
            input.parse::<OpsImplAuto<OpsNdKindUnary>>().map(Self::NdUnary)
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
            definitions: input.parse_terminated(Kind::Definition::parse, Token![,])?,
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

impl Parse for OpsStdSignatureMutable {
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
            comma: content.parse()?,
            rhs_star: content.parse().ok(),
            rhs_vmut: content.parse().ok(),
            rhs_ident: content.parse()?,
            rhs_colon: content.parse()?,
            rhs_ref: content.parse().ok(),
            rhs_type: content.parse()?,
        })
    }
}

impl Parse for OpsStdSignatureBinary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            paren: parenthesized!(content in input),
            lhs_star: content.parse().ok(),
            lhs_vmut: content.parse().ok(),
            lhs_ident: content.parse()?,
            lhs_colon: content.parse()?,
            lhs_ref: content.parse().ok(),
            lhs_type: content.parse()?,
            comma: content.parse()?,
            rhs_star: content.parse().ok(),
            rhs_vmut: content.parse().ok(),
            rhs_ident: content.parse()?,
            rhs_colon: content.parse()?,
            rhs_ref: content.parse().ok(),
            rhs_type: content.parse()?,
            arrow: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl Parse for OpsStdSignatureUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            paren: parenthesized!(content in input),
            self_star: content.parse().ok(),
            self_vmut: content.parse().ok(),
            self_ident: content.parse()?,
            self_colon: content.parse()?,
            self_ref: content.parse().ok(),
            self_type: content.parse()?,
            arrow: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl Parse for OpsNdSignatureMutable {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let paren = parenthesized!(content in input);
        let lhs_pat: PatType = content.parse()?;
        let comma = content.parse()?;
        let rhs_pat: PatType = content.parse()?;

        let lhs_ty = match *lhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_some() => (*val.elem).clone(),
            _ => {
                return Err(Error::new(
                    Span::call_site(),
                    "Failed to parse signature, lhs expected to be mutable reference",
                ));
            },
        };

        let rhs_ty = match *rhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            _ => {
                return Err(Error::new(
                    Span::call_site(),
                    "Failed to parse signature, rhs expected to be reference",
                ));
            },
        };

        Ok(Self {
            paren,
            lhs_pat,
            lhs_ty,
            comma,
            rhs_pat,
            rhs_ty,
        })
    }
}

impl Parse for OpsNdSignatureBinary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let paren = parenthesized!(content in input);
        let lhs_pat: PatType = content.parse()?;
        let comma = content.parse()?;
        let rhs_pat: PatType = content.parse()?;
        let arrow = content.parse()?;
        let ty = content.parse()?;

        let lhs_ty = match *lhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            _ => {
                return Err(Error::new(
                    Span::call_site(),
                    "Failed to parse signature, lhs expected to be reference",
                ));
            },
        };

        let rhs_ty = match *rhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            _ => {
                return Err(Error::new(
                    Span::call_site(),
                    "Failed to parse signature, rhs expected to be reference",
                ));
            },
        };

        Ok(Self {
            paren,
            lhs_pat,
            lhs_ty,
            comma,
            rhs_pat,
            rhs_ty,
            arrow,
            ty,
        })
    }
}

impl Parse for OpsNdSignatureUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let paren = parenthesized!(content in input);
        let self_pat: PatType = content.parse()?;
        let arrow = content.parse()?;
        let ty = content.parse()?;

        let self_ty = match *self_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            _ => {
                return Err(Error::new(
                    Span::call_site(),
                    "Failed to parse signature, self expected to be reference",
                ));
            },
        };

        Ok(Self {
            paren,
            self_pat,
            self_ty,
            arrow,
            ty,
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

impl<Operation: Parse, Qualifier: Parse> Parse for OpsDefinition<Operation, Qualifier> {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek2(kw::ext) {
            Ok(Self::Standard(input.parse()?))
        } else {
            Ok(Self::Extended(input.parse()?))
        }
    }
}

impl<Operation: Parse> Parse for OpsDefinitionStandard<Operation> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            op: input.parse()?,
            expr: input.parse()?,
        })
    }
}

impl<Operation: Parse, Qualifier: Parse> Parse for OpsDefinitionExtended<Operation, Qualifier> {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            op: input.parse()?,
            ext: input.parse()?,
            brace: braced!(content in input),
            elems: content.parse_terminated(OpsDefinitionExtendedElem::<Qualifier>::parse, Token![;])?,
        })
    }
}

impl<Qualifier: Parse> Parse for OpsDefinitionExtendedElem<Qualifier> {
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

impl ToTokens for OpsImpl<OpsStdKindMutable> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            op: &'ops OpsMutable,
            generics: &'ops Generics,
            signature: &'ops OpsStdSignatureMutable,
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

impl ToTokens for OpsImpl<OpsStdKindBinary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            op: &'ops OpsBinary,
            generics: &'ops Generics,
            signature: &'ops OpsStdSignatureBinary,
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

impl ToTokens for OpsImpl<OpsStdKindUnary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            op: &'ops OpsUnary,
            generics: &'ops Generics,
            signature: &'ops OpsStdSignatureUnary,
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

            let self_mut = &spec.signature.self_vmut;
            let self_ident = &spec.signature.self_ident;
            let self_type = &spec.signature.self_type;
            let op_type = &spec.signature.ty;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path for #lhs_ref #self_type #gen_where {
                    type Output = #op_type;

                    fn #ident(self) -> Self::Output {
                        (|#self_mut #self_ident: #lhs_ref #self_type| { (#expr).into() })(self)
                    }
                }
            }
        }

        let self_star = self.signature.self_star.is_some();
        let self_ref = self.signature.self_ref.is_some();

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

            match self_ref {
                true => match self_star {
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

impl ToTokens for OpsImpl<OpsNdKindMutable> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for definition in &self.definitions {
            let ident = definition.op.get_ident();
            let path = definition.op.get_nd_path();

            let (gen_impl, _, gen_where) = self.generics.split_for_impl();

            let lhs_pat = &self.signature.lhs_pat;
            let rhs_pat = &self.signature.rhs_pat;
            let lhs_ty = &self.signature.lhs_ty;
            let rhs_ty = &self.signature.rhs_ty;

            let expr = &definition.expr;

            tokens.extend(quote! {
                impl #gen_impl #path<#lhs_ty, #rhs_ty> for #lhs_ty #gen_where {
                    fn #ident(#lhs_pat, #rhs_pat) {
                        #expr
                    }
                }
            })
        }
    }
}

impl ToTokens for OpsImpl<OpsNdKindBinary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for definition in &self.definitions {
            let ident = definition.op.get_ident();
            let path = definition.op.get_nd_path();

            let (gen_impl, _, gen_where) = self.generics.split_for_impl();

            let lhs_pat = &self.signature.lhs_pat;
            let rhs_pat = &self.signature.rhs_pat;
            let lhs_ty = &self.signature.lhs_ty;
            let rhs_ty = &self.signature.rhs_ty;
            let ty = &self.signature.ty;

            let expr = &definition.expr;

            tokens.extend(quote! {
                impl #gen_impl #path<#lhs_ty, #rhs_ty> for #lhs_ty #gen_where {
                    type Type = #ty;

                    fn #ident(#lhs_pat, #rhs_pat) -> Self::Type {
                        #expr
                    }
                }
            })
        }
    }
}

impl ToTokens for OpsImpl<OpsNdKindUnary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for definition in &self.definitions {
            let ident = definition.op.get_ident();
            let path = definition.op.get_nd_path();

            let (gen_impl, _, gen_where) = self.generics.split_for_impl();

            let self_pat = &self.signature.self_pat;
            let self_ty = &self.signature.self_ty;
            let ty = &self.signature.ty;

            let expr = &definition.expr;

            tokens.extend(quote! {
                impl #gen_impl #path<#self_ty> for #self_ty #gen_where {
                    type Type = #ty;

                    fn #ident(#self_pat) -> Self::Type {
                        #expr
                    }
                }
            })
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

impl From<OpsImplAuto<OpsStdKindMutable>> for OpsImpl<OpsStdKindMutable> {
    fn from(value: OpsImplAuto<OpsStdKindMutable>) -> Self {
        OpsImpl::<OpsStdKindMutable> {
            generics: value.generics,
            signature: value.signature,
            colon: Default::default(),
            definitions: value
                .ops
                .into_iter()
                .map(|op| {
                    let lhs = &value.expression.lhs_expr;
                    let rhs = &value.expression.rhs_expr;

                    OpsDefinition::Standard(OpsDefinitionStandard::<OpsMutable> {
                        op,
                        expr: parse_quote! {{ #lhs #op #rhs; }},
                    })
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsStdKindBinary>> for OpsImpl<OpsStdKindBinary> {
    fn from(value: OpsImplAuto<OpsStdKindBinary>) -> Self {
        OpsImpl::<OpsStdKindBinary> {
            generics: value.generics,
            signature: value.signature,
            colon: Default::default(),
            definitions: value
                .ops
                .into_iter()
                .map(|op| {
                    let lhs = &value.expression.lhs_expr;
                    let rhs = &value.expression.rhs_expr;

                    OpsDefinition::Standard(OpsDefinitionStandard::<OpsBinary> {
                        op,
                        expr: parse_quote! {{ #lhs #op #rhs }},
                    })
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsStdKindUnary>> for OpsImpl<OpsStdKindUnary> {
    fn from(value: OpsImplAuto<OpsStdKindUnary>) -> Self {
        OpsImpl::<OpsStdKindUnary> {
            generics: value.generics,
            signature: value.signature,
            colon: Default::default(),
            definitions: value
                .ops
                .into_iter()
                .map(|op| {
                    let expr = &value.expression.self_expr;

                    OpsDefinition::Standard(OpsDefinitionStandard::<OpsUnary> {
                        op,
                        expr: parse_quote! {{ #op #expr }},
                    })
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsNdKindMutable>> for OpsImpl<OpsNdKindMutable> {
    fn from(value: OpsImplAuto<OpsNdKindMutable>) -> Self {
        todo!()
    }
}

impl From<OpsImplAuto<OpsNdKindBinary>> for OpsImpl<OpsNdKindBinary> {
    fn from(value: OpsImplAuto<OpsNdKindBinary>) -> Self {
        todo!()
    }
}

impl From<OpsImplAuto<OpsNdKindUnary>> for OpsImpl<OpsNdKindUnary> {
    fn from(value: OpsImplAuto<OpsNdKindUnary>) -> Self {
        todo!()
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

    fn get_nd_path(&self) -> Path {
        match self {
            OpsMutable::Add(_) => parse_quote! { NdAddAssign },
            OpsMutable::Sub(_) => parse_quote! { NdSubAssign },
            OpsMutable::Mul(_) => parse_quote! { NdMulAssign },
            OpsMutable::Div(_) => parse_quote! { NdDivAssign },
            OpsMutable::Rem(_) => parse_quote! { NdRemAssign },
            OpsMutable::BitOr(_) => parse_quote! { NdBitOrAssign },
            OpsMutable::BitAnd(_) => parse_quote! { NdBitAndAssign },
            OpsMutable::BitXor(_) => parse_quote! { NdBitXorAssign },
            OpsMutable::Shl(_) => parse_quote! { NdShlAssign },
            OpsMutable::Shr(_) => parse_quote! { NdShrAssign },
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

    fn get_nd_path(&self) -> Path {
        match self {
            OpsBinary::Add(_) => parse_quote! { NdAdd },
            OpsBinary::Sub(_) => parse_quote! { NdSub },
            OpsBinary::Mul(_) => parse_quote! { NdMul },
            OpsBinary::Div(_) => parse_quote! { NdDiv },
            OpsBinary::Rem(_) => parse_quote! { NdRem },
            OpsBinary::BitOr(_) => parse_quote! { NdBitOr },
            OpsBinary::BitAnd(_) => parse_quote! { NdBitAnd },
            OpsBinary::BitXor(_) => parse_quote! { NdBitXor },
            OpsBinary::Shl(_) => parse_quote! { NdShl },
            OpsBinary::Shr(_) => parse_quote! { NdShr },
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

    fn get_nd_path(&self) -> Path {
        match self {
            OpsUnary::Neg(_) => parse_quote! { NdNeg },
            OpsUnary::Not(_) => parse_quote! { NdNot },
        }
    }
}
