use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, quote};
use syn::{
    Error, Expr, Generics, Ident, PatType, Path, Result, Token, Type, WhereClause, WherePredicate, bracketed,
    parenthesized,
    parse::{Parse, ParseStream},
    parse_quote,
    punctuated::Punctuated,
    token::{Bracket, Paren},
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
    StdAssign(OpsImpl<OpsStdKindAssign>),
    StdBinary(OpsImpl<OpsStdKindBinary>),
    StdUnary(OpsImpl<OpsStdKindUnary>),
    NdAssign(OpsImpl<OpsNdKindAssign>),
    NdBinary(OpsImpl<OpsNdKindBinary>),
    NdUnary(OpsImpl<OpsNdKindUnary>),
}

#[allow(clippy::large_enum_variant)]
#[allow(clippy::enum_variant_names)]
pub enum OpsAuto {
    StdAssign(OpsImplAuto<OpsStdKindAssign>),
    StdBinary(OpsImplAuto<OpsStdKindBinary>),
    StdUnary(OpsImplAuto<OpsStdKindUnary>),
    NdAssign(OpsImplAuto<OpsNdKindAssign>),
    NdBinary(OpsImplAuto<OpsNdKindBinary>),
    NdUnary(OpsImplAuto<OpsNdKindUnary>),
}

pub struct OpsStdKindAssign;
pub struct OpsStdKindBinary;
pub struct OpsStdKindUnary;
pub struct OpsNdKindAssign;
pub struct OpsNdKindBinary;
pub struct OpsNdKindUnary;

#[allow(unused)]
pub struct OpsImpl<Kind: OpsKind> {
    pub specifier: Kind::Specifier,
    pub generics: Generics,
    pub signature: Kind::Signature,
    pub colon: Token![,],
    pub definitions: Punctuated<OpsDefinition<Kind::Operation>, Token![,]>,
}

#[allow(unused)]
pub struct OpsImplAuto<Kind: OpsKind> {
    pub specifier: Kind::Specifier,
    pub generics: Generics,
    pub signature: Kind::Signature,
    pub colon: Token![,],
    pub expression: Kind::Expression,
    pub ops_bracket: Bracket,
    pub ops: Punctuated<OpsDefinitionAuto<Kind::Operation>, Token![,]>,
}

pub struct OpsStdSpecifier;

#[allow(unused)]
pub struct OpsNdSpecifier {
    crate_token: Option<Token![crate]>,
    for_token: Token![for],
    ty: Type,
}

#[allow(unused)]
pub struct OpsStdSignatureAssign {
    pub paren: Paren,
    pub lhs_pat: PatType,
    pub lhs_ty: Type,
    pub comma: Token![,],
    pub rhs_star: Option<Token![*]>,
    pub rhs_pat: PatType,
    pub rhs_ref: Option<Token![&]>,
    pub rhs_ty: Type,
}

#[allow(unused)]
pub struct OpsStdSignatureBinary {
    pub paren: Paren,
    pub lhs_star: Option<Token![*]>,
    pub lhs_pat: PatType,
    pub lhs_ref: Option<Token![&]>,
    pub lhs_ty: Type,
    pub comma: Token![,],
    pub rhs_star: Option<Token![*]>,
    pub rhs_pat: PatType,
    pub rhs_ref: Option<Token![&]>,
    pub rhs_ty: Type,
    pub arrow: Token![->],
    pub ty: Type,
}

#[allow(unused)]
pub struct OpsStdSignatureUnary {
    pub paren: Paren,
    pub self_star: Option<Token![*]>,
    pub self_pat: PatType,
    pub self_ref: Option<Token![&]>,
    pub self_ty: Type,
    pub arrow: Token![->],
    pub ty: Type,
}

#[allow(unused)]
pub struct OpsNdSignatureAssign {
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
pub struct OpsExpressionAssign {
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

#[allow(unused)]
pub struct OpsDefinition<Operation: Parse> {
    pub op: Operation,
    pub expr: Expr,
    pub conditions: Option<OpsDefinitionConditions>,
}

#[allow(unused)]
pub struct OpsDefinitionAuto<Operation: Parse> {
    pub op: Operation,
    pub conditions: Option<OpsDefinitionConditions>,
}

#[allow(unused)]
pub struct OpsDefinitionConditions {
    pub token: Token![where],
    pub predicates: Punctuated<WherePredicate, Token![,]>,
}

#[derive(Clone, Copy)]
pub enum OpsAssign {
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
    type Expression: Parse;
    type Operation: Parse;
    type Specifier: Parse;
    type Signature: Parse;
}

impl OpsKind for OpsStdKindAssign {
    type Expression = OpsExpressionAssign;
    type Operation = OpsAssign;
    type Signature = OpsStdSignatureAssign;
    type Specifier = OpsStdSpecifier;
}

impl OpsKind for OpsStdKindBinary {
    type Expression = OpsExpressionBinary;
    type Operation = OpsBinary;
    type Signature = OpsStdSignatureBinary;
    type Specifier = OpsStdSpecifier;
}

impl OpsKind for OpsStdKindUnary {
    type Expression = OpsExpressionUnary;
    type Operation = OpsUnary;
    type Signature = OpsStdSignatureUnary;
    type Specifier = OpsStdSpecifier;
}

impl OpsKind for OpsNdKindAssign {
    type Expression = OpsExpressionAssign;
    type Operation = OpsAssign;
    type Signature = OpsNdSignatureAssign;
    type Specifier = OpsNdSpecifier;
}

impl OpsKind for OpsNdKindBinary {
    type Expression = OpsExpressionBinary;
    type Operation = OpsBinary;
    type Signature = OpsNdSignatureBinary;
    type Specifier = OpsNdSpecifier;
}

impl OpsKind for OpsNdKindUnary {
    type Expression = OpsExpressionUnary;
    type Operation = OpsUnary;
    type Signature = OpsNdSignatureUnary;
    type Specifier = OpsNdSpecifier;
}

impl Parse for Ops {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<Token![@]>()?;

        let lookahead = input.lookahead1();

        if lookahead.peek(kw::stdmut) {
            input.parse::<kw::stdmut>()?;
            input.parse::<OpsImpl<OpsStdKindAssign>>().map(Self::StdAssign)
        } else if lookahead.peek(kw::stdbin) {
            input.parse::<kw::stdbin>()?;
            input.parse::<OpsImpl<OpsStdKindBinary>>().map(Self::StdBinary)
        } else if lookahead.peek(kw::stdun) {
            input.parse::<kw::stdun>()?;
            input.parse::<OpsImpl<OpsStdKindUnary>>().map(Self::StdUnary)
        } else if lookahead.peek(kw::ndmut) {
            input.parse::<kw::ndmut>()?;
            input.parse::<OpsImpl<OpsNdKindAssign>>().map(Self::NdAssign)
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
            input.parse::<OpsImplAuto<OpsStdKindAssign>>().map(Self::StdAssign)
        } else if lookahead.peek(kw::stdbin) {
            input.parse::<kw::stdbin>()?;
            input.parse::<OpsImplAuto<OpsStdKindBinary>>().map(Self::StdBinary)
        } else if lookahead.peek(kw::stdun) {
            input.parse::<kw::stdun>()?;
            input.parse::<OpsImplAuto<OpsStdKindUnary>>().map(Self::StdUnary)
        } else if lookahead.peek(kw::ndmut) {
            input.parse::<kw::ndmut>()?;
            input.parse::<OpsImplAuto<OpsNdKindAssign>>().map(Self::NdAssign)
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
        let specifier = input.parse()?;
        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;

        Ok(Self {
            specifier,
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
        let specifier = input.parse()?;
        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;

        let content;

        Ok(Self {
            specifier,
            generics: Generics {
                where_clause: gen_where,
                ..gen_
            },
            signature: input.parse()?,
            colon: input.parse()?,
            expression: input.parse()?,
            ops_bracket: bracketed!(content in input),
            ops: content.parse_terminated(OpsDefinitionAuto::parse, Token![,])?,
        })
    }
}

impl Parse for OpsStdSpecifier {
    fn parse(_: ParseStream) -> Result<Self> {
        Ok(Self)
    }
}

impl Parse for OpsNdSpecifier {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            crate_token: input.parse()?,
            for_token: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl Parse for OpsStdSignatureAssign {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let paren = parenthesized!(content in input);
        let lhs_pat: PatType = content.parse()?;
        let comma = content.parse()?;
        let rhs_star = content.parse()?;
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

        let (rhs_ty, rhs_ref) = match *rhs_pat.ty {
            Type::Reference(ref val) => match val.mutability {
                Some(_) => {
                    return Err(Error::new(
                        Span::call_site(),
                        "Failed to parse signature, rhs expected to be reference",
                    ));
                },
                None => ((*val.elem).clone(), Some(Default::default())),
            },
            ref val => (val.clone(), None),
        };

        Ok(Self {
            paren,
            lhs_pat,
            lhs_ty,
            comma,
            rhs_star,
            rhs_pat,
            rhs_ref,
            rhs_ty,
        })
    }
}

impl Parse for OpsStdSignatureBinary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let paren = parenthesized!(content in input);
        let lhs_star = content.parse()?;
        let lhs_pat: PatType = content.parse()?;
        let comma = content.parse()?;
        let rhs_star = content.parse()?;
        let rhs_pat: PatType = content.parse()?;
        let arrow = input.parse()?;
        let ty = input.parse()?;

        let (lhs_ty, lhs_ref) = match *lhs_pat.ty {
            Type::Reference(ref val) => match val.mutability {
                Some(_) => {
                    return Err(Error::new(
                        Span::call_site(),
                        "Failed to parse signature, lhs expected to be reference",
                    ));
                },
                None => ((*val.elem).clone(), Some(Default::default())),
            },
            ref val => (val.clone(), None),
        };

        let (rhs_ty, rhs_ref) = match *rhs_pat.ty {
            Type::Reference(ref val) => match val.mutability {
                Some(_) => {
                    return Err(Error::new(
                        Span::call_site(),
                        "Failed to parse signature, rhs expected to be reference",
                    ));
                },
                None => ((*val.elem).clone(), Some(Default::default())),
            },
            ref val => (val.clone(), None),
        };

        Ok(Self {
            paren,
            lhs_star,
            lhs_pat,
            lhs_ref,
            lhs_ty,
            comma,
            rhs_star,
            rhs_pat,
            rhs_ref,
            rhs_ty,
            arrow,
            ty,
        })
    }
}

impl Parse for OpsStdSignatureUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let paren = parenthesized!(content in input);
        let self_star = content.parse()?;
        let self_pat: PatType = content.parse()?;
        let arrow = input.parse()?;
        let ty = input.parse()?;

        let (self_ty, self_ref) = match *self_pat.ty {
            Type::Reference(ref val) => match val.mutability {
                Some(_) => {
                    return Err(Error::new(
                        Span::call_site(),
                        "Failed to parse signature, self expected to be reference",
                    ));
                },
                None => ((*val.elem).clone(), Some(Default::default())),
            },
            ref val => (val.clone(), None),
        };

        Ok(Self {
            paren,
            self_star,
            self_pat,
            self_ref,
            self_ty,
            arrow,
            ty,
        })
    }
}

impl Parse for OpsNdSignatureAssign {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let paren = parenthesized!(content in input);
        let lhs_pat: PatType = content.parse()?;
        let comma = content.parse()?;
        let rhs_pat: PatType = content.parse()?;

        let lhs_ty = match *lhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_some() => (*val.elem).clone(),
            ref val => val.clone(),
        };

        let rhs_ty = match *rhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            ref val => val.clone(),
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
        let arrow = input.parse()?;
        let ty = input.parse()?;

        let lhs_ty = match *lhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            ref val => val.clone(),
        };

        let rhs_ty = match *rhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            ref val => val.clone(),
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
        let arrow = input.parse()?;
        let ty = input.parse()?;

        let self_ty = match *self_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            ref val => val.clone(),
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

impl Parse for OpsExpressionAssign {
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

impl<Operation: Parse> Parse for OpsDefinition<Operation> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            op: input.parse()?,
            expr: input.parse()?,
            conditions: input.parse().ok(),
        })
    }
}

impl<Operation: Parse> Parse for OpsDefinitionAuto<Operation> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            op: input.parse()?,
            conditions: input.parse().ok(),
        })
    }
}

impl Parse for OpsDefinitionConditions {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        let token = input.parse()?;
        let _ = bracketed!(content in input);
        let predicates = content.parse_terminated(WherePredicate::parse, Token![,])?;

        Ok(Self { token, predicates })
    }
}

impl Parse for OpsAssign {
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

impl ToTokens for OpsImpl<OpsStdKindAssign> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            op: &'ops OpsAssign,
            generics: &'ops Generics,
            signature: &'ops OpsStdSignatureAssign,
            expr: &'ops Expr,
            conditions: Option<&'ops OpsDefinitionConditions>,
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

            let lhs_pat = &spec.signature.lhs_pat;
            let lhs_ty = &spec.signature.lhs_ty;
            let rhs_pat = &spec.signature.rhs_pat.pat;
            let rhs_ty = &spec.signature.rhs_ty;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path<#rhs_ref #rhs_ty> for #lhs_ty #gen_where {
                    fn #ident(&mut self, rhs: #rhs_ref #rhs_ty) {
                        #[allow(clippy::needless_borrow)]
                        (|#lhs_pat, #rhs_pat: #rhs_ref #rhs_ty| { #expr })(self, rhs);
                    }
                }
            }
        }

        let rhs_star = self.signature.rhs_star.is_some();
        let rhs_ref = self.signature.rhs_ref.is_some();

        let some = Some(Default::default());
        let none = None;

        for definition in &self.definitions {
            let spec = OpsSpec {
                op: &definition.op,
                generics: &self.generics,
                signature: &self.signature,
                expr: &definition.expr,
                conditions: definition.conditions.as_ref(),
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
            conditions: Option<&'ops OpsDefinitionConditions>,
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

            let lhs_pat = &spec.signature.lhs_pat.pat;
            let lhs_ty = &spec.signature.lhs_ty;
            let rhs_pat = &spec.signature.rhs_pat.pat;
            let rhs_ty = &spec.signature.rhs_ty;
            let op_ty = &spec.signature.ty;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path<#rhs_ref #rhs_ty> for #lhs_ref #lhs_ty #gen_where {
                    type Output = #op_ty;

                    fn #ident(self, rhs: #rhs_ref #rhs_ty) -> Self::Output {
                        #[allow(clippy::needless_borrow)]
                        (|#lhs_pat: #lhs_ref #lhs_ty, #rhs_pat: #rhs_ref #rhs_ty| { <#op_ty>::from(#expr) })(self, rhs)
                    }
                }
            }
        }

        let lhs_star = self.signature.lhs_star.is_some();
        let rhs_star = self.signature.rhs_star.is_some();

        let lhs_ref = self.signature.lhs_ref.is_some();
        let rhs_ref = self.signature.rhs_ref.is_some();

        let some = Some(Default::default());
        let none = None;

        for definition in &self.definitions {
            let spec = OpsSpec {
                op: &definition.op,
                generics: &self.generics,
                signature: &self.signature,
                expr: &definition.expr,
                conditions: definition.conditions.as_ref(),
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
            conditions: Option<&'ops OpsDefinitionConditions>,
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

            let self_pat = &spec.signature.self_pat.pat;
            let self_ty = &spec.signature.self_ty;
            let op_ty = &spec.signature.ty;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path for #lhs_ref #self_ty #gen_where {
                    type Output = #op_ty;

                    fn #ident(self) -> Self::Output {
                        #[allow(clippy::needless_borrow)]
                        (|#self_pat: #lhs_ref #self_ty| { <#op_ty>::from(#expr) })(self)
                    }
                }
            }
        }

        let self_star = self.signature.self_star.is_some();
        let self_ref = self.signature.self_ref.is_some();

        let some = Some(Default::default());
        let none = None;

        for definition in &self.definitions {
            let spec = OpsSpec {
                op: &definition.op,
                generics: &self.generics,
                signature: &self.signature,
                expr: &definition.expr,
                conditions: definition.conditions.as_ref(),
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
    }
}

impl ToTokens for OpsImpl<OpsNdKindAssign> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for definition in &self.definitions {
            let token = self.specifier.crate_token;
            let ident = definition.op.get_ident();
            let path = definition.op.get_nd_path(token);

            let (gen_impl, _, gen_where) = self.generics.split_for_impl();

            let predicates = match &definition.conditions {
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

            let ty = &self.specifier.ty;
            let lhs_pat = &self.signature.lhs_pat;
            let rhs_pat = &self.signature.rhs_pat;
            let lhs_ty = &self.signature.lhs_ty;
            let rhs_ty = &self.signature.rhs_ty;

            let expr = &definition.expr;

            tokens.extend(quote! {
                impl #gen_impl #path<#lhs_ty, #rhs_ty> for #ty #gen_where {
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
            let token = self.specifier.crate_token;
            let ident = definition.op.get_ident();
            let path = definition.op.get_nd_path(token);

            let (gen_impl, _, gen_where) = self.generics.split_for_impl();

            let predicates = match &definition.conditions {
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

            let ty = &self.specifier.ty;
            let lhs_pat = &self.signature.lhs_pat;
            let rhs_pat = &self.signature.rhs_pat;
            let lhs_ty = &self.signature.lhs_ty;
            let rhs_ty = &self.signature.rhs_ty;
            let op_ty = &self.signature.ty;

            let expr = &definition.expr;

            tokens.extend(quote! {
                impl #gen_impl #path<#lhs_ty, #rhs_ty> for #ty #gen_where {
                    type Type = #op_ty;

                    fn #ident(#lhs_pat, #rhs_pat) -> Self::Type {
                        <#op_ty>::from(#expr)
                    }
                }
            })
        }
    }
}

impl ToTokens for OpsImpl<OpsNdKindUnary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for definition in &self.definitions {
            let token = self.specifier.crate_token;
            let ident = definition.op.get_ident();
            let path = definition.op.get_nd_path(token);

            let (gen_impl, _, gen_where) = self.generics.split_for_impl();

            let predicates = match &definition.conditions {
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

            let ty = &self.specifier.ty;
            let self_pat = &self.signature.self_pat;
            let self_ty = &self.signature.self_ty;
            let op_ty = &self.signature.ty;

            let expr = &definition.expr;

            tokens.extend(quote! {
                impl #gen_impl #path<#self_ty> for #ty #gen_where {
                    type Type = #op_ty;

                    fn #ident(#self_pat) -> Self::Type {
                        <#op_ty>::from(#expr)
                    }
                }
            })
        }
    }
}

impl ToTokens for OpsAssign {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            OpsAssign::Add(op) => tokens.extend(quote! { #op }),
            OpsAssign::Sub(op) => tokens.extend(quote! { #op }),
            OpsAssign::Mul(op) => tokens.extend(quote! { #op }),
            OpsAssign::Div(op) => tokens.extend(quote! { #op }),
            OpsAssign::Rem(op) => tokens.extend(quote! { #op }),
            OpsAssign::BitOr(op) => tokens.extend(quote! { #op }),
            OpsAssign::BitXor(op) => tokens.extend(quote! { #op }),
            OpsAssign::BitAnd(op) => tokens.extend(quote! { #op }),
            OpsAssign::Shl(op) => tokens.extend(quote! { #op }),
            OpsAssign::Shr(op) => tokens.extend(quote! { #op }),
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

impl From<OpsImplAuto<OpsStdKindAssign>> for OpsImpl<OpsStdKindAssign> {
    fn from(value: OpsImplAuto<OpsStdKindAssign>) -> Self {
        OpsImpl::<OpsStdKindAssign> {
            specifier: value.specifier,
            generics: value.generics,
            signature: value.signature,
            colon: Default::default(),
            definitions: value
                .ops
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let lhs = &value.expression.lhs_expr;
                    let rhs = &value.expression.rhs_expr;
                    let conditions = definition.conditions;

                    OpsDefinition::<OpsAssign> {
                        op,
                        expr: parse_quote! {{ #lhs #op #rhs; }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsStdKindBinary>> for OpsImpl<OpsStdKindBinary> {
    fn from(value: OpsImplAuto<OpsStdKindBinary>) -> Self {
        OpsImpl::<OpsStdKindBinary> {
            specifier: value.specifier,
            generics: value.generics,
            signature: value.signature,
            colon: Default::default(),
            definitions: value
                .ops
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let lhs = &value.expression.lhs_expr;
                    let rhs = &value.expression.rhs_expr;
                    let conditions = definition.conditions;

                    OpsDefinition::<OpsBinary> {
                        op,
                        expr: parse_quote! {{ #lhs #op #rhs }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsStdKindUnary>> for OpsImpl<OpsStdKindUnary> {
    fn from(value: OpsImplAuto<OpsStdKindUnary>) -> Self {
        OpsImpl::<OpsStdKindUnary> {
            specifier: value.specifier,
            generics: value.generics,
            signature: value.signature,
            colon: Default::default(),
            definitions: value
                .ops
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let expr = &value.expression.self_expr;
                    let conditions = definition.conditions;

                    OpsDefinition::<OpsUnary> {
                        op,
                        expr: parse_quote! {{ #op #expr }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsNdKindAssign>> for OpsImpl<OpsNdKindAssign> {
    fn from(value: OpsImplAuto<OpsNdKindAssign>) -> Self {
        OpsImpl::<OpsNdKindAssign> {
            specifier: value.specifier,
            generics: value.generics,
            signature: value.signature,
            colon: Default::default(),
            definitions: value
                .ops
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let lhs = &value.expression.lhs_expr;
                    let rhs = &value.expression.rhs_expr;
                    let conditions = definition.conditions;

                    OpsDefinition::<OpsAssign> {
                        op,
                        expr: parse_quote! {{ #lhs #op #rhs; }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsNdKindBinary>> for OpsImpl<OpsNdKindBinary> {
    fn from(value: OpsImplAuto<OpsNdKindBinary>) -> Self {
        OpsImpl::<OpsNdKindBinary> {
            specifier: value.specifier,
            generics: value.generics,
            signature: value.signature,
            colon: Default::default(),
            definitions: value
                .ops
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let lhs = &value.expression.lhs_expr;
                    let rhs = &value.expression.rhs_expr;
                    let conditions = definition.conditions;

                    OpsDefinition::<OpsBinary> {
                        op,
                        expr: parse_quote! {{ #lhs #op #rhs }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsNdKindUnary>> for OpsImpl<OpsNdKindUnary> {
    fn from(value: OpsImplAuto<OpsNdKindUnary>) -> Self {
        OpsImpl::<OpsNdKindUnary> {
            specifier: value.specifier,
            generics: value.generics,
            signature: value.signature,
            colon: Default::default(),
            definitions: value
                .ops
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let expr = &value.expression.self_expr;
                    let conditions = definition.conditions;

                    OpsDefinition::<OpsUnary> {
                        op,
                        expr: parse_quote! {{ #op #expr }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl OpsAssign {
    fn get_ident(&self) -> Ident {
        match self {
            OpsAssign::Add(_) => parse_quote! { add_assign },
            OpsAssign::Sub(_) => parse_quote! { sub_assign },
            OpsAssign::Mul(_) => parse_quote! { mul_assign },
            OpsAssign::Div(_) => parse_quote! { div_assign },
            OpsAssign::Rem(_) => parse_quote! { rem_assign },
            OpsAssign::BitOr(_) => parse_quote! { bitor_assign },
            OpsAssign::BitAnd(_) => parse_quote! { bitand_assign },
            OpsAssign::BitXor(_) => parse_quote! { bitxor_assign },
            OpsAssign::Shl(_) => parse_quote! { shl_assign },
            OpsAssign::Shr(_) => parse_quote! { shr_assign },
        }
    }

    fn get_path(&self) -> Path {
        match self {
            OpsAssign::Add(_) => parse_quote! { std::ops::AddAssign },
            OpsAssign::Sub(_) => parse_quote! { std::ops::SubAssign },
            OpsAssign::Mul(_) => parse_quote! { std::ops::MulAssign },
            OpsAssign::Div(_) => parse_quote! { std::ops::DivAssign },
            OpsAssign::Rem(_) => parse_quote! { std::ops::RemAssign },
            OpsAssign::BitOr(_) => parse_quote! { std::ops::BitOrAssign },
            OpsAssign::BitAnd(_) => parse_quote! { std::ops::BitAndAssign },
            OpsAssign::BitXor(_) => parse_quote! { std::ops::BitXorAssign },
            OpsAssign::Shl(_) => parse_quote! { std::ops::ShlAssign },
            OpsAssign::Shr(_) => parse_quote! { std::ops::ShrAssign },
        }
    }

    fn get_nd_path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndlib });

        match self {
            OpsAssign::Add(_) => parse_quote! { #prefix::ops::NdAddAssign },
            OpsAssign::Sub(_) => parse_quote! { #prefix::ops::NdSubAssign },
            OpsAssign::Mul(_) => parse_quote! { #prefix::ops::NdMulAssign },
            OpsAssign::Div(_) => parse_quote! { #prefix::ops::NdDivAssign },
            OpsAssign::Rem(_) => parse_quote! { #prefix::ops::NdRemAssign },
            OpsAssign::BitOr(_) => parse_quote! { #prefix::ops::NdBitOrAssign },
            OpsAssign::BitAnd(_) => parse_quote! { #prefix::ops::NdBitAndAssign },
            OpsAssign::BitXor(_) => parse_quote! { #prefix::ops::NdBitXorAssign },
            OpsAssign::Shl(_) => parse_quote! { #prefix::ops::NdShlAssign },
            OpsAssign::Shr(_) => parse_quote! { #prefix::ops::NdShrAssign },
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

    fn get_nd_path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndlib });

        match self {
            OpsBinary::Add(_) => parse_quote! { #prefix::ops::NdAdd },
            OpsBinary::Sub(_) => parse_quote! { #prefix::ops::NdSub },
            OpsBinary::Mul(_) => parse_quote! { #prefix::ops::NdMul },
            OpsBinary::Div(_) => parse_quote! { #prefix::ops::NdDiv },
            OpsBinary::Rem(_) => parse_quote! { #prefix::ops::NdRem },
            OpsBinary::BitOr(_) => parse_quote! { #prefix::ops::NdBitOr },
            OpsBinary::BitAnd(_) => parse_quote! { #prefix::ops::NdBitAnd },
            OpsBinary::BitXor(_) => parse_quote! { #prefix::ops::NdBitXor },
            OpsBinary::Shl(_) => parse_quote! { #prefix::ops::NdShl },
            OpsBinary::Shr(_) => parse_quote! { #prefix::ops::NdShr },
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

    fn get_nd_path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndlib });

        match self {
            OpsUnary::Neg(_) => parse_quote! { #prefix::ops::NdNeg },
            OpsUnary::Not(_) => parse_quote! { #prefix::ops::NdNot },
        }
    }
}
