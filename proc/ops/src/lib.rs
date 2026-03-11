#![doc = include_str!("../README.md")]

use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::TokenStream;
use quote::{ToTokens, quote};
use syn::{
    Error, Expr, Generics, Ident, PatType, Path, Result, Token, Type, WherePredicate, bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    token::{Bracket, Paren},
};

mod kw {
    syn::custom_keyword!(stdmut);
    syn::custom_keyword!(stdbin);
    syn::custom_keyword!(stdun);

    syn::custom_keyword!(ndmut);
    syn::custom_keyword!(ndbin);
    syn::custom_keyword!(ndun);

    syn::custom_keyword!(ext);

    syn::custom_keyword!(checked);
    syn::custom_keyword!(strict);
    syn::custom_keyword!(wrapping);
    syn::custom_keyword!(saturating);
    syn::custom_keyword!(overflowing);
    syn::custom_keyword!(unbounded);
}

/// Implements `std::ops::*` and `ndcore::ops::*` operations with explicitly provided expressions.
///
/// | Kind      | Operations                                                     | Traits           |
/// | --------- | -------------------------------------------------------------- | ---------------- |
/// | `@stdmut` | `+=`, `-=`, `\*=`, `/=`, `%=`, `\|=`, `&=`, `^=`, `<<=`, `>>=` | `std::ops::*`    |
/// | `@ndmut`  | `+=`, `-=`, `\*=`, `/=`, `%=`, `\|=`, `&=`, `^=`, `<<=`, `>>=` | `ndcore::ops::*` |
/// | `@stdbin` | `+`, `-`, `\*`, `/`, `%`, `\|`, `&`, `^`, `<<`, `>>`           | `std::ops::*`    |
/// | `@ndbin`  | `+`, `-`, `\*`, `/`, `%`, `\|`, `&`, `^`, `<<`, `>>`           | `ndcore::ops::*` |
/// | `@stdun`  | `-`, `!`                                                       | `std::ops::*`    |
/// | `@ndun`   | `-`, `!`                                                       | `ndcore::ops::*` |
///
/// # Syntax
///
/// ```text
/// ndops::all! { KIND SIGNATURE, [
///     (OP EXPR OP_CONDITIONS?),*
/// ] }
///
/// KIND := @stdmut | @stdbin | @stdun | @ndmut | @ndbin | @ndun
/// OP_CONDITIONS := where [(OP_PREDICATE),*]
/// SIG_CONDITIONS := where [(SIG_PREDICATE),*]
/// ```
///
/// For more information and examples, see [crate-level](crate) documentation.
#[proc_macro]
pub fn all(stream: TokenStreamStd) -> TokenStreamStd {
    match parse_macro_input!(stream as Ops) {
        Ops::StdAssign(ops) => quote! { #ops }.into(),
        Ops::StdBinary(ops) => quote! { #ops }.into(),
        Ops::StdUnary(ops) => quote! { #ops }.into(),
        Ops::NdAssign(ops) => quote! { #ops }.into(),
        Ops::NdBinary(ops) => quote! { #ops }.into(),
        Ops::NdUnary(ops) => quote! { #ops }.into(),
    }
}

/// Implements `std::ops::*` and `ndcore::ops::*` operations with implicitly derived expressions.
///
/// | Kind      | Operations                                                     | Traits           |
/// | --------- | -------------------------------------------------------------- | ---------------- |
/// | `@stdmut` | `+=`, `-=`, `\*=`, `/=`, `%=`, `\|=`, `&=`, `^=`, `<<=`, `>>=` | `std::ops::*`    |
/// | `@ndmut`  | `+=`, `-=`, `\*=`, `/=`, `%=`, `\|=`, `&=`, `^=`, `<<=`, `>>=` | `ndcore::ops::*` |
/// | `@stdbin` | `+`, `-`, `\*`, `/`, `%`, `\|`, `&`, `^`, `<<`, `>>`           | `std::ops::*`    |
/// | `@ndbin`  | `+`, `-`, `\*`, `/`, `%`, `\|`, `&`, `^`, `<<`, `>>`           | `ndcore::ops::*` |
/// | `@stdun`  | `-`, `!`                                                       | `std::ops::*`    |
/// | `@ndun`   | `-`, `!`                                                       | `ndcore::ops::*` |
///
/// # Syntax
///
/// ```text
/// ndops::fwd! { KIND SIGNATURE, [
///     (OP OP_CONDITIONS?),*
/// ] }
///
/// KIND := @stdmut | @stdbin | @stdun | @ndmut | @ndbin | @ndun
/// OP_CONDITIONS := where [(OP_PREDICATE),*]
/// SIG_CONDITIONS := where [(SIG_PREDICATE),*]
/// ```
///
/// For more information and examples, see [crate-level](crate) documentation.
#[proc_macro]
pub fn fwd(stream: TokenStreamStd) -> TokenStreamStd {
    match parse_macro_input!(stream as OpsFwd) {
        OpsFwd::StdAssign(ops) => {
            let ops = OpsImpl::<OpsStdKindAssign>::from(ops);

            quote! { #ops }.into()
        },
        OpsFwd::StdBinary(ops) => {
            let ops = OpsImpl::<OpsStdKindBinary>::from(ops);

            quote! { #ops }.into()
        },
        OpsFwd::StdUnary(ops) => {
            let ops = OpsImpl::<OpsStdKindUnary>::from(ops);

            quote! { #ops }.into()
        },
        OpsFwd::NdAssign(ops) => {
            let ops = OpsImpl::<OpsNdKindAssign>::from(ops);

            quote! { #ops }.into()
        },
        OpsFwd::NdBinary(ops) => {
            let ops = OpsImpl::<OpsNdKindBinary>::from(ops);

            quote! { #ops }.into()
        },
        OpsFwd::NdUnary(ops) => {
            let ops = OpsImpl::<OpsNdKindUnary>::from(ops);

            quote! { #ops }.into()
        },
    }
}

struct OpsStdKindAssign;
struct OpsStdKindBinary;
struct OpsStdKindUnary;
struct OpsNdKindAssign;
struct OpsNdKindBinary;
struct OpsNdKindUnary;

#[allow(clippy::large_enum_variant)]
enum Ops {
    StdAssign(OpsImpl<OpsStdKindAssign>),
    StdBinary(OpsImpl<OpsStdKindBinary>),
    StdUnary(OpsImpl<OpsStdKindUnary>),
    NdAssign(OpsImpl<OpsNdKindAssign>),
    NdBinary(OpsImpl<OpsNdKindBinary>),
    NdUnary(OpsImpl<OpsNdKindUnary>),
}

#[allow(clippy::large_enum_variant)]
enum OpsFwd {
    StdAssign(OpsImplFwd<OpsStdKindAssign>),
    StdBinary(OpsImplFwd<OpsStdKindBinary>),
    StdUnary(OpsImplFwd<OpsStdKindUnary>),
    NdAssign(OpsImplFwd<OpsNdKindAssign>),
    NdBinary(OpsImplFwd<OpsNdKindBinary>),
    NdUnary(OpsImplFwd<OpsNdKindUnary>),
}

#[allow(unused)]
struct OpsImpl<Kind: OpsKind> {
    token: Option<Token![crate]>,
    signature: Kind::Signature,
    colon: Token![,],
    definitions_bracket: Bracket,
    definitions: Punctuated<Kind::Definition, Token![,]>,
}

#[allow(unused)]
struct OpsImplFwd<Kind: OpsKindFwd> {
    token: Option<Token![crate]>,
    signature: Kind::Signature,
    colon: Token![,],
    expression: Kind::Expression,
    definitions_bracket: Bracket,
    definitions: Punctuated<Kind::Definition, Token![,]>,
}

#[allow(unused)]
struct OpsStdSignatureAssign {
    generics: Generics,
    conditions: Option<OpsConditions>,
    paren: Paren,
    lhs_pat: PatType,
    lhs_ty: Type,
    comma: Token![,],
    rhs_star: Option<Token![*]>,
    rhs_pat: PatType,
    rhs_ref: Option<Token![&]>,
    rhs_ty: Type,
}

#[allow(unused)]
struct OpsStdSignatureBinary {
    generics: Generics,
    conditions: Option<OpsConditions>,
    paren: Paren,
    lhs_star: Option<Token![*]>,
    lhs_pat: PatType,
    lhs_ref: Option<Token![&]>,
    lhs_ty: Type,
    comma: Token![,],
    rhs_star: Option<Token![*]>,
    rhs_pat: PatType,
    rhs_ref: Option<Token![&]>,
    rhs_ty: Type,
    arrow: Token![->],
    res_ty: Type,
}

#[allow(unused)]
struct OpsStdSignatureUnary {
    generics: Generics,
    conditions: Option<OpsConditions>,
    paren: Paren,
    self_star: Option<Token![*]>,
    self_pat: PatType,
    self_ref: Option<Token![&]>,
    self_ty: Type,
    arrow: Token![->],
    res_ty: Type,
}

#[allow(unused)]
struct OpsNdSignatureAssign {
    generics: Generics,
    conditions: Option<OpsConditions>,
    paren: Paren,
    lhs_pat: PatType,
    lhs_ty: Type,
    comma: Token![,],
    rhs_pat: PatType,
    rhs_ty: Type,
    impl_ty: OpsNdImplType,
}

#[allow(unused)]
struct OpsNdSignatureBinary {
    generics: Generics,
    conditions: Option<OpsConditions>,
    paren: Paren,
    lhs_pat: PatType,
    lhs_ty: Type,
    comma: Token![,],
    rhs_pat: PatType,
    rhs_ty: Type,
    arrow: Token![->],
    res_ty: Type,
    impl_ty: OpsNdImplType,
}

#[allow(unused)]
struct OpsNdSignatureUnary {
    generics: Generics,
    conditions: Option<OpsConditions>,
    paren: Paren,
    self_pat: PatType,
    self_ty: Type,
    arrow: Token![->],
    res_ty: Type,
    impl_ty: OpsNdImplType,
}

enum OpsNdImplType {
    Empty,
    Single(OpsNdImplTypeSingle),
    Multiple(OpsNdImplTypeMultiple),
}

#[allow(unused)]
struct OpsNdImplTypeSingle {
    token: Token![for],
    impl_ty: Type,
}

#[allow(unused)]
struct OpsNdImplTypeMultiple {
    token: Token![for],
    impl_ty: Punctuated<Type, Token![,]>,
}

#[allow(unused)]
struct OpsExpressionAssign {
    ty_paren: Paren,
    ty_expr: Type,
    lhs_paren: Paren,
    lhs_expr: Expr,
    rhs_paren: Paren,
    rhs_expr: Expr,
}

#[allow(unused)]
struct OpsExpressionBinary {
    ty_paren: Paren,
    ty_expr: Type,
    lhs_paren: Paren,
    lhs_expr: Expr,
    rhs_paren: Paren,
    rhs_expr: Expr,
}

#[allow(unused)]
struct OpsExpressionUnary {
    ty_paren: Paren,
    ty_expr: Type,
    self_paren: Paren,
    self_expr: Expr,
}

#[allow(unused)]
struct OpsDefinition<Operation: Parse> {
    op: Operation,
    expr: Expr,
    conditions: Option<OpsConditions>,
}

#[allow(unused)]
struct OpsDefinitionFwd<Operation: Parse> {
    op: Operation,
    conditions: Option<OpsConditions>,
}

#[allow(unused)]
struct OpsConditions {
    token: Token![where],
    predicates: Punctuated<WherePredicate, Token![,]>,
}

#[derive(Clone, Copy)]
enum OpsAssign {
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
enum OpsBinary {
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
enum OpsUnary {
    Not(Token![!]),
    Neg(Token![-]),
}

#[allow(unused)]
#[derive(Clone, Copy)]
enum OpsAssignExt {
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
    AddStrict(Token![+=], Token![@], kw::strict),
    SubStrict(Token![-=], Token![@], kw::strict),
    MulStrict(Token![*=], Token![@], kw::strict),
    DivStrict(Token![/=], Token![@], kw::strict),
    RemStrict(Token![%=], Token![@], kw::strict),
    ShlStrict(Token![<<=], Token![@], kw::strict),
    ShrStrict(Token![>>=], Token![@], kw::strict),
    AddWrapping(Token![+=], Token![@], kw::wrapping),
    SubWrapping(Token![-=], Token![@], kw::wrapping),
    MulWrapping(Token![*=], Token![@], kw::wrapping),
    DivWrapping(Token![/=], Token![@], kw::wrapping),
    RemWrapping(Token![%=], Token![@], kw::wrapping),
    AddSaturating(Token![+=], Token![@], kw::saturating),
    SubSaturating(Token![-=], Token![@], kw::saturating),
    MulSaturating(Token![*=], Token![@], kw::saturating),
    DivSaturating(Token![/=], Token![@], kw::saturating),
    RemSaturating(Token![%=], Token![@], kw::saturating),
    ShlUnbounded(Token![<<=], Token![@], kw::unbounded),
    ShrUnbounded(Token![>>=], Token![@], kw::unbounded),
}

#[allow(unused)]
#[derive(Clone, Copy)]
enum OpsBinaryExt {
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
    AddChecked(Token![+], Token![@], kw::checked),
    SubChecked(Token![-], Token![@], kw::checked),
    MulChecked(Token![*], Token![@], kw::checked),
    DivChecked(Token![/], Token![@], kw::checked),
    RemChecked(Token![%], Token![@], kw::checked),
    ShlChecked(Token![<<], Token![@], kw::checked),
    ShrChecked(Token![>>], Token![@], kw::checked),
    AddStrict(Token![+], Token![@], kw::strict),
    SubStrict(Token![-], Token![@], kw::strict),
    MulStrict(Token![*], Token![@], kw::strict),
    DivStrict(Token![/], Token![@], kw::strict),
    RemStrict(Token![%], Token![@], kw::strict),
    ShlStrict(Token![<<], Token![@], kw::strict),
    ShrStrict(Token![>>], Token![@], kw::strict),
    AddWrapping(Token![+], Token![@], kw::wrapping),
    SubWrapping(Token![-], Token![@], kw::wrapping),
    MulWrapping(Token![*], Token![@], kw::wrapping),
    DivWrapping(Token![/], Token![@], kw::wrapping),
    RemWrapping(Token![%], Token![@], kw::wrapping),
    AddSaturating(Token![+], Token![@], kw::saturating),
    SubSaturating(Token![-], Token![@], kw::saturating),
    MulSaturating(Token![*], Token![@], kw::saturating),
    DivSaturating(Token![/], Token![@], kw::saturating),
    RemSaturating(Token![%], Token![@], kw::saturating),
    AddOverflowing(Token![+], Token![@], kw::overflowing),
    SubOverflowing(Token![-], Token![@], kw::overflowing),
    MulOverflowing(Token![*], Token![@], kw::overflowing),
    DivOverflowing(Token![/], Token![@], kw::overflowing),
    RemOverflowing(Token![%], Token![@], kw::overflowing),
    ShlOverflowing(Token![<<], Token![@], kw::overflowing),
    ShrOverflowing(Token![>>], Token![@], kw::overflowing),
    ShlUnbounded(Token![<<], Token![@], kw::unbounded),
    ShrUnbounded(Token![>>], Token![@], kw::unbounded),
}

#[allow(unused)]
#[derive(Clone, Copy)]
enum OpsUnaryExt {
    Not(Token![!]),
    Neg(Token![-]),
    NegChecked(Token![-], Token![@], kw::checked),
    NegStrict(Token![-], Token![@], kw::strict),
    NegWrapping(Token![-], Token![@], kw::wrapping),
    NegSaturating(Token![-], Token![@], kw::saturating),
    NegOverflowing(Token![-], Token![@], kw::overflowing),
}

#[allow(unused)]
#[derive(Clone, Copy)]
enum OpsMode {
    Default,
    Checked(Token![@], kw::checked),
    Strict(Token![@], kw::strict),
    Wrapping(Token![@], kw::wrapping),
    Saturating(Token![@], kw::saturating),
    Overflowing(Token![@], kw::overflowing),
    Unbounded(Token![@], kw::unbounded),
}

trait OpsKind {
    type Definition: Parse;
    type Signature: Parse;
}

trait OpsKindFwd {
    type Definition: Parse;
    type Expression: Parse;
    type Signature: Parse;
}

impl OpsKind for OpsStdKindAssign {
    type Definition = OpsDefinition<OpsAssign>;
    type Signature = OpsStdSignatureAssign;
}

impl OpsKind for OpsStdKindBinary {
    type Definition = OpsDefinition<OpsBinary>;
    type Signature = OpsStdSignatureBinary;
}

impl OpsKind for OpsStdKindUnary {
    type Definition = OpsDefinition<OpsUnary>;
    type Signature = OpsStdSignatureUnary;
}

impl OpsKind for OpsNdKindAssign {
    type Definition = OpsDefinition<OpsAssignExt>;
    type Signature = OpsNdSignatureAssign;
}

impl OpsKind for OpsNdKindBinary {
    type Definition = OpsDefinition<OpsBinaryExt>;
    type Signature = OpsNdSignatureBinary;
}

impl OpsKind for OpsNdKindUnary {
    type Definition = OpsDefinition<OpsUnaryExt>;
    type Signature = OpsNdSignatureUnary;
}

impl OpsKindFwd for OpsStdKindAssign {
    type Definition = OpsDefinitionFwd<OpsAssign>;
    type Expression = OpsExpressionAssign;
    type Signature = OpsStdSignatureAssign;
}

impl OpsKindFwd for OpsStdKindBinary {
    type Definition = OpsDefinitionFwd<OpsBinary>;
    type Expression = OpsExpressionBinary;
    type Signature = OpsStdSignatureBinary;
}

impl OpsKindFwd for OpsStdKindUnary {
    type Definition = OpsDefinitionFwd<OpsUnary>;
    type Expression = OpsExpressionUnary;
    type Signature = OpsStdSignatureUnary;
}

impl OpsKindFwd for OpsNdKindAssign {
    type Definition = OpsDefinitionFwd<OpsAssignExt>;
    type Expression = OpsExpressionAssign;
    type Signature = OpsNdSignatureAssign;
}

impl OpsKindFwd for OpsNdKindBinary {
    type Definition = OpsDefinitionFwd<OpsBinaryExt>;
    type Expression = OpsExpressionBinary;
    type Signature = OpsNdSignatureBinary;
}

impl OpsKindFwd for OpsNdKindUnary {
    type Definition = OpsDefinitionFwd<OpsUnaryExt>;
    type Expression = OpsExpressionUnary;
    type Signature = OpsNdSignatureUnary;
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

impl Parse for OpsFwd {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<Token![@]>()?;

        let lookahead = input.lookahead1();

        if lookahead.peek(kw::stdmut) {
            input.parse::<kw::stdmut>()?;
            input.parse::<OpsImplFwd<OpsStdKindAssign>>().map(Self::StdAssign)
        } else if lookahead.peek(kw::stdbin) {
            input.parse::<kw::stdbin>()?;
            input.parse::<OpsImplFwd<OpsStdKindBinary>>().map(Self::StdBinary)
        } else if lookahead.peek(kw::stdun) {
            input.parse::<kw::stdun>()?;
            input.parse::<OpsImplFwd<OpsStdKindUnary>>().map(Self::StdUnary)
        } else if lookahead.peek(kw::ndmut) {
            input.parse::<kw::ndmut>()?;
            input.parse::<OpsImplFwd<OpsNdKindAssign>>().map(Self::NdAssign)
        } else if lookahead.peek(kw::ndbin) {
            input.parse::<kw::ndbin>()?;
            input.parse::<OpsImplFwd<OpsNdKindBinary>>().map(Self::NdBinary)
        } else if lookahead.peek(kw::ndun) {
            input.parse::<kw::ndun>()?;
            input.parse::<OpsImplFwd<OpsNdKindUnary>>().map(Self::NdUnary)
        } else {
            Err(lookahead.error())
        }
    }
}

impl<Kind: OpsKind> Parse for OpsImpl<Kind> {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            token: input.parse()?,
            signature: input.parse()?,
            colon: input.parse()?,
            definitions_bracket: bracketed!(content in input),
            definitions: content.parse_terminated(Kind::Definition::parse, Token![,])?,
        })
    }
}

impl<Kind: OpsKindFwd> Parse for OpsImplFwd<Kind> {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            token: input.parse()?,
            signature: input.parse()?,
            colon: input.parse()?,
            expression: input.parse()?,
            definitions_bracket: bracketed!(content in input),
            definitions: content.parse_terminated(Kind::Definition::parse, Token![,])?,
        })
    }
}

impl Parse for OpsStdSignatureAssign {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let generics = input.parse::<Generics>()?;
        let conditions = input.parse().ok();
        let paren = parenthesized!(content in input);
        let lhs_pat: PatType = content.parse()?;
        let comma = content.parse()?;
        let rhs_star = content.parse()?;
        let rhs_pat: PatType = content.parse()?;

        let lhs_ty = match *lhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_some() => (*val.elem).clone(),
            _ => {
                return Err(Error::new_spanned(
                    lhs_pat.ty,
                    "Failed to parse signature, lhs expected to be mutable reference",
                ));
            },
        };

        let (rhs_ty, rhs_ref) = match *rhs_pat.ty {
            Type::Reference(ref val) => match val.mutability {
                Some(_) => {
                    return Err(Error::new_spanned(
                        rhs_pat.ty,
                        "Failed to parse signature, rhs expected to be reference",
                    ));
                },
                None => ((*val.elem).clone(), Some(Default::default())),
            },
            ref val => (val.clone(), None),
        };

        Ok(Self {
            generics,
            conditions,
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

        let generics = input.parse::<Generics>()?;
        let conditions = input.parse().ok();
        let paren = parenthesized!(content in input);
        let lhs_star = content.parse()?;
        let lhs_pat: PatType = content.parse()?;
        let comma = content.parse()?;
        let rhs_star = content.parse()?;
        let rhs_pat: PatType = content.parse()?;
        let arrow = input.parse()?;
        let res_ty = input.parse()?;

        let (lhs_ty, lhs_ref) = match *lhs_pat.ty {
            Type::Reference(ref val) => match val.mutability {
                Some(_) => {
                    return Err(Error::new_spanned(
                        lhs_pat.ty,
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
                    return Err(Error::new_spanned(
                        rhs_pat.ty,
                        "Failed to parse signature, rhs expected to be reference",
                    ));
                },
                None => ((*val.elem).clone(), Some(Default::default())),
            },
            ref val => (val.clone(), None),
        };

        Ok(Self {
            generics,
            conditions,
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
            res_ty,
        })
    }
}

impl Parse for OpsStdSignatureUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let generics = input.parse::<Generics>()?;
        let conditions = input.parse().ok();
        let paren = parenthesized!(content in input);
        let self_star = content.parse()?;
        let self_pat: PatType = content.parse()?;
        let arrow = input.parse()?;
        let res_ty = input.parse()?;

        let (self_ty, self_ref) = match *self_pat.ty {
            Type::Reference(ref val) => match val.mutability {
                Some(_) => {
                    return Err(Error::new_spanned(
                        self_pat.ty,
                        "Failed to parse signature, self expected to be reference",
                    ));
                },
                None => ((*val.elem).clone(), Some(Default::default())),
            },
            ref val => (val.clone(), None),
        };

        Ok(Self {
            generics,
            conditions,
            paren,
            self_star,
            self_pat,
            self_ref,
            self_ty,
            arrow,
            res_ty,
        })
    }
}

impl Parse for OpsNdSignatureAssign {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let generics = input.parse::<Generics>()?;
        let conditions = input.parse().ok();
        let paren = parenthesized!(content in input);
        let lhs_pat: PatType = content.parse()?;
        let comma = content.parse()?;
        let rhs_pat: PatType = content.parse()?;
        let impl_ty = input.parse()?;

        let lhs_ty = match *lhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_some() => (*val.elem).clone(),
            ref val => val.clone(),
        };

        let rhs_ty = match *rhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            ref val => val.clone(),
        };

        Ok(Self {
            generics,
            conditions,
            paren,
            lhs_pat,
            lhs_ty,
            comma,
            rhs_pat,
            rhs_ty,
            impl_ty,
        })
    }
}

impl Parse for OpsNdSignatureBinary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let generics = input.parse::<Generics>()?;
        let conditions = input.parse().ok();
        let paren = parenthesized!(content in input);
        let lhs_pat: PatType = content.parse()?;
        let comma = content.parse()?;
        let rhs_pat: PatType = content.parse()?;
        let arrow = input.parse()?;
        let res_ty = input.parse()?;
        let impl_ty = input.parse()?;

        let lhs_ty = match *lhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            ref val => val.clone(),
        };

        let rhs_ty = match *rhs_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            ref val => val.clone(),
        };

        Ok(Self {
            generics,
            conditions,
            paren,
            lhs_pat,
            lhs_ty,
            comma,
            rhs_pat,
            rhs_ty,
            arrow,
            res_ty,
            impl_ty,
        })
    }
}

impl Parse for OpsNdSignatureUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let generics = input.parse::<Generics>()?;
        let conditions = input.parse().ok();
        let paren = parenthesized!(content in input);
        let self_pat: PatType = content.parse()?;
        let arrow = input.parse()?;
        let res_ty = input.parse()?;
        let impl_ty = input.parse()?;

        let self_ty = match *self_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            ref val => val.clone(),
        };

        Ok(Self {
            generics,
            conditions,
            paren,
            self_pat,
            self_ty,
            arrow,
            res_ty,
            impl_ty,
        })
    }
}

impl Parse for OpsNdImplType {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(Token![for]) {
            return Ok(Self::Empty);
        }

        if !input.peek2(Bracket) {
            return Ok(Self::Single(input.parse()?));
        }

        Ok(Self::Multiple(input.parse()?))
    }
}

impl Parse for OpsNdImplTypeSingle {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            token: input.parse()?,
            impl_ty: input.parse()?,
        })
    }
}

impl Parse for OpsNdImplTypeMultiple {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let token = input.parse()?;
        let _ = bracketed!(content in input);
        let impl_ty = content.parse_terminated(Type::parse, Token![,])?;

        Ok(Self { token, impl_ty })
    }
}

impl Parse for OpsExpressionAssign {
    fn parse(input: ParseStream) -> Result<Self> {
        let ty_content;
        let lhs_content;
        let rhs_content;

        Ok(Self {
            ty_paren: parenthesized!(ty_content in input),
            ty_expr: ty_content.parse()?,
            lhs_paren: parenthesized!(lhs_content in input),
            lhs_expr: lhs_content.parse()?,
            rhs_paren: parenthesized!(rhs_content in input),
            rhs_expr: rhs_content.parse()?,
        })
    }
}

impl Parse for OpsExpressionBinary {
    fn parse(input: ParseStream) -> Result<Self> {
        let ty_content;
        let lhs_content;
        let rhs_content;

        Ok(Self {
            ty_paren: parenthesized!(ty_content in input),
            ty_expr: ty_content.parse()?,
            lhs_paren: parenthesized!(lhs_content in input),
            lhs_expr: lhs_content.parse()?,
            rhs_paren: parenthesized!(rhs_content in input),
            rhs_expr: rhs_content.parse()?,
        })
    }
}

impl Parse for OpsExpressionUnary {
    fn parse(input: ParseStream) -> Result<Self> {
        let ty_content;
        let self_content;

        Ok(Self {
            ty_paren: parenthesized!(ty_content in input),
            ty_expr: ty_content.parse()?,
            self_paren: parenthesized!(self_content in input),
            self_expr: self_content.parse()?,
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

impl<Operation: Parse> Parse for OpsDefinitionFwd<Operation> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            op: input.parse()?,
            conditions: input.parse().ok(),
        })
    }
}

impl Parse for OpsConditions {
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

        if lookahead.peek(Token![!]) {
            input.parse::<Token![!]>().map(Self::Not)
        } else if lookahead.peek(Token![-]) {
            input.parse::<Token![-]>().map(Self::Neg)
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsAssignExt {
    fn parse(input: ParseStream) -> Result<Self> {
        let op = input.parse::<OpsAssign>()?;

        if !input.peek(Token![@]) {
            return Ok(Self::from(op));
        }

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::strict) {
            let ext = input.parse()?;

            match op {
                OpsAssign::Add(val) => Ok(Self::AddStrict(val, token, ext)),
                OpsAssign::Sub(val) => Ok(Self::SubStrict(val, token, ext)),
                OpsAssign::Mul(val) => Ok(Self::MulStrict(val, token, ext)),
                OpsAssign::Div(val) => Ok(Self::DivStrict(val, token, ext)),
                OpsAssign::Rem(val) => Ok(Self::RemStrict(val, token, ext)),
                OpsAssign::Shl(val) => Ok(Self::ShlStrict(val, token, ext)),
                OpsAssign::Shr(val) => Ok(Self::ShrStrict(val, token, ext)),
                OpsAssign::BitOr(_) | OpsAssign::BitAnd(_) | OpsAssign::BitXor(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse bitwise operation, @strict is unsupported",
                )),
            }
        } else if lookahead.peek(kw::wrapping) {
            let ext = input.parse()?;

            match op {
                OpsAssign::Add(val) => Ok(Self::AddWrapping(val, token, ext)),
                OpsAssign::Sub(val) => Ok(Self::SubWrapping(val, token, ext)),
                OpsAssign::Mul(val) => Ok(Self::MulWrapping(val, token, ext)),
                OpsAssign::Div(val) => Ok(Self::DivWrapping(val, token, ext)),
                OpsAssign::Rem(val) => Ok(Self::RemWrapping(val, token, ext)),
                OpsAssign::BitOr(_) | OpsAssign::BitAnd(_) | OpsAssign::BitXor(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse bitwise operation, @wrapping is unsupported",
                )),
                OpsAssign::Shl(_) | OpsAssign::Shr(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse shift operation, @wrapping is unsupported",
                )),
            }
        } else if lookahead.peek(kw::saturating) {
            let ext = input.parse()?;

            match op {
                OpsAssign::Add(val) => Ok(Self::AddSaturating(val, token, ext)),
                OpsAssign::Sub(val) => Ok(Self::SubSaturating(val, token, ext)),
                OpsAssign::Mul(val) => Ok(Self::MulSaturating(val, token, ext)),
                OpsAssign::Div(val) => Ok(Self::DivSaturating(val, token, ext)),
                OpsAssign::Rem(val) => Ok(Self::RemSaturating(val, token, ext)),
                OpsAssign::BitOr(_) | OpsAssign::BitAnd(_) | OpsAssign::BitXor(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse bitwise operation, @saturating is unsupported",
                )),
                OpsAssign::Shl(_) | OpsAssign::Shr(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse shift operation, @saturating is unsupported",
                )),
            }
        } else if lookahead.peek(kw::unbounded) {
            let ext = input.parse()?;

            match op {
                OpsAssign::Shl(val) => Ok(Self::ShlUnbounded(val, token, ext)),
                OpsAssign::Shr(val) => Ok(Self::ShrUnbounded(val, token, ext)),
                OpsAssign::Add(_) | OpsAssign::Sub(_) | OpsAssign::Mul(_) | OpsAssign::Div(_) | OpsAssign::Rem(_) => {
                    Err(Error::new_spanned(
                        ext,
                        "Failed to parse arithmetic operation, @unbounded is unsupported",
                    ))
                },
                OpsAssign::BitOr(_) | OpsAssign::BitAnd(_) | OpsAssign::BitXor(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse bitwise operation, @unbounded is unsupported",
                )),
            }
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsBinaryExt {
    fn parse(input: ParseStream) -> Result<Self> {
        let op = input.parse::<OpsBinary>()?;

        if !input.peek(Token![@]) {
            return Ok(Self::from(op));
        }

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::checked) {
            let ext = input.parse()?;

            match op {
                OpsBinary::Add(val) => Ok(Self::AddChecked(val, token, ext)),
                OpsBinary::Sub(val) => Ok(Self::SubChecked(val, token, ext)),
                OpsBinary::Mul(val) => Ok(Self::MulChecked(val, token, ext)),
                OpsBinary::Div(val) => Ok(Self::DivChecked(val, token, ext)),
                OpsBinary::Rem(val) => Ok(Self::RemChecked(val, token, ext)),
                OpsBinary::Shl(val) => Ok(Self::ShlChecked(val, token, ext)),
                OpsBinary::Shr(val) => Ok(Self::ShrChecked(val, token, ext)),
                OpsBinary::BitOr(_) | OpsBinary::BitAnd(_) | OpsBinary::BitXor(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse bitwise operation, @checked is unsupported",
                )),
            }
        } else if lookahead.peek(kw::strict) {
            let ext = input.parse()?;

            match op {
                OpsBinary::Add(val) => Ok(Self::AddStrict(val, token, ext)),
                OpsBinary::Sub(val) => Ok(Self::SubStrict(val, token, ext)),
                OpsBinary::Mul(val) => Ok(Self::MulStrict(val, token, ext)),
                OpsBinary::Div(val) => Ok(Self::DivStrict(val, token, ext)),
                OpsBinary::Rem(val) => Ok(Self::RemStrict(val, token, ext)),
                OpsBinary::Shl(val) => Ok(Self::ShlStrict(val, token, ext)),
                OpsBinary::Shr(val) => Ok(Self::ShrStrict(val, token, ext)),
                OpsBinary::BitOr(_) | OpsBinary::BitAnd(_) | OpsBinary::BitXor(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse bitwise operation, @strict is unsupported",
                )),
            }
        } else if lookahead.peek(kw::wrapping) {
            let ext = input.parse()?;

            match op {
                OpsBinary::Add(val) => Ok(Self::AddWrapping(val, token, ext)),
                OpsBinary::Sub(val) => Ok(Self::SubWrapping(val, token, ext)),
                OpsBinary::Mul(val) => Ok(Self::MulWrapping(val, token, ext)),
                OpsBinary::Div(val) => Ok(Self::DivWrapping(val, token, ext)),
                OpsBinary::Rem(val) => Ok(Self::RemWrapping(val, token, ext)),
                OpsBinary::BitOr(_) | OpsBinary::BitAnd(_) | OpsBinary::BitXor(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse bitwise operation, @wrapping is unsupported",
                )),
                OpsBinary::Shl(_) | OpsBinary::Shr(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse shift operation, @wrapping is unsupported",
                )),
            }
        } else if lookahead.peek(kw::saturating) {
            let ext = input.parse()?;

            match op {
                OpsBinary::Add(val) => Ok(Self::AddSaturating(val, token, ext)),
                OpsBinary::Sub(val) => Ok(Self::SubSaturating(val, token, ext)),
                OpsBinary::Mul(val) => Ok(Self::MulSaturating(val, token, ext)),
                OpsBinary::Div(val) => Ok(Self::DivSaturating(val, token, ext)),
                OpsBinary::Rem(val) => Ok(Self::RemSaturating(val, token, ext)),
                OpsBinary::BitOr(_) | OpsBinary::BitAnd(_) | OpsBinary::BitXor(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse bitwise operation, @saturating is unsupported",
                )),
                OpsBinary::Shl(_) | OpsBinary::Shr(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse shift operation, @saturating is unsupported",
                )),
            }
        } else if lookahead.peek(kw::overflowing) {
            let ext = input.parse()?;

            match op {
                OpsBinary::Add(val) => Ok(Self::AddOverflowing(val, token, ext)),
                OpsBinary::Sub(val) => Ok(Self::SubOverflowing(val, token, ext)),
                OpsBinary::Mul(val) => Ok(Self::MulOverflowing(val, token, ext)),
                OpsBinary::Div(val) => Ok(Self::DivOverflowing(val, token, ext)),
                OpsBinary::Rem(val) => Ok(Self::RemOverflowing(val, token, ext)),
                OpsBinary::Shl(val) => Ok(Self::ShlOverflowing(val, token, ext)),
                OpsBinary::Shr(val) => Ok(Self::ShrOverflowing(val, token, ext)),
                OpsBinary::BitOr(_) | OpsBinary::BitAnd(_) | OpsBinary::BitXor(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse bitwise operation, @overflowing is unsupported",
                )),
            }
        } else if lookahead.peek(kw::unbounded) {
            let ext = input.parse()?;

            match op {
                OpsBinary::Shl(val) => Ok(Self::ShlUnbounded(val, token, ext)),
                OpsBinary::Shr(val) => Ok(Self::ShrUnbounded(val, token, ext)),
                OpsBinary::Add(_) | OpsBinary::Sub(_) | OpsBinary::Mul(_) | OpsBinary::Div(_) | OpsBinary::Rem(_) => {
                    Err(Error::new_spanned(
                        ext,
                        "Failed to parse arithmetic operation, @unbounded is unsupported",
                    ))
                },
                OpsBinary::BitOr(_) | OpsBinary::BitAnd(_) | OpsBinary::BitXor(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse bitwise operation, @unbounded is unsupported",
                )),
            }
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsUnaryExt {
    fn parse(input: ParseStream) -> Result<Self> {
        let op = input.parse::<OpsUnary>()?;

        if !input.peek(Token![@]) {
            return Ok(Self::from(op));
        }

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::checked) {
            let ext = input.parse()?;

            match op {
                OpsUnary::Neg(val) => Ok(Self::NegChecked(val, token, ext)),
                OpsUnary::Not(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse not operation, @checked is unsupported",
                )),
            }
        } else if lookahead.peek(kw::strict) {
            let ext = input.parse()?;

            match op {
                OpsUnary::Neg(val) => Ok(Self::NegStrict(val, token, ext)),
                OpsUnary::Not(_) => {
                    Err(Error::new_spanned(ext, "Failed to parse not operation, @strict is unsupported"))
                },
            }
        } else if lookahead.peek(kw::wrapping) {
            let ext = input.parse()?;

            match op {
                OpsUnary::Neg(val) => Ok(Self::NegWrapping(val, token, ext)),
                OpsUnary::Not(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse not operation, @wrapping is unsupported",
                )),
            }
        } else if lookahead.peek(kw::saturating) {
            let ext = input.parse()?;

            match op {
                OpsUnary::Neg(val) => Ok(Self::NegSaturating(val, token, ext)),
                OpsUnary::Not(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse not operation, @saturating is unsupported",
                )),
            }
        } else if lookahead.peek(kw::overflowing) {
            let ext = input.parse()?;

            match op {
                OpsUnary::Neg(val) => Ok(Self::NegOverflowing(val, token, ext)),
                OpsUnary::Not(_) => Err(Error::new_spanned(
                    ext,
                    "Failed to parse not operation, @overflowing is unsupported",
                )),
            }
        } else {
            Err(lookahead.error())
        }
    }
}

impl ToTokens for OpsImpl<OpsStdKindAssign> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        #[derive(Clone, Copy)]
        struct OpsSpec<'ops> {
            signature: &'ops OpsStdSignatureAssign,
            op: &'ops OpsAssign,
            expr: &'ops Expr,
            conditions: Option<&'ops OpsConditions>,
        }

        fn get_impl(spec: OpsSpec, rhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.get_ident();
            let path = spec.op.get_path();

            let (gen_impl, _, _) = spec.signature.generics.split_for_impl();

            let sig_predicates = spec.signature.conditions.as_ref().map(|val| val.predicates.iter());
            let op_predicates = spec.conditions.map(|val| val.predicates.iter());

            let gen_where = match (sig_predicates, op_predicates) {
                (Some(sig), Some(op)) => quote! { where #(#sig,)* #(#op,)* },
                (Some(sig), None) => quote! { where #(#sig,)* },
                (None, Some(op)) => quote! { where #(#op,)* },
                (None, None) => quote! { where },
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
                signature: &self.signature,
                op: &definition.op,
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
            signature: &'ops OpsStdSignatureBinary,
            op: &'ops OpsBinary,
            expr: &'ops Expr,
            conditions: Option<&'ops OpsConditions>,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>, rhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.get_ident();
            let path = spec.op.get_path();

            let (gen_impl, _, _) = spec.signature.generics.split_for_impl();

            let sig_predicates = spec.signature.conditions.as_ref().map(|val| val.predicates.iter());
            let op_predicates = spec.conditions.map(|val| val.predicates.iter());

            let gen_where = match (sig_predicates, op_predicates) {
                (Some(sig), Some(op)) => quote! { where #(#sig,)* #(#op,)* },
                (Some(sig), None) => quote! { where #(#sig,)* },
                (None, Some(op)) => quote! { where #(#op,)* },
                (None, None) => quote! { where },
            };

            let lhs_pat = &spec.signature.lhs_pat.pat;
            let lhs_ty = &spec.signature.lhs_ty;
            let rhs_pat = &spec.signature.rhs_pat.pat;
            let rhs_ty = &spec.signature.rhs_ty;
            let res_ty = &spec.signature.res_ty;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path<#rhs_ref #rhs_ty> for #lhs_ref #lhs_ty #gen_where {
                    type Output = #res_ty;

                    fn #ident(self, rhs: #rhs_ref #rhs_ty) -> Self::Output {
                        #[allow(clippy::needless_borrow)]
                        <#res_ty>::from((|#lhs_pat: #lhs_ref #lhs_ty, #rhs_pat: #rhs_ref #rhs_ty| { #expr })(self, rhs))
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
                signature: &self.signature,
                op: &definition.op,
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
            signature: &'ops OpsStdSignatureUnary,
            op: &'ops OpsUnary,
            expr: &'ops Expr,
            conditions: Option<&'ops OpsConditions>,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.get_ident();
            let path = spec.op.get_path();

            let (gen_impl, _, _) = spec.signature.generics.split_for_impl();

            let sig_predicates = spec.signature.conditions.as_ref().map(|val| val.predicates.iter());
            let op_predicates = spec.conditions.map(|val| val.predicates.iter());

            let gen_where = match (sig_predicates, op_predicates) {
                (Some(sig), Some(op)) => quote! { where #(#sig,)* #(#op,)* },
                (Some(sig), None) => quote! { where #(#sig,)* },
                (None, Some(op)) => quote! { where #(#op,)* },
                (None, None) => quote! { where },
            };

            let self_pat = &spec.signature.self_pat.pat;
            let self_ty = &spec.signature.self_ty;
            let res_ty = &spec.signature.res_ty;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path for #lhs_ref #self_ty #gen_where {
                    type Output = #res_ty;

                    fn #ident(self) -> Self::Output {
                        #[allow(clippy::needless_borrow)]
                        <#res_ty>::from((|#self_pat: #lhs_ref #self_ty| { #expr })(self))
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
                signature: &self.signature,
                op: &definition.op,
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
            let ident = definition.op.get_ident();
            let path = definition.op.get_path(self.token);

            let (gen_impl, _, _) = self.signature.generics.split_for_impl();

            let sig_predicates = self.signature.conditions.as_ref().map(|val| val.predicates.iter());
            let op_predicates = definition.conditions.as_ref().map(|val| val.predicates.iter());

            let gen_where = match (sig_predicates, op_predicates) {
                (Some(sig), Some(op)) => quote! { where #(#sig,)* #(#op,)* },
                (Some(sig), None) => quote! { where #(#sig,)* },
                (None, Some(op)) => quote! { where #(#op,)* },
                (None, None) => quote! { where },
            };

            let lhs_pat = &self.signature.lhs_pat;
            let rhs_pat = &self.signature.rhs_pat;
            let lhs_ty = &self.signature.lhs_ty;
            let rhs_ty = &self.signature.rhs_ty;

            let expr = &definition.expr;

            let quote = |impl_ty: &Type| {
                quote! {
                    impl #gen_impl #path<#lhs_ty, #rhs_ty> for #impl_ty #gen_where {
                        fn #ident(#lhs_pat, #rhs_pat) {
                            #expr
                        }
                    }
                }
            };

            match &self.signature.impl_ty {
                OpsNdImplType::Empty => tokens.extend(quote(lhs_ty)),
                OpsNdImplType::Single(val) => tokens.extend(quote(&val.impl_ty)),
                OpsNdImplType::Multiple(val) => val.impl_ty.iter().for_each(|ty| tokens.extend(quote(ty))),
            }
        }
    }
}

impl ToTokens for OpsImpl<OpsNdKindBinary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for definition in &self.definitions {
            let ident = definition.op.get_ident();
            let path = definition.op.get_path(self.token);

            let (gen_impl, _, _) = self.signature.generics.split_for_impl();

            let sig_predicates = self.signature.conditions.as_ref().map(|val| val.predicates.iter());
            let op_predicates = definition.conditions.as_ref().map(|val| val.predicates.iter());

            let gen_where = match (sig_predicates, op_predicates) {
                (Some(sig), Some(op)) => quote! { where #(#sig,)* #(#op,)* },
                (Some(sig), None) => quote! { where #(#sig,)* },
                (None, Some(op)) => quote! { where #(#op,)* },
                (None, None) => quote! { where },
            };

            let lhs_pat = &self.signature.lhs_pat;
            let rhs_pat = &self.signature.rhs_pat;
            let lhs_ty = &self.signature.lhs_ty;
            let rhs_ty = &self.signature.rhs_ty;
            let res_ty = &self.signature.res_ty;
            let ty = definition.op.get_type(res_ty);

            let expr = &definition.expr;

            let quote = |impl_ty: &Type| {
                quote! {
                    impl #gen_impl #path<#lhs_ty, #rhs_ty> for #impl_ty #gen_where {
                        type Type = #res_ty;

                        fn #ident(#lhs_pat, #rhs_pat) -> #ty {
                            <#ty>::from(#expr)
                        }
                    }
                }
            };

            match &self.signature.impl_ty {
                OpsNdImplType::Empty => tokens.extend(quote(res_ty)),
                OpsNdImplType::Single(val) => tokens.extend(quote(&val.impl_ty)),
                OpsNdImplType::Multiple(val) => val.impl_ty.iter().for_each(|ty| tokens.extend(quote(ty))),
            }
        }
    }
}

impl ToTokens for OpsImpl<OpsNdKindUnary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for definition in &self.definitions {
            let ident = definition.op.get_ident();
            let path = definition.op.get_path(self.token);

            let (gen_impl, _, _) = self.signature.generics.split_for_impl();

            let sig_predicates = self.signature.conditions.as_ref().map(|val| val.predicates.iter());
            let op_predicates = definition.conditions.as_ref().map(|val| val.predicates.iter());

            let gen_where = match (sig_predicates, op_predicates) {
                (Some(sig), Some(op)) => quote! { where #(#sig,)* #(#op,)* },
                (Some(sig), None) => quote! { where #(#sig,)* },
                (None, Some(op)) => quote! { where #(#op,)* },
                (None, None) => quote! { where },
            };

            let self_pat = &self.signature.self_pat;
            let self_ty = &self.signature.self_ty;
            let res_ty = &self.signature.res_ty;
            let ty = definition.op.get_type(res_ty);

            let expr = &definition.expr;

            let quote = |impl_ty: &Type| {
                quote! {
                    impl #gen_impl #path<#self_ty> for #impl_ty #gen_where {
                        type Type = #res_ty;

                        fn #ident(#self_pat) -> #ty {
                            <#ty>::from(#expr)
                        }
                    }
                }
            };

            match &self.signature.impl_ty {
                OpsNdImplType::Empty => tokens.extend(quote(res_ty)),
                OpsNdImplType::Single(val) => tokens.extend(quote(&val.impl_ty)),
                OpsNdImplType::Multiple(val) => val.impl_ty.iter().for_each(|ty| tokens.extend(quote(ty))),
            }
        }
    }
}

impl From<OpsImplFwd<OpsStdKindAssign>> for OpsImpl<OpsStdKindAssign> {
    fn from(value: OpsImplFwd<OpsStdKindAssign>) -> Self {
        OpsImpl::<OpsStdKindAssign> {
            token: value.token,
            signature: value.signature,
            colon: Default::default(),
            definitions_bracket: value.definitions_bracket,
            definitions: value
                .definitions
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let ty = &value.expression.ty_expr;
                    let lhs = &value.expression.lhs_expr;
                    let rhs = &value.expression.rhs_expr;
                    let conditions = definition.conditions;

                    let ext = OpsAssignExt::from(op);
                    let ident = ext.get_ident();
                    let path = ext.get_path(value.token);

                    OpsDefinition::<OpsAssign> {
                        op,
                        expr: parse_quote! {{ use #path; #ty::#ident(#lhs, #rhs); }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplFwd<OpsStdKindBinary>> for OpsImpl<OpsStdKindBinary> {
    fn from(value: OpsImplFwd<OpsStdKindBinary>) -> Self {
        OpsImpl::<OpsStdKindBinary> {
            token: value.token,
            signature: value.signature,
            colon: Default::default(),
            definitions_bracket: value.definitions_bracket,
            definitions: value
                .definitions
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let ty = &value.expression.ty_expr;
                    let lhs = &value.expression.lhs_expr;
                    let rhs = &value.expression.rhs_expr;
                    let conditions = definition.conditions;

                    let ext = OpsBinaryExt::from(op);
                    let ident = ext.get_ident();
                    let path = ext.get_path(value.token);

                    OpsDefinition::<OpsBinary> {
                        op,
                        expr: parse_quote! {{ use #path; #ty::#ident(#lhs, #rhs) }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplFwd<OpsStdKindUnary>> for OpsImpl<OpsStdKindUnary> {
    fn from(value: OpsImplFwd<OpsStdKindUnary>) -> Self {
        OpsImpl::<OpsStdKindUnary> {
            token: value.token,
            signature: value.signature,
            colon: Default::default(),
            definitions_bracket: value.definitions_bracket,
            definitions: value
                .definitions
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let ty = &value.expression.ty_expr;
                    let expr = &value.expression.self_expr;
                    let conditions = definition.conditions;

                    let ext = OpsUnaryExt::from(op);
                    let ident = ext.get_ident();
                    let path = ext.get_path(value.token);

                    OpsDefinition::<OpsUnary> {
                        op,
                        expr: parse_quote! {{ use #path; #ty::#ident(#expr) }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplFwd<OpsNdKindAssign>> for OpsImpl<OpsNdKindAssign> {
    fn from(value: OpsImplFwd<OpsNdKindAssign>) -> Self {
        OpsImpl::<OpsNdKindAssign> {
            token: value.token,
            signature: value.signature,
            colon: Default::default(),
            definitions_bracket: value.definitions_bracket,
            definitions: value
                .definitions
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let ty = &value.expression.ty_expr;
                    let lhs = &value.expression.lhs_expr;
                    let rhs = &value.expression.rhs_expr;
                    let conditions = definition.conditions;

                    let ident = op.get_ident();
                    let path = op.get_path(value.token);

                    OpsDefinition::<OpsAssignExt> {
                        op,
                        expr: parse_quote! {{ use #path; #ty::#ident(#lhs, #rhs); }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplFwd<OpsNdKindBinary>> for OpsImpl<OpsNdKindBinary> {
    fn from(value: OpsImplFwd<OpsNdKindBinary>) -> Self {
        OpsImpl::<OpsNdKindBinary> {
            token: value.token,
            signature: value.signature,
            colon: Default::default(),
            definitions_bracket: value.definitions_bracket,
            definitions: value
                .definitions
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let ty = &value.expression.ty_expr;
                    let lhs = &value.expression.lhs_expr;
                    let rhs = &value.expression.rhs_expr;
                    let conditions = definition.conditions;

                    let ident = op.get_ident();
                    let path = op.get_path(value.token);

                    OpsDefinition::<OpsBinaryExt> {
                        op,
                        expr: parse_quote! {{ use #path; #ty::#ident(#lhs, #rhs) }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplFwd<OpsNdKindUnary>> for OpsImpl<OpsNdKindUnary> {
    fn from(value: OpsImplFwd<OpsNdKindUnary>) -> Self {
        OpsImpl::<OpsNdKindUnary> {
            token: value.token,
            signature: value.signature,
            colon: Default::default(),
            definitions_bracket: value.definitions_bracket,
            definitions: value
                .definitions
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let ty = &value.expression.ty_expr;
                    let expr = &value.expression.self_expr;
                    let conditions = definition.conditions;

                    let ident = op.get_ident();
                    let path = op.get_path(value.token);

                    OpsDefinition::<OpsUnaryExt> {
                        op,
                        expr: parse_quote! {{ use #path; #ty::#ident(#expr) }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsAssign> for OpsAssignExt {
    fn from(value: OpsAssign) -> Self {
        match value {
            OpsAssign::Add(token) => Self::Add(token),
            OpsAssign::Sub(token) => Self::Sub(token),
            OpsAssign::Mul(token) => Self::Mul(token),
            OpsAssign::Div(token) => Self::Div(token),
            OpsAssign::Rem(token) => Self::Rem(token),
            OpsAssign::BitOr(token) => Self::BitOr(token),
            OpsAssign::BitAnd(token) => Self::BitAnd(token),
            OpsAssign::BitXor(token) => Self::BitXor(token),
            OpsAssign::Shl(token) => Self::Shl(token),
            OpsAssign::Shr(token) => Self::Shr(token),
        }
    }
}

impl From<OpsBinary> for OpsBinaryExt {
    fn from(value: OpsBinary) -> Self {
        match value {
            OpsBinary::Add(token) => Self::Add(token),
            OpsBinary::Sub(token) => Self::Sub(token),
            OpsBinary::Mul(token) => Self::Mul(token),
            OpsBinary::Div(token) => Self::Div(token),
            OpsBinary::Rem(token) => Self::Rem(token),
            OpsBinary::BitOr(token) => Self::BitOr(token),
            OpsBinary::BitAnd(token) => Self::BitAnd(token),
            OpsBinary::BitXor(token) => Self::BitXor(token),
            OpsBinary::Shl(token) => Self::Shl(token),
            OpsBinary::Shr(token) => Self::Shr(token),
        }
    }
}

impl From<OpsUnary> for OpsUnaryExt {
    fn from(value: OpsUnary) -> Self {
        match value {
            OpsUnary::Not(token) => Self::Not(token),
            OpsUnary::Neg(token) => Self::Neg(token),
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
            OpsUnary::Not(_) => parse_quote! { not },
            OpsUnary::Neg(_) => parse_quote! { neg },
        }
    }

    fn get_path(&self) -> Path {
        match self {
            OpsUnary::Not(_) => parse_quote! { std::ops::Not },
            OpsUnary::Neg(_) => parse_quote! { std::ops::Neg },
        }
    }
}

impl OpsAssignExt {
    fn get_ident(&self) -> Ident {
        match self {
            OpsAssignExt::Add(_) => parse_quote! { nd_add_assign },
            OpsAssignExt::Sub(_) => parse_quote! { nd_sub_assign },
            OpsAssignExt::Mul(_) => parse_quote! { nd_mul_assign },
            OpsAssignExt::Div(_) => parse_quote! { nd_div_assign },
            OpsAssignExt::Rem(_) => parse_quote! { nd_rem_assign },
            OpsAssignExt::BitOr(_) => parse_quote! { nd_bitor_assign },
            OpsAssignExt::BitAnd(_) => parse_quote! { nd_bitand_assign },
            OpsAssignExt::BitXor(_) => parse_quote! { nd_bitxor_assign },
            OpsAssignExt::Shl(_) => parse_quote! { nd_shl_assign },
            OpsAssignExt::Shr(_) => parse_quote! { nd_shr_assign },
            OpsAssignExt::AddStrict(_, _, _) => parse_quote! { nd_add_assign_strict },
            OpsAssignExt::SubStrict(_, _, _) => parse_quote! { nd_sub_assign_strict },
            OpsAssignExt::MulStrict(_, _, _) => parse_quote! { nd_mul_assign_strict },
            OpsAssignExt::DivStrict(_, _, _) => parse_quote! { nd_div_assign_strict },
            OpsAssignExt::RemStrict(_, _, _) => parse_quote! { nd_rem_assign_strict },
            OpsAssignExt::ShlStrict(_, _, _) => parse_quote! { nd_shl_assign_strict },
            OpsAssignExt::ShrStrict(_, _, _) => parse_quote! { nd_shr_assign_strict },
            OpsAssignExt::AddWrapping(_, _, _) => parse_quote! { nd_add_assign_wrapping },
            OpsAssignExt::SubWrapping(_, _, _) => parse_quote! { nd_sub_assign_wrapping },
            OpsAssignExt::MulWrapping(_, _, _) => parse_quote! { nd_mul_assign_wrapping },
            OpsAssignExt::DivWrapping(_, _, _) => parse_quote! { nd_div_assign_wrapping },
            OpsAssignExt::RemWrapping(_, _, _) => parse_quote! { nd_rem_assign_wrapping },
            OpsAssignExt::AddSaturating(_, _, _) => parse_quote! { nd_add_assign_saturating },
            OpsAssignExt::SubSaturating(_, _, _) => parse_quote! { nd_sub_assign_saturating },
            OpsAssignExt::MulSaturating(_, _, _) => parse_quote! { nd_mul_assign_saturating },
            OpsAssignExt::DivSaturating(_, _, _) => parse_quote! { nd_div_assign_saturating },
            OpsAssignExt::RemSaturating(_, _, _) => parse_quote! { nd_rem_assign_saturating },
            OpsAssignExt::ShlUnbounded(_, _, _) => parse_quote! { nd_shl_assign_unbounded },
            OpsAssignExt::ShrUnbounded(_, _, _) => parse_quote! { nd_shr_assign_unbounded },
        }
    }

    fn get_path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndcore });

        match self {
            OpsAssignExt::Add(_) => parse_quote! { #prefix::ops::NdAddAssign },
            OpsAssignExt::Sub(_) => parse_quote! { #prefix::ops::NdSubAssign },
            OpsAssignExt::Mul(_) => parse_quote! { #prefix::ops::NdMulAssign },
            OpsAssignExt::Div(_) => parse_quote! { #prefix::ops::NdDivAssign },
            OpsAssignExt::Rem(_) => parse_quote! { #prefix::ops::NdRemAssign },
            OpsAssignExt::BitOr(_) => parse_quote! { #prefix::ops::NdBitOrAssign },
            OpsAssignExt::BitAnd(_) => parse_quote! { #prefix::ops::NdBitAndAssign },
            OpsAssignExt::BitXor(_) => parse_quote! { #prefix::ops::NdBitXorAssign },
            OpsAssignExt::Shl(_) => parse_quote! { #prefix::ops::NdShlAssign },
            OpsAssignExt::Shr(_) => parse_quote! { #prefix::ops::NdShrAssign },
            OpsAssignExt::AddStrict(_, _, _) => parse_quote! { #prefix::ops::NdAddAssignStrict },
            OpsAssignExt::SubStrict(_, _, _) => parse_quote! { #prefix::ops::NdSubAssignStrict },
            OpsAssignExt::MulStrict(_, _, _) => parse_quote! { #prefix::ops::NdMulAssignStrict },
            OpsAssignExt::DivStrict(_, _, _) => parse_quote! { #prefix::ops::NdDivAssignStrict },
            OpsAssignExt::RemStrict(_, _, _) => parse_quote! { #prefix::ops::NdRemAssignStrict },
            OpsAssignExt::ShlStrict(_, _, _) => parse_quote! { #prefix::ops::NdShlAssignStrict },
            OpsAssignExt::ShrStrict(_, _, _) => parse_quote! { #prefix::ops::NdShrAssignStrict },
            OpsAssignExt::AddWrapping(_, _, _) => parse_quote! { #prefix::ops::NdAddAssignWrapping },
            OpsAssignExt::SubWrapping(_, _, _) => parse_quote! { #prefix::ops::NdSubAssignWrapping },
            OpsAssignExt::MulWrapping(_, _, _) => parse_quote! { #prefix::ops::NdMulAssignWrapping },
            OpsAssignExt::DivWrapping(_, _, _) => parse_quote! { #prefix::ops::NdDivAssignWrapping },
            OpsAssignExt::RemWrapping(_, _, _) => parse_quote! { #prefix::ops::NdRemAssignWrapping },
            OpsAssignExt::AddSaturating(_, _, _) => parse_quote! { #prefix::ops::NdAddAssignSaturating },
            OpsAssignExt::SubSaturating(_, _, _) => parse_quote! { #prefix::ops::NdSubAssignSaturating },
            OpsAssignExt::MulSaturating(_, _, _) => parse_quote! { #prefix::ops::NdMulAssignSaturating },
            OpsAssignExt::DivSaturating(_, _, _) => parse_quote! { #prefix::ops::NdDivAssignSaturating },
            OpsAssignExt::RemSaturating(_, _, _) => parse_quote! { #prefix::ops::NdRemAssignSaturating },
            OpsAssignExt::ShlUnbounded(_, _, _) => parse_quote! { #prefix::ops::NdShlAssignUnbounded },
            OpsAssignExt::ShrUnbounded(_, _, _) => parse_quote! { #prefix::ops::NdShrAssignUnbounded },
        }
    }
}

impl OpsBinaryExt {
    fn get_ident(&self) -> Ident {
        match self {
            OpsBinaryExt::Add(_) => parse_quote! { nd_add },
            OpsBinaryExt::Sub(_) => parse_quote! { nd_sub },
            OpsBinaryExt::Mul(_) => parse_quote! { nd_mul },
            OpsBinaryExt::Div(_) => parse_quote! { nd_div },
            OpsBinaryExt::Rem(_) => parse_quote! { nd_rem },
            OpsBinaryExt::BitOr(_) => parse_quote! { nd_bitor },
            OpsBinaryExt::BitAnd(_) => parse_quote! { nd_bitand },
            OpsBinaryExt::BitXor(_) => parse_quote! { nd_bitxor },
            OpsBinaryExt::Shl(_) => parse_quote! { nd_shl },
            OpsBinaryExt::Shr(_) => parse_quote! { nd_shr },
            OpsBinaryExt::AddChecked(_, _, _) => parse_quote! { nd_add_checked },
            OpsBinaryExt::SubChecked(_, _, _) => parse_quote! { nd_sub_checked },
            OpsBinaryExt::MulChecked(_, _, _) => parse_quote! { nd_mul_checked },
            OpsBinaryExt::DivChecked(_, _, _) => parse_quote! { nd_div_checked },
            OpsBinaryExt::RemChecked(_, _, _) => parse_quote! { nd_rem_checked },
            OpsBinaryExt::ShlChecked(_, _, _) => parse_quote! { nd_shl_checked },
            OpsBinaryExt::ShrChecked(_, _, _) => parse_quote! { nd_shr_checked },
            OpsBinaryExt::AddStrict(_, _, _) => parse_quote! { nd_add_strict },
            OpsBinaryExt::SubStrict(_, _, _) => parse_quote! { nd_sub_strict },
            OpsBinaryExt::MulStrict(_, _, _) => parse_quote! { nd_mul_strict },
            OpsBinaryExt::DivStrict(_, _, _) => parse_quote! { nd_div_strict },
            OpsBinaryExt::RemStrict(_, _, _) => parse_quote! { nd_rem_strict },
            OpsBinaryExt::ShlStrict(_, _, _) => parse_quote! { nd_shl_strict },
            OpsBinaryExt::ShrStrict(_, _, _) => parse_quote! { nd_shr_strict },
            OpsBinaryExt::AddWrapping(_, _, _) => parse_quote! { nd_add_wrapping },
            OpsBinaryExt::SubWrapping(_, _, _) => parse_quote! { nd_sub_wrapping },
            OpsBinaryExt::MulWrapping(_, _, _) => parse_quote! { nd_mul_wrapping },
            OpsBinaryExt::DivWrapping(_, _, _) => parse_quote! { nd_div_wrapping },
            OpsBinaryExt::RemWrapping(_, _, _) => parse_quote! { nd_rem_wrapping },
            OpsBinaryExt::AddSaturating(_, _, _) => parse_quote! { nd_add_saturating },
            OpsBinaryExt::SubSaturating(_, _, _) => parse_quote! { nd_sub_saturating },
            OpsBinaryExt::MulSaturating(_, _, _) => parse_quote! { nd_mul_saturating },
            OpsBinaryExt::DivSaturating(_, _, _) => parse_quote! { nd_div_saturating },
            OpsBinaryExt::RemSaturating(_, _, _) => parse_quote! { nd_rem_saturating },
            OpsBinaryExt::AddOverflowing(_, _, _) => parse_quote! { nd_add_overflowing },
            OpsBinaryExt::SubOverflowing(_, _, _) => parse_quote! { nd_sub_overflowing },
            OpsBinaryExt::MulOverflowing(_, _, _) => parse_quote! { nd_mul_overflowing },
            OpsBinaryExt::DivOverflowing(_, _, _) => parse_quote! { nd_div_overflowing },
            OpsBinaryExt::RemOverflowing(_, _, _) => parse_quote! { nd_rem_overflowing },
            OpsBinaryExt::ShlOverflowing(_, _, _) => parse_quote! { nd_shl_overflowing },
            OpsBinaryExt::ShrOverflowing(_, _, _) => parse_quote! { nd_shr_overflowing },
            OpsBinaryExt::ShlUnbounded(_, _, _) => parse_quote! { nd_shl_unbounded },
            OpsBinaryExt::ShrUnbounded(_, _, _) => parse_quote! { nd_shr_unbounded },
        }
    }

    fn get_path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndcore });

        match self {
            OpsBinaryExt::Add(_) => parse_quote! { #prefix::ops::NdAdd },
            OpsBinaryExt::Sub(_) => parse_quote! { #prefix::ops::NdSub },
            OpsBinaryExt::Mul(_) => parse_quote! { #prefix::ops::NdMul },
            OpsBinaryExt::Div(_) => parse_quote! { #prefix::ops::NdDiv },
            OpsBinaryExt::Rem(_) => parse_quote! { #prefix::ops::NdRem },
            OpsBinaryExt::BitOr(_) => parse_quote! { #prefix::ops::NdBitOr },
            OpsBinaryExt::BitAnd(_) => parse_quote! { #prefix::ops::NdBitAnd },
            OpsBinaryExt::BitXor(_) => parse_quote! { #prefix::ops::NdBitXor },
            OpsBinaryExt::Shl(_) => parse_quote! { #prefix::ops::NdShl },
            OpsBinaryExt::Shr(_) => parse_quote! { #prefix::ops::NdShr },
            OpsBinaryExt::AddChecked(_, _, _) => parse_quote! { #prefix::ops::NdAddChecked },
            OpsBinaryExt::SubChecked(_, _, _) => parse_quote! { #prefix::ops::NdSubChecked },
            OpsBinaryExt::MulChecked(_, _, _) => parse_quote! { #prefix::ops::NdMulChecked },
            OpsBinaryExt::DivChecked(_, _, _) => parse_quote! { #prefix::ops::NdDivChecked },
            OpsBinaryExt::RemChecked(_, _, _) => parse_quote! { #prefix::ops::NdRemChecked },
            OpsBinaryExt::ShlChecked(_, _, _) => parse_quote! { #prefix::ops::NdShlChecked },
            OpsBinaryExt::ShrChecked(_, _, _) => parse_quote! { #prefix::ops::NdShrChecked },
            OpsBinaryExt::AddStrict(_, _, _) => parse_quote! { #prefix::ops::NdAddStrict },
            OpsBinaryExt::SubStrict(_, _, _) => parse_quote! { #prefix::ops::NdSubStrict },
            OpsBinaryExt::MulStrict(_, _, _) => parse_quote! { #prefix::ops::NdMulStrict },
            OpsBinaryExt::DivStrict(_, _, _) => parse_quote! { #prefix::ops::NdDivStrict },
            OpsBinaryExt::RemStrict(_, _, _) => parse_quote! { #prefix::ops::NdRemStrict },
            OpsBinaryExt::ShlStrict(_, _, _) => parse_quote! { #prefix::ops::NdShlStrict },
            OpsBinaryExt::ShrStrict(_, _, _) => parse_quote! { #prefix::ops::NdShrStrict },
            OpsBinaryExt::AddWrapping(_, _, _) => parse_quote! { #prefix::ops::NdAddWrapping },
            OpsBinaryExt::SubWrapping(_, _, _) => parse_quote! { #prefix::ops::NdSubWrapping },
            OpsBinaryExt::MulWrapping(_, _, _) => parse_quote! { #prefix::ops::NdMulWrapping },
            OpsBinaryExt::DivWrapping(_, _, _) => parse_quote! { #prefix::ops::NdDivWrapping },
            OpsBinaryExt::RemWrapping(_, _, _) => parse_quote! { #prefix::ops::NdRemWrapping },
            OpsBinaryExt::AddSaturating(_, _, _) => parse_quote! { #prefix::ops::NdAddSaturating },
            OpsBinaryExt::SubSaturating(_, _, _) => parse_quote! { #prefix::ops::NdSubSaturating },
            OpsBinaryExt::MulSaturating(_, _, _) => parse_quote! { #prefix::ops::NdMulSaturating },
            OpsBinaryExt::DivSaturating(_, _, _) => parse_quote! { #prefix::ops::NdDivSaturating },
            OpsBinaryExt::RemSaturating(_, _, _) => parse_quote! { #prefix::ops::NdRemSaturating },
            OpsBinaryExt::AddOverflowing(_, _, _) => parse_quote! { #prefix::ops::NdAddOverflowing },
            OpsBinaryExt::SubOverflowing(_, _, _) => parse_quote! { #prefix::ops::NdSubOverflowing },
            OpsBinaryExt::MulOverflowing(_, _, _) => parse_quote! { #prefix::ops::NdMulOverflowing },
            OpsBinaryExt::DivOverflowing(_, _, _) => parse_quote! { #prefix::ops::NdDivOverflowing },
            OpsBinaryExt::RemOverflowing(_, _, _) => parse_quote! { #prefix::ops::NdRemOverflowing },
            OpsBinaryExt::ShlOverflowing(_, _, _) => parse_quote! { #prefix::ops::NdShlOverflowing },
            OpsBinaryExt::ShrOverflowing(_, _, _) => parse_quote! { #prefix::ops::NdShrOverflowing },
            OpsBinaryExt::ShlUnbounded(_, _, _) => parse_quote! { #prefix::ops::NdShlUnbounded },
            OpsBinaryExt::ShrUnbounded(_, _, _) => parse_quote! { #prefix::ops::NdShrUnbounded },
        }
    }

    fn get_type(&self, ty: &Type) -> Type {
        match self {
            OpsBinaryExt::AddChecked(_, _, _)
            | OpsBinaryExt::SubChecked(_, _, _)
            | OpsBinaryExt::MulChecked(_, _, _)
            | OpsBinaryExt::DivChecked(_, _, _)
            | OpsBinaryExt::RemChecked(_, _, _)
            | OpsBinaryExt::ShlChecked(_, _, _)
            | OpsBinaryExt::ShrChecked(_, _, _) => parse_quote! { Option<#ty> },
            OpsBinaryExt::AddOverflowing(_, _, _)
            | OpsBinaryExt::SubOverflowing(_, _, _)
            | OpsBinaryExt::MulOverflowing(_, _, _)
            | OpsBinaryExt::DivOverflowing(_, _, _)
            | OpsBinaryExt::RemOverflowing(_, _, _)
            | OpsBinaryExt::ShlOverflowing(_, _, _)
            | OpsBinaryExt::ShrOverflowing(_, _, _) => parse_quote! { (#ty, bool) },
            _ => ty.clone(),
        }
    }
}

impl OpsUnaryExt {
    fn get_ident(&self) -> Ident {
        match self {
            OpsUnaryExt::Not(_) => parse_quote! { nd_not },
            OpsUnaryExt::Neg(_) => parse_quote! { nd_neg },
            OpsUnaryExt::NegChecked(_, _, _) => parse_quote! { nd_neg_checked },
            OpsUnaryExt::NegStrict(_, _, _) => parse_quote! { nd_neg_strict },
            OpsUnaryExt::NegWrapping(_, _, _) => parse_quote! { nd_neg_wrapping },
            OpsUnaryExt::NegSaturating(_, _, _) => parse_quote! { nd_neg_saturating },
            OpsUnaryExt::NegOverflowing(_, _, _) => parse_quote! { nd_neg_overflowing },
        }
    }

    fn get_path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndcore });

        match self {
            OpsUnaryExt::Not(_) => parse_quote! { #prefix::ops::NdNot },
            OpsUnaryExt::Neg(_) => parse_quote! { #prefix::ops::NdNeg },
            OpsUnaryExt::NegChecked(_, _, _) => parse_quote! { #prefix::ops::NdNegChecked },
            OpsUnaryExt::NegStrict(_, _, _) => parse_quote! { #prefix::ops::NdNegStrict },
            OpsUnaryExt::NegWrapping(_, _, _) => parse_quote! { #prefix::ops::NdNegWrapping },
            OpsUnaryExt::NegSaturating(_, _, _) => parse_quote! { #prefix::ops::NdNegSaturating },
            OpsUnaryExt::NegOverflowing(_, _, _) => parse_quote! { #prefix::ops::NdNegOverflowing },
        }
    }

    fn get_type(&self, ty: &Type) -> Type {
        match self {
            OpsUnaryExt::NegChecked(_, _, _) => parse_quote! { Option<#ty> },
            OpsUnaryExt::NegOverflowing(_, _, _) => parse_quote! { (#ty, bool) },
            _ => ty.clone(),
        }
    }
}
