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
    syn::custom_keyword!(with);

    syn::custom_keyword!(stdmut);
    syn::custom_keyword!(stdbin);
    syn::custom_keyword!(stdun);

    syn::custom_keyword!(ndmut);
    syn::custom_keyword!(ndbin);
    syn::custom_keyword!(ndun);

    syn::custom_keyword!(checked);
    syn::custom_keyword!(strict);
    syn::custom_keyword!(wrapping);
    syn::custom_keyword!(saturating);
    syn::custom_keyword!(overflowing);
    syn::custom_keyword!(unbounded);
}

/// Zero-boilerplate operations defintion.
///
/// The macro defines operation implementation with provided expressions.
///
/// - For `Std-kind` operations definition it supports asterisk notation.
/// - For `Nd-kind` operations definition it supports seven modes.
///
/// # Syntax
///
/// ```text
/// ndops::def! { <kind> <generics> <signature>, [
///     (<operation> <expr> <conditions>?),*
/// ] }
///
/// <kind> := @stdmut | @stdbin | @stdun | @ndmut | @ndbin | @ndun
/// <mode> := "" | @checked | @strict | @wrapping | @saturating | @overflowing | @unbounded
///
/// <operation> := <op> <mode>?
///
/// <generics> := <<param>,*> <conditions>?
/// <conditions> := where [<predicate>,*]
///
/// <signature> :=
///     (<pat>: &mut <type>, (*)? <pat>: <type>)                    | // @stdmut
///     ((*)? <pat>: <type>, (*)? <pat>: <type>) -> <type>          | // @stdbin
///     ((*)? <pat>: <type>)                     -> <type>          | // @stdun
///     (<pat>: &mut <type>, <pat>: &<type>)           <impl_type>? | // @ndmut
///     (<pat>: &<type>,     <pat>: &<type>) -> <type> <impl_type>? | // @ndbin
///     (<pat>: &<type>)                     -> <type> <impl_type>? | // @ndun
///
/// <impl_type> := for <type> | for [<type>,*]
/// ```
///
/// # Examples
///
/// ```rust
/// struct Num(i64);
///
/// // Required (optionally) to construct operation result
/// impl From<i64> for Num {
///     fn from(value: i64) -> Self {
///         Num(value)
///     }
/// }
///
/// // Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
/// ndops::def! { @stdmut (lhs: &mut Num, *rhs: &Num), [
///     += lhs.0 += rhs.0,
///     -= lhs.0 -= rhs.0,
///     *= lhs.0 *= rhs.0,
///     /= lhs.0 /= rhs.0,
///     %= lhs.0 %= rhs.0,
///     |= lhs.0 |= rhs.0,
///     &= lhs.0 &= rhs.0,
///     ^= lhs.0 ^= rhs.0,
/// ] }
///
/// // Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
/// ndops::def! { @stdmut (lhs: &mut Num, *rhs: &Num), [
///     <<= lhs.0 <<= rhs.0,
///     >>= lhs.0 >>= rhs.0,
/// ] }
///
/// // Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
/// ndops::def! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num, [
///     + lhs.0 + rhs.0,
///     - lhs.0 - rhs.0,
///     * lhs.0 * rhs.0,
///     / lhs.0 / rhs.0,
///     % lhs.0 % rhs.0,
///     | lhs.0 | rhs.0,
///     & lhs.0 & rhs.0,
///     ^ lhs.0 ^ rhs.0,
/// ] }
///
/// // Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
/// ndops::def! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num, [
///     << lhs.0 << rhs.0,
///     >> lhs.0 >> rhs.0,
/// ] }
///
/// // Implements corresponding std::ops::* for &Num, Num
/// ndops::def! { @stdun (*value: &Num) -> Num, [
///     ! !value.0,
///     - -value.0,
/// ] }
/// ```
///
/// For more examples, see `ndlibr/proc/ops/examples`.
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro]
pub fn def(stream: TokenStreamStd) -> TokenStreamStd {
    match parse_macro_input!(stream as Ops) {
        Ops::StdAssign(ops) => quote! { #ops }.into(),
        Ops::StdBinary(ops) => quote! { #ops }.into(),
        Ops::StdUnary(ops) => quote! { #ops }.into(),
        Ops::NdAssign(ops) => quote! { #ops }.into(),
        Ops::NdBinary(ops) => quote! { #ops }.into(),
        Ops::NdUnary(ops) => quote! { #ops }.into(),
    }
}

/// Zero-boilerplate operations forwarding.
///
/// The macro forwards operation implementation to corresponding `Nd-kind`
/// operation of type specified in `<impl>`.
///
/// - For `Std-kind` operations forwarding it supports asterisk notation.
/// - For `Nd-kind` operations forwarding it supports seven modes.
///
/// # Syntax
///
/// ```text
/// ndops::fwd! { <kind> <generics> <signature>, <impl> [
///     (<operation> <conditions>?),*
/// ] }
///
/// <kind> := @stdmut | @stdbin | @stdun | @ndmut | @ndbin | @ndun
/// <mode> := "" | @checked | @strict | @wrapping | @saturating | @overflowing | @unbounded
///
/// <operation> := <op> <mode>?
///
/// <generics> := <<param>,*> <conditions>?
/// <conditions> := where [<predicate>,*]
///
/// <signature> :=
///     (<pat>: &mut <type>, (*)? <pat>: <type>)                    | // @stdmut
///     ((*)? <pat>: <type>, (*)? <pat>: <type>) -> <type>          | // @stdbin
///     ((*)? <pat>: <type>)                     -> <type>          | // @stdun
///     (<pat>: &mut <type>, <pat>: &<type>)           <impl_type>? | // @ndmut
///     (<pat>: &<type>,     <pat>: &<type>) -> <type> <impl_type>? | // @ndbin
///     (<pat>: &<type>)                     -> <type> <impl_type>? | // @ndun
///
/// <impl_type> := for <type> | for [<type>,*]
/// <impl> :=
///     (<type>) (<lhs_expr>) (<rhs_expr>) | // @stdmut, @stdbin, @ndmut, @ndbin
///     (<type>) (<value_expr>)            | // @stdun, @ndun
/// ```
///
/// # Examples
///
/// ```rust
/// struct Num(i64);
///
/// // Required to construct operation result
/// impl From<i64> for Num {
///     fn from(value: i64) -> Self {
///         Num(value)
///     }
/// }
///
/// // Implements corresponding std::ops::* for (Num, &Num), (Num, Num)
/// ndops::fwd! { @stdmut (lhs: &mut Num, *rhs: &Num), (i64) (&mut lhs.0) (&rhs.0) [+=, -=, *=, /=, %=, |=, &=, ^=] }
///
/// // Implements corresponding std::ops::* for Num
/// ndops::fwd! { @stdmut (lhs: &mut Num, rhs: usize), (i64) (&mut lhs.0) (rhs) [<<=, >>=] }
///
/// // Implements corresponding std::ops::* for (&Num, &Num), (&Num, Num), (Num, &Num), (Num, Num)
/// ndops::fwd! { @stdbin (*lhs: &Num, *rhs: &Num) -> Num, (i64) (&lhs.0) (&rhs.0) [+, -, *, /, %, |, &, ^] }
///
/// // Implements corresponding std::ops::* for &Num, Num
/// ndops::fwd! { @stdbin (*lhs: &Num, rhs: usize) -> Num, (i64) (&lhs.0) (rhs) [<<, >>] }
///
/// // Implements corresponding std::ops::* for &Num, Num
/// ndops::fwd! { @stdun (*value: &Num) -> Num, (i64) (&value.0) [!, -] }
/// ```
///
/// For more examples, see `ndlibr/proc/ops/examples`.
///
/// For more info, see [crate-level](crate) documentation.
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

#[allow(unused)]
struct OpsNoop;
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
    impl_ty: OpsImplType,
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
    impl_ty: OpsImplType,
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
    impl_ty: OpsImplType,
}

enum OpsImplType {
    Empty,
    Single(OpsImplTypeSingle),
    Multiple(OpsImplTypeMultiple),
}

#[allow(unused)]
struct OpsImplTypeSingle {
    token: Token![for],
    impl_ty: Type,
}

#[allow(unused)]
struct OpsImplTypeMultiple {
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

enum OpsAssign<Ext: Parse, ShiftExt: Parse> {
    Add(Token![+=], Ext),
    Sub(Token![-=], Ext),
    Mul(Token![*=], Ext),
    Div(Token![/=], Ext),
    Rem(Token![%=], Ext),
    BitOr(Token![|=]),
    BitAnd(Token![&=]),
    BitXor(Token![^=]),
    Shl(Token![<<=], ShiftExt),
    Shr(Token![>>=], ShiftExt),
}

enum OpsAssignMode<Ext: Parse> {
    Default(Ext),
    Strict(Token![@], kw::strict),
    Wrapping(Token![@], kw::wrapping),
    Saturating(Token![@], kw::saturating),
}

#[derive(Clone, Copy)]
enum OpsAssignModeWith {
    Default,
    Strict(Token![@], kw::strict),
    Wrapping(Token![@], kw::wrapping),
    Saturating(Token![@], kw::saturating),
}

enum OpsAssignShiftMode<Ext: Parse> {
    Default(Ext),
    Strict(Token![@], kw::strict),
    Unbounded(Token![@], kw::unbounded),
}

#[derive(Clone, Copy)]
enum OpsAssignShiftModeWith {
    Default,
    Strict(Token![@], kw::strict),
    Unbounded(Token![@], kw::unbounded),
}

enum OpsBinary<Ext: Parse, ShiftExt: Parse> {
    Add(Token![+], Ext),
    Sub(Token![-], Ext),
    Mul(Token![*], Ext),
    Div(Token![/], Ext),
    Rem(Token![%], Ext),
    BitOr(Token![|]),
    BitAnd(Token![&]),
    BitXor(Token![^]),
    Shl(Token![<<], ShiftExt),
    Shr(Token![>>], ShiftExt),
}

enum OpsBinaryMode<Ext: Parse> {
    Default(Ext),
    Checked(Token![@], kw::checked),
    Strict(Token![@], kw::strict),
    Wrapping(Token![@], kw::wrapping),
    Saturating(Token![@], kw::saturating),
    Overflowing(Token![@], kw::overflowing),
}

#[derive(Clone, Copy)]
enum OpsBinaryModeWith {
    Default,
    Strict(Token![@], kw::strict),
    Wrapping(Token![@], kw::wrapping),
    Saturating(Token![@], kw::saturating),
}

enum OpsBinaryShiftMode<Ext: Parse> {
    Default(Ext),
    Checked(Token![@], kw::checked),
    Strict(Token![@], kw::strict),
    Unbounded(Token![@], kw::unbounded),
    Overflowing(Token![@], kw::overflowing),
}

#[derive(Clone, Copy)]
enum OpsBinaryShiftModeWith {
    Default,
    Strict(Token![@], kw::strict),
    Unbounded(Token![@], kw::unbounded),
}

enum OpsUnary<Ext: Parse> {
    Not(Token![!]),
    Neg(Token![-], Ext),
}

enum OpsUnaryMode<Ext: Parse> {
    Default(Ext),
    Checked(Token![@], kw::checked),
    Strict(Token![@], kw::strict),
    Wrapping(Token![@], kw::wrapping),
    Saturating(Token![@], kw::saturating),
    Overflowing(Token![@], kw::overflowing),
}

#[derive(Clone, Copy)]
enum OpsUnaryModeWith {
    Default,
    Strict(Token![@], kw::strict),
    Wrapping(Token![@], kw::wrapping),
    Saturating(Token![@], kw::saturating),
}

type OpsStdAssign = OpsAssign<OpsNoop, OpsNoop>;
type OpsStdBinary = OpsBinary<OpsNoop, OpsNoop>;
type OpsStdUnary = OpsUnary<OpsNoop>;

type OpsNdAssign = OpsAssign<OpsAssignMode<OpsNoop>, OpsAssignShiftMode<OpsNoop>>;
type OpsNdBinary = OpsBinary<OpsBinaryMode<OpsNoop>, OpsBinaryShiftMode<OpsNoop>>;
type OpsNdUnary = OpsUnary<OpsUnaryMode<OpsNoop>>;

type OpsStdAssignFwd = OpsAssign<OpsAssignModeWith, OpsAssignShiftModeWith>;
type OpsStdBinaryFwd = OpsBinary<OpsBinaryModeWith, OpsBinaryShiftModeWith>;
type OpsStdUnaryFwd = OpsUnary<OpsUnaryModeWith>;

type OpsNdAssignFwd = OpsAssign<OpsAssignMode<OpsAssignModeWith>, OpsAssignShiftMode<OpsAssignShiftModeWith>>;
type OpsNdBinaryFwd = OpsBinary<OpsBinaryMode<OpsBinaryModeWith>, OpsBinaryShiftMode<OpsBinaryShiftModeWith>>;
type OpsNdUnaryFwd = OpsUnary<OpsUnaryMode<OpsUnaryModeWith>>;

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
    type Definition = OpsDefinition<OpsStdAssign>;
    type Signature = OpsStdSignatureAssign;
}

impl OpsKind for OpsStdKindBinary {
    type Definition = OpsDefinition<OpsStdBinary>;
    type Signature = OpsStdSignatureBinary;
}

impl OpsKind for OpsStdKindUnary {
    type Definition = OpsDefinition<OpsStdUnary>;
    type Signature = OpsStdSignatureUnary;
}

impl OpsKind for OpsNdKindAssign {
    type Definition = OpsDefinition<OpsNdAssign>;
    type Signature = OpsNdSignatureAssign;
}

impl OpsKind for OpsNdKindBinary {
    type Definition = OpsDefinition<OpsNdBinary>;
    type Signature = OpsNdSignatureBinary;
}

impl OpsKind for OpsNdKindUnary {
    type Definition = OpsDefinition<OpsNdUnary>;
    type Signature = OpsNdSignatureUnary;
}

impl OpsKindFwd for OpsStdKindAssign {
    type Definition = OpsDefinitionFwd<OpsStdAssignFwd>;
    type Expression = OpsExpressionAssign;
    type Signature = OpsStdSignatureAssign;
}

impl OpsKindFwd for OpsStdKindBinary {
    type Definition = OpsDefinitionFwd<OpsStdBinaryFwd>;
    type Expression = OpsExpressionBinary;
    type Signature = OpsStdSignatureBinary;
}

impl OpsKindFwd for OpsStdKindUnary {
    type Definition = OpsDefinitionFwd<OpsStdUnaryFwd>;
    type Expression = OpsExpressionUnary;
    type Signature = OpsStdSignatureUnary;
}

impl OpsKindFwd for OpsNdKindAssign {
    type Definition = OpsDefinitionFwd<OpsNdAssignFwd>;
    type Expression = OpsExpressionAssign;
    type Signature = OpsNdSignatureAssign;
}

impl OpsKindFwd for OpsNdKindBinary {
    type Definition = OpsDefinitionFwd<OpsNdBinaryFwd>;
    type Expression = OpsExpressionBinary;
    type Signature = OpsNdSignatureBinary;
}

impl OpsKindFwd for OpsNdKindUnary {
    type Definition = OpsDefinitionFwd<OpsNdUnaryFwd>;
    type Expression = OpsExpressionUnary;
    type Signature = OpsNdSignatureUnary;
}

impl Parse for OpsNoop {
    fn parse(_: ParseStream) -> Result<Self> {
        Ok(Self)
    }
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

impl Parse for OpsImplType {
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

impl Parse for OpsImplTypeSingle {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            token: input.parse()?,
            impl_ty: input.parse()?,
        })
    }
}

impl Parse for OpsImplTypeMultiple {
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

impl<Ext: Parse, ShiftExt: Parse> Parse for OpsAssign<Ext, ShiftExt> {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(Token![+=]) {
            Ok(Self::Add(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![-=]) {
            Ok(Self::Sub(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![*=]) {
            Ok(Self::Mul(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![/=]) {
            Ok(Self::Div(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![%=]) {
            Ok(Self::Rem(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![|=]) {
            Ok(Self::BitOr(input.parse()?))
        } else if lookahead.peek(Token![&=]) {
            Ok(Self::BitAnd(input.parse()?))
        } else if lookahead.peek(Token![^=]) {
            Ok(Self::BitXor(input.parse()?))
        } else if lookahead.peek(Token![<<=]) {
            Ok(Self::Shl(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![>>=]) {
            Ok(Self::Shr(input.parse()?, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl<Ext: Parse> Parse for OpsAssignMode<Ext> {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(Token![@]) {
            return Ok(Self::Default(input.parse()?));
        }

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::wrapping) {
            Ok(Self::Wrapping(token, input.parse()?))
        } else if lookahead.peek(kw::saturating) {
            Ok(Self::Saturating(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsAssignModeWith {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(kw::with) {
            return Ok(Self::Default);
        }

        input.parse::<kw::with>()?;

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::wrapping) {
            Ok(Self::Wrapping(token, input.parse()?))
        } else if lookahead.peek(kw::saturating) {
            Ok(Self::Saturating(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl<Ext: Parse> Parse for OpsAssignShiftMode<Ext> {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(Token![@]) {
            return Ok(Self::Default(input.parse()?));
        }

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::unbounded) {
            Ok(Self::Unbounded(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsAssignShiftModeWith {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(kw::with) {
            return Ok(Self::Default);
        }

        input.parse::<kw::with>()?;

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::wrapping) {
            Ok(Self::Unbounded(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl<Ext: Parse, ShiftExt: Parse> Parse for OpsBinary<Ext, ShiftExt> {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(Token![+]) {
            Ok(Self::Add(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![-]) {
            Ok(Self::Sub(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![*]) {
            Ok(Self::Mul(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![/]) {
            Ok(Self::Div(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![%]) {
            Ok(Self::Rem(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![|]) {
            Ok(Self::BitOr(input.parse()?))
        } else if lookahead.peek(Token![&]) {
            Ok(Self::BitAnd(input.parse()?))
        } else if lookahead.peek(Token![^]) {
            Ok(Self::BitXor(input.parse()?))
        } else if lookahead.peek(Token![<<]) {
            Ok(Self::Shl(input.parse()?, input.parse()?))
        } else if lookahead.peek(Token![>>]) {
            Ok(Self::Shr(input.parse()?, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl<Ext: Parse> Parse for OpsBinaryMode<Ext> {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(Token![@]) {
            return Ok(Self::Default(input.parse()?));
        }

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::checked) {
            Ok(Self::Checked(token, input.parse()?))
        } else if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::wrapping) {
            Ok(Self::Wrapping(token, input.parse()?))
        } else if lookahead.peek(kw::saturating) {
            Ok(Self::Saturating(token, input.parse()?))
        } else if lookahead.peek(kw::overflowing) {
            Ok(Self::Overflowing(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsBinaryModeWith {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(kw::with) {
            return Ok(Self::Default);
        }

        input.parse::<kw::with>()?;

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::wrapping) {
            Ok(Self::Wrapping(token, input.parse()?))
        } else if lookahead.peek(kw::saturating) {
            Ok(Self::Saturating(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl<Ext: Parse> Parse for OpsBinaryShiftMode<Ext> {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(Token![@]) {
            return Ok(Self::Default(input.parse()?));
        }

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::checked) {
            Ok(Self::Checked(token, input.parse()?))
        } else if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::unbounded) {
            Ok(Self::Unbounded(token, input.parse()?))
        } else if lookahead.peek(kw::overflowing) {
            Ok(Self::Overflowing(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsBinaryShiftModeWith {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(kw::with) {
            return Ok(Self::Default);
        }

        input.parse::<kw::with>()?;

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::wrapping) {
            Ok(Self::Unbounded(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl<Ext: Parse> Parse for OpsUnary<Ext> {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(Token![!]) {
            Ok(Self::Not(input.parse()?))
        } else if lookahead.peek(Token![-]) {
            Ok(Self::Neg(input.parse()?, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl<Ext: Parse> Parse for OpsUnaryMode<Ext> {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(Token![@]) {
            return Ok(Self::Default(input.parse()?));
        }

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::checked) {
            Ok(Self::Checked(token, input.parse()?))
        } else if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::wrapping) {
            Ok(Self::Wrapping(token, input.parse()?))
        } else if lookahead.peek(kw::saturating) {
            Ok(Self::Saturating(token, input.parse()?))
        } else if lookahead.peek(kw::overflowing) {
            Ok(Self::Overflowing(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsUnaryModeWith {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(kw::with) {
            return Ok(Self::Default);
        }

        input.parse::<kw::with>()?;

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::wrapping) {
            Ok(Self::Wrapping(token, input.parse()?))
        } else if lookahead.peek(kw::saturating) {
            Ok(Self::Saturating(token, input.parse()?))
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
            op: &'ops OpsAssign<OpsNoop, OpsNoop>,
            expr: &'ops Expr,
            conditions: Option<&'ops OpsConditions>,
        }

        fn get_impl(spec: OpsSpec, rhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.ident();
            let path = spec.op.path();

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
            op: &'ops OpsBinary<OpsNoop, OpsNoop>,
            expr: &'ops Expr,
            conditions: Option<&'ops OpsConditions>,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>, rhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.ident();
            let path = spec.op.path();

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
            op: &'ops OpsUnary<OpsNoop>,
            expr: &'ops Expr,
            conditions: Option<&'ops OpsConditions>,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.ident();
            let path = spec.op.path();

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
            let ident = definition.op.ident();
            let path = definition.op.path(self.token);

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
                OpsImplType::Empty => tokens.extend(quote(lhs_ty)),
                OpsImplType::Single(val) => tokens.extend(quote(&val.impl_ty)),
                OpsImplType::Multiple(val) => val.impl_ty.iter().for_each(|ty| tokens.extend(quote(ty))),
            }
        }
    }
}

impl ToTokens for OpsImpl<OpsNdKindBinary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for definition in &self.definitions {
            let ident = definition.op.ident();
            let path = definition.op.path(self.token);

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
            let ty = definition.op.ty(res_ty);

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
                OpsImplType::Empty => tokens.extend(quote(res_ty)),
                OpsImplType::Single(val) => tokens.extend(quote(&val.impl_ty)),
                OpsImplType::Multiple(val) => val.impl_ty.iter().for_each(|ty| tokens.extend(quote(ty))),
            }
        }
    }
}

impl ToTokens for OpsImpl<OpsNdKindUnary> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for definition in &self.definitions {
            let ident = definition.op.ident();
            let path = definition.op.path(self.token);

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
            let ty = definition.op.ty(res_ty);

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
                OpsImplType::Empty => tokens.extend(quote(res_ty)),
                OpsImplType::Single(val) => tokens.extend(quote(&val.impl_ty)),
                OpsImplType::Multiple(val) => val.impl_ty.iter().for_each(|ty| tokens.extend(quote(ty))),
            }
        }
    }
}

impl From<OpsImplFwd<OpsStdKindAssign>> for OpsImpl<OpsStdKindAssign> {
    fn from(value: OpsImplFwd<OpsStdKindAssign>) -> Self {
        OpsImpl {
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

                    let op_impl = op.to_impl();
                    let ident = op_impl.ident();
                    let path = op_impl.path(value.token);

                    OpsDefinition {
                        op: op.into(),
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
        OpsImpl {
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

                    let op_impl = op.to_impl();
                    let ident = op_impl.ident();
                    let path = op_impl.path(value.token);

                    OpsDefinition {
                        op: op.into(),
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
        OpsImpl {
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

                    let op_impl = op.to_impl();
                    let ident = op_impl.ident();
                    let path = op_impl.path(value.token);

                    OpsDefinition {
                        op: op.into(),
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
        OpsImpl {
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

                    let op_impl = op.to_impl();
                    let ident = op_impl.ident();
                    let path = op_impl.path(value.token);
                    let expr = parse_quote! {{ use #path; #ty::#ident(#lhs, #rhs); }};

                    OpsDefinition {
                        op: op.into(),
                        expr,
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplFwd<OpsNdKindBinary>> for OpsImpl<OpsNdKindBinary> {
    fn from(value: OpsImplFwd<OpsNdKindBinary>) -> Self {
        OpsImpl {
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

                    let op_impl = op.to_impl();
                    let ident = op_impl.ident();
                    let path = op_impl.path(value.token);
                    let expr = op_impl.expr(parse_quote! {{ use #path; #ty::#ident(#lhs, #rhs) }});

                    OpsDefinition {
                        op: op.into(),
                        expr,
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplFwd<OpsNdKindUnary>> for OpsImpl<OpsNdKindUnary> {
    fn from(value: OpsImplFwd<OpsNdKindUnary>) -> Self {
        OpsImpl {
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

                    let op_impl = op.to_impl();
                    let ident = op_impl.ident();
                    let path = op_impl.path(value.token);
                    let expr = op_impl.expr(parse_quote! {{ use #path; #ty::#ident(#expr) }});

                    OpsDefinition {
                        op: op.into(),
                        expr,
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsStdAssignFwd> for OpsStdAssign {
    fn from(value: OpsStdAssignFwd) -> Self {
        match value {
            OpsAssign::Add(token, _) => Self::Add(token, OpsNoop),
            OpsAssign::Sub(token, _) => Self::Sub(token, OpsNoop),
            OpsAssign::Mul(token, _) => Self::Mul(token, OpsNoop),
            OpsAssign::Div(token, _) => Self::Div(token, OpsNoop),
            OpsAssign::Rem(token, _) => Self::Rem(token, OpsNoop),
            OpsAssign::BitOr(token) => Self::BitOr(token),
            OpsAssign::BitAnd(token) => Self::BitAnd(token),
            OpsAssign::BitXor(token) => Self::BitXor(token),
            OpsAssign::Shl(token, _) => Self::Shl(token, OpsNoop),
            OpsAssign::Shr(token, _) => Self::Shr(token, OpsNoop),
        }
    }
}

impl From<OpsStdBinaryFwd> for OpsStdBinary {
    fn from(value: OpsStdBinaryFwd) -> Self {
        match value {
            OpsBinary::Add(token, _) => Self::Add(token, OpsNoop),
            OpsBinary::Sub(token, _) => Self::Sub(token, OpsNoop),
            OpsBinary::Mul(token, _) => Self::Mul(token, OpsNoop),
            OpsBinary::Div(token, _) => Self::Div(token, OpsNoop),
            OpsBinary::Rem(token, _) => Self::Rem(token, OpsNoop),
            OpsBinary::BitOr(token) => Self::BitOr(token),
            OpsBinary::BitAnd(token) => Self::BitAnd(token),
            OpsBinary::BitXor(token) => Self::BitXor(token),
            OpsBinary::Shl(token, _) => Self::Shl(token, OpsNoop),
            OpsBinary::Shr(token, _) => Self::Shr(token, OpsNoop),
        }
    }
}

impl From<OpsStdUnaryFwd> for OpsStdUnary {
    fn from(value: OpsStdUnaryFwd) -> Self {
        match value {
            OpsUnary::Not(token) => Self::Not(token),
            OpsUnary::Neg(token, _) => Self::Neg(token, OpsNoop),
        }
    }
}

impl From<OpsNdAssignFwd> for OpsNdAssign {
    fn from(value: OpsNdAssignFwd) -> Self {
        match value {
            OpsAssign::Add(token, mode) => Self::Add(token, mode.into()),
            OpsAssign::Sub(token, mode) => Self::Sub(token, mode.into()),
            OpsAssign::Mul(token, mode) => Self::Mul(token, mode.into()),
            OpsAssign::Div(token, mode) => Self::Div(token, mode.into()),
            OpsAssign::Rem(token, mode) => Self::Rem(token, mode.into()),
            OpsAssign::BitOr(token) => Self::BitOr(token),
            OpsAssign::BitAnd(token) => Self::BitAnd(token),
            OpsAssign::BitXor(token) => Self::BitXor(token),
            OpsAssign::Shl(token, mode) => Self::Shl(token, mode.into()),
            OpsAssign::Shr(token, mode) => Self::Shr(token, mode.into()),
        }
    }
}

impl From<OpsNdBinaryFwd> for OpsNdBinary {
    fn from(value: OpsNdBinaryFwd) -> Self {
        match value {
            OpsBinary::Add(token, mode) => Self::Add(token, mode.into()),
            OpsBinary::Sub(token, mode) => Self::Sub(token, mode.into()),
            OpsBinary::Mul(token, mode) => Self::Mul(token, mode.into()),
            OpsBinary::Div(token, mode) => Self::Div(token, mode.into()),
            OpsBinary::Rem(token, mode) => Self::Rem(token, mode.into()),
            OpsBinary::BitOr(token) => Self::BitOr(token),
            OpsBinary::BitAnd(token) => Self::BitAnd(token),
            OpsBinary::BitXor(token) => Self::BitXor(token),
            OpsBinary::Shl(token, mode) => Self::Shl(token, mode.into()),
            OpsBinary::Shr(token, mode) => Self::Shr(token, mode.into()),
        }
    }
}

impl From<OpsNdUnaryFwd> for OpsNdUnary {
    fn from(value: OpsNdUnaryFwd) -> Self {
        match value {
            OpsUnary::Not(token) => Self::Not(token),
            OpsUnary::Neg(token, mode) => Self::Neg(token, mode.into()),
        }
    }
}

impl From<OpsAssignMode<OpsAssignModeWith>> for OpsAssignMode<OpsNoop> {
    fn from(value: OpsAssignMode<OpsAssignModeWith>) -> Self {
        match value {
            OpsAssignMode::Default(_) => Self::Default(OpsNoop),
            OpsAssignMode::Strict(token, kw) => Self::Strict(token, kw),
            OpsAssignMode::Wrapping(token, kw) => Self::Wrapping(token, kw),
            OpsAssignMode::Saturating(token, kw) => Self::Saturating(token, kw),
        }
    }
}

impl From<OpsAssignShiftMode<OpsAssignShiftModeWith>> for OpsAssignShiftMode<OpsNoop> {
    fn from(value: OpsAssignShiftMode<OpsAssignShiftModeWith>) -> Self {
        match value {
            OpsAssignShiftMode::Default(_) => Self::Default(OpsNoop),
            OpsAssignShiftMode::Strict(token, kw) => Self::Strict(token, kw),
            OpsAssignShiftMode::Unbounded(token, kw) => Self::Unbounded(token, kw),
        }
    }
}

impl From<OpsBinaryMode<OpsBinaryModeWith>> for OpsBinaryMode<OpsNoop> {
    fn from(value: OpsBinaryMode<OpsBinaryModeWith>) -> Self {
        match value {
            OpsBinaryMode::Default(_) => Self::Default(OpsNoop),
            OpsBinaryMode::Checked(token, kw) => Self::Checked(token, kw),
            OpsBinaryMode::Strict(token, kw) => Self::Strict(token, kw),
            OpsBinaryMode::Wrapping(token, kw) => Self::Wrapping(token, kw),
            OpsBinaryMode::Saturating(token, kw) => Self::Saturating(token, kw),
            OpsBinaryMode::Overflowing(token, kw) => Self::Overflowing(token, kw),
        }
    }
}

impl From<OpsBinaryShiftMode<OpsBinaryShiftModeWith>> for OpsBinaryShiftMode<OpsNoop> {
    fn from(value: OpsBinaryShiftMode<OpsBinaryShiftModeWith>) -> Self {
        match value {
            OpsBinaryShiftMode::Default(_) => Self::Default(OpsNoop),
            OpsBinaryShiftMode::Checked(token, kw) => Self::Checked(token, kw),
            OpsBinaryShiftMode::Strict(token, kw) => Self::Strict(token, kw),
            OpsBinaryShiftMode::Unbounded(token, kw) => Self::Unbounded(token, kw),
            OpsBinaryShiftMode::Overflowing(token, kw) => Self::Overflowing(token, kw),
        }
    }
}

impl From<OpsUnaryMode<OpsUnaryModeWith>> for OpsUnaryMode<OpsNoop> {
    fn from(value: OpsUnaryMode<OpsUnaryModeWith>) -> Self {
        match value {
            OpsUnaryMode::Default(_) => Self::Default(OpsNoop),
            OpsUnaryMode::Checked(token, kw) => Self::Checked(token, kw),
            OpsUnaryMode::Strict(token, kw) => Self::Strict(token, kw),
            OpsUnaryMode::Wrapping(token, kw) => Self::Wrapping(token, kw),
            OpsUnaryMode::Saturating(token, kw) => Self::Saturating(token, kw),
            OpsUnaryMode::Overflowing(token, kw) => Self::Overflowing(token, kw),
        }
    }
}

impl From<&OpsAssignModeWith> for OpsAssignMode<OpsNoop> {
    fn from(value: &OpsAssignModeWith) -> Self {
        match value {
            OpsAssignModeWith::Default => Self::Default(OpsNoop),
            OpsAssignModeWith::Strict(token, kw) => Self::Strict(*token, *kw),
            OpsAssignModeWith::Wrapping(token, kw) => Self::Wrapping(*token, *kw),
            OpsAssignModeWith::Saturating(token, kw) => Self::Saturating(*token, *kw),
        }
    }
}

impl From<&OpsAssignShiftModeWith> for OpsAssignShiftMode<OpsNoop> {
    fn from(value: &OpsAssignShiftModeWith) -> Self {
        match value {
            OpsAssignShiftModeWith::Default => Self::Default(OpsNoop),
            OpsAssignShiftModeWith::Strict(token, kw) => Self::Strict(*token, *kw),
            OpsAssignShiftModeWith::Unbounded(token, kw) => Self::Unbounded(*token, *kw),
        }
    }
}

impl From<&OpsBinaryModeWith> for OpsBinaryMode<OpsNoop> {
    fn from(value: &OpsBinaryModeWith) -> Self {
        match value {
            OpsBinaryModeWith::Default => Self::Default(OpsNoop),
            OpsBinaryModeWith::Strict(token, kw) => Self::Strict(*token, *kw),
            OpsBinaryModeWith::Wrapping(token, kw) => Self::Wrapping(*token, *kw),
            OpsBinaryModeWith::Saturating(token, kw) => Self::Saturating(*token, *kw),
        }
    }
}

impl From<&OpsBinaryShiftModeWith> for OpsBinaryShiftMode<OpsNoop> {
    fn from(value: &OpsBinaryShiftModeWith) -> Self {
        match value {
            OpsBinaryShiftModeWith::Default => Self::Default(OpsNoop),
            OpsBinaryShiftModeWith::Strict(token, kw) => Self::Strict(*token, *kw),
            OpsBinaryShiftModeWith::Unbounded(token, kw) => Self::Unbounded(*token, *kw),
        }
    }
}

impl From<&OpsUnaryModeWith> for OpsUnaryMode<OpsNoop> {
    fn from(value: &OpsUnaryModeWith) -> Self {
        match value {
            OpsUnaryModeWith::Default => Self::Default(OpsNoop),
            OpsUnaryModeWith::Strict(token, kw) => Self::Strict(*token, *kw),
            OpsUnaryModeWith::Wrapping(token, kw) => Self::Wrapping(*token, *kw),
            OpsUnaryModeWith::Saturating(token, kw) => Self::Saturating(*token, *kw),
        }
    }
}

impl OpsStdAssign {
    fn ident(&self) -> Ident {
        match self {
            OpsAssign::Add(_, _) => parse_quote! { add_assign },
            OpsAssign::Sub(_, _) => parse_quote! { sub_assign },
            OpsAssign::Mul(_, _) => parse_quote! { mul_assign },
            OpsAssign::Div(_, _) => parse_quote! { div_assign },
            OpsAssign::Rem(_, _) => parse_quote! { rem_assign },
            OpsAssign::BitOr(_) => parse_quote! { bitor_assign },
            OpsAssign::BitAnd(_) => parse_quote! { bitand_assign },
            OpsAssign::BitXor(_) => parse_quote! { bitxor_assign },
            OpsAssign::Shl(_, _) => parse_quote! { shl_assign },
            OpsAssign::Shr(_, _) => parse_quote! { shr_assign },
        }
    }

    fn path(&self) -> Path {
        match self {
            OpsAssign::Add(_, _) => parse_quote! { std::ops::AddAssign },
            OpsAssign::Sub(_, _) => parse_quote! { std::ops::SubAssign },
            OpsAssign::Mul(_, _) => parse_quote! { std::ops::MulAssign },
            OpsAssign::Div(_, _) => parse_quote! { std::ops::DivAssign },
            OpsAssign::Rem(_, _) => parse_quote! { std::ops::RemAssign },
            OpsAssign::BitOr(_) => parse_quote! { std::ops::BitOrAssign },
            OpsAssign::BitAnd(_) => parse_quote! { std::ops::BitAndAssign },
            OpsAssign::BitXor(_) => parse_quote! { std::ops::BitXorAssign },
            OpsAssign::Shl(_, _) => parse_quote! { std::ops::ShlAssign },
            OpsAssign::Shr(_, _) => parse_quote! { std::ops::ShrAssign },
        }
    }
}

impl OpsStdBinary {
    fn ident(&self) -> Ident {
        match self {
            OpsBinary::Add(_, _) => parse_quote! { add },
            OpsBinary::Sub(_, _) => parse_quote! { sub },
            OpsBinary::Mul(_, _) => parse_quote! { mul },
            OpsBinary::Div(_, _) => parse_quote! { div },
            OpsBinary::Rem(_, _) => parse_quote! { rem },
            OpsBinary::BitOr(_) => parse_quote! { bitor },
            OpsBinary::BitAnd(_) => parse_quote! { bitand },
            OpsBinary::BitXor(_) => parse_quote! { bitxor },
            OpsBinary::Shl(_, _) => parse_quote! { shl },
            OpsBinary::Shr(_, _) => parse_quote! { shr },
        }
    }

    fn path(&self) -> Path {
        match self {
            OpsBinary::Add(_, _) => parse_quote! { std::ops::Add },
            OpsBinary::Sub(_, _) => parse_quote! { std::ops::Sub },
            OpsBinary::Mul(_, _) => parse_quote! { std::ops::Mul },
            OpsBinary::Div(_, _) => parse_quote! { std::ops::Div },
            OpsBinary::Rem(_, _) => parse_quote! { std::ops::Rem },
            OpsBinary::BitOr(_) => parse_quote! { std::ops::BitOr },
            OpsBinary::BitAnd(_) => parse_quote! { std::ops::BitAnd },
            OpsBinary::BitXor(_) => parse_quote! { std::ops::BitXor },
            OpsBinary::Shl(_, _) => parse_quote! { std::ops::Shl },
            OpsBinary::Shr(_, _) => parse_quote! { std::ops::Shr },
        }
    }
}

impl OpsStdUnary {
    fn ident(&self) -> Ident {
        match self {
            OpsUnary::Not(_) => parse_quote! { not },
            OpsUnary::Neg(_, _) => parse_quote! { neg },
        }
    }

    fn path(&self) -> Path {
        match self {
            OpsUnary::Not(_) => parse_quote! { std::ops::Not },
            OpsUnary::Neg(_, _) => parse_quote! { std::ops::Neg },
        }
    }
}

impl OpsNdAssign {
    fn ident(&self) -> Ident {
        match self {
            OpsAssign::Add(_, mode) => match mode {
                OpsAssignMode::Default(_) => parse_quote! { nd_add_assign },
                OpsAssignMode::Strict(_, _) => parse_quote! { nd_add_assign_strict },
                OpsAssignMode::Wrapping(_, _) => parse_quote! { nd_add_assign_wrapping },
                OpsAssignMode::Saturating(_, _) => parse_quote! { nd_add_assign_saturating },
            },
            OpsAssign::Sub(_, mode) => match mode {
                OpsAssignMode::Default(_) => parse_quote! { nd_sub_assign },
                OpsAssignMode::Strict(_, _) => parse_quote! { nd_sub_assign_strict },
                OpsAssignMode::Wrapping(_, _) => parse_quote! { nd_sub_assign_wrapping },
                OpsAssignMode::Saturating(_, _) => parse_quote! { nd_sub_assign_saturating },
            },
            OpsAssign::Mul(_, mode) => match mode {
                OpsAssignMode::Default(_) => parse_quote! { nd_mul_assign },
                OpsAssignMode::Strict(_, _) => parse_quote! { nd_mul_assign_strict },
                OpsAssignMode::Wrapping(_, _) => parse_quote! { nd_mul_assign_wrapping },
                OpsAssignMode::Saturating(_, _) => parse_quote! { nd_mul_assign_saturating },
            },
            OpsAssign::Div(_, mode) => match mode {
                OpsAssignMode::Default(_) => parse_quote! { nd_div_assign },
                OpsAssignMode::Strict(_, _) => parse_quote! { nd_div_assign_strict },
                OpsAssignMode::Wrapping(_, _) => parse_quote! { nd_div_assign_wrapping },
                OpsAssignMode::Saturating(_, _) => parse_quote! { nd_div_assign_saturating },
            },
            OpsAssign::Rem(_, mode) => match mode {
                OpsAssignMode::Default(_) => parse_quote! { nd_rem_assign },
                OpsAssignMode::Strict(_, _) => parse_quote! { nd_rem_assign_strict },
                OpsAssignMode::Wrapping(_, _) => parse_quote! { nd_rem_assign_wrapping },
                OpsAssignMode::Saturating(_, _) => parse_quote! { nd_rem_assign_saturating },
            },
            OpsAssign::BitOr(_) => parse_quote! { nd_bitor_assign },
            OpsAssign::BitAnd(_) => parse_quote! { nd_bitand_assign },
            OpsAssign::BitXor(_) => parse_quote! { nd_bitxor_assign },
            OpsAssign::Shl(_, mode) => match mode {
                OpsAssignShiftMode::Default(_) => parse_quote! { nd_shl_assign },
                OpsAssignShiftMode::Strict(_, _) => parse_quote! { nd_shl_assign_strict },
                OpsAssignShiftMode::Unbounded(_, _) => parse_quote! { nd_shl_assign_unbounded },
            },
            OpsAssign::Shr(_, mode) => match mode {
                OpsAssignShiftMode::Default(_) => parse_quote! { nd_shr_assign },
                OpsAssignShiftMode::Strict(_, _) => parse_quote! { nd_shr_assign_strict },
                OpsAssignShiftMode::Unbounded(_, _) => parse_quote! { nd_shr_assign_unbounded },
            },
        }
    }

    fn path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndext });

        match self {
            OpsAssign::Add(_, mode) => match mode {
                OpsAssignMode::Default(_) => parse_quote! { #prefix::ops::NdAddAssign },
                OpsAssignMode::Strict(_, _) => parse_quote! { #prefix::ops::NdAddAssignStrict },
                OpsAssignMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdAddAssignWrapping },
                OpsAssignMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdAddAssignSaturating },
            },
            OpsAssign::Sub(_, mode) => match mode {
                OpsAssignMode::Default(_) => parse_quote! { #prefix::ops::NdSubAssign },
                OpsAssignMode::Strict(_, _) => parse_quote! { #prefix::ops::NdSubAssignStrict },
                OpsAssignMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdSubAssignWrapping },
                OpsAssignMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdSubAssignSaturating },
            },
            OpsAssign::Mul(_, mode) => match mode {
                OpsAssignMode::Default(_) => parse_quote! { #prefix::ops::NdMulAssign },
                OpsAssignMode::Strict(_, _) => parse_quote! { #prefix::ops::NdMulAssignStrict },
                OpsAssignMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdMulAssignWrapping },
                OpsAssignMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdMulAssignSaturating },
            },
            OpsAssign::Div(_, mode) => match mode {
                OpsAssignMode::Default(_) => parse_quote! { #prefix::ops::NdDivAssign },
                OpsAssignMode::Strict(_, _) => parse_quote! { #prefix::ops::NdDivAssignStrict },
                OpsAssignMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdDivAssignWrapping },
                OpsAssignMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdDivAssignSaturating },
            },
            OpsAssign::Rem(_, mode) => match mode {
                OpsAssignMode::Default(_) => parse_quote! { #prefix::ops::NdRemAssign },
                OpsAssignMode::Strict(_, _) => parse_quote! { #prefix::ops::NdRemAssignStrict },
                OpsAssignMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdRemAssignWrapping },
                OpsAssignMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdRemAssignSaturating },
            },
            OpsAssign::BitOr(_) => parse_quote! { #prefix::ops::NdBitOrAssign },
            OpsAssign::BitAnd(_) => parse_quote! { #prefix::ops::NdBitAndAssign },
            OpsAssign::BitXor(_) => parse_quote! { #prefix::ops::NdBitXorAssign },
            OpsAssign::Shl(_, mode) => match mode {
                OpsAssignShiftMode::Default(_) => parse_quote! { #prefix::ops::NdShlAssign },
                OpsAssignShiftMode::Strict(_, _) => parse_quote! { #prefix::ops::NdShlAssignStrict },
                OpsAssignShiftMode::Unbounded(_, _) => parse_quote! { #prefix::ops::NdShlAssignUnbounded },
            },
            OpsAssign::Shr(_, mode) => match mode {
                OpsAssignShiftMode::Default(_) => parse_quote! { #prefix::ops::NdShrAssign },
                OpsAssignShiftMode::Strict(_, _) => parse_quote! { #prefix::ops::NdShrAssignStrict },
                OpsAssignShiftMode::Unbounded(_, _) => parse_quote! { #prefix::ops::NdShrAssignUnbounded },
            },
        }
    }
}

impl OpsNdBinary {
    fn ident(&self) -> Ident {
        match self {
            OpsBinary::Add(_, mode) => match mode {
                OpsBinaryMode::Default(_) => parse_quote! { nd_add },
                OpsBinaryMode::Checked(_, _) => parse_quote! { nd_add_checked },
                OpsBinaryMode::Strict(_, _) => parse_quote! { nd_add_strict },
                OpsBinaryMode::Wrapping(_, _) => parse_quote! { nd_add_wrapping },
                OpsBinaryMode::Saturating(_, _) => parse_quote! { nd_add_saturating },
                OpsBinaryMode::Overflowing(_, _) => parse_quote! { nd_add_overflowing },
            },
            OpsBinary::Sub(_, mode) => match mode {
                OpsBinaryMode::Default(_) => parse_quote! { nd_sub },
                OpsBinaryMode::Checked(_, _) => parse_quote! { nd_sub_checked },
                OpsBinaryMode::Strict(_, _) => parse_quote! { nd_sub_strict },
                OpsBinaryMode::Wrapping(_, _) => parse_quote! { nd_sub_wrapping },
                OpsBinaryMode::Saturating(_, _) => parse_quote! { nd_sub_saturating },
                OpsBinaryMode::Overflowing(_, _) => parse_quote! { nd_sub_overflowing },
            },
            OpsBinary::Mul(_, mode) => match mode {
                OpsBinaryMode::Default(_) => parse_quote! { nd_mul },
                OpsBinaryMode::Checked(_, _) => parse_quote! { nd_mul_checked },
                OpsBinaryMode::Strict(_, _) => parse_quote! { nd_mul_strict },
                OpsBinaryMode::Wrapping(_, _) => parse_quote! { nd_mul_wrapping },
                OpsBinaryMode::Saturating(_, _) => parse_quote! { nd_mul_saturating },
                OpsBinaryMode::Overflowing(_, _) => parse_quote! { nd_mul_overflowing },
            },
            OpsBinary::Div(_, mode) => match mode {
                OpsBinaryMode::Default(_) => parse_quote! { nd_div },
                OpsBinaryMode::Checked(_, _) => parse_quote! { nd_div_checked },
                OpsBinaryMode::Strict(_, _) => parse_quote! { nd_div_strict },
                OpsBinaryMode::Wrapping(_, _) => parse_quote! { nd_div_wrapping },
                OpsBinaryMode::Saturating(_, _) => parse_quote! { nd_div_saturating },
                OpsBinaryMode::Overflowing(_, _) => parse_quote! { nd_div_overflowing },
            },
            OpsBinary::Rem(_, mode) => match mode {
                OpsBinaryMode::Default(_) => parse_quote! { nd_rem },
                OpsBinaryMode::Checked(_, _) => parse_quote! { nd_rem_checked },
                OpsBinaryMode::Strict(_, _) => parse_quote! { nd_rem_strict },
                OpsBinaryMode::Wrapping(_, _) => parse_quote! { nd_rem_wrapping },
                OpsBinaryMode::Saturating(_, _) => parse_quote! { nd_rem_saturating },
                OpsBinaryMode::Overflowing(_, _) => parse_quote! { nd_rem_overflowing },
            },
            OpsBinary::BitOr(_) => parse_quote! { nd_bitor },
            OpsBinary::BitAnd(_) => parse_quote! { nd_bitand },
            OpsBinary::BitXor(_) => parse_quote! { nd_bitxor },
            OpsBinary::Shl(_, mode) => match mode {
                OpsBinaryShiftMode::Default(_) => parse_quote! { nd_shl },
                OpsBinaryShiftMode::Checked(_, _) => parse_quote! { nd_shl_checked },
                OpsBinaryShiftMode::Strict(_, _) => parse_quote! { nd_shl_strict },
                OpsBinaryShiftMode::Unbounded(_, _) => parse_quote! { nd_shl_unbounded },
                OpsBinaryShiftMode::Overflowing(_, _) => parse_quote! { nd_shl_overflowing },
            },
            OpsBinary::Shr(_, mode) => match mode {
                OpsBinaryShiftMode::Default(_) => parse_quote! { nd_shr },
                OpsBinaryShiftMode::Checked(_, _) => parse_quote! { nd_shr_checked },
                OpsBinaryShiftMode::Strict(_, _) => parse_quote! { nd_shr_strict },
                OpsBinaryShiftMode::Unbounded(_, _) => parse_quote! { nd_shr_unbounded },
                OpsBinaryShiftMode::Overflowing(_, _) => parse_quote! { nd_shr_overflowing },
            },
        }
    }

    fn path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndext });

        match self {
            OpsBinary::Add(_, mode) => match mode {
                OpsBinaryMode::Default(_) => parse_quote! { #prefix::ops::NdAdd },
                OpsBinaryMode::Checked(_, _) => parse_quote! { #prefix::ops::NdAddChecked },
                OpsBinaryMode::Strict(_, _) => parse_quote! { #prefix::ops::NdAddStrict },
                OpsBinaryMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdAddWrapping },
                OpsBinaryMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdAddSaturating },
                OpsBinaryMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdAddOverflowing },
            },
            OpsBinary::Sub(_, mode) => match mode {
                OpsBinaryMode::Default(_) => parse_quote! { #prefix::ops::NdSub },
                OpsBinaryMode::Checked(_, _) => parse_quote! { #prefix::ops::NdSubChecked },
                OpsBinaryMode::Strict(_, _) => parse_quote! { #prefix::ops::NdSubStrict },
                OpsBinaryMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdSubWrapping },
                OpsBinaryMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdSubSaturating },
                OpsBinaryMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdSubOverflowing },
            },
            OpsBinary::Mul(_, mode) => match mode {
                OpsBinaryMode::Default(_) => parse_quote! { #prefix::ops::NdMul },
                OpsBinaryMode::Checked(_, _) => parse_quote! { #prefix::ops::NdMulChecked },
                OpsBinaryMode::Strict(_, _) => parse_quote! { #prefix::ops::NdMulStrict },
                OpsBinaryMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdMulWrapping },
                OpsBinaryMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdMulSaturating },
                OpsBinaryMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdMulOverflowing },
            },
            OpsBinary::Div(_, mode) => match mode {
                OpsBinaryMode::Default(_) => parse_quote! { #prefix::ops::NdDiv },
                OpsBinaryMode::Checked(_, _) => parse_quote! { #prefix::ops::NdDivChecked },
                OpsBinaryMode::Strict(_, _) => parse_quote! { #prefix::ops::NdDivStrict },
                OpsBinaryMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdDivWrapping },
                OpsBinaryMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdDivSaturating },
                OpsBinaryMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdDivOverflowing },
            },
            OpsBinary::Rem(_, mode) => match mode {
                OpsBinaryMode::Default(_) => parse_quote! { #prefix::ops::NdRem },
                OpsBinaryMode::Checked(_, _) => parse_quote! { #prefix::ops::NdRemChecked },
                OpsBinaryMode::Strict(_, _) => parse_quote! { #prefix::ops::NdRemStrict },
                OpsBinaryMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdRemWrapping },
                OpsBinaryMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdRemSaturating },
                OpsBinaryMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdRemOverflowing },
            },
            OpsBinary::BitOr(_) => parse_quote! { #prefix::ops::NdBitOr },
            OpsBinary::BitAnd(_) => parse_quote! { #prefix::ops::NdBitAnd },
            OpsBinary::BitXor(_) => parse_quote! { #prefix::ops::NdBitXor },
            OpsBinary::Shl(_, mode) => match mode {
                OpsBinaryShiftMode::Default(_) => parse_quote! { #prefix::ops::NdShl },
                OpsBinaryShiftMode::Checked(_, _) => parse_quote! { #prefix::ops::NdShlChecked },
                OpsBinaryShiftMode::Strict(_, _) => parse_quote! { #prefix::ops::NdShlStrict },
                OpsBinaryShiftMode::Unbounded(_, _) => parse_quote! { #prefix::ops::NdShlUnbounded },
                OpsBinaryShiftMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdShlOverflowing },
            },
            OpsBinary::Shr(_, mode) => match mode {
                OpsBinaryShiftMode::Default(_) => parse_quote! { #prefix::ops::NdShr },
                OpsBinaryShiftMode::Checked(_, _) => parse_quote! { #prefix::ops::NdShrChecked },
                OpsBinaryShiftMode::Strict(_, _) => parse_quote! { #prefix::ops::NdShrStrict },
                OpsBinaryShiftMode::Unbounded(_, _) => parse_quote! { #prefix::ops::NdShrUnbounded },
                OpsBinaryShiftMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdShrOverflowing },
            },
        }
    }

    fn ty(&self, ty: &Type) -> Type {
        match self {
            OpsBinary::Add(_, OpsBinaryMode::Checked(_, _))
            | OpsBinary::Sub(_, OpsBinaryMode::Checked(_, _))
            | OpsBinary::Mul(_, OpsBinaryMode::Checked(_, _))
            | OpsBinary::Div(_, OpsBinaryMode::Checked(_, _))
            | OpsBinary::Rem(_, OpsBinaryMode::Checked(_, _))
            | OpsBinary::Shl(_, OpsBinaryShiftMode::Checked(_, _))
            | OpsBinary::Shr(_, OpsBinaryShiftMode::Checked(_, _)) => parse_quote! { Option<#ty> },
            OpsBinary::Add(_, OpsBinaryMode::Overflowing(_, _))
            | OpsBinary::Sub(_, OpsBinaryMode::Overflowing(_, _))
            | OpsBinary::Mul(_, OpsBinaryMode::Overflowing(_, _))
            | OpsBinary::Div(_, OpsBinaryMode::Overflowing(_, _))
            | OpsBinary::Rem(_, OpsBinaryMode::Overflowing(_, _))
            | OpsBinary::Shl(_, OpsBinaryShiftMode::Overflowing(_, _))
            | OpsBinary::Shr(_, OpsBinaryShiftMode::Overflowing(_, _)) => parse_quote! { (#ty, bool) },
            _ => ty.clone(),
        }
    }

    fn expr(&self, expr: Expr) -> Expr {
        match self {
            OpsBinary::Add(_, OpsBinaryMode::Checked(_, _))
            | OpsBinary::Sub(_, OpsBinaryMode::Checked(_, _))
            | OpsBinary::Mul(_, OpsBinaryMode::Checked(_, _))
            | OpsBinary::Div(_, OpsBinaryMode::Checked(_, _))
            | OpsBinary::Rem(_, OpsBinaryMode::Checked(_, _))
            | OpsBinary::Shl(_, OpsBinaryShiftMode::Checked(_, _))
            | OpsBinary::Shr(_, OpsBinaryShiftMode::Checked(_, _)) => parse_quote! { (#expr).map(Self::from) },
            OpsBinary::Add(_, OpsBinaryMode::Overflowing(_, _))
            | OpsBinary::Sub(_, OpsBinaryMode::Overflowing(_, _))
            | OpsBinary::Mul(_, OpsBinaryMode::Overflowing(_, _))
            | OpsBinary::Div(_, OpsBinaryMode::Overflowing(_, _))
            | OpsBinary::Rem(_, OpsBinaryMode::Overflowing(_, _))
            | OpsBinary::Shl(_, OpsBinaryShiftMode::Overflowing(_, _))
            | OpsBinary::Shr(_, OpsBinaryShiftMode::Overflowing(_, _)) => {
                parse_quote! {{ let (val, flag) = (#expr); (Self::from(val), flag) }}
            },
            _ => expr,
        }
    }
}

impl OpsNdUnary {
    fn ident(&self) -> Ident {
        match self {
            OpsUnary::Not(_) => parse_quote! { nd_not },
            OpsUnary::Neg(_, mode) => match mode {
                OpsUnaryMode::Default(_) => parse_quote! { nd_neg },
                OpsUnaryMode::Checked(_, _) => parse_quote! { nd_neg_checked },
                OpsUnaryMode::Strict(_, _) => parse_quote! { nd_neg_strict },
                OpsUnaryMode::Wrapping(_, _) => parse_quote! { nd_neg_wrapping },
                OpsUnaryMode::Saturating(_, _) => parse_quote! { nd_neg_saturating },
                OpsUnaryMode::Overflowing(_, _) => parse_quote! { nd_neg_overflowing },
            },
        }
    }

    fn path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndext });

        match self {
            OpsUnary::Not(_) => parse_quote! { #prefix::ops::NdNot },
            OpsUnary::Neg(_, mode) => match mode {
                OpsUnaryMode::Default(_) => parse_quote! { #prefix::ops::NdNeg },
                OpsUnaryMode::Checked(_, _) => parse_quote! { #prefix::ops::NdNegChecked },
                OpsUnaryMode::Strict(_, _) => parse_quote! { #prefix::ops::NdNegStrict },
                OpsUnaryMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdNegWrapping },
                OpsUnaryMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdNegSaturating },
                OpsUnaryMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdNegOverflowing },
            },
        }
    }

    fn ty(&self, ty: &Type) -> Type {
        match self {
            OpsUnary::Neg(_, OpsUnaryMode::Checked(_, _)) => parse_quote! { Option<#ty> },
            OpsUnary::Neg(_, OpsUnaryMode::Overflowing(_, _)) => parse_quote! { (#ty, bool) },
            _ => ty.clone(),
        }
    }

    fn expr(&self, expr: Expr) -> Expr {
        match self {
            OpsUnary::Neg(_, OpsUnaryMode::Checked(_, _)) => parse_quote! { (#expr).map(Self::from) },
            OpsUnary::Neg(_, OpsUnaryMode::Overflowing(_, _)) => {
                parse_quote! {{ let (val, flag) = (#expr); (Self::from(val), flag) }}
            },
            _ => expr,
        }
    }
}

impl OpsStdAssignFwd {
    fn to_impl(&self) -> OpsNdAssign {
        match self {
            OpsAssign::Add(token, mode) => OpsAssign::Add(*token, mode.into()),
            OpsAssign::Sub(token, mode) => OpsAssign::Sub(*token, mode.into()),
            OpsAssign::Mul(token, mode) => OpsAssign::Mul(*token, mode.into()),
            OpsAssign::Div(token, mode) => OpsAssign::Div(*token, mode.into()),
            OpsAssign::Rem(token, mode) => OpsAssign::Rem(*token, mode.into()),
            OpsAssign::BitOr(token) => OpsAssign::BitOr(*token),
            OpsAssign::BitAnd(token) => OpsAssign::BitAnd(*token),
            OpsAssign::BitXor(token) => OpsAssign::BitXor(*token),
            OpsAssign::Shl(token, mode) => OpsAssign::Shl(*token, mode.into()),
            OpsAssign::Shr(token, mode) => OpsAssign::Shr(*token, mode.into()),
        }
    }
}

impl OpsStdBinaryFwd {
    fn to_impl(&self) -> OpsNdBinary {
        match self {
            OpsBinary::Add(token, mode) => OpsBinary::Add(*token, mode.into()),
            OpsBinary::Sub(token, mode) => OpsBinary::Sub(*token, mode.into()),
            OpsBinary::Mul(token, mode) => OpsBinary::Mul(*token, mode.into()),
            OpsBinary::Div(token, mode) => OpsBinary::Div(*token, mode.into()),
            OpsBinary::Rem(token, mode) => OpsBinary::Rem(*token, mode.into()),
            OpsBinary::BitOr(token) => OpsBinary::BitOr(*token),
            OpsBinary::BitAnd(token) => OpsBinary::BitAnd(*token),
            OpsBinary::BitXor(token) => OpsBinary::BitXor(*token),
            OpsBinary::Shl(token, mode) => OpsBinary::Shl(*token, mode.into()),
            OpsBinary::Shr(token, mode) => OpsBinary::Shr(*token, mode.into()),
        }
    }
}

impl OpsStdUnaryFwd {
    fn to_impl(&self) -> OpsNdUnary {
        match self {
            OpsUnary::Not(token) => OpsUnary::Not(*token),
            OpsUnary::Neg(token, mode) => OpsUnary::Neg(*token, mode.into()),
        }
    }
}

impl OpsNdAssignFwd {
    fn to_impl(&self) -> OpsNdAssign {
        fn get_mode(mode: &OpsAssignMode<OpsAssignModeWith>) -> OpsAssignMode<OpsNoop> {
            match mode {
                OpsAssignMode::Default(mode) => mode.into(),
                OpsAssignMode::Strict(token, kw) => OpsAssignMode::Strict(*token, *kw),
                OpsAssignMode::Wrapping(token, kw) => OpsAssignMode::Wrapping(*token, *kw),
                OpsAssignMode::Saturating(token, kw) => OpsAssignMode::Saturating(*token, *kw),
            }
        }

        fn get_shift_mode(mode: &OpsAssignShiftMode<OpsAssignShiftModeWith>) -> OpsAssignShiftMode<OpsNoop> {
            match mode {
                OpsAssignShiftMode::Default(mode) => mode.into(),
                OpsAssignShiftMode::Strict(token, kw) => OpsAssignShiftMode::Strict(*token, *kw),
                OpsAssignShiftMode::Unbounded(token, kw) => OpsAssignShiftMode::Unbounded(*token, *kw),
            }
        }

        match self {
            OpsAssign::Add(token, mode) => OpsAssign::Add(*token, get_mode(mode)),
            OpsAssign::Sub(token, mode) => OpsAssign::Sub(*token, get_mode(mode)),
            OpsAssign::Mul(token, mode) => OpsAssign::Mul(*token, get_mode(mode)),
            OpsAssign::Div(token, mode) => OpsAssign::Div(*token, get_mode(mode)),
            OpsAssign::Rem(token, mode) => OpsAssign::Rem(*token, get_mode(mode)),
            OpsAssign::BitOr(token) => OpsAssign::BitOr(*token),
            OpsAssign::BitAnd(token) => OpsAssign::BitAnd(*token),
            OpsAssign::BitXor(token) => OpsAssign::BitXor(*token),
            OpsAssign::Shl(token, mode) => OpsAssign::Shl(*token, get_shift_mode(mode)),
            OpsAssign::Shr(token, mode) => OpsAssign::Shr(*token, get_shift_mode(mode)),
        }
    }
}

impl OpsNdBinaryFwd {
    fn to_impl(&self) -> OpsNdBinary {
        fn get_mode(mode: &OpsBinaryMode<OpsBinaryModeWith>) -> OpsBinaryMode<OpsNoop> {
            match mode {
                OpsBinaryMode::Default(mode) => mode.into(),
                OpsBinaryMode::Checked(token, kw) => OpsBinaryMode::Checked(*token, *kw),
                OpsBinaryMode::Strict(token, kw) => OpsBinaryMode::Strict(*token, *kw),
                OpsBinaryMode::Wrapping(token, kw) => OpsBinaryMode::Wrapping(*token, *kw),
                OpsBinaryMode::Saturating(token, kw) => OpsBinaryMode::Saturating(*token, *kw),
                OpsBinaryMode::Overflowing(token, kw) => OpsBinaryMode::Overflowing(*token, *kw),
            }
        }

        fn get_shift_mode(mode: &OpsBinaryShiftMode<OpsBinaryShiftModeWith>) -> OpsBinaryShiftMode<OpsNoop> {
            match mode {
                OpsBinaryShiftMode::Default(mode) => mode.into(),
                OpsBinaryShiftMode::Checked(token, kw) => OpsBinaryShiftMode::Checked(*token, *kw),
                OpsBinaryShiftMode::Strict(token, kw) => OpsBinaryShiftMode::Strict(*token, *kw),
                OpsBinaryShiftMode::Unbounded(token, kw) => OpsBinaryShiftMode::Unbounded(*token, *kw),
                OpsBinaryShiftMode::Overflowing(token, kw) => OpsBinaryShiftMode::Overflowing(*token, *kw),
            }
        }

        match self {
            OpsBinary::Add(token, mode) => OpsBinary::Add(*token, get_mode(mode)),
            OpsBinary::Sub(token, mode) => OpsBinary::Sub(*token, get_mode(mode)),
            OpsBinary::Mul(token, mode) => OpsBinary::Mul(*token, get_mode(mode)),
            OpsBinary::Div(token, mode) => OpsBinary::Div(*token, get_mode(mode)),
            OpsBinary::Rem(token, mode) => OpsBinary::Rem(*token, get_mode(mode)),
            OpsBinary::BitOr(token) => OpsBinary::BitOr(*token),
            OpsBinary::BitAnd(token) => OpsBinary::BitAnd(*token),
            OpsBinary::BitXor(token) => OpsBinary::BitXor(*token),
            OpsBinary::Shl(token, mode) => OpsBinary::Shl(*token, get_shift_mode(mode)),
            OpsBinary::Shr(token, mode) => OpsBinary::Shr(*token, get_shift_mode(mode)),
        }
    }
}

impl OpsNdUnaryFwd {
    fn to_impl(&self) -> OpsNdUnary {
        match self {
            OpsUnary::Not(token) => OpsUnary::Not(*token),
            OpsUnary::Neg(token, mode) => OpsUnary::Neg(
                *token,
                match mode {
                    OpsUnaryMode::Default(mode) => mode.into(),
                    OpsUnaryMode::Checked(token, kw) => OpsUnaryMode::Checked(*token, *kw),
                    OpsUnaryMode::Strict(token, kw) => OpsUnaryMode::Strict(*token, *kw),
                    OpsUnaryMode::Wrapping(token, kw) => OpsUnaryMode::Wrapping(*token, *kw),
                    OpsUnaryMode::Saturating(token, kw) => OpsUnaryMode::Saturating(*token, *kw),
                    OpsUnaryMode::Overflowing(token, kw) => OpsUnaryMode::Overflowing(*token, *kw),
                },
            ),
        }
    }
}
