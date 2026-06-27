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

    syn::custom_keyword!(posx);
    syn::custom_keyword!(negx);
    syn::custom_keyword!(addx);
    syn::custom_keyword!(mulx);

    syn::custom_keyword!(shift);
    syn::custom_keyword!(default);
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
/// <mode> := "" | @default | @checked | @strict | @wrapping | @saturating | @overflowing | @unbounded
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
/// <mode> := "" | @default | @checked | @strict | @wrapping | @saturating | @overflowing | @unbounded
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

/// Zero-boilerplate operations automation.
#[proc_macro]
pub fn auto(stream: TokenStreamStd) -> TokenStreamStd {
    match parse_macro_input!(stream as OpsAuto) {
        OpsAuto::StdAssign(ops) => {
            let ops = OpsImplFwd::<OpsStdKindAssign>::from(ops);
            let ops = OpsImpl::<OpsStdKindAssign>::from(ops);

            quote! { #ops }.into()
        },
        OpsAuto::StdBinary(ops) => {
            let ops = OpsImplFwd::<OpsStdKindBinary>::from(ops);
            let ops = OpsImpl::<OpsStdKindBinary>::from(ops);

            quote! { #ops }.into()
        },
        OpsAuto::StdUnary(ops) => {
            let ops = OpsImplFwd::<OpsStdKindUnary>::from(ops);
            let ops = OpsImpl::<OpsStdKindUnary>::from(ops);

            quote! { #ops }.into()
        },
        OpsAuto::NdAssign(ops) => {
            let ops = OpsImplFwd::<OpsNdKindAssign>::from(ops);
            let ops = OpsImpl::<OpsNdKindAssign>::from(ops);

            quote! { #ops }.into()
        },
        OpsAuto::NdBinary(ops) => {
            let ops = OpsImplFwd::<OpsNdKindBinary>::from(ops);
            let ops = OpsImpl::<OpsNdKindBinary>::from(ops);

            quote! { #ops }.into()
        },
        OpsAuto::NdUnary(ops) => {
            let ops = OpsImplFwd::<OpsNdKindUnary>::from(ops);
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

#[allow(clippy::large_enum_variant)]
enum OpsAuto {
    StdAssign(OpsImplAuto<OpsStdKindAssign>),
    StdBinary(OpsImplAuto<OpsStdKindBinary>),
    StdUnary(OpsImplAuto<OpsStdKindUnary>),
    NdAssign(OpsImplAuto<OpsNdKindAssign>),
    NdBinary(OpsImplAuto<OpsNdKindBinary>),
    NdUnary(OpsImplAuto<OpsNdKindUnary>),
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
struct OpsImplAuto<Kind: OpsKindAuto> {
    mode: Kind::Mode,
    token: Option<Token![crate]>,
    signature: Kind::Signature,
    colon: Token![,],
    expression: Kind::Expression,
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
    value_star: Option<Token![*]>,
    value_pat: PatType,
    value_ref: Option<Token![&]>,
    value_ty: Type,
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
    value_pat: PatType,
    value_ty: Type,
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
struct OpsExpressionAssignFwd {
    ty_paren: Paren,
    ty_expr: Type,
    lhs_paren: Paren,
    lhs_expr: Expr,
    rhs_paren: Paren,
    rhs_expr: Expr,
}

#[allow(unused)]
struct OpsExpressionAssignAuto {
    lhs_ty_paren: Paren,
    lhs_ty_expr: Type,
    rhs_ty_paren: Paren,
    rhs_ty_expr: Type,
    lhs_paren: Paren,
    lhs_expr: Expr,
    rhs_paren: Paren,
    rhs_expr: Expr,
}

#[allow(unused)]
struct OpsExpressionBinaryFwd {
    ty_paren: Paren,
    ty_expr: Type,
    lhs_paren: Paren,
    lhs_expr: Expr,
    rhs_paren: Paren,
    rhs_expr: Expr,
}

#[allow(unused)]
struct OpsExpressionBinaryAuto {
    lhs_ty_paren: Paren,
    lhs_ty_expr: Type,
    rhs_ty_paren: Paren,
    rhs_ty_expr: Type,
    ty_paren: Paren,
    ty_expr: Type,
    lhs_paren: Paren,
    lhs_expr: Expr,
    rhs_paren: Paren,
    rhs_expr: Expr,
}

#[allow(unused)]
struct OpsExpressionUnaryFwd {
    ty_paren: Paren,
    ty_expr: Type,
    value_paren: Paren,
    value_expr: Expr,
}

#[allow(unused)]
struct OpsExpressionUnaryAuto {
    value_ty_paren: Paren,
    value_ty_expr: Type,
    ty_paren: Paren,
    ty_expr: Type,
    value_paren: Paren,
    value_expr: Expr,
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
struct OpsDefinitionAuto<Operation: Parse> {
    ops: Punctuated<Operation, Token![,]>,
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

enum OpsAssignExtra<Ext: Parse, ShiftExt: Parse> {
    Std(OpsAssign<Ext, ShiftExt>),
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

#[derive(Clone, Copy)]
enum OpsAssignModeAuto {
    Std(OpsAssignModeWith),
    Shift(OpsAssignShiftModeWith),
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

enum OpsBinaryExtra<Ext: Parse, ShiftExt: Parse> {
    Std(OpsBinary<Ext, ShiftExt>),
    Addx(kw::addx),
    Mulx(kw::mulx),
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

#[derive(Clone, Copy)]
enum OpsBinaryModeAuto {
    Std(OpsBinaryModeWith),
    Shift(OpsBinaryShiftModeWith),
}

enum OpsUnary<Ext: Parse> {
    Not(Token![!]),
    Neg(Token![-], Ext),
}

enum OpsUnaryExtra<Ext: Parse> {
    Std(OpsUnary<Ext>),
    Posx(kw::posx, Ext),
    Negx(kw::negx, Ext),
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

#[derive(Clone, Copy)]
enum OpsUnaryModeAuto {
    Std(OpsUnaryModeWith),
}

type OpsStdAssign = OpsAssign<OpsNoop, OpsNoop>;
type OpsStdBinary = OpsBinary<OpsNoop, OpsNoop>;
type OpsStdUnary = OpsUnary<OpsNoop>;

type OpsNdAssign = OpsAssignExtra<OpsAssignMode<OpsNoop>, OpsAssignShiftMode<OpsNoop>>;
type OpsNdBinary = OpsBinaryExtra<OpsBinaryMode<OpsNoop>, OpsBinaryShiftMode<OpsNoop>>;
type OpsNdUnary = OpsUnaryExtra<OpsUnaryMode<OpsNoop>>;

type OpsStdAssignFwd = OpsAssign<OpsAssignModeWith, OpsAssignShiftModeWith>;
type OpsStdBinaryFwd = OpsBinary<OpsBinaryModeWith, OpsBinaryShiftModeWith>;
type OpsStdUnaryFwd = OpsUnary<OpsUnaryModeWith>;

type OpsNdAssignFwd = OpsAssignExtra<OpsAssignMode<OpsAssignModeWith>, OpsAssignShiftMode<OpsAssignShiftModeWith>>;
type OpsNdBinaryFwd = OpsBinaryExtra<OpsBinaryMode<OpsBinaryModeWith>, OpsBinaryShiftMode<OpsBinaryShiftModeWith>>;
type OpsNdUnaryFwd = OpsUnaryExtra<OpsUnaryMode<OpsUnaryModeWith>>;

trait OpsKind {
    type Signature: Parse;
    type Definition: Parse;
}

trait OpsKindFwd {
    type Signature: Parse;
    type Expression: Parse;
    type Definition: Parse;
}

trait OpsKindAuto {
    type Mode: Parse;
    type Signature: Parse;
    type Expression: Parse;
}

impl OpsKind for OpsStdKindAssign {
    type Signature = OpsStdSignatureAssign;
    type Definition = OpsDefinition<OpsStdAssign>;
}

impl OpsKind for OpsStdKindBinary {
    type Signature = OpsStdSignatureBinary;
    type Definition = OpsDefinition<OpsStdBinary>;
}

impl OpsKind for OpsStdKindUnary {
    type Signature = OpsStdSignatureUnary;
    type Definition = OpsDefinition<OpsStdUnary>;
}

impl OpsKind for OpsNdKindAssign {
    type Signature = OpsNdSignatureAssign;
    type Definition = OpsDefinition<OpsNdAssign>;
}

impl OpsKind for OpsNdKindBinary {
    type Signature = OpsNdSignatureBinary;
    type Definition = OpsDefinition<OpsNdBinary>;
}

impl OpsKind for OpsNdKindUnary {
    type Signature = OpsNdSignatureUnary;
    type Definition = OpsDefinition<OpsNdUnary>;
}

impl OpsKindFwd for OpsStdKindAssign {
    type Signature = OpsStdSignatureAssign;
    type Expression = OpsExpressionAssignFwd;
    type Definition = OpsDefinitionFwd<OpsStdAssignFwd>;
}

impl OpsKindFwd for OpsStdKindBinary {
    type Signature = OpsStdSignatureBinary;
    type Expression = OpsExpressionBinaryFwd;
    type Definition = OpsDefinitionFwd<OpsStdBinaryFwd>;
}

impl OpsKindFwd for OpsStdKindUnary {
    type Signature = OpsStdSignatureUnary;
    type Expression = OpsExpressionUnaryFwd;
    type Definition = OpsDefinitionFwd<OpsStdUnaryFwd>;
}

impl OpsKindFwd for OpsNdKindAssign {
    type Signature = OpsNdSignatureAssign;
    type Expression = OpsExpressionAssignFwd;
    type Definition = OpsDefinitionFwd<OpsNdAssignFwd>;
}

impl OpsKindFwd for OpsNdKindBinary {
    type Signature = OpsNdSignatureBinary;
    type Expression = OpsExpressionBinaryFwd;
    type Definition = OpsDefinitionFwd<OpsNdBinaryFwd>;
}

impl OpsKindFwd for OpsNdKindUnary {
    type Signature = OpsNdSignatureUnary;
    type Expression = OpsExpressionUnaryFwd;
    type Definition = OpsDefinitionFwd<OpsNdUnaryFwd>;
}

impl OpsKindAuto for OpsStdKindAssign {
    type Mode = OpsAssignModeAuto;
    type Signature = OpsStdSignatureAssign;
    type Expression = OpsExpressionAssignAuto;
}

impl OpsKindAuto for OpsStdKindBinary {
    type Mode = OpsBinaryModeAuto;
    type Signature = OpsStdSignatureBinary;
    type Expression = OpsExpressionBinaryAuto;
}

impl OpsKindAuto for OpsStdKindUnary {
    type Mode = OpsUnaryModeAuto;
    type Signature = OpsStdSignatureUnary;
    type Expression = OpsExpressionUnaryAuto;
}

impl OpsKindAuto for OpsNdKindAssign {
    type Mode = OpsAssignModeAuto;
    type Signature = OpsNdSignatureAssign;
    type Expression = OpsExpressionAssignAuto;
}

impl OpsKindAuto for OpsNdKindBinary {
    type Mode = OpsBinaryModeAuto;
    type Signature = OpsNdSignatureBinary;
    type Expression = OpsExpressionBinaryAuto;
}

impl OpsKindAuto for OpsNdKindUnary {
    type Mode = OpsUnaryModeAuto;
    type Signature = OpsNdSignatureUnary;
    type Expression = OpsExpressionUnaryAuto;
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

impl<Kind: OpsKindAuto> Parse for OpsImplAuto<Kind> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            mode: input.parse()?,
            token: input.parse()?,
            signature: input.parse()?,
            colon: input.parse()?,
            expression: input.parse()?,
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
        let value_star = content.parse()?;
        let value_pat: PatType = content.parse()?;
        let arrow = input.parse()?;
        let res_ty = input.parse()?;

        let (value_ty, value_ref) = match *value_pat.ty {
            Type::Reference(ref val) => match val.mutability {
                Some(_) => {
                    return Err(Error::new_spanned(
                        value_pat.ty,
                        "Failed to parse signature, value expected to be reference",
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
            value_star,
            value_pat,
            value_ref,
            value_ty,
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
        let value_pat: PatType = content.parse()?;
        let arrow = input.parse()?;
        let res_ty = input.parse()?;
        let impl_ty = input.parse()?;

        let value_ty = match *value_pat.ty {
            Type::Reference(ref val) if val.mutability.is_none() => (*val.elem).clone(),
            ref val => val.clone(),
        };

        Ok(Self {
            generics,
            conditions,
            paren,
            value_pat,
            value_ty,
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

impl Parse for OpsExpressionAssignFwd {
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

impl Parse for OpsExpressionAssignAuto {
    fn parse(input: ParseStream) -> Result<Self> {
        let lhs_ty_content;
        let rhs_ty_content;
        let lhs_content;
        let rhs_content;

        Ok(Self {
            lhs_ty_paren: parenthesized!(lhs_ty_content in input),
            lhs_ty_expr: lhs_ty_content.parse()?,
            rhs_ty_paren: parenthesized!(rhs_ty_content in input),
            rhs_ty_expr: rhs_ty_content.parse()?,
            lhs_paren: parenthesized!(lhs_content in input),
            lhs_expr: lhs_content.parse()?,
            rhs_paren: parenthesized!(rhs_content in input),
            rhs_expr: rhs_content.parse()?,
        })
    }
}

impl Parse for OpsExpressionBinaryFwd {
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

impl Parse for OpsExpressionBinaryAuto {
    fn parse(input: ParseStream) -> Result<Self> {
        let lhs_ty_content;
        let rhs_ty_content;
        let ty_content;
        let lhs_content;
        let rhs_content;

        Ok(Self {
            lhs_ty_paren: parenthesized!(lhs_ty_content in input),
            lhs_ty_expr: lhs_ty_content.parse()?,
            rhs_ty_paren: parenthesized!(rhs_ty_content in input),
            rhs_ty_expr: rhs_ty_content.parse()?,
            ty_paren: parenthesized!(ty_content in input),
            ty_expr: ty_content.parse()?,
            lhs_paren: parenthesized!(lhs_content in input),
            lhs_expr: lhs_content.parse()?,
            rhs_paren: parenthesized!(rhs_content in input),
            rhs_expr: rhs_content.parse()?,
        })
    }
}

impl Parse for OpsExpressionUnaryFwd {
    fn parse(input: ParseStream) -> Result<Self> {
        let ty_content;
        let value_content;

        Ok(Self {
            ty_paren: parenthesized!(ty_content in input),
            ty_expr: ty_content.parse()?,
            value_paren: parenthesized!(value_content in input),
            value_expr: value_content.parse()?,
        })
    }
}

impl Parse for OpsExpressionUnaryAuto {
    fn parse(input: ParseStream) -> Result<Self> {
        let value_ty_content;
        let ty_content;
        let value_content;

        Ok(Self {
            value_ty_paren: parenthesized!(value_ty_content in input),
            value_ty_expr: value_ty_content.parse()?,
            ty_paren: parenthesized!(ty_content in input),
            ty_expr: ty_content.parse()?,
            value_paren: parenthesized!(value_content in input),
            value_expr: value_content.parse()?,
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

impl<Operation: Parse> Parse for OpsDefinitionAuto<Operation> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            ops: input.parse_terminated(Operation::parse, Token![,])?,
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

impl<Ext: Parse, ShiftExt: Parse> Parse for OpsAssignExtra<Ext, ShiftExt> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self::Std(input.parse()?))
    }
}

impl<Ext: Parse> Parse for OpsAssignMode<Ext> {
    fn parse(input: ParseStream) -> Result<Self> {
        if !input.peek(Token![@]) {
            return Ok(Self::Default(input.parse()?));
        }

        let token = input.parse()?;
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::default) {
            input.parse::<kw::default>()?;

            Ok(Self::Default(input.parse()?))
        } else if lookahead.peek(kw::strict) {
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

        if lookahead.peek(kw::default) {
            input.parse::<kw::default>()?;

            Ok(Self::Default)
        } else if lookahead.peek(kw::strict) {
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

        if lookahead.peek(kw::default) {
            input.parse::<kw::default>()?;

            Ok(Self::Default(input.parse()?))
        } else if lookahead.peek(kw::strict) {
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

        if lookahead.peek(kw::default) {
            input.parse::<kw::default>()?;

            Ok(Self::Default)
        } else if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::unbounded) {
            Ok(Self::Unbounded(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsAssignModeAuto {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![@]) && input.peek2(kw::shift) {
            input.parse::<Token![@]>()?;
            input.parse::<kw::shift>()?;

            return Ok(Self::Shift(input.parse()?));
        }

        Ok(Self::Std(input.parse()?))
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

impl<Ext: Parse, ShiftExt: Parse> Parse for OpsBinaryExtra<Ext, ShiftExt> {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::addx) {
            Ok(Self::Addx(input.parse()?))
        } else if lookahead.peek(kw::mulx) {
            Ok(Self::Mulx(input.parse()?))
        } else {
            input.parse().map(Self::Std).map_err(|mut err| {
                err.extend(lookahead.error());
                err
            })
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

        if lookahead.peek(kw::default) {
            input.parse::<kw::default>()?;

            Ok(Self::Default(input.parse()?))
        } else if lookahead.peek(kw::checked) {
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

        if lookahead.peek(kw::default) {
            input.parse::<kw::default>()?;

            Ok(Self::Default)
        } else if lookahead.peek(kw::strict) {
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

        if lookahead.peek(kw::default) {
            input.parse::<kw::default>()?;

            Ok(Self::Default(input.parse()?))
        } else if lookahead.peek(kw::checked) {
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

        if lookahead.peek(kw::default) {
            input.parse::<kw::default>()?;

            Ok(Self::Default)
        } else if lookahead.peek(kw::strict) {
            Ok(Self::Strict(token, input.parse()?))
        } else if lookahead.peek(kw::unbounded) {
            Ok(Self::Unbounded(token, input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Parse for OpsBinaryModeAuto {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![@]) && input.peek2(kw::shift) {
            input.parse::<Token![@]>()?;
            input.parse::<kw::shift>()?;

            return Ok(Self::Shift(input.parse()?));
        }

        Ok(Self::Std(input.parse()?))
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

impl<Ext: Parse> Parse for OpsUnaryExtra<Ext> {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(kw::posx) {
            Ok(Self::Posx(input.parse()?, input.parse()?))
        } else if lookahead.peek(kw::negx) {
            Ok(Self::Negx(input.parse()?, input.parse()?))
        } else {
            input.parse().map(Self::Std).map_err(|mut err| {
                err.extend(lookahead.error());
                err
            })
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

        if lookahead.peek(kw::default) {
            input.parse::<kw::default>()?;

            Ok(Self::Default(input.parse()?))
        } else if lookahead.peek(kw::checked) {
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

        if lookahead.peek(kw::default) {
            input.parse::<kw::default>()?;

            Ok(Self::Default)
        } else if lookahead.peek(kw::strict) {
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

impl Parse for OpsUnaryModeAuto {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self::Std(input.parse()?))
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
                    #[inline]
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

                    #[inline]
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

            let value_pat = &spec.signature.value_pat.pat;
            let value_ty = &spec.signature.value_ty;
            let res_ty = &spec.signature.res_ty;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path for #lhs_ref #value_ty #gen_where {
                    type Output = #res_ty;

                    #[inline]
                    fn #ident(self) -> Self::Output {
                        #[allow(clippy::needless_borrow)]
                        <#res_ty>::from((|#value_pat: #lhs_ref #value_ty| { #expr })(self))
                    }
                }
            }
        }

        let value_star = self.signature.value_star.is_some();
        let value_ref = self.signature.value_ref.is_some();

        let some = Some(Default::default());
        let none = None;

        for definition in &self.definitions {
            let spec = OpsSpec {
                signature: &self.signature,
                op: &definition.op,
                expr: &definition.expr,
                conditions: definition.conditions.as_ref(),
            };

            match value_ref {
                true => match value_star {
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
                        #[inline]
                        fn #ident(#lhs_pat, #rhs_pat) {
                            #expr;
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

                        #[inline]
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

            let value_pat = &self.signature.value_pat;
            let value_ty = &self.signature.value_ty;
            let res_ty = &self.signature.res_ty;
            let ty = definition.op.ty(res_ty);

            let expr = &definition.expr;

            let quote = |impl_ty: &Type| {
                quote! {
                    impl #gen_impl #path<#value_ty> for #impl_ty #gen_where {
                        type Type = #res_ty;

                        #[inline]
                        fn #ident(#value_pat) -> #ty {
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
            colon: value.colon,
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
                        expr: parse_quote! {{ use #path; <#ty>::#ident(#lhs, #rhs); }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsStdKindAssign>> for OpsImplFwd<OpsStdKindAssign> {
    fn from(value: OpsImplAuto<OpsStdKindAssign>) -> Self {
        let definitions = value.mode.std_definitions(&value.expression).ops;

        OpsImplFwd {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
            expression: OpsExpressionAssignFwd {
                ty_paren: value.expression.lhs_ty_paren,
                ty_expr: value.expression.lhs_ty_expr,
                lhs_paren: value.expression.lhs_paren,
                lhs_expr: value.expression.lhs_expr,
                rhs_paren: value.expression.rhs_paren,
                rhs_expr: value.expression.rhs_expr,
            },
            definitions_bracket: Default::default(),
            definitions,
        }
    }
}

impl From<OpsImplFwd<OpsStdKindBinary>> for OpsImpl<OpsStdKindBinary> {
    fn from(value: OpsImplFwd<OpsStdKindBinary>) -> Self {
        OpsImpl {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
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
                        expr: parse_quote! {{ use #path; <#ty>::#ident(#lhs, #rhs) }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsStdKindBinary>> for OpsImplFwd<OpsStdKindBinary> {
    fn from(value: OpsImplAuto<OpsStdKindBinary>) -> Self {
        let definitions = value.mode.std_definitions(&value.expression).ops;

        OpsImplFwd {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
            expression: OpsExpressionBinaryFwd {
                ty_paren: value.expression.ty_paren,
                ty_expr: value.expression.ty_expr,
                lhs_paren: value.expression.lhs_paren,
                lhs_expr: value.expression.lhs_expr,
                rhs_paren: value.expression.rhs_paren,
                rhs_expr: value.expression.rhs_expr,
            },
            definitions_bracket: Default::default(),
            definitions,
        }
    }
}

impl From<OpsImplFwd<OpsStdKindUnary>> for OpsImpl<OpsStdKindUnary> {
    fn from(value: OpsImplFwd<OpsStdKindUnary>) -> Self {
        OpsImpl {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
            definitions_bracket: value.definitions_bracket,
            definitions: value
                .definitions
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let ty = &value.expression.ty_expr;
                    let expr = &value.expression.value_expr;
                    let conditions = definition.conditions;

                    let op_impl = op.to_impl();
                    let ident = op_impl.ident();
                    let path = op_impl.path(value.token);

                    OpsDefinition {
                        op: op.into(),
                        expr: parse_quote! {{ use #path; <#ty>::#ident(#expr) }},
                        conditions,
                    }
                })
                .collect(),
        }
    }
}

impl From<OpsImplAuto<OpsStdKindUnary>> for OpsImplFwd<OpsStdKindUnary> {
    fn from(value: OpsImplAuto<OpsStdKindUnary>) -> Self {
        let definitions = value.mode.std_definitions(&value.expression).ops;

        OpsImplFwd {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
            expression: OpsExpressionUnaryFwd {
                ty_paren: value.expression.ty_paren,
                ty_expr: value.expression.ty_expr,
                value_paren: value.expression.value_paren,
                value_expr: value.expression.value_expr,
            },
            definitions_bracket: Default::default(),
            definitions,
        }
    }
}

impl From<OpsImplFwd<OpsNdKindAssign>> for OpsImpl<OpsNdKindAssign> {
    fn from(value: OpsImplFwd<OpsNdKindAssign>) -> Self {
        OpsImpl {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
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
                    let expr = parse_quote! {{ use #path; <#ty>::#ident(#lhs, #rhs); }};

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

impl From<OpsImplAuto<OpsNdKindAssign>> for OpsImplFwd<OpsNdKindAssign> {
    fn from(value: OpsImplAuto<OpsNdKindAssign>) -> Self {
        let definitions = value.mode.nd_definitions(&value.expression).ops;

        OpsImplFwd {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
            expression: OpsExpressionAssignFwd {
                ty_paren: value.expression.lhs_ty_paren,
                ty_expr: value.expression.lhs_ty_expr,
                lhs_paren: value.expression.lhs_paren,
                lhs_expr: value.expression.lhs_expr,
                rhs_paren: value.expression.rhs_paren,
                rhs_expr: value.expression.rhs_expr,
            },
            definitions_bracket: Default::default(),
            definitions,
        }
    }
}

impl From<OpsImplFwd<OpsNdKindBinary>> for OpsImpl<OpsNdKindBinary> {
    fn from(value: OpsImplFwd<OpsNdKindBinary>) -> Self {
        let res_ty = value.signature.res_ty.clone();

        OpsImpl {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
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
                    let expr = op_impl.expr(&res_ty, parse_quote! {{ use #path; <#ty>::#ident(#lhs, #rhs) }});

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

impl From<OpsImplAuto<OpsNdKindBinary>> for OpsImplFwd<OpsNdKindBinary> {
    fn from(value: OpsImplAuto<OpsNdKindBinary>) -> Self {
        let definitions = value.mode.nd_definitions(&value.expression).ops;

        OpsImplFwd {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
            expression: OpsExpressionBinaryFwd {
                ty_paren: value.expression.ty_paren,
                ty_expr: value.expression.ty_expr,
                lhs_paren: value.expression.lhs_paren,
                lhs_expr: value.expression.lhs_expr,
                rhs_paren: value.expression.rhs_paren,
                rhs_expr: value.expression.rhs_expr,
            },
            definitions_bracket: Default::default(),
            definitions,
        }
    }
}

impl From<OpsImplFwd<OpsNdKindUnary>> for OpsImpl<OpsNdKindUnary> {
    fn from(value: OpsImplFwd<OpsNdKindUnary>) -> Self {
        let res_ty = value.signature.res_ty.clone();

        OpsImpl {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
            definitions_bracket: value.definitions_bracket,
            definitions: value
                .definitions
                .into_iter()
                .map(|definition| {
                    let op = definition.op;
                    let ty = &value.expression.ty_expr;
                    let expr = &value.expression.value_expr;
                    let conditions = definition.conditions;

                    let op_impl = op.to_impl();
                    let ident = op_impl.ident();
                    let path = op_impl.path(value.token);
                    let expr = op_impl.expr(&res_ty, parse_quote! {{ use #path; <#ty>::#ident(#expr) }});

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

impl From<OpsImplAuto<OpsNdKindUnary>> for OpsImplFwd<OpsNdKindUnary> {
    fn from(value: OpsImplAuto<OpsNdKindUnary>) -> Self {
        let definitions = value.mode.nd_definitions(&value.expression).ops;

        OpsImplFwd {
            token: value.token,
            signature: value.signature,
            colon: value.colon,
            expression: OpsExpressionUnaryFwd {
                ty_paren: value.expression.ty_paren,
                ty_expr: value.expression.ty_expr,
                value_paren: value.expression.value_paren,
                value_expr: value.expression.value_expr,
            },
            definitions_bracket: Default::default(),
            definitions,
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
            OpsAssignExtra::Std(value) => Self::Std(match value {
                OpsAssign::Add(token, mode) => OpsAssign::Add(token, mode.into()),
                OpsAssign::Sub(token, mode) => OpsAssign::Sub(token, mode.into()),
                OpsAssign::Mul(token, mode) => OpsAssign::Mul(token, mode.into()),
                OpsAssign::Div(token, mode) => OpsAssign::Div(token, mode.into()),
                OpsAssign::Rem(token, mode) => OpsAssign::Rem(token, mode.into()),
                OpsAssign::BitOr(token) => OpsAssign::BitOr(token),
                OpsAssign::BitAnd(token) => OpsAssign::BitAnd(token),
                OpsAssign::BitXor(token) => OpsAssign::BitXor(token),
                OpsAssign::Shl(token, mode) => OpsAssign::Shl(token, mode.into()),
                OpsAssign::Shr(token, mode) => OpsAssign::Shr(token, mode.into()),
            }),
        }
    }
}

impl From<OpsNdBinaryFwd> for OpsNdBinary {
    fn from(value: OpsNdBinaryFwd) -> Self {
        match value {
            OpsBinaryExtra::Std(value) => Self::Std(match value {
                OpsBinary::Add(token, mode) => OpsBinary::Add(token, mode.into()),
                OpsBinary::Sub(token, mode) => OpsBinary::Sub(token, mode.into()),
                OpsBinary::Mul(token, mode) => OpsBinary::Mul(token, mode.into()),
                OpsBinary::Div(token, mode) => OpsBinary::Div(token, mode.into()),
                OpsBinary::Rem(token, mode) => OpsBinary::Rem(token, mode.into()),
                OpsBinary::BitOr(token) => OpsBinary::BitOr(token),
                OpsBinary::BitAnd(token) => OpsBinary::BitAnd(token),
                OpsBinary::BitXor(token) => OpsBinary::BitXor(token),
                OpsBinary::Shl(token, mode) => OpsBinary::Shl(token, mode.into()),
                OpsBinary::Shr(token, mode) => OpsBinary::Shr(token, mode.into()),
            }),
            OpsBinaryExtra::Addx(token) => Self::Addx(token),
            OpsBinaryExtra::Mulx(token) => Self::Mulx(token),
        }
    }
}

impl From<OpsNdUnaryFwd> for OpsNdUnary {
    fn from(value: OpsNdUnaryFwd) -> Self {
        match value {
            OpsUnaryExtra::Std(value) => Self::Std(match value {
                OpsUnary::Not(token) => OpsUnary::Not(token),
                OpsUnary::Neg(token, mode) => OpsUnary::Neg(token, mode.into()),
            }),
            OpsUnaryExtra::Posx(token, mode) => Self::Posx(token, mode.into()),
            OpsUnaryExtra::Negx(token, mode) => Self::Negx(token, mode.into()),
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
            Self::Add(_, _) => parse_quote! { add_assign },
            Self::Sub(_, _) => parse_quote! { sub_assign },
            Self::Mul(_, _) => parse_quote! { mul_assign },
            Self::Div(_, _) => parse_quote! { div_assign },
            Self::Rem(_, _) => parse_quote! { rem_assign },
            Self::BitOr(_) => parse_quote! { bitor_assign },
            Self::BitAnd(_) => parse_quote! { bitand_assign },
            Self::BitXor(_) => parse_quote! { bitxor_assign },
            Self::Shl(_, _) => parse_quote! { shl_assign },
            Self::Shr(_, _) => parse_quote! { shr_assign },
        }
    }

    fn path(&self) -> Path {
        match self {
            Self::Add(_, _) => parse_quote! { std::ops::AddAssign },
            Self::Sub(_, _) => parse_quote! { std::ops::SubAssign },
            Self::Mul(_, _) => parse_quote! { std::ops::MulAssign },
            Self::Div(_, _) => parse_quote! { std::ops::DivAssign },
            Self::Rem(_, _) => parse_quote! { std::ops::RemAssign },
            Self::BitOr(_) => parse_quote! { std::ops::BitOrAssign },
            Self::BitAnd(_) => parse_quote! { std::ops::BitAndAssign },
            Self::BitXor(_) => parse_quote! { std::ops::BitXorAssign },
            Self::Shl(_, _) => parse_quote! { std::ops::ShlAssign },
            Self::Shr(_, _) => parse_quote! { std::ops::ShrAssign },
        }
    }
}

impl OpsStdBinary {
    fn ident(&self) -> Ident {
        match self {
            Self::Add(_, _) => parse_quote! { add },
            Self::Sub(_, _) => parse_quote! { sub },
            Self::Mul(_, _) => parse_quote! { mul },
            Self::Div(_, _) => parse_quote! { div },
            Self::Rem(_, _) => parse_quote! { rem },
            Self::BitOr(_) => parse_quote! { bitor },
            Self::BitAnd(_) => parse_quote! { bitand },
            Self::BitXor(_) => parse_quote! { bitxor },
            Self::Shl(_, _) => parse_quote! { shl },
            Self::Shr(_, _) => parse_quote! { shr },
        }
    }

    fn path(&self) -> Path {
        match self {
            Self::Add(_, _) => parse_quote! { std::ops::Add },
            Self::Sub(_, _) => parse_quote! { std::ops::Sub },
            Self::Mul(_, _) => parse_quote! { std::ops::Mul },
            Self::Div(_, _) => parse_quote! { std::ops::Div },
            Self::Rem(_, _) => parse_quote! { std::ops::Rem },
            Self::BitOr(_) => parse_quote! { std::ops::BitOr },
            Self::BitAnd(_) => parse_quote! { std::ops::BitAnd },
            Self::BitXor(_) => parse_quote! { std::ops::BitXor },
            Self::Shl(_, _) => parse_quote! { std::ops::Shl },
            Self::Shr(_, _) => parse_quote! { std::ops::Shr },
        }
    }
}

impl OpsStdUnary {
    fn ident(&self) -> Ident {
        match self {
            Self::Not(_) => parse_quote! { not },
            Self::Neg(_, _) => parse_quote! { neg },
        }
    }

    fn path(&self) -> Path {
        match self {
            Self::Not(_) => parse_quote! { std::ops::Not },
            Self::Neg(_, _) => parse_quote! { std::ops::Neg },
        }
    }
}

impl OpsNdAssign {
    fn ident(&self) -> Ident {
        match self {
            Self::Std(value) => match value {
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
            },
        }
    }

    fn path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndext });

        match self {
            Self::Std(value) => match value {
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
            },
        }
    }
}

impl OpsNdBinary {
    fn ident(&self) -> Ident {
        match self {
            Self::Std(value) => match value {
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
            },
            Self::Addx(_) => parse_quote! { nd_addx },
            Self::Mulx(_) => parse_quote! { nd_mulx },
        }
    }

    fn path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndext });

        match self {
            Self::Std(value) => match value {
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
            },
            Self::Addx(_) => parse_quote! { #prefix::ops::NdAddx },
            Self::Mulx(_) => parse_quote! { #prefix::ops::NdMulx },
        }
    }

    fn ty(&self, ty: &Type) -> Type {
        match self {
            Self::Std(value) => match value {
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
            },
            _ => ty.clone(),
        }
    }

    fn expr(&self, ty: &Type, expr: Expr) -> Expr {
        match self {
            Self::Std(value) => match value {
                OpsBinary::Add(_, OpsBinaryMode::Checked(_, _))
                | OpsBinary::Sub(_, OpsBinaryMode::Checked(_, _))
                | OpsBinary::Mul(_, OpsBinaryMode::Checked(_, _))
                | OpsBinary::Div(_, OpsBinaryMode::Checked(_, _))
                | OpsBinary::Rem(_, OpsBinaryMode::Checked(_, _))
                | OpsBinary::Shl(_, OpsBinaryShiftMode::Checked(_, _))
                | OpsBinary::Shr(_, OpsBinaryShiftMode::Checked(_, _)) => parse_quote! { (#expr).map(<#ty>::from) },
                OpsBinary::Add(_, OpsBinaryMode::Overflowing(_, _))
                | OpsBinary::Sub(_, OpsBinaryMode::Overflowing(_, _))
                | OpsBinary::Mul(_, OpsBinaryMode::Overflowing(_, _))
                | OpsBinary::Div(_, OpsBinaryMode::Overflowing(_, _))
                | OpsBinary::Rem(_, OpsBinaryMode::Overflowing(_, _))
                | OpsBinary::Shl(_, OpsBinaryShiftMode::Overflowing(_, _))
                | OpsBinary::Shr(_, OpsBinaryShiftMode::Overflowing(_, _)) => {
                    parse_quote! {{ let (val, flag) = (#expr); (<#ty>::from(val), flag) }}
                },
                _ => expr,
            },
            _ => expr,
        }
    }
}

impl OpsNdUnary {
    fn ident(&self) -> Ident {
        match self {
            Self::Std(value) => match value {
                OpsUnary::Not(_) => parse_quote! { nd_not },
                OpsUnary::Neg(_, mode) => match mode {
                    OpsUnaryMode::Default(_) => parse_quote! { nd_neg },
                    OpsUnaryMode::Checked(_, _) => parse_quote! { nd_neg_checked },
                    OpsUnaryMode::Strict(_, _) => parse_quote! { nd_neg_strict },
                    OpsUnaryMode::Wrapping(_, _) => parse_quote! { nd_neg_wrapping },
                    OpsUnaryMode::Saturating(_, _) => parse_quote! { nd_neg_saturating },
                    OpsUnaryMode::Overflowing(_, _) => parse_quote! { nd_neg_overflowing },
                },
            },
            Self::Posx(_, mode) => match mode {
                OpsUnaryMode::Default(_) => parse_quote! { nd_posx },
                OpsUnaryMode::Checked(_, _) => parse_quote! { nd_posx_checked },
                OpsUnaryMode::Strict(_, _) => parse_quote! { nd_posx_strict },
                OpsUnaryMode::Wrapping(_, _) => parse_quote! { nd_posx_wrapping },
                OpsUnaryMode::Saturating(_, _) => parse_quote! { nd_posx_saturating },
                OpsUnaryMode::Overflowing(_, _) => parse_quote! { nd_posx_overflowing },
            },
            Self::Negx(_, mode) => match mode {
                OpsUnaryMode::Default(_) => parse_quote! { nd_negx },
                OpsUnaryMode::Checked(_, _) => parse_quote! { nd_negx_checked },
                OpsUnaryMode::Strict(_, _) => parse_quote! { nd_negx_strict },
                OpsUnaryMode::Wrapping(_, _) => parse_quote! { nd_negx_wrapping },
                OpsUnaryMode::Saturating(_, _) => parse_quote! { nd_negx_saturating },
                OpsUnaryMode::Overflowing(_, _) => parse_quote! { nd_negx_overflowing },
            },
        }
    }

    fn path(&self, token: Option<Token![crate]>) -> Path {
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndext });

        match self {
            Self::Std(value) => match value {
                OpsUnary::Not(_) => parse_quote! { #prefix::ops::NdNot },
                OpsUnary::Neg(_, mode) => match mode {
                    OpsUnaryMode::Default(_) => parse_quote! { #prefix::ops::NdNeg },
                    OpsUnaryMode::Checked(_, _) => parse_quote! { #prefix::ops::NdNegChecked },
                    OpsUnaryMode::Strict(_, _) => parse_quote! { #prefix::ops::NdNegStrict },
                    OpsUnaryMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdNegWrapping },
                    OpsUnaryMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdNegSaturating },
                    OpsUnaryMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdNegOverflowing },
                },
            },
            Self::Posx(_, mode) => match mode {
                OpsUnaryMode::Default(_) => parse_quote! { #prefix::ops::NdPosx },
                OpsUnaryMode::Checked(_, _) => parse_quote! { #prefix::ops::NdPosxChecked },
                OpsUnaryMode::Strict(_, _) => parse_quote! { #prefix::ops::NdPosxStrict },
                OpsUnaryMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdPosxWrapping },
                OpsUnaryMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdPosxSaturating },
                OpsUnaryMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdPosxOverflowing },
            },
            Self::Negx(_, mode) => match mode {
                OpsUnaryMode::Default(_) => parse_quote! { #prefix::ops::NdNegx },
                OpsUnaryMode::Checked(_, _) => parse_quote! { #prefix::ops::NdNegxChecked },
                OpsUnaryMode::Strict(_, _) => parse_quote! { #prefix::ops::NdNegxStrict },
                OpsUnaryMode::Wrapping(_, _) => parse_quote! { #prefix::ops::NdNegxWrapping },
                OpsUnaryMode::Saturating(_, _) => parse_quote! { #prefix::ops::NdNegxSaturating },
                OpsUnaryMode::Overflowing(_, _) => parse_quote! { #prefix::ops::NdNegxOverflowing },
            },
        }
    }

    fn ty(&self, ty: &Type) -> Type {
        match self {
            Self::Std(value) => match value {
                OpsUnary::Neg(_, OpsUnaryMode::Checked(_, _)) => parse_quote! { Option<#ty> },
                OpsUnary::Neg(_, OpsUnaryMode::Overflowing(_, _)) => parse_quote! { (#ty, bool) },
                _ => ty.clone(),
            },
            Self::Posx(_, OpsUnaryMode::Checked(_, _)) => parse_quote! { Option<#ty> },
            Self::Posx(_, OpsUnaryMode::Overflowing(_, _)) => parse_quote! { (#ty, bool) },
            Self::Negx(_, OpsUnaryMode::Checked(_, _)) => parse_quote! { Option<#ty> },
            Self::Negx(_, OpsUnaryMode::Overflowing(_, _)) => parse_quote! { (#ty, bool) },
            _ => ty.clone(),
        }
    }

    fn expr(&self, ty: &Type, expr: Expr) -> Expr {
        match self {
            Self::Std(value) => match value {
                OpsUnary::Neg(_, OpsUnaryMode::Checked(_, _)) => parse_quote! { (#expr).map(<#ty>::from) },
                OpsUnary::Neg(_, OpsUnaryMode::Overflowing(_, _)) => {
                    parse_quote! {{ let (val, flag) = (#expr); (<#ty>::from(val), flag) }}
                },
                _ => expr,
            },
            Self::Posx(_, OpsUnaryMode::Checked(_, _)) => parse_quote! { (#expr).map(<#ty>::from) },
            Self::Posx(_, OpsUnaryMode::Overflowing(_, _)) => {
                parse_quote! {{ let (val, flag) = (#expr); (<#ty>::from(val), flag) }}
            },
            Self::Negx(_, OpsUnaryMode::Checked(_, _)) => parse_quote! { (#expr).map(<#ty>::from) },
            Self::Negx(_, OpsUnaryMode::Overflowing(_, _)) => {
                parse_quote! {{ let (val, flag) = (#expr); (<#ty>::from(val), flag) }}
            },
            _ => expr,
        }
    }
}

impl OpsStdAssignFwd {
    fn to_impl(&self) -> OpsNdAssign {
        OpsNdAssign::Std(match self {
            Self::Add(token, mode) => OpsAssign::Add(*token, mode.into()),
            Self::Sub(token, mode) => OpsAssign::Sub(*token, mode.into()),
            Self::Mul(token, mode) => OpsAssign::Mul(*token, mode.into()),
            Self::Div(token, mode) => OpsAssign::Div(*token, mode.into()),
            Self::Rem(token, mode) => OpsAssign::Rem(*token, mode.into()),
            Self::BitOr(token) => OpsAssign::BitOr(*token),
            Self::BitAnd(token) => OpsAssign::BitAnd(*token),
            Self::BitXor(token) => OpsAssign::BitXor(*token),
            Self::Shl(token, mode) => OpsAssign::Shl(*token, mode.into()),
            Self::Shr(token, mode) => OpsAssign::Shr(*token, mode.into()),
        })
    }
}

impl OpsStdBinaryFwd {
    fn to_impl(&self) -> OpsNdBinary {
        OpsNdBinary::Std(match self {
            Self::Add(token, mode) => OpsBinary::Add(*token, mode.into()),
            Self::Sub(token, mode) => OpsBinary::Sub(*token, mode.into()),
            Self::Mul(token, mode) => OpsBinary::Mul(*token, mode.into()),
            Self::Div(token, mode) => OpsBinary::Div(*token, mode.into()),
            Self::Rem(token, mode) => OpsBinary::Rem(*token, mode.into()),
            Self::BitOr(token) => OpsBinary::BitOr(*token),
            Self::BitAnd(token) => OpsBinary::BitAnd(*token),
            Self::BitXor(token) => OpsBinary::BitXor(*token),
            Self::Shl(token, mode) => OpsBinary::Shl(*token, mode.into()),
            Self::Shr(token, mode) => OpsBinary::Shr(*token, mode.into()),
        })
    }
}

impl OpsStdUnaryFwd {
    fn to_impl(&self) -> OpsNdUnary {
        OpsNdUnary::Std(match self {
            Self::Not(token) => OpsUnary::Not(*token),
            Self::Neg(token, mode) => OpsUnary::Neg(*token, mode.into()),
        })
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

        OpsNdAssign::Std(match self {
            Self::Std(value) => match value {
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
            },
        })
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
            Self::Std(value) => OpsNdBinary::Std(match value {
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
            }),
            Self::Addx(token) => OpsNdBinary::Addx(*token),
            Self::Mulx(token) => OpsNdBinary::Mulx(*token),
        }
    }
}

impl OpsNdUnaryFwd {
    fn to_impl(&self) -> OpsNdUnary {
        match self {
            Self::Std(value) => OpsNdUnary::Std(match value {
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
            }),
            Self::Posx(token, mode) => OpsNdUnary::Posx(
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
            Self::Negx(token, mode) => OpsNdUnary::Negx(
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

impl OpsAssignModeAuto {
    fn std_definitions(&self, expr: &OpsExpressionAssignAuto) -> OpsDefinitionAuto<OpsDefinitionFwd<OpsStdAssignFwd>> {
        let lhs_ty = &expr.lhs_ty_expr;
        let rhs_ty = &expr.rhs_ty_expr;

        match self {
            OpsAssignModeAuto::Std(mode) => {
                let quote = quote! {
                    |= where [#lhs_ty: NdBitOrAssign <#lhs_ty, #rhs_ty>],
                    &= where [#lhs_ty: NdBitAndAssign<#lhs_ty, #rhs_ty>],
                    ^= where [#lhs_ty: NdBitXorAssign<#lhs_ty, #rhs_ty>],
                };

                match mode {
                    OpsAssignModeWith::Default => parse_quote! {
                        += where [#lhs_ty: NdAddAssign<#lhs_ty, #rhs_ty>],
                        -= where [#lhs_ty: NdSubAssign<#lhs_ty, #rhs_ty>],
                        *= where [#lhs_ty: NdMulAssign<#lhs_ty, #rhs_ty>],
                        /= where [#lhs_ty: NdDivAssign<#lhs_ty, #rhs_ty>],
                        %= where [#lhs_ty: NdRemAssign<#lhs_ty, #rhs_ty>],

                        #quote
                    },
                    OpsAssignModeWith::Strict(_, _) => parse_quote! {
                        += with @strict where [#lhs_ty: NdAddAssignStrict<#lhs_ty, #rhs_ty>],
                        -= with @strict where [#lhs_ty: NdSubAssignStrict<#lhs_ty, #rhs_ty>],
                        *= with @strict where [#lhs_ty: NdMulAssignStrict<#lhs_ty, #rhs_ty>],
                        /= with @strict where [#lhs_ty: NdDivAssignStrict<#lhs_ty, #rhs_ty>],
                        %= with @strict where [#lhs_ty: NdRemAssignStrict<#lhs_ty, #rhs_ty>],

                        #quote
                    },
                    OpsAssignModeWith::Wrapping(_, _) => parse_quote! {
                        += with @wrapping where [#lhs_ty: NdAddAssignWrapping<#lhs_ty, #rhs_ty>],
                        -= with @wrapping where [#lhs_ty: NdSubAssignWrapping<#lhs_ty, #rhs_ty>],
                        *= with @wrapping where [#lhs_ty: NdMulAssignWrapping<#lhs_ty, #rhs_ty>],
                        /= with @wrapping where [#lhs_ty: NdDivAssignWrapping<#lhs_ty, #rhs_ty>],
                        %= with @wrapping where [#lhs_ty: NdRemAssignWrapping<#lhs_ty, #rhs_ty>],

                        #quote
                    },
                    OpsAssignModeWith::Saturating(_, _) => parse_quote! {
                        += with @saturating where [#lhs_ty: NdAddAssignSaturating<#lhs_ty, #rhs_ty>],
                        -= with @saturating where [#lhs_ty: NdSubAssignSaturating<#lhs_ty, #rhs_ty>],
                        *= with @saturating where [#lhs_ty: NdMulAssignSaturating<#lhs_ty, #rhs_ty>],
                        /= with @saturating where [#lhs_ty: NdDivAssignSaturating<#lhs_ty, #rhs_ty>],
                        %= with @saturating where [#lhs_ty: NdRemAssignSaturating<#lhs_ty, #rhs_ty>],

                        #quote
                    },
                }
            },
            OpsAssignModeAuto::Shift(mode) => match mode {
                OpsAssignShiftModeWith::Default => parse_quote! {
                    <<= where [#lhs_ty: NdShlAssign<#lhs_ty, #rhs_ty>],
                    >>= where [#lhs_ty: NdShrAssign<#lhs_ty, #rhs_ty>],
                },
                OpsAssignShiftModeWith::Strict(_, _) => parse_quote! {
                    <<= with @strict where [#lhs_ty: NdShlAssignStrict<#lhs_ty, #rhs_ty>],
                    >>= with @strict where [#lhs_ty: NdShrAssignStrict<#lhs_ty, #rhs_ty>],
                },
                OpsAssignShiftModeWith::Unbounded(_, _) => parse_quote! {
                    <<= with @unbounded where [#lhs_ty: NdShlAssignUnbounded<#lhs_ty, #rhs_ty>],
                    >>= with @unbounded where [#lhs_ty: NdShrAssignUnbounded<#lhs_ty, #rhs_ty>],
                },
            },
        }
    }

    fn nd_definitions(&self, expr: &OpsExpressionAssignAuto) -> OpsDefinitionAuto<OpsDefinitionFwd<OpsNdAssignFwd>> {
        let lhs_ty = &expr.lhs_ty_expr;
        let rhs_ty = &expr.rhs_ty_expr;

        match self {
            OpsAssignModeAuto::Std(mode) => {
                let quote = quote! {
                    |= where [#lhs_ty: NdBitOrAssign <#lhs_ty, #rhs_ty>],
                    &= where [#lhs_ty: NdBitAndAssign<#lhs_ty, #rhs_ty>],
                    ^= where [#lhs_ty: NdBitXorAssign<#lhs_ty, #rhs_ty>],
                };

                match mode {
                    OpsAssignModeWith::Default => parse_quote! {
                        += where             [#lhs_ty: NdAddAssign          <#lhs_ty, #rhs_ty>],
                        -= where             [#lhs_ty: NdSubAssign          <#lhs_ty, #rhs_ty>],
                        *= where             [#lhs_ty: NdMulAssign          <#lhs_ty, #rhs_ty>],
                        /= where             [#lhs_ty: NdDivAssign          <#lhs_ty, #rhs_ty>],
                        %= where             [#lhs_ty: NdRemAssign          <#lhs_ty, #rhs_ty>],
                        += @strict where     [#lhs_ty: NdAddAssignStrict    <#lhs_ty, #rhs_ty>],
                        -= @strict where     [#lhs_ty: NdSubAssignStrict    <#lhs_ty, #rhs_ty>],
                        *= @strict where     [#lhs_ty: NdMulAssignStrict    <#lhs_ty, #rhs_ty>],
                        /= @strict where     [#lhs_ty: NdDivAssignStrict    <#lhs_ty, #rhs_ty>],
                        %= @strict where     [#lhs_ty: NdRemAssignStrict    <#lhs_ty, #rhs_ty>],
                        += @wrapping where   [#lhs_ty: NdAddAssignWrapping  <#lhs_ty, #rhs_ty>],
                        -= @wrapping where   [#lhs_ty: NdSubAssignWrapping  <#lhs_ty, #rhs_ty>],
                        *= @wrapping where   [#lhs_ty: NdMulAssignWrapping  <#lhs_ty, #rhs_ty>],
                        /= @wrapping where   [#lhs_ty: NdDivAssignWrapping  <#lhs_ty, #rhs_ty>],
                        %= @wrapping where   [#lhs_ty: NdRemAssignWrapping  <#lhs_ty, #rhs_ty>],
                        += @saturating where [#lhs_ty: NdAddAssignSaturating<#lhs_ty, #rhs_ty>],
                        -= @saturating where [#lhs_ty: NdSubAssignSaturating<#lhs_ty, #rhs_ty>],
                        *= @saturating where [#lhs_ty: NdMulAssignSaturating<#lhs_ty, #rhs_ty>],
                        /= @saturating where [#lhs_ty: NdDivAssignSaturating<#lhs_ty, #rhs_ty>],
                        %= @saturating where [#lhs_ty: NdRemAssignSaturating<#lhs_ty, #rhs_ty>],

                        #quote
                    },
                    OpsAssignModeWith::Strict(_, _) => parse_quote! {
                        += with @strict where [#lhs_ty: NdAddAssignStrict<#lhs_ty, #rhs_ty>],
                        -= with @strict where [#lhs_ty: NdSubAssignStrict<#lhs_ty, #rhs_ty>],
                        *= with @strict where [#lhs_ty: NdMulAssignStrict<#lhs_ty, #rhs_ty>],
                        /= with @strict where [#lhs_ty: NdDivAssignStrict<#lhs_ty, #rhs_ty>],
                        %= with @strict where [#lhs_ty: NdRemAssignStrict<#lhs_ty, #rhs_ty>],

                        #quote
                    },
                    OpsAssignModeWith::Wrapping(_, _) => parse_quote! {
                        += with @wrapping where [#lhs_ty: NdAddAssignWrapping<#lhs_ty, #rhs_ty>],
                        -= with @wrapping where [#lhs_ty: NdSubAssignWrapping<#lhs_ty, #rhs_ty>],
                        *= with @wrapping where [#lhs_ty: NdMulAssignWrapping<#lhs_ty, #rhs_ty>],
                        /= with @wrapping where [#lhs_ty: NdDivAssignWrapping<#lhs_ty, #rhs_ty>],
                        %= with @wrapping where [#lhs_ty: NdRemAssignWrapping<#lhs_ty, #rhs_ty>],

                        #quote
                    },
                    OpsAssignModeWith::Saturating(_, _) => parse_quote! {
                        += with @saturating where [#lhs_ty: NdAddAssignSaturating<#lhs_ty, #rhs_ty>],
                        -= with @saturating where [#lhs_ty: NdSubAssignSaturating<#lhs_ty, #rhs_ty>],
                        *= with @saturating where [#lhs_ty: NdMulAssignSaturating<#lhs_ty, #rhs_ty>],
                        /= with @saturating where [#lhs_ty: NdDivAssignSaturating<#lhs_ty, #rhs_ty>],
                        %= with @saturating where [#lhs_ty: NdRemAssignSaturating<#lhs_ty, #rhs_ty>],

                        #quote
                    },
                }
            },
            OpsAssignModeAuto::Shift(mode) => match mode {
                OpsAssignShiftModeWith::Default => parse_quote! {
                    <<= where            [#lhs_ty: NdShlAssign         <#lhs_ty, #rhs_ty>],
                    >>= where            [#lhs_ty: NdShrAssign         <#lhs_ty, #rhs_ty>],
                    <<= @strict where    [#lhs_ty: NdShlAssignStrict   <#lhs_ty, #rhs_ty>],
                    >>= @strict where    [#lhs_ty: NdShrAssignStrict   <#lhs_ty, #rhs_ty>],
                    <<= @unbounded where [#lhs_ty: NdShlAssignUnbounded<#lhs_ty, #rhs_ty>],
                    >>= @unbounded where [#lhs_ty: NdShrAssignUnbounded<#lhs_ty, #rhs_ty>],
                },
                OpsAssignShiftModeWith::Strict(_, _) => parse_quote! {
                    <<= with @strict where [#lhs_ty: NdShlAssignStrict<#lhs_ty, #rhs_ty>],
                    >>= with @strict where [#lhs_ty: NdShrAssignStrict<#lhs_ty, #rhs_ty>],
                },
                OpsAssignShiftModeWith::Unbounded(_, _) => parse_quote! {
                    <<= with @unbounded where [#lhs_ty: NdShlAssignUnbounded<#lhs_ty, #rhs_ty>],
                    >>= with @unbounded where [#lhs_ty: NdShrAssignUnbounded<#lhs_ty, #rhs_ty>],
                },
            },
        }
    }
}

impl OpsBinaryModeAuto {
    fn std_definitions(&self, expr: &OpsExpressionBinaryAuto) -> OpsDefinitionAuto<OpsDefinitionFwd<OpsStdBinaryFwd>> {
        let lhs_ty = &expr.lhs_ty_expr;
        let rhs_ty = &expr.rhs_ty_expr;
        let ty = &expr.ty_expr;

        match self {
            OpsBinaryModeAuto::Std(mode) => {
                let quote = quote! {
                    | where [#lhs_ty: NdBitOr <#lhs_ty, #rhs_ty, Type = #ty>],
                    & where [#lhs_ty: NdBitAnd<#lhs_ty, #rhs_ty, Type = #ty>],
                    ^ where [#lhs_ty: NdBitXor<#lhs_ty, #rhs_ty, Type = #ty>],

                    addx where [#lhs_ty: NdAddx<#lhs_ty, #rhs_ty, Type = #ty>],
                    mulx where [#lhs_ty: NdMulx<#lhs_ty, #rhs_ty, Type = #ty>],
                };

                match mode {
                    OpsBinaryModeWith::Default => parse_quote! {
                        + where [#lhs_ty: NdAdd<#lhs_ty, #rhs_ty, Type = #ty>],
                        - where [#lhs_ty: NdSub<#lhs_ty, #rhs_ty, Type = #ty>],
                        * where [#lhs_ty: NdMul<#lhs_ty, #rhs_ty, Type = #ty>],
                        / where [#lhs_ty: NdDiv<#lhs_ty, #rhs_ty, Type = #ty>],
                        % where [#lhs_ty: NdRem<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                    OpsBinaryModeWith::Strict(_, _) => parse_quote! {
                        + with @strict where [#lhs_ty: NdAddStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                        - with @strict where [#lhs_ty: NdSubStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                        * with @strict where [#lhs_ty: NdMulStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                        / with @strict where [#lhs_ty: NdDivStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                        % with @strict where [#lhs_ty: NdRemStrict<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                    OpsBinaryModeWith::Wrapping(_, _) => parse_quote! {
                        + with @wrapping where [#lhs_ty: NdAddWrapping<#lhs_ty, #rhs_ty, Type = #ty>],
                        - with @wrapping where [#lhs_ty: NdSubWrapping<#lhs_ty, #rhs_ty, Type = #ty>],
                        * with @wrapping where [#lhs_ty: NdMulWrapping<#lhs_ty, #rhs_ty, Type = #ty>],
                        / with @wrapping where [#lhs_ty: NdDivWrapping<#lhs_ty, #rhs_ty, Type = #ty>],
                        % with @wrapping where [#lhs_ty: NdRemWrapping<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                    OpsBinaryModeWith::Saturating(_, _) => parse_quote! {
                        + with @saturating where [#lhs_ty: NdAddSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        - with @saturating where [#lhs_ty: NdSubSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        * with @saturating where [#lhs_ty: NdMulSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        / with @saturating where [#lhs_ty: NdDivSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        % with @saturating where [#lhs_ty: NdRemSaturating<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                }
            },
            OpsBinaryModeAuto::Shift(mode) => match mode {
                OpsBinaryShiftModeWith::Default => parse_quote! {
                    << where [#lhs_ty: NdShl<#lhs_ty, #rhs_ty, Type = #ty>],
                    >> where [#lhs_ty: NdShr<#lhs_ty, #rhs_ty, Type = #ty>],
                },
                OpsBinaryShiftModeWith::Strict(_, _) => parse_quote! {
                    << with @strict where [#lhs_ty: NdShlStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                    >> with @strict where [#lhs_ty: NdShrStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                },
                OpsBinaryShiftModeWith::Unbounded(_, _) => parse_quote! {
                    << with @unbounded where [#lhs_ty: NdShlUnbounded<#lhs_ty, #rhs_ty, Type = #ty>],
                    >> with @unbounded where [#lhs_ty: NdShrUnbounded<#lhs_ty, #rhs_ty, Type = #ty>],
                },
            },
        }
    }

    fn nd_definitions(&self, expr: &OpsExpressionBinaryAuto) -> OpsDefinitionAuto<OpsDefinitionFwd<OpsNdBinaryFwd>> {
        let lhs_ty = &expr.lhs_ty_expr;
        let rhs_ty = &expr.rhs_ty_expr;
        let ty = &expr.ty_expr;

        match self {
            OpsBinaryModeAuto::Std(mode) => {
                let quote = quote! {
                    | where              [#lhs_ty: NdBitOr         <#lhs_ty, #rhs_ty, Type = #ty>],
                    & where              [#lhs_ty: NdBitAnd        <#lhs_ty, #rhs_ty, Type = #ty>],
                    ^ where              [#lhs_ty: NdBitXor        <#lhs_ty, #rhs_ty, Type = #ty>],
                    + @checked where     [#lhs_ty: NdAddChecked    <#lhs_ty, #rhs_ty, Type = #ty>],
                    - @checked where     [#lhs_ty: NdSubChecked    <#lhs_ty, #rhs_ty, Type = #ty>],
                    * @checked where     [#lhs_ty: NdMulChecked    <#lhs_ty, #rhs_ty, Type = #ty>],
                    / @checked where     [#lhs_ty: NdDivChecked    <#lhs_ty, #rhs_ty, Type = #ty>],
                    % @checked where     [#lhs_ty: NdRemChecked    <#lhs_ty, #rhs_ty, Type = #ty>],
                    + @overflowing where [#lhs_ty: NdAddOverflowing<#lhs_ty, #rhs_ty, Type = #ty>],
                    - @overflowing where [#lhs_ty: NdSubOverflowing<#lhs_ty, #rhs_ty, Type = #ty>],
                    * @overflowing where [#lhs_ty: NdMulOverflowing<#lhs_ty, #rhs_ty, Type = #ty>],
                    / @overflowing where [#lhs_ty: NdDivOverflowing<#lhs_ty, #rhs_ty, Type = #ty>],
                    % @overflowing where [#lhs_ty: NdRemOverflowing<#lhs_ty, #rhs_ty, Type = #ty>],
                };

                match mode {
                    OpsBinaryModeWith::Default => parse_quote! {
                        + where             [#lhs_ty: NdAdd          <#lhs_ty, #rhs_ty, Type = #ty>],
                        - where             [#lhs_ty: NdSub          <#lhs_ty, #rhs_ty, Type = #ty>],
                        * where             [#lhs_ty: NdMul          <#lhs_ty, #rhs_ty, Type = #ty>],
                        / where             [#lhs_ty: NdDiv          <#lhs_ty, #rhs_ty, Type = #ty>],
                        % where             [#lhs_ty: NdRem          <#lhs_ty, #rhs_ty, Type = #ty>],
                        + @strict where     [#lhs_ty: NdAddStrict    <#lhs_ty, #rhs_ty, Type = #ty>],
                        - @strict where     [#lhs_ty: NdSubStrict    <#lhs_ty, #rhs_ty, Type = #ty>],
                        * @strict where     [#lhs_ty: NdMulStrict    <#lhs_ty, #rhs_ty, Type = #ty>],
                        / @strict where     [#lhs_ty: NdDivStrict    <#lhs_ty, #rhs_ty, Type = #ty>],
                        % @strict where     [#lhs_ty: NdRemStrict    <#lhs_ty, #rhs_ty, Type = #ty>],
                        + @wrapping where   [#lhs_ty: NdAddWrapping  <#lhs_ty, #rhs_ty, Type = #ty>],
                        - @wrapping where   [#lhs_ty: NdSubWrapping  <#lhs_ty, #rhs_ty, Type = #ty>],
                        * @wrapping where   [#lhs_ty: NdMulWrapping  <#lhs_ty, #rhs_ty, Type = #ty>],
                        / @wrapping where   [#lhs_ty: NdDivWrapping  <#lhs_ty, #rhs_ty, Type = #ty>],
                        % @wrapping where   [#lhs_ty: NdRemWrapping  <#lhs_ty, #rhs_ty, Type = #ty>],
                        + @saturating where [#lhs_ty: NdAddSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        - @saturating where [#lhs_ty: NdSubSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        * @saturating where [#lhs_ty: NdMulSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        / @saturating where [#lhs_ty: NdDivSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        % @saturating where [#lhs_ty: NdRemSaturating<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                    OpsBinaryModeWith::Strict(_, _) => parse_quote! {
                        + with @strict where [#lhs_ty: NdAddStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                        - with @strict where [#lhs_ty: NdSubStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                        * with @strict where [#lhs_ty: NdMulStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                        / with @strict where [#lhs_ty: NdDivStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                        % with @strict where [#lhs_ty: NdRemStrict<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                    OpsBinaryModeWith::Wrapping(_, _) => parse_quote! {
                        + with @wrapping where [#lhs_ty: NdAddWrapping<#lhs_ty, #rhs_ty, Type = #ty>],
                        - with @wrapping where [#lhs_ty: NdSubWrapping<#lhs_ty, #rhs_ty, Type = #ty>],
                        * with @wrapping where [#lhs_ty: NdMulWrapping<#lhs_ty, #rhs_ty, Type = #ty>],
                        / with @wrapping where [#lhs_ty: NdDivWrapping<#lhs_ty, #rhs_ty, Type = #ty>],
                        % with @wrapping where [#lhs_ty: NdRemWrapping<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                    OpsBinaryModeWith::Saturating(_, _) => parse_quote! {
                        + with @saturating where [#lhs_ty: NdAddSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        - with @saturating where [#lhs_ty: NdSubSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        * with @saturating where [#lhs_ty: NdMulSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        / with @saturating where [#lhs_ty: NdDivSaturating<#lhs_ty, #rhs_ty, Type = #ty>],
                        % with @saturating where [#lhs_ty: NdRemSaturating<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                }
            },
            OpsBinaryModeAuto::Shift(mode) => {
                let quote = quote! {
                    << @checked where     [#lhs_ty: NdShlChecked    <#lhs_ty, #rhs_ty, Type = #ty>],
                    >> @checked where     [#lhs_ty: NdShrChecked    <#lhs_ty, #rhs_ty, Type = #ty>],
                    << @overflowing where [#lhs_ty: NdShlOverflowing<#lhs_ty, #rhs_ty, Type = #ty>],
                    >> @overflowing where [#lhs_ty: NdShrOverflowing<#lhs_ty, #rhs_ty, Type = #ty>],
                };

                match mode {
                    OpsBinaryShiftModeWith::Default => parse_quote! {
                        << where            [#lhs_ty: NdShl         <#lhs_ty, #rhs_ty, Type = #ty>],
                        >> where            [#lhs_ty: NdShr         <#lhs_ty, #rhs_ty, Type = #ty>],
                        << @strict where    [#lhs_ty: NdShlStrict   <#lhs_ty, #rhs_ty, Type = #ty>],
                        >> @strict where    [#lhs_ty: NdShrStrict   <#lhs_ty, #rhs_ty, Type = #ty>],
                        << @unbounded where [#lhs_ty: NdShlUnbounded<#lhs_ty, #rhs_ty, Type = #ty>],
                        >> @unbounded where [#lhs_ty: NdShrUnbounded<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                    OpsBinaryShiftModeWith::Strict(_, _) => parse_quote! {
                        << with @strict where [#lhs_ty: NdShlStrict<#lhs_ty, #rhs_ty, Type = #ty>],
                        >> with @strict where [#lhs_ty: NdShrStrict<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                    OpsBinaryShiftModeWith::Unbounded(_, _) => parse_quote! {
                        << with @unbounded where [#lhs_ty: NdShlUnbounded<#lhs_ty, #rhs_ty, Type = #ty>],
                        >> with @unbounded where [#lhs_ty: NdShrUnbounded<#lhs_ty, #rhs_ty, Type = #ty>],

                        #quote
                    },
                }
            },
        }
    }
}

impl OpsUnaryModeAuto {
    fn std_definitions(&self, expr: &OpsExpressionUnaryAuto) -> OpsDefinitionAuto<OpsDefinitionFwd<OpsStdUnaryFwd>> {
        let value_ty = &expr.value_ty_expr;
        let ty = &expr.ty_expr;

        match self {
            OpsUnaryModeAuto::Std(mode) => match mode {
                OpsUnaryModeWith::Default => parse_quote! {
                    ! where [#value_ty: NdNot<#value_ty, Type = #ty>],
                    - where [#value_ty: NdNeg<#value_ty, Type = #ty>],
                },
                OpsUnaryModeWith::Strict(_, _) => parse_quote! {
                    ! where [#value_ty: NdNot<#value_ty, Type = #ty>],

                    - with @strict where [#value_ty: NdNegStrict <#value_ty, Type = #ty>],
                },
                OpsUnaryModeWith::Wrapping(_, _) => parse_quote! {
                    ! where [#value_ty: NdNot<#value_ty, Type = #ty>],

                    - with @wrapping where [#value_ty: NdNegWrapping <#value_ty, Type = #ty>],
                },
                OpsUnaryModeWith::Saturating(_, _) => parse_quote! {
                    ! where [#value_ty: NdNot<#value_ty, Type = #ty>],

                    - with @saturating where [#value_ty: NdNegSaturating <#value_ty, Type = #ty>],
                },
            },
        }
    }

    fn nd_definitions(&self, expr: &OpsExpressionUnaryAuto) -> OpsDefinitionAuto<OpsDefinitionFwd<OpsNdUnaryFwd>> {
        let value_ty = &expr.value_ty_expr;
        let ty = &expr.ty_expr;

        match self {
            OpsUnaryModeAuto::Std(mode) => match mode {
                OpsUnaryModeWith::Default => parse_quote! {
                    ! where                 [#value_ty: NdNot           <#value_ty, Type = #ty>],
                    - where                 [#value_ty: NdNeg           <#value_ty, Type = #ty>],
                    - @checked where        [#value_ty: NdNegChecked    <#value_ty, Type = #ty>],
                    - @strict where         [#value_ty: NdNegStrict     <#value_ty, Type = #ty>],
                    - @wrapping where       [#value_ty: NdNegWrapping   <#value_ty, Type = #ty>],
                    - @saturating where     [#value_ty: NdNegSaturating <#value_ty, Type = #ty>],
                    - @overflowing where    [#value_ty: NdNegOverflowing<#value_ty, Type = #ty>],

                    posx where              [#value_ty: NdPosx           <#value_ty, Type = #ty>],
                    posx @checked where     [#value_ty: NdPosxChecked    <#value_ty, Type = #ty>],
                    posx @strict where      [#value_ty: NdPosxStrict     <#value_ty, Type = #ty>],
                    posx @wrapping where    [#value_ty: NdPosxWrapping   <#value_ty, Type = #ty>],
                    posx @saturating where  [#value_ty: NdPosxSaturating <#value_ty, Type = #ty>],
                    posx @overflowing where [#value_ty: NdPosxOverflowing<#value_ty, Type = #ty>],

                    negx where              [#value_ty: NdNegx           <#value_ty, Type = #ty>],
                    negx @checked where     [#value_ty: NdNegxChecked    <#value_ty, Type = #ty>],
                    negx @strict where      [#value_ty: NdNegxStrict     <#value_ty, Type = #ty>],
                    negx @wrapping where    [#value_ty: NdNegxWrapping   <#value_ty, Type = #ty>],
                    negx @saturating where  [#value_ty: NdNegxSaturating <#value_ty, Type = #ty>],
                    negx @overflowing where [#value_ty: NdNegxOverflowing<#value_ty, Type = #ty>],
                },
                OpsUnaryModeWith::Strict(_, _) => parse_quote! {
                    ! where [#value_ty: NdNot<#value_ty, Type = #ty>],

                    -    with @strict where [#value_ty: NdNegStrict <#value_ty, Type = #ty>],
                    posx with @strict where [#value_ty: NdPosxStrict<#value_ty, Type = #ty>],
                    negx with @strict where [#value_ty: NdNegxStrict<#value_ty, Type = #ty>],
                },
                OpsUnaryModeWith::Wrapping(_, _) => parse_quote! {
                    ! where [#value_ty: NdNot<#value_ty, Type = #ty>],

                    -    with @wrapping where [#value_ty: NdNegWrapping <#value_ty, Type = #ty>],
                    posx with @wrapping where [#value_ty: NdPosxWrapping<#value_ty, Type = #ty>],
                    negx with @wrapping where [#value_ty: NdNegxWrapping<#value_ty, Type = #ty>],
                },
                OpsUnaryModeWith::Saturating(_, _) => parse_quote! {
                    ! where [#value_ty: NdNot<#value_ty, Type = #ty>],

                    -    with @saturating where [#value_ty: NdNegSaturating <#value_ty, Type = #ty>],
                    posx with @saturating where [#value_ty: NdPosxSaturating<#value_ty, Type = #ty>],
                    negx with @saturating where [#value_ty: NdNegxSaturating<#value_ty, Type = #ty>],
                },
            },
        }
    }
}
