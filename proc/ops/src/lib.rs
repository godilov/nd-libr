use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, quote};
use syn::{
    Error, Expr, Generics, Ident, PatType, Path, Result, Token, Type, WhereClause, WherePredicate, bracketed,
    parenthesized,
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
}

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

#[proc_macro]
pub fn all_auto(stream: TokenStreamStd) -> TokenStreamStd {
    match parse_macro_input!(stream as OpsAuto) {
        OpsAuto::StdAssign(ops) => {
            let ops = OpsImpl::<OpsStdKindAssign>::from(ops);

            quote! { #ops }.into()
        },
        OpsAuto::StdBinary(ops) => {
            let ops = OpsImpl::<OpsStdKindBinary>::from(ops);

            quote! { #ops }.into()
        },
        OpsAuto::StdUnary(ops) => {
            let ops = OpsImpl::<OpsStdKindUnary>::from(ops);

            quote! { #ops }.into()
        },
        OpsAuto::NdAssign(ops) => {
            let ops = OpsImpl::<OpsNdKindAssign>::from(ops);

            quote! { #ops }.into()
        },
        OpsAuto::NdBinary(ops) => {
            let ops = OpsImpl::<OpsNdKindBinary>::from(ops);

            quote! { #ops }.into()
        },
        OpsAuto::NdUnary(ops) => {
            let ops = OpsImpl::<OpsNdKindUnary>::from(ops);

            quote! { #ops }.into()
        },
    }
}

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
#[allow(clippy::enum_variant_names)]
enum OpsAuto {
    StdAssign(OpsImplAuto<OpsStdKindAssign>),
    StdBinary(OpsImplAuto<OpsStdKindBinary>),
    StdUnary(OpsImplAuto<OpsStdKindUnary>),
    NdAssign(OpsImplAuto<OpsNdKindAssign>),
    NdBinary(OpsImplAuto<OpsNdKindBinary>),
    NdUnary(OpsImplAuto<OpsNdKindUnary>),
}

struct OpsStdKindAssign;
struct OpsStdKindBinary;
struct OpsStdKindUnary;
struct OpsNdKindAssign;
struct OpsNdKindBinary;
struct OpsNdKindUnary;

#[allow(unused)]
struct OpsImpl<Kind: OpsKind> {
    signature: Kind::Signature,
    colon: Token![,],
    definitions: Punctuated<OpsDefinition<Kind::Operation>, Token![,]>,
}

#[allow(unused)]
struct OpsImplAuto<Kind: OpsKind> {
    signature: Kind::Signature,
    colon: Token![,],
    expression: Kind::Expression,
    ops_bracket: Bracket,
    ops: Punctuated<OpsDefinitionAuto<Kind::Operation>, Token![,]>,
}

#[allow(unused)]
struct OpsStdSignatureAssign {
    generics: Generics,
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
    token: Option<Token![crate]>,
    generics: Generics,
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
    token: Option<Token![crate]>,
    generics: Generics,
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
    token: Option<Token![crate]>,
    generics: Generics,
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
    lhs_paren: Paren,
    lhs_expr: Expr,
    rhs_paren: Paren,
    rhs_expr: Expr,
}

#[allow(unused)]
struct OpsExpressionBinary {
    lhs_paren: Paren,
    lhs_expr: Expr,
    rhs_paren: Paren,
    rhs_expr: Expr,
}

#[allow(unused)]
struct OpsExpressionUnary {
    self_paren: Paren,
    self_expr: Expr,
}

#[allow(unused)]
struct OpsDefinition<Operation: Parse> {
    op: Operation,
    expr: Expr,
    conditions: Option<OpsDefinitionConditions>,
}

#[allow(unused)]
struct OpsDefinitionAuto<Operation: Parse> {
    op: Operation,
    conditions: Option<OpsDefinitionConditions>,
}

#[allow(unused)]
struct OpsDefinitionConditions {
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
    Neg(Token![-]),
    Not(Token![!]),
}

trait OpsKind {
    type Expression: Parse;
    type Operation: Parse;
    type Signature: Parse;
}

impl OpsKind for OpsStdKindAssign {
    type Expression = OpsExpressionAssign;
    type Operation = OpsAssign;
    type Signature = OpsStdSignatureAssign;
}

impl OpsKind for OpsStdKindBinary {
    type Expression = OpsExpressionBinary;
    type Operation = OpsBinary;
    type Signature = OpsStdSignatureBinary;
}

impl OpsKind for OpsStdKindUnary {
    type Expression = OpsExpressionUnary;
    type Operation = OpsUnary;
    type Signature = OpsStdSignatureUnary;
}

impl OpsKind for OpsNdKindAssign {
    type Expression = OpsExpressionAssign;
    type Operation = OpsAssign;
    type Signature = OpsNdSignatureAssign;
}

impl OpsKind for OpsNdKindBinary {
    type Expression = OpsExpressionBinary;
    type Operation = OpsBinary;
    type Signature = OpsNdSignatureBinary;
}

impl OpsKind for OpsNdKindUnary {
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
        Ok(Self {
            signature: input.parse()?,
            colon: input.parse()?,
            definitions: input.parse_terminated(OpsDefinition::parse, Token![,])?,
        })
    }
}

impl<Kind: OpsKind> Parse for OpsImplAuto<Kind> {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        Ok(Self {
            signature: input.parse()?,
            colon: input.parse()?,
            expression: input.parse()?,
            ops_bracket: bracketed!(content in input),
            ops: content.parse_terminated(OpsDefinitionAuto::parse, Token![,])?,
        })
    }
}

impl Parse for OpsStdSignatureAssign {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;

        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;
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
            generics: get_normalized_generics(Generics {
                where_clause: gen_where,
                ..gen_
            }),
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

        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;
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
            generics: get_normalized_generics(Generics {
                where_clause: gen_where,
                ..gen_
            }),
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

        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;
        let paren = parenthesized!(content in input);
        let self_star = content.parse()?;
        let self_pat: PatType = content.parse()?;
        let arrow = input.parse()?;
        let res_ty = input.parse()?;

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
            generics: get_normalized_generics(Generics {
                where_clause: gen_where,
                ..gen_
            }),
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

        let token = input.parse()?;
        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;
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
            token,
            generics: get_normalized_generics(Generics {
                where_clause: gen_where,
                ..gen_
            }),
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

        let token = input.parse()?;
        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;
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
            token,
            generics: get_normalized_generics(Generics {
                where_clause: gen_where,
                ..gen_
            }),
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

        let token = input.parse()?;
        let gen_ = input.parse::<Generics>()?;
        let gen_where = input.parse::<Option<WhereClause>>()?;
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
            token,
            generics: get_normalized_generics(Generics {
                where_clause: gen_where,
                ..gen_
            }),
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
            signature: &'ops OpsStdSignatureAssign,
            op: &'ops OpsAssign,
            expr: &'ops Expr,
            conditions: Option<&'ops OpsDefinitionConditions>,
        }

        fn get_impl(spec: OpsSpec, rhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.get_ident();
            let path = spec.op.get_path();

            let (gen_impl, _, gen_where) = spec.signature.generics.split_for_impl();

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
            conditions: Option<&'ops OpsDefinitionConditions>,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>, rhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.get_ident();
            let path = spec.op.get_path();

            let (gen_impl, _, gen_where) = spec.signature.generics.split_for_impl();

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
            let res_ty = &spec.signature.res_ty;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path<#rhs_ref #rhs_ty> for #lhs_ref #lhs_ty #gen_where {
                    type Output = #res_ty;

                    fn #ident(self, rhs: #rhs_ref #rhs_ty) -> Self::Output {
                        #[allow(clippy::needless_borrow)]
                        (|#lhs_pat: #lhs_ref #lhs_ty, #rhs_pat: #rhs_ref #rhs_ty| { <#res_ty>::from(#expr) })(self, rhs)
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
            conditions: Option<&'ops OpsDefinitionConditions>,
        }

        fn get_impl(spec: OpsSpec, lhs_ref: Option<Token![&]>) -> TokenStream {
            let ident = spec.op.get_ident();
            let path = spec.op.get_path();

            let (gen_impl, _, gen_where) = spec.signature.generics.split_for_impl();

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
            let res_ty = &spec.signature.res_ty;

            let expr = &spec.expr;

            quote! {
                impl #gen_impl #path for #lhs_ref #self_ty #gen_where {
                    type Output = #res_ty;

                    fn #ident(self) -> Self::Output {
                        #[allow(clippy::needless_borrow)]
                        (|#self_pat: #lhs_ref #self_ty| { <#res_ty>::from(#expr) })(self)
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
            let token = self.signature.token;
            let ident = definition.op.get_ident();
            let path = definition.op.get_nd_path(token);

            let (gen_impl, _, gen_where) = self.signature.generics.split_for_impl();

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
            let token = self.signature.token;
            let ident = definition.op.get_ident();
            let path = definition.op.get_nd_path(token);

            let (gen_impl, _, gen_where) = self.signature.generics.split_for_impl();

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

            let lhs_pat = &self.signature.lhs_pat;
            let rhs_pat = &self.signature.rhs_pat;
            let lhs_ty = &self.signature.lhs_ty;
            let rhs_ty = &self.signature.rhs_ty;
            let res_ty = &self.signature.res_ty;

            let expr = &definition.expr;

            let quote = |impl_ty: &Type| {
                quote! {
                    impl #gen_impl #path<#lhs_ty, #rhs_ty> for #impl_ty #gen_where {
                        type Type = #res_ty;

                        fn #ident(#lhs_pat, #rhs_pat) -> Self::Type {
                            <#res_ty>::from(#expr)
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
            let token = self.signature.token;
            let ident = definition.op.get_ident();
            let path = definition.op.get_nd_path(token);

            let (gen_impl, _, gen_where) = self.signature.generics.split_for_impl();

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

            let self_pat = &self.signature.self_pat;
            let self_ty = &self.signature.self_ty;
            let res_ty = &self.signature.res_ty;

            let expr = &definition.expr;

            let quote = |impl_ty: &Type| {
                quote! {
                    impl #gen_impl #path<#self_ty> for #impl_ty #gen_where {
                        type Type = #res_ty;

                        fn #ident(#self_pat) -> Self::Type {
                            <#res_ty>::from(#expr)
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
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndnum });

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
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndnum });

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
        let prefix = token.map(|token| quote! { #token }).unwrap_or(quote! { ndnum });

        match self {
            OpsUnary::Neg(_) => parse_quote! { #prefix::ops::NdNeg },
            OpsUnary::Not(_) => parse_quote! { #prefix::ops::NdNot },
        }
    }
}

fn get_normalized_generics(mut generics: Generics) -> Generics {
    generics.params.pop_punct();
    generics.where_clause.as_mut().map(|clause| clause.predicates.pop_punct());
    generics
}
