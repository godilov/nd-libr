#![doc = include_str!("../README.md")]

use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{
    Attribute, Error, Expr, FnArg, Generics, Ident, Item, ItemEnum, ItemImpl, ItemStruct, ItemTrait, ItemUnion, Meta,
    Path, Result, Signature, Token, TraitItem, TraitItemConst, TraitItemFn, TraitItemType, Type, WhereClause,
    parse::{Parse, ParseStream},
    parse_macro_input, parse_quote,
};

mod kw {
    syn::custom_keyword!(with);
}

/// Zero-boilerplate all standard traits forwarding for **struct**, **enum** and **union**.
///
/// Forwards all standard traits to specified expression.
///
/// # Syntax
///
/// ```text
/// #[ndfwd::all(<expr> with <type>)]
/// struct Any(<type>);
/// ```
///
/// # Examples
///
/// ```rust
/// #[ndfwd::all(self.0 with N)]
/// struct Num<N>(N);
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro_attribute]
pub fn all(attr: TokenStreamStd, ty: TokenStreamStd) -> TokenStreamStd {
    let ty = parse_macro_input!(ty as FwdType);
    let attr = parse_macro_input!(attr as FwdAttr);

    let forwards = ty.fwds(&attr);

    let std_impls = [FwdStd::Ref, FwdStd::Mut];
    let cmp_impls = [FwdCmp::Eq, FwdCmp::EqPartial, FwdCmp::Ord, FwdCmp::OrdPartial];
    let fmt_impls = [
        FwdFmt::Display,
        FwdFmt::Binary,
        FwdFmt::Octal,
        FwdFmt::HexLower,
        FwdFmt::HexUpper,
    ];
    let iter_impls = [FwdIter::From, FwdIter::Into, FwdIter::IntoRef, FwdIter::IntoMut];

    let std_impls = std_impls.into_iter().map(|std| ty.std(&attr, &forwards, std));
    let cmp_impls = cmp_impls.into_iter().map(|cmp| ty.cmp(&attr, &forwards, cmp));
    let fmt_impls = fmt_impls.into_iter().map(|fmt| ty.fmt(&attr, &forwards, fmt));
    let iter_impls = iter_impls.into_iter().map(|iter| ty.iter(&attr, &forwards, iter));

    quote! {
        #ty

        #(#std_impls)*
        #(#cmp_impls)*
        #(#fmt_impls)*
        #(#iter_impls)*
    }
    .into()
}

/// Zero-boilerplate standard traits forwarding for **struct**, **enum** and **union**.
///
/// Forwards [`AsRef`], [`AsMut`] to specified expression.
///
/// # Syntax
///
/// ```text
/// #[ndfwd::std(<expr> with <type>)]
/// struct Any(<type>);
/// ```
///
/// # Examples
///
/// ```rust
/// #[ndfwd::std(self.0 with i64)]
/// struct Num(i64);
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro_attribute]
pub fn std(attr: TokenStreamStd, ty: TokenStreamStd) -> TokenStreamStd {
    let ty = parse_macro_input!(ty as FwdType);
    let attr = parse_macro_input!(attr as FwdAttr);

    let forwards = ty.fwds(&attr);

    let impls = [FwdStd::Ref, FwdStd::Mut];
    let impls = impls.into_iter().map(|std| ty.std(&attr, &forwards, std));

    quote! {
        #ty

        #(#impls)*
    }
    .into()
}

/// Zero-boilerplate comparison traits forwarding for **struct**, **enum** and **union**.
///
/// Forwards [`PartialEq`], [`Eq`], [`PartialOrd`], [`Ord`] to specified expression.
///
/// # Syntax
///
/// ```text
/// #[ndfwd::cmp(<expr> with <type>)]
/// struct Any(<type>);
/// ```
///
/// # Examples
///
/// ```rust
/// #[ndfwd::cmp(self.0 with i64)]
/// struct Num(i64);
///
/// assert_eq!(Num(1337).eq(&Num(1338)), 1337.eq(&1338));
/// assert_eq!(Num(1337).cmp(&Num(1338)), 1337.cmp(&1338));
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro_attribute]
pub fn cmp(attr: TokenStreamStd, ty: TokenStreamStd) -> TokenStreamStd {
    let ty = parse_macro_input!(ty as FwdType);
    let attr = parse_macro_input!(attr as FwdAttr);

    let forwards = ty.fwds(&attr);

    let impls = [FwdCmp::Eq, FwdCmp::EqPartial, FwdCmp::Ord, FwdCmp::OrdPartial];
    let impls = impls.into_iter().map(|cmp| ty.cmp(&attr, &forwards, cmp));

    quote! {
        #ty

        #(#impls)*
    }
    .into()
}

/// Zero-boilerplate formatting traits forwarding for **struct**, **enum** and **union**.
///
/// Forwards [`Display`](std::fmt::Display), [`Binary`](std::fmt::Binary), [`Octal`](std::fmt::Octal),
/// [`LowerHex`](std::fmt::LowerHex), [`UpperHex`](std::fmt::UpperHex) to specified expression.
///
/// # Syntax
///
/// ```text
/// #[ndfwd::fmt(<expr> with <type>)]
/// struct Any(<type>);
/// ```
///
/// # Examples
///
/// ```rust
/// #[ndfwd::fmt(self.0 with i64)]
/// struct Num(i64);
///
/// assert_eq!(format!("{:}", Num(1337)), format!("{:}", 1337));
/// assert_eq!(format!("{:b}", Num(1337)), format!("{:b}", 1337));
/// assert_eq!(format!("{:o}", Num(1337)), format!("{:o}", 1337));
/// assert_eq!(format!("{:x}", Num(1337)), format!("{:x}", 1337));
/// assert_eq!(format!("{:X}", Num(1337)), format!("{:X}", 1337));
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro_attribute]
pub fn fmt(attr: TokenStreamStd, ty: TokenStreamStd) -> TokenStreamStd {
    let ty = parse_macro_input!(ty as FwdType);
    let attr = parse_macro_input!(attr as FwdAttr);

    let forwards = ty.fwds(&attr);

    let impls = [
        FwdFmt::Display,
        FwdFmt::Binary,
        FwdFmt::Octal,
        FwdFmt::HexLower,
        FwdFmt::HexUpper,
    ];

    let impls = impls.into_iter().map(|fmt| ty.fmt(&attr, &forwards, fmt));

    quote! {
        #ty

        #(#impls)*
    }
    .into()
}

/// Zero-boilerplate iterators traits forwarding for **struct**, **enum** and **union**.
///
/// Forwards [`FromIterator`] and [`IntoIterator`] (by value, by immutable reference, by mutable reference) to specified expression.
///
/// Requires [`From`] for [`FromIterator`].
///
/// # Syntax
///
/// ```text
/// #[ndfwd::iter(<expr> with <type>)]
/// struct Any(<type>);
/// ```
///
/// # Examples
///
/// ```rust
/// #[ndfwd::iter(self.0 with [u64; 3])]
/// struct Vec3([u64; 3]);
///
/// // Required for FromIterator
/// impl From<[u64; 3]> for Vec3 {
///     fn from(value: [u64; 3]) -> Vec3 {
///         Self(value)
///     }
/// }
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro_attribute]
pub fn iter(attr: TokenStreamStd, ty: TokenStreamStd) -> TokenStreamStd {
    let ty = parse_macro_input!(ty as FwdType);
    let attr = parse_macro_input!(attr as FwdAttr);

    let forwards = ty.fwds(&attr);

    let impls = [FwdIter::From, FwdIter::Into, FwdIter::IntoRef, FwdIter::IntoMut];
    let impls = impls.into_iter().map(|iter| ty.iter(&attr, &forwards, iter));

    quote! {
        #ty

        #(#impls)*
    }
    .into()
}

/// Zero-boilerplate user traits forwarding declaration.
///
/// Declares forwardable trait.
///
/// # Related
///
/// - [`def`]
/// - [`as_into`]
/// - [`as_self`]
/// - [`as_expr`]
/// - [`as_map`]
#[proc_macro_attribute]
pub fn decl(_: TokenStreamStd, decl: TokenStreamStd) -> TokenStreamStd {
    let FwdDecl::Trait(decl) = parse_macro_input!(decl as FwdDecl);

    let ident = &decl.ident;
    let macros = format_ident!("__NdFwd{}", ident);

    let supertraits = decl.supertraits.iter();
    let gen_params = decl.generics.params.iter();
    let (_, gen_type, gen_where) = decl.generics.split_for_impl();

    let gen_params = quote! { #(#gen_params,)* };

    let gen_where = match gen_where.map(|val| val.predicates.iter()) {
        Some(val) => quote! { where Self: #(#supertraits)+*, #(#val,)* },
        None => quote! { where Self: #(#supertraits)+*, },
    };

    let forwards = decl
        .items
        .iter()
        .filter_map(|item| match item {
            TraitItem::Type(val) => Some(Ok((false, get_forward_type(&decl, val)))),
            TraitItem::Const(val) => Some(Ok((false, get_forward_const(&decl, val)))),
            TraitItem::Fn(val) => Some(get_forward_fn(&decl, val)),
            _ => None,
        })
        .collect::<Result<Vec<(bool, TokenStream)>>>();

    let forwards = match forwards {
        Ok(val) => val,
        Err(err) => return err.into_compile_error().into(),
    };

    let all = forwards.iter().map(|(_, stream)| stream);
    let defaults = forwards.iter().filter(|(flag, _)| !flag).map(|(_, stream)| stream);

    quote! {
        #decl

        #[doc(hidden)]
        #[allow(unused_macros)]
        macro_rules! #macros {
            ($self:ty, $ty:ty, ($($gen_params:tt)*), ($($gen_where:tt)*)) => {
                impl <#gen_params $($gen_params)*> #ident #gen_type for $self #gen_where $($gen_where)* {
                    #(#all)*
                }
            };

            (! $self:ty, $ty:ty, ($($gen_params:tt)*), ($($gen_where:tt)*)) => {
                impl <#gen_params $($gen_params)*> #ident #gen_type for $self #gen_where $($gen_where)* {
                    #(#defaults)*
                }
            };
        }

        #[allow(unused_imports)]
        pub(crate) use #macros;
    }
    .into()
}

/// Zero-boilerplate user traits forwarding definition.
///
/// Defines forwardable trait.
///
/// # Syntax
///
/// ```text
/// #[ndfwd::def(<expr> with <type>: <trait> <conditions>?)]
/// struct Any(<type>);
///
/// <trait> := <path> | <path>!
/// <conditions> := where [<predicate>,*]
/// ```
///
/// Trait in `<trait>` allows optional `!` for specifying source implementation.
///
/// - Without `!` - forwarded to type implementation.
/// - With `!` (when trait fn has no default implementation) - forwarded to type implementation.
/// - With `!` (when trait fn has default implementation) - forwarded to default implementation.
///
/// # Examples
///
/// ```rust,ignore
/// #[ndfwd::decl]
/// trait Trait {
///     fn function() -> usize;
/// }
///
/// #[ndfwd::def(self.0 with Inner: Trait)]
/// struct Outer(Inner);
/// struct Inner;
///
/// impl Trait for Inner {
///     fn function() -> usize {
///         1337
///     }
/// }
/// ```
///
/// # Related
///
/// - [`decl`]
/// - [`as_into`]
/// - [`as_self`]
/// - [`as_expr`]
/// - [`as_map`]
#[proc_macro_attribute]
pub fn def(attr: TokenStreamStd, def: TokenStreamStd) -> TokenStreamStd {
    let def = parse_macro_input!(def as FwdDef);
    let attr = parse_macro_input!(attr as FwdDefAttr);

    let (ident, self_ty, generics) = match def.args() {
        Ok(val) => val,
        Err(err) => return err.into_compile_error().into(),
    };

    let forwards = match def.fwds(&attr.fwd) {
        Ok(val) => val,
        Err(err) => return err.into_compile_error().into(),
    };

    let ty = &attr.fwd.ty;
    let path = &attr.path;
    let defaults = &attr.defaults;

    let sig_predicates = generics.where_clause.as_ref().map(|val| val.predicates.iter());
    let attr_predicates = attr.conditions.as_ref().map(|val| val.predicates.iter());

    let gen_params = &generics.params;
    let gen_where = match (sig_predicates, attr_predicates) {
        (Some(sig), Some(attr)) => quote! { #ty: #path, #(#sig,)* #(#attr,)* },
        (Some(sig), None) => quote! { #ty: #path, #(#sig,)* },
        (None, Some(attr)) => quote! { #ty: #path, #(#attr,)* },
        (None, None) => quote! { #ty: #path, },
    };

    let segs = path.segments.iter().take(path.segments.len().saturating_sub(1));
    let id = match path.segments.last() {
        Some(val) => &val.ident,
        None => {
            return Error::new_spanned(&path.segments, "Failed to forward definition, path is empty")
                .into_compile_error()
                .into();
        },
    };

    let module = format_ident!("__NdFwd{}Impl{}", &id, &ident);
    let macros = format_ident!("__NdFwd{}", &id);

    quote! {
        #def

        #[doc(hidden)]
        #[allow(non_snake_case)]
        mod #module {
            #forwards

            #(#segs::)*#macros!(#defaults #self_ty, #ty, (#gen_params), (#gen_where));

            use super::*;

            #[allow(unused_imports)]
            use #path;
        }
    }
    .into()
}

/// Alters expression for [`decl`].
///
/// The resulting forwarding expression: `<expr>.into()`.
///
/// # Example
///
/// ```rust
/// #[ndfwd::decl]
/// trait Trait {
///     #[ndfwd::as_into]
///     fn function() -> Self;
/// }
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro_attribute]
pub fn as_into(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    item
}

/// Alters expression for [`decl`].
///
/// The resulting forwarding expression: `<expr>; self`.
///
/// # Example
///
/// ```rust
/// #[ndfwd::decl]
/// trait Trait {
///     #[ndfwd::as_self]
///     fn function(&mut self) -> &mut Self;
/// }
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro_attribute]
pub fn as_self(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    item
}

/// Alters expression for [`decl`].
///
/// The resulting forwarding expression: `(<closure>)(<expr>)`.
///
/// # Example
///
/// ```rust
/// #[ndfwd::decl]
/// trait Trait: Sized {
///     #[ndfwd::as_expr(|(a, b)| (Self::from(a), Self::from(b)))]
///     fn function() -> (Self, Self);
/// }
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro_attribute]
pub fn as_expr(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    item
}

/// Alters expression for [`decl`].
///
/// The resulting forwarding expression: `<expr>.map(<closure>)`.
///
/// # Example
///
/// ```rust
/// #[ndfwd::decl]
/// trait Trait: Sized {
///     #[ndfwd::as_map(Self::from)]
///     fn function() -> Option<Self>;
/// }
/// ```
///
/// For more info, see [crate-level](crate) documentation.
#[proc_macro_attribute]
pub fn as_map(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    item
}

enum FwdStd {
    Ref,
    Mut,
}

enum FwdCmp {
    Eq,
    EqPartial,
    Ord,
    OrdPartial,
}

enum FwdFmt {
    Display,
    Binary,
    Octal,
    HexLower,
    HexUpper,
}

enum FwdIter {
    From,
    Into,
    IntoRef,
    IntoMut,
}

struct Fwds(TokenStream);

#[allow(unused)]
struct FwdAttr {
    expr: Expr,
    with: kw::with,
    ty: Type,
}

enum FwdType {
    Struct(ItemStruct),
    Enum(ItemEnum),
    Union(ItemUnion),
}

enum FwdDecl {
    Trait(ItemTrait),
}

enum FwdDeclAttr {
    Default,
    AsInto,
    AsSelf,
    AsExpr(Expr),
    AsMap(Expr),
}

struct FwdDeclTypes;
struct FwdDeclConsts;
struct FwdDeclFuncs;

#[derive(Debug, Clone, Copy)]
enum FwdDeclArgKind {
    Raw,
    Ref,
    Mut,
}

struct FwdDeclArg<'ty> {
    expr: TokenStream,
    ty: &'ty Type,
    kind: FwdDeclArgKind,
}

enum FwdDeclArgExpr {
    Raw(TokenStream),
    Alt(TokenStream),
}

enum FwdDef {
    Struct(ItemStruct),
    Enum(ItemEnum),
    Union(ItemUnion),
    Impl(ItemImpl),
}

#[allow(unused)]
struct FwdDefAttr {
    fwd: FwdAttr,
    colon: Token![:],
    path: Path,
    defaults: Option<Token![!]>,
    conditions: Option<WhereClause>,
}

#[derive(Debug, Clone)]
enum FwdExpr {
    Raw(TokenStream),
    Ref(TokenStream),
    Mut(TokenStream),
}

#[derive(Debug, Clone)]
enum FwdArg {
    Raw(TokenStream),
    Alt(TokenStream),
}

impl Parse for FwdAttr {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            expr: input.parse()?,
            with: input.parse()?,
            ty: input.parse()?,
        })
    }
}

impl Parse for FwdType {
    fn parse(input: ParseStream) -> Result<Self> {
        let item = input.parse::<Item>()?;

        match item {
            Item::Struct(val) => Ok(Self::Struct(val)),
            Item::Enum(val) => Ok(Self::Enum(val)),
            Item::Union(val) => Ok(Self::Union(val)),
            _ => Err(input.error("Failed to find correct item, expected struct, enum or union")),
        }
    }
}

impl Parse for FwdDecl {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self::Trait(input.parse::<ItemTrait>()?))
    }
}

impl Parse for FwdDef {
    fn parse(input: ParseStream) -> Result<Self> {
        let item = input.parse::<Item>()?;

        match item {
            Item::Struct(val) => Ok(Self::Struct(val)),
            Item::Enum(val) => Ok(Self::Enum(val)),
            Item::Union(val) => Ok(Self::Union(val)),
            Item::Impl(val) => match &val.trait_ {
                Some((not, path, _)) => match not {
                    Some(val) => Err(Error::new_spanned(
                        val,
                        "Failed to find correct NdForward impl marker: ! is not allowed",
                    )),
                    None => match path.segments.last().is_some_and(|seg| seg.ident == "NdForward") {
                        true => Ok(Self::Impl(val)),
                        false => Err(Error::new_spanned(
                            path,
                            "Failed to find correct NdForward impl marker: ident is expected to be NdForward",
                        )),
                    },
                },
                None => Err(Error::new_spanned(val, "Failed to find correct NdForward impl marker")),
            },
            _ => Err(Error::new_spanned(
                item,
                "Failed to find correct item, expected struct, enum, union or impl",
            )),
        }
    }
}

impl Parse for FwdDefAttr {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            fwd: input.parse()?,
            colon: input.parse()?,
            path: input.parse()?,
            defaults: input.parse()?,
            conditions: input.parse()?,
        })
    }
}

impl ToTokens for Fwds {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.0.to_tokens(tokens);
    }
}

impl ToTokens for FwdType {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            FwdType::Struct(val) => val.to_tokens(tokens),
            FwdType::Enum(val) => val.to_tokens(tokens),
            FwdType::Union(val) => val.to_tokens(tokens),
        }
    }
}

impl ToTokens for FwdDef {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            FwdDef::Struct(val) => val.to_tokens(tokens),
            FwdDef::Enum(val) => val.to_tokens(tokens),
            FwdDef::Union(val) => val.to_tokens(tokens),
            FwdDef::Impl(val) => val.to_tokens(tokens),
        }
    }
}

impl ToTokens for FwdDeclArgExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            FwdDeclArgExpr::Raw(val) => val.to_tokens(tokens),
            FwdDeclArgExpr::Alt(val) => val.to_tokens(tokens),
        }
    }
}

impl ToTokens for FwdExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            FwdExpr::Raw(val) => val.to_tokens(tokens),
            FwdExpr::Ref(val) => val.to_tokens(tokens),
            FwdExpr::Mut(val) => val.to_tokens(tokens),
        }
    }
}

impl Fwds {
    fn from_raw(self_ty: TokenStream, generics: &Generics, attr: &FwdAttr) -> Self {
        let (expr, ty) = attr.args();
        let (gen_impl, _, gen_where) = generics.split_for_impl();

        Fwds(quote! {
            trait Forward {
                type Type;

                fn forward(self) -> Self::Type;

                fn forward_ref(&self) -> &Self::Type;

                fn forward_mut(&mut self) -> &mut Self::Type;
            }

            impl #gen_impl Forward for #self_ty #gen_where {
                type Type = #ty;

                #[inline]
                fn forward(self) -> Self::Type {
                    #expr
                }

                #[inline]
                fn forward_ref(&self) -> &Self::Type {
                    &#expr
                }

                #[inline]
                fn forward_mut(&mut self) -> &mut Self::Type {
                    &mut #expr
                }
            }
        })
    }
}

impl FwdAttr {
    fn args(&self) -> (&Expr, &Type) {
        (&self.expr, &self.ty)
    }
}

impl FwdType {
    fn args(&self) -> (&Ident, &Generics) {
        match self {
            FwdType::Struct(ItemStruct { ident, generics, .. }) => (ident, generics),
            FwdType::Enum(ItemEnum { ident, generics, .. }) => (ident, generics),
            FwdType::Union(ItemUnion { ident, generics, .. }) => (ident, generics),
        }
    }

    fn fwds(&self, attr: &FwdAttr) -> Fwds {
        let (ident, generics) = self.args();
        let (_, gen_type, _) = generics.split_for_impl();

        Fwds::from_raw(quote! { #ident #gen_type }, generics, attr)
    }

    fn std(&self, attr: &FwdAttr, _: &Fwds, std: FwdStd) -> TokenStream {
        let (ident, generics) = self.args();
        let (expr, ty) = attr.args();

        let gen_params = generics.params.iter();
        let (_, gen_type, gen_where) = generics.split_for_impl();

        match std {
            FwdStd::Ref => {
                let conditions = match gen_where.map(|val| val.predicates.iter()) {
                    Some(val) => quote! { where #(#val,)* #ty: std::convert::AsRef<AsRefRet> },
                    None => quote! { where #ty: std::convert::AsRef<AsRefRet> },
                };

                quote! {
                    impl<#(#gen_params,)* AsRefRet> std::convert::AsRef<AsRefRet> for #ident #gen_type #conditions {
                        #[inline]
                        fn as_ref(&self) -> &AsRefRet {
                            #expr.as_ref()
                        }
                    }
                }
            },
            FwdStd::Mut => {
                let conditions = match gen_where.map(|val| val.predicates.iter()) {
                    Some(val) => quote! { where #(#val,)* #ty: std::convert::AsMut<AsMutRet> },
                    None => quote! { where #ty: std::convert::AsMut<AsMutRet> },
                };

                quote! {
                    impl<#(#gen_params,)* AsMutRet> std::convert::AsMut<AsMutRet> for #ident #gen_type #conditions {
                        #[inline]
                        fn as_mut(&mut self) -> &mut AsMutRet {
                            #expr.as_mut()
                        }
                    }
                }
            },
        }
    }

    fn cmp(&self, attr: &FwdAttr, fwds: &Fwds, cmp: FwdCmp) -> TokenStream {
        let (ident, generics) = self.args();
        let (_, ty) = attr.args();

        let (gen_impl, gen_type, gen_where) = generics.split_for_impl();

        match cmp {
            FwdCmp::Eq => {
                let conditions = match gen_where.map(|val| val.predicates.iter()) {
                    Some(val) => quote! { where #(#val,)* #ty: std::cmp::Eq },
                    None => quote! { where #ty: std::cmp::Eq },
                };

                quote! {
                    impl #gen_impl std::cmp::Eq for #ident #gen_type #conditions {}
                }
            },
            FwdCmp::EqPartial => {
                let conditions = match gen_where.map(|val| val.predicates.iter()) {
                    Some(val) => quote! { where #(#val,)* #ty: std::cmp::PartialEq },
                    None => quote! { where #ty: std::cmp::PartialEq },
                };

                quote! {
                    impl #gen_impl std::cmp::PartialEq for #ident #gen_type #conditions {
                        #[inline]
                        fn eq(&self, other: &Self) -> bool {
                            #fwds

                            self.forward_ref().eq(other.forward_ref())
                        }
                    }
                }
            },
            FwdCmp::Ord => {
                let conditions = match gen_where.map(|val| val.predicates.iter()) {
                    Some(val) => quote! { where #(#val,)* #ty: std::cmp::Ord },
                    None => quote! { where #ty: std::cmp::Ord },
                };

                quote! {
                    impl #gen_impl std::cmp::Ord for #ident #gen_type #conditions {
                        #[inline]
                        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                            #fwds

                            self.forward_ref().cmp(other.forward_ref())
                        }
                    }
                }
            },
            FwdCmp::OrdPartial => {
                let conditions = match gen_where.map(|val| val.predicates.iter()) {
                    Some(val) => quote! { where #(#val,)* #ty: std::cmp::PartialOrd },
                    None => quote! { where #ty: std::cmp::PartialOrd },
                };

                quote! {
                    impl #gen_impl std::cmp::PartialOrd for #ident #gen_type #conditions {
                        #[inline]
                        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                            #fwds

                            self.forward_ref().partial_cmp(other.forward_ref())
                        }
                    }
                }
            },
        }
    }

    fn fmt(&self, attr: &FwdAttr, _: &Fwds, fmt: FwdFmt) -> TokenStream {
        let (ident, generics) = self.args();
        let (expr, ty) = attr.args();

        let (gen_impl, gen_type, gen_where) = generics.split_for_impl();

        let display = match fmt {
            FwdFmt::Display => quote! { std::fmt::Display },
            FwdFmt::Binary => quote! { std::fmt::Binary },
            FwdFmt::Octal => quote! { std::fmt::Octal },
            FwdFmt::HexLower => quote! { std::fmt::LowerHex },
            FwdFmt::HexUpper => quote! { std::fmt::UpperHex },
        };

        let conditions = match gen_where.map(|val| val.predicates.iter()) {
            Some(val) => quote! { where #(#val,)* #ty: #display },
            None => quote! { where #ty: #display },
        };

        quote! {
            impl #gen_impl #display for #ident #gen_type #conditions {
                #[inline]
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    #expr.fmt(f)
                }
            }
        }
    }

    fn iter(&self, attr: &FwdAttr, _: &Fwds, iter: FwdIter) -> TokenStream {
        let (ident, generics) = self.args();
        let (expr, ty) = attr.args();

        let gen_params = generics.params.iter();
        let (_, gen_type, gen_where) = generics.split_for_impl();

        match iter {
            FwdIter::From => {
                let conditions = match gen_where.map(|val| val.predicates.iter()) {
                    Some(val) => quote! { where Self: From<#ty>, #(#val,)* #ty: std::iter::FromIterator<Elem> },
                    None => quote! { where Self: From<#ty>, #ty: std::iter::FromIterator<Elem> },
                };

                quote! {
                    impl<#(#gen_params,)* Elem> std::iter::FromIterator<Elem> for #ident #gen_type #conditions {
                        #[inline]
                        fn from_iter<Iter: IntoIterator<Item = Elem>>(iter: Iter) -> Self {
                            <#ty>::from_iter(iter).into()
                        }
                    }
                }
            },
            FwdIter::Into => {
                let conditions = match gen_where.map(|val| val.predicates.iter()) {
                    Some(val) => quote! { where #(#val,)* #ty: std::iter::IntoIterator },
                    None => quote! { where #ty: std::iter::IntoIterator },
                };

                quote! {
                    impl<#(#gen_params,)*> std::iter::IntoIterator for #ident #gen_type #conditions {
                        type Item = <#ty as std::iter::IntoIterator>::Item;
                        type IntoIter = <#ty as std::iter::IntoIterator>::IntoIter;

                        #[inline]
                        fn into_iter(self) -> Self::IntoIter {
                            #expr.into_iter()
                        }
                    }
                }
            },
            FwdIter::IntoRef => {
                let conditions = match gen_where.map(|val| val.predicates.iter()) {
                    Some(val) => quote! { where #(#val,)* &'reference #ty: std::iter::IntoIterator },
                    None => quote! { where &'reference #ty: std::iter::IntoIterator },
                };

                quote! {
                    impl<'reference, #(#gen_params,)*> std::iter::IntoIterator for &'reference #ident #gen_type #conditions {
                        type Item = <&'reference #ty as std::iter::IntoIterator>::Item;
                        type IntoIter = <&'reference #ty as std::iter::IntoIterator>::IntoIter;

                        #[inline]
                        fn into_iter(self) -> Self::IntoIter {
                            (&#expr).into_iter()
                        }
                    }
                }
            },
            FwdIter::IntoMut => {
                let conditions = match gen_where.map(|val| val.predicates.iter()) {
                    Some(val) => quote! { where #(#val,)* &'reference mut #ty: std::iter::IntoIterator },
                    None => quote! { where &'reference mut #ty: std::iter::IntoIterator },
                };

                quote! {
                    impl<'reference, #(#gen_params,)*> std::iter::IntoIterator for &'reference mut #ident #gen_type #conditions {
                        type Item = <&'reference mut #ty as std::iter::IntoIterator>::Item;
                        type IntoIter = <&'reference mut #ty as std::iter::IntoIterator>::IntoIter;

                        #[inline]
                        fn into_iter(self) -> Self::IntoIter {
                            (&mut #expr).into_iter()
                        }
                    }
                }
            },
        }
    }
}

impl FwdDeclAttr {
    fn from_attrs<'attr, Attrs: Clone + Iterator<Item = &'attr Attribute>>(attrs: Attrs) -> Result<Self> {
        fn expr(attr: &Attribute) -> Result<Expr> {
            match &attr.meta {
                Meta::List(val) => syn::parse2::<Expr>(val.tokens.clone()),
                Meta::Path(val) => Err(Error::new_spanned(val, "Failed to forward as expression, expected expression")),
                Meta::NameValue(val) => {
                    Err(Error::new_spanned(val, "Failed to forward as expression, expected expression"))
                },
            }
        }

        fn check(attr: &Attribute, path: &[&str]) -> bool {
            let segments = &attr.path().segments;

            segments.len() == path.len() && segments.iter().map(|seg| &seg.ident).zip(path).all(|(lhs, rhs)| lhs == rhs)
        }

        let as_into = ["ndfwd", "as_into"];
        let as_self = ["ndfwd", "as_self"];
        let as_expr = ["ndfwd", "as_expr"];
        let as_map = ["ndfwd", "as_map"];

        if attrs.clone().find(|attr| check(attr, &as_into)).is_some() {
            Ok(Self::AsInto)
        } else if attrs.clone().find(|attr| check(attr, &as_self)).is_some() {
            Ok(Self::AsSelf)
        } else if let Some(attr) = attrs.clone().find(|attr| check(attr, &as_expr)) {
            Ok(Self::AsExpr(expr(attr)?))
        } else if let Some(attr) = attrs.clone().find(|attr| check(attr, &as_map)) {
            Ok(Self::AsMap(expr(attr)?))
        } else {
            Ok(Self::Default)
        }
    }
}

impl FwdDeclTypes {
    fn from_decl(decl: &FwdDecl) -> impl Iterator<Item = TokenStream> {
        let FwdDecl::Trait(decl) = decl;

        decl.items.iter().filter_map(|item| match item {
            TraitItem::Type(val) => Some({
                let attrs = &val.attrs;
                let ident = &val.ident;

                let (gen_impl, gen_type, _) = val.generics.split_for_impl();

                let id = &decl.ident;
                let (_, gen_type_id, _) = decl.generics.split_for_impl();

                quote! {
                    #(#attrs)*
                    type #ident #gen_impl = <$ty as #id #gen_type_id>::#ident #gen_type;
                }
            }),
            _ => None,
        })
    }
}

impl FwdDeclConsts {
    fn from_decl(decl: &FwdDecl) -> impl Iterator<Item = TokenStream> {
        let FwdDecl::Trait(decl) = decl;

        decl.items.iter().filter_map(|item| match item {
            TraitItem::Const(val) => Some({
                let attrs = &val.attrs;
                let ident = &val.ident;
                let ty = &val.ty;

                let id = &decl.ident;
                let (_, gen_type_id, _) = decl.generics.split_for_impl();

                quote! {
                    #(#attrs)*
                    const #ident: #ty = <$ty as #id #gen_type_id>::#ident;
                }
            }),
            _ => None,
        })
    }
}

impl FwdDeclFuncs {
    fn from_decl(decl: &FwdDecl) -> Result<(Vec<TokenStream>, Vec<TokenStream>)> {
        fn forward(item: &TraitItemFn) -> Result<TokenStream> {
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

            let inputs = inputs
                .iter()
                .filter_map(|arg| match arg {
                    FnArg::Receiver(_) => None,
                    FnArg::Typed(val) => Some(val),
                })
                .enumerate();

            let args = inputs.clone().map(|(idx, val)| {
                let ident = format_ident!("arg{}", idx);

                let attrs = &val.attrs;
                let ty = &val.ty;

                quote! { #(#attrs)* #ident: #ty }
            });

            let args_expr = inputs
                .clone()
                .map(|(idx, val)| {
                    let ident = format_ident!("arg{}", idx);

                    FwdDeclArgExpr::from_arg(FwdDeclArg {
                        expr: quote! { #ident },
                        ty: &val.ty,
                        kind: FwdDeclArgKind::Raw,
                    })
                })
                .collect::<Result<Vec<FwdDeclArgExpr>>>()?;

            let forward = match recv {
                Some(val) => match (val.reference.is_some(), val.mutability.is_some()) {
                    (true, true) => quote! { self.forward_mut().#ident(#(#args_expr),*) },
                    (true, false) => quote! { self.forward_ref().#ident(#(#args_expr),*) },
                    _ => quote! { self.forward().#ident(#(#args_expr),*) },
                },
                None => quote! { <$ty>::#ident(#(#args_expr),*) },
            };

            let expr = match FwdDeclAttr::from_attrs(attrs.iter())? {
                FwdDeclAttr::Default => quote! { #forward },
                FwdDeclAttr::AsInto => quote! { #forward.into() },
                FwdDeclAttr::AsSelf => quote! { #forward; self },
                FwdDeclAttr::AsExpr(expr) => quote! { (#expr)(#forward) },
                FwdDeclAttr::AsMap(expr) => quote! { #forward.map(#expr) },
            };

            let attr_inline: Path = parse_quote! { inline };
            let attrs = attrs.iter().filter(|attr| attr.path() != &attr_inline);

            let recv = match recv {
                Some(val) => quote! { #val, },
                None => quote! {},
            };

            Ok(quote! {
                #[allow(unused_mut)]
                #[inline]
                #(#attrs)*
                #constness #asyncness #unsafety #abi fn #ident #generics (#recv #(#args),*) #output {
                    #expr
                }
            })
        }

        let FwdDecl::Trait(decl) = decl;

        let forwards = decl
            .items
            .iter()
            .filter_map(|item| match item {
                TraitItem::Fn(val) => Some(forward(val).map(|res| (res, val.default.is_some()))),
                _ => None,
            })
            .collect::<Result<Vec<(TokenStream, bool)>>>()?;

        Ok((
            forwards.iter().cloned().map(|(stream, _)| stream).collect(),
            forwards
                .iter()
                .filter(|(_, default)| !default)
                .cloned()
                .map(|(stream, _)| stream)
                .collect(),
        ))
    }
}

impl FwdDeclArgExpr {
    fn from_arg(arg: FwdDeclArg) -> Result<Self> {
        let FwdDeclArg { expr, ty, kind } = arg;

        match ty {
            Type::Path(val) => {
                if val.path.segments.last().is_some_and(|seg| seg.ident == "Self") {
                    return Ok(match kind {
                        FwdDeclArgKind::Raw => Self::Alt(quote! { #expr.forward() }),
                        FwdDeclArgKind::Ref => Self::Alt(quote! { #expr.forward_ref() }),
                        FwdDeclArgKind::Mut => Self::Alt(quote! { #expr.forward_mut() }),
                    });
                }

                if val.path.segments.first().is_some_and(|seg| seg.ident == "Self") {
                    return Ok(Self::Alt(quote! { #expr.into() }));
                }

                Ok(Self::Raw(expr))
            },
            Type::Array(val) => match Self::from_arg(FwdDeclArg { expr, ty: &val.elem, kind })? {
                Self::Raw(val) => Ok(Self::Raw(val)),
                Self::Alt(val) => Err(Error::new_spanned(
                    val,
                    "Failed to forward argument, alternating in array is unsupported",
                )),
            },
            Type::Slice(val) => match Self::from_arg(FwdDeclArg { expr, ty: &val.elem, kind })? {
                Self::Raw(val) => Ok(Self::Raw(val)),
                Self::Alt(val) => Err(Error::new_spanned(
                    val,
                    "Failed to forward argument, alternating in slice is unsupported",
                )),
            },
            Type::Tuple(val) => {
                let args = val
                    .elems
                    .iter()
                    .enumerate()
                    .map(|(idx, elem)| FwdDeclArg {
                        expr: quote! { #expr.#idx },
                        ty: elem,
                        kind,
                    })
                    .map(Self::from_arg)
                    .collect::<Result<Vec<Self>>>()?;

                if args.iter().all(|arg| match arg {
                    Self::Raw(_) => true,
                    Self::Alt(_) => false,
                }) {
                    return Ok(Self::Raw(expr));
                }

                let args = args.iter().map(|arg| match arg {
                    Self::Raw(val) => quote! { #val },
                    Self::Alt(val) => quote! { #val },
                });

                Ok(Self::Alt(quote! { #(#args),* }))
            },
            Type::Group(val) => Self::from_arg(FwdDeclArg { expr, ty: &val.elem, kind }),
            Type::Paren(val) => Self::from_arg(FwdDeclArg { expr, ty: &val.elem, kind }),
            Type::Ptr(val) => Self::from_arg(match val.mutability {
                Some(_) => FwdDeclArg {
                    expr,
                    ty: &val.elem,
                    kind: FwdDeclArgKind::Mut,
                },
                None => FwdDeclArg {
                    expr,
                    ty: &val.elem,
                    kind: FwdDeclArgKind::Ref,
                },
            }),
            Type::Reference(val) => Self::from_arg(match val.mutability {
                Some(_) => FwdDeclArg {
                    expr,
                    ty: &val.elem,
                    kind: FwdDeclArgKind::Mut,
                },
                None => FwdDeclArg {
                    expr,
                    ty: &val.elem,
                    kind: FwdDeclArgKind::Ref,
                },
            }),
            Type::Never(val) => Err(Error::new_spanned(val, "Failed to forward argument, never type is unsupported")),
            Type::Macro(val) => Err(Error::new_spanned(val, "Failed to forward argument, macro type is unsupported")),
            Type::BareFn(_) => Ok(Self::Raw(expr)),
            Type::ImplTrait(_) => Ok(Self::Raw(expr)),
            Type::TraitObject(_) => Ok(Self::Raw(expr)),
            Type::Verbatim(val) => Err(Error::new_spanned(val, "Failed to forward argument, verbatim was found")),
            ty => Err(Error::new_spanned(ty, "Failed to forward argument, unknown type was found")),
        }
    }
}

impl FwdDef {
    fn args(&self) -> Result<(Ident, TokenStream, &Generics)> {
        fn ty(ident: &Ident, generics: &Generics) -> TokenStream {
            let (_, gen_type, _) = generics.split_for_impl();

            quote! { #ident #gen_type }
        }

        match self {
            FwdDef::Struct(ItemStruct { ident, generics, .. }) => Ok((ident.clone(), ty(ident, generics), generics)),
            FwdDef::Enum(ItemEnum { ident, generics, .. }) => Ok((ident.clone(), ty(ident, generics), generics)),
            FwdDef::Union(ItemUnion { ident, generics, .. }) => Ok((ident.clone(), ty(ident, generics), generics)),
            FwdDef::Impl(ItemImpl { self_ty, generics, .. }) => match self_ty.as_ref() {
                Type::Path(val) => Ok((
                    format_ident!(
                        "{}",
                        val.path
                            .segments
                            .iter()
                            .fold(String::new(), |acc, seg| format!("{}{}", &acc, seg.ident))
                    ),
                    quote! { #val },
                    generics,
                )),
                ty => Err(Error::new_spanned(
                    ty,
                    "Failed to forward definition, expected path for impl type",
                )),
            },
        }
    }

    fn fwds(&self, attr: &FwdAttr) -> Result<Fwds> {
        let (_, ty, generics) = self.args()?;

        Ok(Fwds::from_raw(ty, generics, attr))
    }
}

impl FwdExpr {
    fn stream(self) -> TokenStream {
        match self {
            FwdExpr::Raw(val) => val,
            FwdExpr::Ref(val) => val,
            FwdExpr::Mut(val) => val,
        }
    }
}

impl FwdArg {
    fn stream(self) -> TokenStream {
        match self {
            FwdArg::Raw(val) => val,
            FwdArg::Alt(val) => val,
        }
    }
}

fn get_forward_type(interface: &ItemTrait, item: &TraitItemType) -> TokenStream {
    let attrs = &item.attrs;
    let ident = &item.ident;

    let (gen_impl, gen_type, _) = item.generics.split_for_impl();

    let id = &interface.ident;
    let (_, gen_type_id, _) = interface.generics.split_for_impl();

    quote! {
        #(#attrs)*
        type #ident #gen_impl = <$ty as #id #gen_type_id>::#ident #gen_type;
    }
}

fn get_forward_const(interface: &ItemTrait, item: &TraitItemConst) -> TokenStream {
    let attrs = &item.attrs;
    let ident = &item.ident;
    let ty = &item.ty;

    let id = &interface.ident;
    let (_, gen_type_id, _) = interface.generics.split_for_impl();

    quote! {
        #(#attrs)*
        const #ident: #ty = <$ty as #id #gen_type_id>::#ident;
    }
}

fn get_forward_fn(_: &ItemTrait, item: &TraitItemFn) -> Result<(bool, TokenStream)> {
    let TraitItemFn {
        attrs,
        sig,
        default,
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

    let args = inputs
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

    let args_expr = inputs
        .iter()
        .filter_map(|arg| match arg {
            FnArg::Receiver(_) => None,
            FnArg::Typed(val) => Some(val),
        })
        .enumerate()
        .map(|(idx, val)| {
            let ident = format_ident!("arg{}", idx);

            let arg = get_forward_argument(FwdExpr::Raw(quote! { #ident }), &val.ty);

            Ok(arg?.stream())
        })
        .collect::<Result<Vec<TokenStream>>>()?;

    let as_into_path: Path = parse_quote! { ndfwd::as_into };
    let as_self_path: Path = parse_quote! { ndfwd::as_self };
    let as_expr_path: Path = parse_quote! { ndfwd::as_expr };
    let as_map_path: Path = parse_quote! { ndfwd::as_map };
    let inline_path: Path = parse_quote! { inline };

    let as_into = attrs.iter().any(|attr| *attr.path() == as_into_path);
    let as_self = attrs.iter().any(|attr| *attr.path() == as_self_path);
    let as_expr = attrs.iter().find(|attr| *attr.path() == as_expr_path);
    let as_map = attrs.iter().find(|attr| *attr.path() == as_map_path);
    let attrs = attrs.iter().filter(|attr| *attr.path() != inline_path);

    let expr = match recv {
        Some(val) => {
            let fwd = match (val.reference.is_some(), val.mutability.is_some()) {
                (true, true) => quote! { self.forward_mut().#ident(#(#args_expr),*) },
                (true, false) => quote! { self.forward_ref().#ident(#(#args_expr),*) },
                _ => quote! { self.forward().#ident(#(#args_expr),*) },
            };

            if as_into {
                quote! {
                    #fwd.into()
                }
            } else if as_self {
                quote! {
                    #fwd;

                    self
                }
            } else if let Some(as_expr) = as_expr {
                let expr = get_forward_expr(&as_expr.meta)?;

                quote! {
                    (#expr)(#fwd)
                }
            } else if let Some(as_map) = as_map {
                let expr = get_forward_expr(&as_map.meta)?;

                quote! {
                    #fwd.map(#expr)
                }
            } else {
                quote! {
                    #fwd
                }
            }
        },
        None => {
            if as_into {
                quote! {
                    <$ty>::#ident(#(#args_expr),*).into()
                }
            } else if let Some(as_expr) = as_expr {
                let expr = get_forward_expr(&as_expr.meta)?;

                quote! {
                    (#expr)(<$ty>::#ident(#(#args_expr),*))
                }
            } else if let Some(as_map) = as_map {
                let expr = get_forward_expr(&as_map.meta)?;

                quote! {
                    <$ty>::#ident(#(#args_expr),*).map(#expr)
                }
            } else {
                quote! {
                    <$ty>::#ident(#(#args_expr),*)
                }
            }
        },
    };

    let recv = match recv {
        Some(val) => quote! { #val, },
        None => quote! {},
    };

    Ok((
        default.is_some(),
        quote! {
            #[allow(unused_mut)]
            #[inline]
            #(#attrs)*
            #constness #asyncness #unsafety #abi fn #ident #generics (#recv #(#args),*) #output {
                #expr
            }
        },
    ))
}

fn get_forward_expr(meta: &Meta) -> Result<Expr> {
    match meta {
        Meta::List(val) => syn::parse2::<Expr>(val.tokens.clone()),
        Meta::Path(val) => Err(Error::new_spanned(val, "Failed to forward as expression, expected expression")),
        Meta::NameValue(val) => Err(Error::new_spanned(val, "Failed to forward as expression, expected expression")),
    }
}

fn get_forward_argument(expr: FwdExpr, ty: &Type) -> Result<FwdArg> {
    match ty {
        Type::Path(val) => {
            if val.path.segments.last().is_some_and(|seg| seg.ident == "Self") {
                return Ok(match expr {
                    FwdExpr::Raw(val) => FwdArg::Alt(quote! { #val.forward() }),
                    FwdExpr::Ref(val) => FwdArg::Alt(quote! { #val.forward_ref() }),
                    FwdExpr::Mut(val) => FwdArg::Alt(quote! { #val.forward_mut() }),
                });
            }

            if val.path.segments.first().is_some_and(|seg| seg.ident == "Self") {
                return Ok(FwdArg::Alt(quote! { #expr.into() }));
            }

            Ok(FwdArg::Raw(expr.stream()))
        },
        Type::Array(val) => match get_forward_argument(expr, &val.elem)? {
            FwdArg::Raw(val) => Ok(FwdArg::Raw(val)),
            FwdArg::Alt(val) => Err(Error::new_spanned(
                val,
                "Failed to forward argument, alternating in array is unsupported",
            )),
        },
        Type::Slice(val) => match get_forward_argument(expr, &val.elem)? {
            FwdArg::Raw(val) => Ok(FwdArg::Raw(val)),
            FwdArg::Alt(val) => Err(Error::new_spanned(
                val,
                "Failed to forward argument, alternating in slice is unsupported",
            )),
        },
        Type::Tuple(val) => {
            let args = val
                .elems
                .iter()
                .enumerate()
                .map(|(idx, elem)| get_forward_argument(FwdExpr::Raw(quote! { #expr.#idx }), elem))
                .collect::<Result<Vec<FwdArg>>>()?;

            if args.iter().all(|arg| match arg {
                FwdArg::Raw(_) => true,
                FwdArg::Alt(_) => false,
            }) {
                return Ok(FwdArg::Raw(expr.stream()));
            }

            let args = args.iter().map(|arg| match arg {
                FwdArg::Raw(val) => quote! { #val },
                FwdArg::Alt(val) => quote! { #val },
            });

            Ok(FwdArg::Alt(quote! { #(#args),* }))
        },
        Type::Group(val) => get_forward_argument(FwdExpr::Raw(expr.stream()), &val.elem),
        Type::Paren(val) => get_forward_argument(FwdExpr::Raw(expr.stream()), &val.elem),
        Type::Ptr(val) => get_forward_argument(
            match val.mutability {
                Some(_) => FwdExpr::Mut(expr.stream()),
                None => FwdExpr::Ref(expr.stream()),
            },
            &val.elem,
        ),
        Type::Reference(val) => get_forward_argument(
            match val.mutability {
                Some(_) => FwdExpr::Mut(expr.stream()),
                None => FwdExpr::Ref(expr.stream()),
            },
            &val.elem,
        ),
        Type::Never(val) => Err(Error::new_spanned(val, "Failed to forward argument, never type is unsupported")),
        Type::Macro(val) => Err(Error::new_spanned(val, "Failed to forward argument, macro type is unsupported")),
        Type::BareFn(_) => Ok(FwdArg::Raw(expr.stream())),
        Type::ImplTrait(_) => Ok(FwdArg::Raw(expr.stream())),
        Type::TraitObject(_) => Ok(FwdArg::Raw(expr.stream())),
        Type::Verbatim(val) => Err(Error::new_spanned(val, "Failed to forward argument, verbatim was found")),
        ty => Err(Error::new_spanned(ty, "Failed to forward argument, unknown type was found")),
    }
}
