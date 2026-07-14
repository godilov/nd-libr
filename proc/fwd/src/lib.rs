#![doc = include_str!("../README.md")]

use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{
    Error, Expr, FnArg, Generics, Ident, Item, ItemEnum, ItemImpl, ItemStruct, ItemTrait, ItemUnion, Meta, Path,
    Result, Signature, Token, TraitItem, TraitItemConst, TraitItemFn, TraitItemType, Type, TypePath, WhereClause,
    parse::{Parse, ParseStream},
    parse_macro_input, parse_quote,
};

mod kw {
    syn::custom_keyword!(with);
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

    let as_ref = ty.as_ref(&attr);
    let as_mut = ty.as_mut(&attr);

    quote! {
        #ty

        #as_ref
        #as_mut
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

    let (ident, generics) = ty.args();
    let (expr_impl, ty_impl) = attr.args();

    let (gen_impl, gen_type, gen_where) = generics.split_for_impl();

    let predicates = gen_where.map(|val| val.predicates.iter());

    let partial_ord = match predicates.clone() {
        Some(val) => quote! { where #(#val,)* #ty_impl: std::cmp::PartialOrd },
        None => quote! { where #ty_impl: std::cmp::PartialOrd },
    };

    let partial_eq = match predicates.clone() {
        Some(val) => quote! { where #(#val,)* #ty_impl: std::cmp::PartialEq },
        None => quote! { where #ty_impl: std::cmp::PartialEq },
    };

    let ord = match predicates.clone() {
        Some(val) => quote! { where #(#val,)* #ty_impl: std::cmp::Ord },
        None => quote! { where #ty_impl: std::cmp::Ord },
    };

    let eq = match predicates.clone() {
        Some(val) => quote! { where #(#val,)* #ty_impl: std::cmp::Eq },
        None => quote! { where #ty_impl: std::cmp::Eq },
    };

    let path = parse_quote! { #ident #gen_type };
    let forward_impl = get_forward_impl(&path, generics, expr_impl, ty_impl);

    quote! {
        #ty

        impl #gen_impl std::cmp::Eq for #ident #gen_type #eq {}

        impl #gen_impl std::cmp::Ord for #ident #gen_type #ord {
            #[inline]
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                #forward_impl

                self.forward_ref().cmp(other.forward_ref())
            }
        }

        impl #gen_impl std::cmp::PartialEq for #ident #gen_type #partial_eq {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                #forward_impl

                self.forward_ref().eq(other.forward_ref())
            }
        }

        impl #gen_impl std::cmp::PartialOrd for #ident #gen_type #partial_ord {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                #forward_impl

                self.forward_ref().partial_cmp(other.forward_ref())
            }
        }
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
    fn fmt_impl(
        ident: &Ident,
        generics: &Generics,
        expr: &Expr,
        display: TokenStream,
        display_where: TokenStream,
    ) -> TokenStream {
        let (gen_impl, gen_type, _) = generics.split_for_impl();

        quote! {
            impl #gen_impl #display for #ident #gen_type #display_where {
                #[inline]
                fn fmt(&self,f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    #expr.fmt(f)
                }
            }
        }
    }

    let ty = parse_macro_input!(ty as FwdType);
    let attr = parse_macro_input!(attr as FwdAttr);

    let (ident, generics) = ty.args();
    let (expr_impl, ty_impl) = attr.args();

    let (_, _, gen_where) = generics.split_for_impl();

    let predicates = gen_where.map(|val| val.predicates.iter());

    let display = fmt_impl(
        ident,
        generics,
        expr_impl,
        quote! { std::fmt::Display },
        match predicates.clone() {
            Some(val) => quote! { where #(#val,)* #ty_impl: std::fmt::Display },
            None => quote! { where #ty_impl: std::fmt::Display },
        },
    );

    let binary = fmt_impl(
        ident,
        generics,
        expr_impl,
        quote! { std::fmt::Binary },
        match predicates.clone() {
            Some(val) => quote! { where #(#val,)* #ty_impl: std::fmt::Binary },
            None => quote! { where #ty_impl: std::fmt::Binary },
        },
    );

    let octal = fmt_impl(
        ident,
        generics,
        expr_impl,
        quote! { std::fmt::Octal },
        match predicates.clone() {
            Some(val) => quote! { where #(#val,)* #ty_impl: std::fmt::Octal },
            None => quote! { where #ty_impl: std::fmt::Octal },
        },
    );

    let lhex = fmt_impl(
        ident,
        generics,
        expr_impl,
        quote! { std::fmt::LowerHex },
        match predicates.clone() {
            Some(val) => quote! { where #(#val,)* #ty_impl: std::fmt::LowerHex },
            None => quote! { where #ty_impl: std::fmt::LowerHex },
        },
    );

    let uhex = fmt_impl(
        ident,
        generics,
        expr_impl,
        quote! { std::fmt::UpperHex },
        match predicates.clone() {
            Some(val) => quote! { where #(#val,)* #ty_impl: std::fmt::UpperHex },
            None => quote! { where #ty_impl: std::fmt::UpperHex },
        },
    );

    quote! {
        #ty
        #display
        #binary
        #octal
        #lhex
        #uhex
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

    let (ident, generics) = ty.args();
    let (expr_impl, ty_impl) = attr.args();

    let gen_params = &generics.params;
    let (_, gen_type, gen_where) = generics.split_for_impl();

    let params = gen_params.iter();
    let predicates = gen_where.map(|val| val.predicates.iter());

    let from_iter = match predicates.clone() {
        Some(val) => quote! { where Self: From<#ty_impl>, #(#val,)* #ty_impl: std::iter::FromIterator<Elem> },
        None => quote! { where Self: From<#ty_impl>, #ty_impl: std::iter::FromIterator<Elem> },
    };

    let into_iter = match predicates.clone() {
        Some(val) => quote! { where #(#val,)* #ty_impl: std::iter::IntoIterator },
        None => quote! { where #ty_impl: std::iter::IntoIterator },
    };

    let into_iter_ref = match predicates.clone() {
        Some(val) => quote! { where #(#val,)* &'reference #ty_impl: std::iter::IntoIterator },
        None => quote! { where &'reference #ty_impl: std::iter::IntoIterator },
    };

    let into_iter_mut = match predicates.clone() {
        Some(val) => quote! { where #(#val,)* &'reference mut #ty_impl: std::iter::IntoIterator },
        None => quote! { where &'reference mut #ty_impl: std::iter::IntoIterator },
    };

    quote! {
        #ty

        impl<#(#params,)* Elem> std::iter::FromIterator<Elem> for #ident #gen_type #from_iter {
            #[inline]
            fn from_iter<Iter: IntoIterator<Item = Elem>>(iter: Iter) -> Self {
                <#ty_impl>::from_iter(iter).into()
            }
        }

        impl<#gen_params> std::iter::IntoIterator for #ident #gen_type #into_iter {
            type Item = <#ty_impl as std::iter::IntoIterator>::Item;
            type IntoIter = <#ty_impl as std::iter::IntoIterator>::IntoIter;

            #[inline]
            fn into_iter(self) -> Self::IntoIter {
                #expr_impl.into_iter()
            }
        }

        impl<'reference, #gen_params> std::iter::IntoIterator for &'reference #ident #gen_type #into_iter_ref {
            type Item = <&'reference #ty_impl as std::iter::IntoIterator>::Item;
            type IntoIter = <&'reference #ty_impl as std::iter::IntoIterator>::IntoIter;

            #[inline]
            fn into_iter(self) -> Self::IntoIter {
                (&#expr_impl).into_iter()
            }
        }

        impl<'reference, #gen_params> std::iter::IntoIterator for &'reference mut #ident #gen_type #into_iter_mut {
            type Item = <&'reference mut #ty_impl as std::iter::IntoIterator>::Item;
            type IntoIter = <&'reference mut #ty_impl as std::iter::IntoIterator>::IntoIter;

            #[inline]
            fn into_iter(self) -> Self::IntoIter {
                (&mut #expr_impl).into_iter()
            }
        }
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
            TraitItem::Type(val) => Some(Ok(get_forward_type(&decl, val))),
            TraitItem::Const(val) => Some(Ok(get_forward_const(&decl, val))),
            TraitItem::Fn(val) => Some(get_forward_fn(&decl, val)),
            _ => None,
        })
        .collect::<Result<Vec<(&Ident, bool, TokenStream)>>>();

    let forwards = match forwards {
        Ok(val) => val,
        Err(err) => return err.into_compile_error().into(),
    };

    let all = forwards.iter().map(|(_, _, stream)| stream);
    let defaults = forwards.iter().filter(|(_, flag, _)| !flag).map(|(_, _, stream)| stream);

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
    macro_rules! forward {
        ($def:expr, $attr:expr) => {{
            let def = $def;
            let attr = $attr;
            let quote = quote! { #def };

            let ident = &def.ident;
            let (_, gen_type, _) = &def.generics.split_for_impl();

            forward(parse_quote! { #ident #gen_type }, &def.generics, &attr, quote)
        }};
    }

    fn forward(path: TypePath, generics: &Generics, attr: &FwdDefAttr, def: TokenStream) -> TokenStreamStd {
        let gen_params = &generics.params;

        let expr = &attr.fwd.expr;
        let ty = &attr.fwd.ty;
        let interface = &attr.path;
        let defaults = &attr.defaults;

        let sig_predicates = generics.where_clause.as_ref().map(|val| val.predicates.iter());
        let attr_predicates = attr.conditions.as_ref().map(|val| val.predicates.iter());

        let gen_where = match (sig_predicates, attr_predicates) {
            (Some(sig), Some(attr)) => quote! { #ty: #interface, #(#sig,)* #(#attr,)* },
            (Some(sig), None) => quote! { #ty: #interface, #(#sig,)* },
            (None, Some(attr)) => quote! { #ty: #interface, #(#attr,)* },
            (None, None) => quote! { #ty: #interface, },
        };

        let segs = interface.segments.iter().take(interface.segments.len().saturating_sub(1));
        let id = match interface.segments.last() {
            Some(val) => &val.ident,
            None => {
                return Error::new_spanned(&interface.segments, "Failed to forward definition, path is empty")
                    .into_compile_error()
                    .into();
            },
        };

        let name = path
            .path
            .segments
            .iter()
            .fold(String::new(), |acc, seg| format!("{}{}", &acc, seg.ident));

        let forward = get_forward_impl(&path, generics, expr, ty);
        let module = format_ident!("__NdFwd{}Impl{}", &id, &name);
        let macros = format_ident!("__NdFwd{}", &id);

        quote! {
            #def

            #[doc(hidden)]
            #[allow(non_snake_case)]
            mod #module {
                #forward

                #macros!(#defaults #path, #ty, (#gen_params), (#gen_where));

                use super::*;

                #[allow(unused_imports)]
                use #(#segs::)*#macros;

                #[allow(unused_imports)]
                use #interface;
            }
        }
        .into()
    }

    let def = parse_macro_input!(def as FwdDef);

    match def {
        FwdDef::Struct(val) => forward!(val, parse_macro_input!(attr as FwdDefAttr)),
        FwdDef::Enum(val) => forward!(val, parse_macro_input!(attr as FwdDefAttr)),
        FwdDef::Union(val) => forward!(val, parse_macro_input!(attr as FwdDefAttr)),
        FwdDef::Impl(val) => {
            let quote = quote! { #val };
            let path = match *val.self_ty {
                Type::Path(val) => val,
                ty => {
                    return Error::new_spanned(ty, "Failed to forward definition, expected path for impl type")
                        .into_compile_error()
                        .into();
                },
            };

            let generics = &val.generics;

            forward(path, generics, &parse_macro_input!(attr as FwdDefAttr), quote)
        },
    }
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
                    None => match path.is_ident(&format_ident!("NdForward")) {
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

impl ToTokens for FwdExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            FwdExpr::Raw(val) => val.to_tokens(tokens),
            FwdExpr::Ref(val) => val.to_tokens(tokens),
            FwdExpr::Mut(val) => val.to_tokens(tokens),
        }
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
            FwdType::Struct(val) => (&val.ident, &val.generics),
            FwdType::Enum(val) => (&val.ident, &val.generics),
            FwdType::Union(val) => (&val.ident, &val.generics),
        }
    }

    fn as_ref(&self, attr: &FwdAttr) -> TokenStream {
        let (ident, generics) = self.args();
        let (expr, ty) = attr.args();

        let gen_params = generics.params.iter();
        let (_, gen_type, gen_where) = generics.split_for_impl();

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
    }

    fn as_mut(&self, attr: &FwdAttr) -> TokenStream {
        let (ident, generics) = self.args();
        let (expr, ty) = attr.args();

        let gen_params = generics.params.iter();
        let (_, gen_type, gen_where) = generics.split_for_impl();

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

fn get_forward_impl(path: &TypePath, generics: &Generics, expr: &Expr, ty: &Type) -> TokenStream {
    let (gen_impl, _, gen_where) = generics.split_for_impl();

    quote! {
        trait Forward {
            type Type;

            fn forward(self) -> Self::Type;

            fn forward_ref(&self) -> &Self::Type;

            fn forward_mut(&mut self) -> &mut Self::Type;
        }

        impl #gen_impl Forward for #path #gen_where {
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
    }
}

fn get_forward_type<'item>(interface: &ItemTrait, item: &'item TraitItemType) -> (&'item Ident, bool, TokenStream) {
    let attrs = &item.attrs;
    let ident = &item.ident;

    let (gen_impl, gen_type, _) = item.generics.split_for_impl();

    let id = &interface.ident;
    let (_, gen_type_id, _) = interface.generics.split_for_impl();

    (
        ident,
        false,
        quote! {
            #(#attrs)*
            type #ident #gen_impl = <$ty as #id #gen_type_id>::#ident #gen_type;
        },
    )
}

fn get_forward_const<'item>(interface: &ItemTrait, item: &'item TraitItemConst) -> (&'item Ident, bool, TokenStream) {
    let attrs = &item.attrs;
    let ident = &item.ident;
    let ty = &item.ty;

    let id = &interface.ident;
    let (_, gen_type_id, _) = interface.generics.split_for_impl();

    (
        ident,
        false,
        quote! {
            #(#attrs)*
            const #ident: #ty = <$ty as #id #gen_type_id>::#ident;
        },
    )
}

fn get_forward_fn<'item>(_: &ItemTrait, item: &'item TraitItemFn) -> Result<(&'item Ident, bool, TokenStream)> {
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

    let declarations = inputs
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

    let definitions = inputs
        .iter()
        .filter_map(|arg| match arg {
            FnArg::Receiver(_) => None,
            FnArg::Typed(val) => Some(val),
        })
        .enumerate()
        .map(|(idx, val)| {
            let ident = format_ident!("arg{}", idx);
            let expr = quote! { #ident };

            let arg = get_forward_argument(FwdExpr::Raw(expr), &val.ty);

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
        Some(val) if val.reference.is_some() && val.mutability.is_some() => {
            if as_into {
                quote! {
                    self.forward_mut().#ident(#(#definitions),*).into()
                }
            } else if as_self {
                quote! {
                    self.forward_mut().#ident(#(#definitions),*);
                    self
                }
            } else if let Some(as_expr) = as_expr {
                let expr = get_forward_expr(&as_expr.meta)?;

                quote! {
                    (#expr)(self.forward_mut().#ident(#(#definitions),*))
                }
            } else if let Some(as_map) = as_map {
                let expr = get_forward_expr(&as_map.meta)?;

                quote! {
                    self.forward_mut().#ident(#(#definitions),*).map(#expr)
                }
            } else {
                quote! {
                    self.forward_mut().#ident(#(#definitions),*)
                }
            }
        },
        Some(val) if val.reference.is_some() => {
            if as_into {
                quote! {
                    self.forward_ref().#ident(#(#definitions),*).into()
                }
            } else if as_self {
                quote! {
                    self.forward_ref().#ident(#(#definitions),*);
                    self
                }
            } else if let Some(as_expr) = as_expr {
                let expr = get_forward_expr(&as_expr.meta)?;

                quote! {
                    (#expr)(self.forward_ref().#ident(#(#definitions),*))
                }
            } else if let Some(as_map) = as_map {
                let expr = get_forward_expr(&as_map.meta)?;

                quote! {
                    self.forward_ref().#ident(#(#definitions),*).map(#expr)
                }
            } else {
                quote! {
                    self.forward_ref().#ident(#(#definitions),*)
                }
            }
        },
        Some(_) => {
            if as_into {
                quote! {
                    self.forward().#ident(#(#definitions),*).into()
                }
            } else if as_self {
                quote! {
                    self.forward().#ident(#(#definitions),*);
                    self
                }
            } else if let Some(as_expr) = as_expr {
                let expr = get_forward_expr(&as_expr.meta)?;

                quote! {
                    (#expr)(self.forward().#ident(#(#definitions),*))
                }
            } else if let Some(as_map) = as_map {
                let expr = get_forward_expr(&as_map.meta)?;

                quote! {
                    self.forward().#ident(#(#definitions),*).map(#expr)
                }
            } else {
                quote! {
                    self.forward().#ident(#(#definitions),*)
                }
            }
        },
        None => {
            if as_into {
                quote! {
                    <$ty>::#ident(#(#definitions),*).into()
                }
            } else if let Some(as_expr) = as_expr {
                let expr = get_forward_expr(&as_expr.meta)?;

                quote! {
                    (#expr)(<$ty>::#ident(#(#definitions),*))
                }
            } else if let Some(as_map) = as_map {
                let expr = get_forward_expr(&as_map.meta)?;

                quote! {
                    <$ty>::#ident(#(#definitions),*).map(#expr)
                }
            } else {
                quote! {
                    <$ty>::#ident(#(#definitions),*)
                }
            }
        },
    };

    let recv = match recv {
        Some(val) => quote! { #val, },
        None => quote! {},
    };

    Ok((
        ident,
        default.is_some(),
        quote! {
            #[allow(unused_mut)]
            #[inline]
            #(#attrs)*
            #constness #asyncness #unsafety #abi fn #ident #generics (#recv #(#declarations),*) #output {
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
