use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::{
    Error, Expr, ExprClosure, FnArg, Generics, Ident, Item, ItemEnum, ItemImpl, ItemStruct, ItemTrait, ItemUnion, Meta,
    Path, Result, Signature, Token, TraitItem, TraitItemConst, TraitItemFn, TraitItemType, Type, WhereClause,
    parse::{Parse, ParseStream},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
};

mod kw {
    syn::custom_keyword!(with);
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
                Self::from(<#ty>::from_iter(iter))
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
        ($item:expr, $attr:expr) => {{
            let item = $item;
            let attr = $attr;

            let ident = &item.ident;
            let generics = &item.generics;
            let gen_params = &item.generics.params;
            let (_, gen_type, gen_where) = item.generics.split_for_impl();

            let expr = &attr.fwd.expr;
            let ty = &attr.fwd.ty;
            let path = &attr.path;
            let predicates = attr.conditions.as_ref().map(|conditions| &conditions.predicates);

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
        ForwardDefItem::Struct(val) => forward!(val, parse_macro_input!(attr as ForwardData)),
        ForwardDefItem::Enum(val) => forward!(val, parse_macro_input!(attr as ForwardData)),
        ForwardDefItem::Union(val) => forward!(val, parse_macro_input!(attr as ForwardData)),
        ForwardDefItem::Impl(val) => {
            let ForwardImpl { fwd: _, idents: _ } = parse_macro_input!(attr as ForwardImpl);

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

#[allow(unused)]
struct Forward {
    expr: Expr,
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

#[allow(unused)]
struct ForwardData {
    fwd: Forward,
    colon: Token![:],
    path: Path,
    conditions: Option<WhereClause>,
}

#[allow(unused)]
struct ForwardImpl {
    fwd: Forward,
    idents: Option<ForwardIdents>,
}

#[allow(unused)]
struct ForwardIdents {
    colon: Token![:],
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

impl Parse for ForwardData {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            fwd: input.parse()?,
            colon: input.parse()?,
            path: input.parse()?,
            conditions: input.parse()?,
        })
    }
}

impl Parse for ForwardImpl {
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

fn get_forward_impl(ident: &Ident, generics: &Generics, expr: &Expr, ty: &Type) -> TokenStream {
    let (gen_impl, gen_type, gen_where) = generics.split_for_impl();

    quote! {
        trait Forward {
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
                    self.forward_mut().#ident(#(#definitions),*).into()
                }
            } else if forward_self {
                quote! {
                    self.forward_mut().#ident(#(#definitions),*);
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
                    (self.forward_mut().#ident(#(#definitions),*))
                }
            } else {
                quote! {
                    self.forward_mut().#ident(#(#definitions),*)
                }
            }
        },
        Some(val) if val.reference.is_some() => {
            if forward_into {
                quote! {
                    self.forward_ref().#ident(#(#definitions),*).into()
                }
            } else if forward_self {
                quote! {
                    self.forward_ref().#ident(#(#definitions),*);
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
                    (self.forward_ref().#ident(#(#definitions),*))
                }
            } else {
                quote! {
                    self.forward_ref().#ident(#(#definitions),*)
                }
            }
        },
        Some(_) => {
            if forward_into {
                quote! {
                    self.forward().#ident(#(#definitions),*).into()
                }
            } else if forward_self {
                quote! {
                    self.forward().#ident(#(#definitions),*);
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
                    (self.forward().#ident(#(#definitions),*))
                }
            } else {
                quote! {
                    self.forward().#ident(#(#definitions),*)
                }
            }
        },
        None => quote! {
            <$ty>::#ident(#(#definitions),*).into()
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
            #constness #asyncness #unsafety #abi fn #ident #generics (#recv #(#declarations),*) #output {
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

fn get_normalized_generics(mut generics: Generics) -> Generics {
    generics.params.pop_punct();
    generics.where_clause.as_mut().map(|clause| clause.predicates.pop_punct());
    generics
}
