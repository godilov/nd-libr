use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::{
    Error, Expr, ExprClosure, FnArg, Generics, Ident, Item, ItemEnum, ItemImpl, ItemStruct, ItemTrait, ItemUnion, Meta,
    Path, Result, Signature, Token, TraitItemConst, TraitItemFn, TraitItemType, Type, WhereClause,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
};

use crate::get_normalized_generics;

mod kw {
    syn::custom_keyword!(with);
}

#[allow(unused)]
pub struct Forward {
    pub expr: Expr,
    pub with: kw::with,
    pub ty: Type,
}

pub enum ForwardDataItem {
    Struct(ItemStruct),
    Enum(ItemEnum),
    Union(ItemUnion),
}

pub enum ForwardDeclItem {
    Trait(ItemTrait),
}

pub enum ForwardDefItem {
    Struct(ItemStruct),
    Enum(ItemEnum),
    Union(ItemUnion),
    Impl(ItemImpl),
}

#[allow(unused)]
pub struct ForwardData {
    pub fwd: Forward,
    pub colon: Token![:],
    pub path: Path,
    pub conditions: Option<WhereClause>,
}

#[allow(unused)]
pub struct ForwardImpl {
    pub fwd: Forward,
    pub idents: Option<ForwardIdents>,
}

#[allow(unused)]
pub struct ForwardIdents {
    pub colon: Token![:],
    pub elems: Punctuated<Ident, Token![,]>,
}

#[derive(Debug, Clone)]
pub enum ForwardExpression {
    Raw(TokenStream),
    Ref(TokenStream),
    Mut(TokenStream),
}

#[derive(Debug, Clone)]
pub enum ForwardArgument {
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
    pub fn forward_args(&self) -> (&Expr, &Type) {
        (&self.expr, &self.ty)
    }
}

impl ForwardDataItem {
    pub fn forward_args(&self) -> (&Ident, &Generics) {
        match self {
            ForwardDataItem::Struct(val) => (&val.ident, &val.generics),
            ForwardDataItem::Enum(val) => (&val.ident, &val.generics),
            ForwardDataItem::Union(val) => (&val.ident, &val.generics),
        }
    }
}

impl ForwardExpression {
    pub fn stream(self) -> TokenStream {
        match self {
            ForwardExpression::Raw(val) => val,
            ForwardExpression::Ref(val) => val,
            ForwardExpression::Mut(val) => val,
        }
    }
}

impl ForwardArgument {
    pub fn stream(self) -> TokenStream {
        match self {
            ForwardArgument::Raw(val) => val,
            ForwardArgument::Alt(val) => val,
        }
    }
}

pub fn get_forward_impl(ident: &Ident, generics: &Generics, expr: &Expr, ty: &Type) -> TokenStream {
    let (gen_impl, gen_type, gen_where) = generics.split_for_impl();

    quote! {
        pub trait Forward {
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

pub fn get_forward_type<'item>(interface: &ItemTrait, item: &'item TraitItemType) -> (&'item Ident, TokenStream) {
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

pub fn get_forward_const<'item>(interface: &ItemTrait, item: &'item TraitItemConst) -> (&'item Ident, TokenStream) {
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

pub fn get_forward_fn<'item>(_: &ItemTrait, item: &'item TraitItemFn) -> Result<(&'item Ident, TokenStream)> {
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
