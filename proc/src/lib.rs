use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{
    Error, Expr, Generics, Ident, Item, Path, Result, Token, TraitItem, WhereClause, parse_macro_input, parse_quote,
    punctuated::Punctuated,
};

use crate::{
    forward::{
        Forward, ForwardData, ForwardDataItem, ForwardDeclItem, ForwardDefItem, ForwardImpl, get_forward_const,
        get_forward_fn, get_forward_impl, get_forward_type,
    },
    ops::{
        Ops, OpsAuto, OpsDefinition, OpsDefinitionStandard, OpsStdImpl, OpsStdKindBinary, OpsStdKindMutable,
        OpsStdKindUnary,
    },
};

mod forward;
mod ops;

#[proc_macro]
pub fn ops_impl(stream: TokenStreamStd) -> TokenStreamStd {
    match parse_macro_input!(stream as Ops) {
        Ops::StdMutable(ops) => quote! { #ops }.into(),
        Ops::StdBinary(ops) => quote! { #ops }.into(),
        Ops::StdUnary(ops) => quote! { #ops }.into(),
        Ops::NdMutable(_) => quote! {}.into(),
        Ops::NdBinary(_) => quote! {}.into(),
        Ops::NdUnary(_) => quote! {}.into(),
    }
}

#[proc_macro]
pub fn ops_impl_auto(stream: TokenStreamStd) -> TokenStreamStd {
    match parse_macro_input!(stream as OpsAuto) {
        OpsAuto::StdMutable(ops) => {
            let ops = OpsStdImpl::<OpsStdKindMutable> {
                generics: ops.generics,
                signature: ops.signature,
                colon: Default::default(),
                definitions: ops
                    .ops
                    .into_iter()
                    .map(|op| {
                        let lhs = &ops.expression.lhs_expr;
                        let rhs = &ops.expression.rhs_expr;

                        OpsDefinition::Standard(OpsDefinitionStandard::<OpsStdKindMutable> {
                            op,
                            expr: parse_quote! {{ #lhs #op #rhs; }},
                        })
                    })
                    .collect::<Punctuated<OpsDefinition<OpsStdKindMutable>, Token![,]>>(),
            };

            quote! { #ops }.into()
        },
        OpsAuto::StdBinary(ops) => {
            let ops = OpsStdImpl::<OpsStdKindBinary> {
                generics: ops.generics,
                signature: ops.signature,
                colon: Default::default(),
                definitions: ops
                    .ops
                    .into_iter()
                    .map(|op| {
                        let lhs = &ops.expression.lhs_expr;
                        let rhs = &ops.expression.rhs_expr;

                        OpsDefinition::Standard(OpsDefinitionStandard::<OpsStdKindBinary> {
                            op,
                            expr: parse_quote! {{ #lhs #op #rhs }},
                        })
                    })
                    .collect::<Punctuated<OpsDefinition<OpsStdKindBinary>, Token![,]>>(),
            };

            quote! { #ops }.into()
        },
        OpsAuto::StdUnary(ops) => {
            let ops = OpsStdImpl::<OpsStdKindUnary> {
                generics: ops.generics,
                signature: ops.signature,
                colon: Default::default(),
                definitions: ops
                    .ops
                    .into_iter()
                    .map(|op| {
                        let expr = &ops.expression.self_expr;

                        OpsDefinition::Standard(OpsDefinitionStandard::<OpsStdKindUnary> {
                            op,
                            expr: parse_quote! {{ #op #expr }},
                        })
                    })
                    .collect::<Punctuated<OpsDefinition<OpsStdKindUnary>, Token![,]>>(),
            };

            quote! { #ops }.into()
        },
        OpsAuto::NdMutable(_) => quote! {}.into(),
        OpsAuto::NdBinary(_) => quote! {}.into(),
        OpsAuto::NdUnary(_) => quote! {}.into(),
    }
}

#[proc_macro_attribute]
pub fn align(_: TokenStreamStd, item: TokenStreamStd) -> TokenStreamStd {
    let item = parse_macro_input!(item as Item);

    match item {
        Item::Struct(item) => quote! {
            #[cfg_attr(target_arch = "x86",     repr(align(64)))]
            #[cfg_attr(target_arch = "x86_64",  repr(align(64)))]
            #[cfg_attr(target_arch = "arm",     repr(align(64)))]
            #[cfg_attr(target_arch = "aarch64", repr(align(128)))]
            #item
        }
        .into(),
        Item::Enum(item) => quote! {
            #[cfg_attr(target_arch = "x86",     repr(align(64)))]
            #[cfg_attr(target_arch = "x86_64",  repr(align(64)))]
            #[cfg_attr(target_arch = "arm",     repr(align(64)))]
            #[cfg_attr(target_arch = "aarch64", repr(align(128)))]
            #item
        }
        .into(),
        Item::Union(item) => quote! {
            #[cfg_attr(target_arch = "x86",     repr(align(64)))]
            #[cfg_attr(target_arch = "x86_64",  repr(align(64)))]
            #[cfg_attr(target_arch = "arm",     repr(align(64)))]
            #[cfg_attr(target_arch = "aarch64", repr(align(128)))]
            #item
        }
        .into(),
        _ => Error::new(Span::call_site(), "Failed to align, expected struct, enum or union")
            .into_compile_error()
            .into(),
    }
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

fn get_normalized_generics(mut generics: Generics) -> Generics {
    generics.params.pop_punct();
    generics.where_clause.as_mut().map(|clause| clause.predicates.pop_punct());
    generics
}
