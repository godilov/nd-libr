#![doc = include_str!("../README.md")]

use proc_macro::TokenStream as TokenStreamStd;
use quote::quote;
use syn::{Error, Item, parse_macro_input};

/// Aligns **struct**, **enum** or **union** to approximate architecture cacheline size.
///
/// | Architecture | Alignment |
/// | ------------ | --------- |
/// | **x86**      | 64 bytes  |
/// | **x86_64**   | 64 bytes  |
/// | **arm**      | 64 bytes  |
/// | **aarch64**  | 128 bytes |
///
/// For more info, see [crate-level](crate) documentation.
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
        _ => Error::new_spanned(item, "Failed to align, expected struct, enum or union")
            .into_compile_error()
            .into(),
    }
}
