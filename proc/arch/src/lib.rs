#![doc = include_str!("../README.md")]

use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::Span;
use quote::quote;
use syn::{Error, Item, parse_macro_input};

/// Applies an architecture-appropriate cache-line alignment to a struct, enum, or union.
///
/// This attribute macro expands to a set of `#[cfg_attr(target_arch = "…", repr(align(…)))]`
/// attributes targeting the architectures listed below.  All other architectures are left
/// unaffected — no alignment attribute is emitted for them.
///
/// | Architecture | Alignment |
/// |--------------|-----------|
/// | `x86`        | 64 bytes  |
/// | `x86_64`     | 64 bytes  |
/// | `arm`        | 64 bytes  |
/// | `aarch64`    | 128 bytes |
///
/// The macro accepts no arguments and can be applied to structs, enums, and unions.
/// Applying it to any other item is a compile-time error.
///
/// # Usage
///
/// ```rust
/// #[ndarch::align]
/// struct SimdBuffer([f32; 16]);
///
/// #[ndarch::align]
/// enum Packet {
///     Data([u8; 56]),
///     Control(u32),
/// }
///
/// #[ndarch::align]
/// union RawSlot {
///     integer: u64,
///     bytes: [u8; 8],
/// }
/// ```
///
/// # Expansion
///
/// The macro rewrites the item in place, prepending `cfg_attr`-guarded `repr(align(…))`
/// attributes.  The struct definition itself is otherwise unchanged.  For example:
///
/// ```rust
/// #[ndarch::align]
/// struct Foo(u8);
/// ```
///
/// expands to:
///
/// ```rust
/// #[cfg_attr(target_arch = "x86",     repr(align(64)))]
/// #[cfg_attr(target_arch = "x86_64",  repr(align(64)))]
/// #[cfg_attr(target_arch = "arm",     repr(align(64)))]
/// #[cfg_attr(target_arch = "aarch64", repr(align(128)))]
/// struct Foo(u8);
/// ```
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
