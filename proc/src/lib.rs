use proc_macro::TokenStream as TokenStreamStd;
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, quote};
use syn::{
    Error, Expr, GenericParam, Generics, Ident, Path, Token, Type, WherePredicate, braced,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    token,
};
use syn::{parse_str, parse2};

#[allow(dead_code)]
struct OpsGeneric {
    pub l_token: Token![<],
    pub params: Punctuated<GenericParam, Token![,]>,
    pub r_token: Token![>],
}

#[allow(dead_code)]
struct OpsWhere {
    pub token: Token![where],
    pub predicates: Punctuated<WherePredicate, Token![,]>,
}

#[allow(dead_code)]
struct OpsRaw {
    id: String,
    body: TokenStream,
}

#[allow(dead_code)]
struct OpsId<Id: Parse> {
    at: Token![@],
    id: Id,
}

#[allow(dead_code)]
struct OpsSignatureMutable {
    lhs_token: Token![|],
    lhs_ident: Ident,
    lhs_colon: Token![:],
    lhs_ref: Option<Token![&]>,
    lhs_mut: Token![mut],
    lhs_type: Type,
    delim: Token![,],
    rhs_ident: Ident,
    rhs_colon: Token![:],
    rhs_ref: Option<Token![&]>,
    rhs_type: Type,
    rhs_token: Token![|],
}

#[allow(dead_code)]
struct OpsSignatureBinary {
    lhs_token: Token![|],
    lhs_ident: Ident,
    lhs_colon: Token![:],
    lhs_ref: Option<Token![&]>,
    lhs_type: Type,
    delim: Token![,],
    rhs_ident: Ident,
    rhs_colon: Token![:],
    rhs_ref: Option<Token![&]>,
    rhs_type: Type,
    rhs_token: Token![|],
    arrow: Token![->],
    op_type: Type,
}

#[allow(dead_code)]
struct OpsSignatureUnary {
    lhs_token: Token![|],
    lhs_ident: Ident,
    lhs_colon: Token![:],
    lhs_ref: Option<Token![&]>,
    lhs_type: Type,
    rhs_token: Token![|],
    arrow: Token![->],
    op_type: Type,
}

#[allow(dead_code)]
struct OpsImplStd<OpsSignature: Parse> {
    ident: Ident,
    generics: Option<Generics>,
    signature: OpsSignature,
    brace: token::Brace,
    expr: Expr,
}

type OpsImplStdMutable = OpsImplStd<OpsSignatureMutable>;
type OpsImplStdBinary = OpsImplStd<OpsSignatureBinary>;
type OpsImplStdUnary = OpsImplStd<OpsSignatureUnary>;

impl Parse for OpsGeneric {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            l_token: input.parse()?,
            params: input.parse_terminated(GenericParam::parse, Token![,])?,
            r_token: input.parse()?,
        })
    }
}

impl Parse for OpsWhere {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            token: input.parse()?,
            predicates: input.parse_terminated(WherePredicate::parse, Token![,])?,
        })
    }
}

impl Parse for OpsRaw {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _ = input.parse::<Token![@]>()?;

        let ident = if input.peek(Token![mut]) {
            input.parse::<Token![mut]>()?.into_token_stream()
        } else {
            input.parse::<Ident>()?.into_token_stream()
        };

        let body = input.parse::<TokenStream>()?;

        Ok(Self {
            id: format!("@{}", ident),
            body,
        })
    }
}

impl<Id: Parse> Parse for OpsId<Id> {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            at: input.parse()?,
            id: input.parse()?,
        })
    }
}

impl Parse for OpsSignatureMutable {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            lhs_token: input.parse()?,
            lhs_ident: input.parse()?,
            lhs_colon: input.parse()?,
            lhs_ref: input.parse().ok(),
            lhs_mut: input.parse()?,
            lhs_type: input.parse()?,
            delim: input.parse()?,
            rhs_ident: input.parse()?,
            rhs_colon: input.parse()?,
            rhs_ref: input.parse().ok(),
            rhs_type: input.parse()?,
            rhs_token: input.parse()?,
        })
    }
}

impl Parse for OpsSignatureBinary {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            lhs_token: input.parse()?,
            lhs_ident: input.parse()?,
            lhs_colon: input.parse()?,
            lhs_ref: input.parse().ok(),
            lhs_type: input.parse()?,
            delim: input.parse()?,
            rhs_ident: input.parse()?,
            rhs_colon: input.parse()?,
            rhs_ref: input.parse().ok(),
            rhs_type: input.parse()?,
            rhs_token: input.parse()?,
            arrow: input.parse()?,
            op_type: input.parse()?,
        })
    }
}

impl Parse for OpsSignatureUnary {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            lhs_token: input.parse()?,
            lhs_ident: input.parse()?,
            lhs_colon: input.parse()?,
            lhs_ref: input.parse().ok(),
            lhs_type: input.parse()?,
            rhs_token: input.parse()?,
            arrow: input.parse()?,
            op_type: input.parse()?,
        })
    }
}

impl<OpsSinature: Parse> Parse for OpsImplStd<OpsSinature> {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let expr;

        let ident = input.parse()?;
        let generics = input.parse().ok().map(|val: Generics| Generics {
            lt_token: val.lt_token,
            params: val.params,
            gt_token: val.gt_token,
            where_clause: input.parse().ok(),
        });

        Ok(Self {
            ident,
            generics,
            signature: input.parse()?,
            brace: braced!(expr in input),
            expr: expr.parse()?,
        })
    }
}

impl ToTokens for OpsImplStdMutable {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        fn get_impl(val: &OpsImplStdMutable, lhs_ref: Option<Token![&]>, rhs_ref: Option<Token![&]>) -> TokenStream {
            let (ident, path) = match get_std_path_mut(&val.ident) {
                | Ok(val) => val,
                | Err(err) => {
                    return err.into_compile_error();
                },
            };

            let generics = val.generics.as_ref().map(|val| val.split_for_impl());
            let (implgen, wheregen) = match generics {
                | Some((implgen, _, wheregen)) => (Some(implgen), wheregen),
                | None => (None, None),
            };

            let lhs_ident = &val.signature.lhs_ident;
            let lhs_type = &val.signature.lhs_type;
            let rhs_ident = &val.signature.rhs_ident;
            let rhs_type = &val.signature.rhs_type;

            let expr = &val.expr;

            let lhs_ref = lhs_ref.map(|_| quote! { &mut });

            quote! {
                impl #implgen #path<#rhs_ref #rhs_type> for #lhs_ref #lhs_type #wheregen {
                    fn #ident(&mut self, rhs: #rhs_ref #rhs_type ) {
                        #[allow(clippy::redundant_closure_call)]
                        (|#lhs_ident: &mut #lhs_type, #rhs_ident: #rhs_ref #rhs_type| { #expr })(self, rhs);
                    }
                }
            }
        }

        let lhs = self.signature.lhs_ref.is_some();
        let rhs = self.signature.rhs_ref.is_some();
        let some = Some(Default::default());
        let none = None;

        match (lhs, rhs) {
            | (true, true) => {
                tokens.extend(get_impl(self, some, some));
                tokens.extend(get_impl(self, some, none));
                tokens.extend(get_impl(self, none, some));
                tokens.extend(get_impl(self, none, none));
            },
            | (true, false) => {
                tokens.extend(get_impl(self, some, none));
                tokens.extend(get_impl(self, none, none));
            },
            | (false, true) => {
                tokens.extend(get_impl(self, none, some));
                tokens.extend(get_impl(self, none, none));
            },
            | (false, false) => {
                tokens.extend(get_impl(self, none, none));
            },
        }
    }
}

impl ToTokens for OpsImplStdBinary {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        fn get_impl(val: &OpsImplStdBinary, lhs_ref: Option<Token![&]>, rhs_ref: Option<Token![&]>) -> TokenStream {
            let (ident, path) = match get_std_path_binary(&val.ident) {
                | Ok(val) => val,
                | Err(err) => {
                    return err.into_compile_error();
                },
            };

            let generics = val.generics.as_ref().map(|val| val.split_for_impl());
            let (implgen, wheregen) = match generics {
                | Some((implgen, _, wheregen)) => (Some(implgen), wheregen),
                | None => (None, None),
            };

            let lhs_ident = &val.signature.lhs_ident;
            let lhs_type = &val.signature.lhs_type;
            let rhs_ident = &val.signature.rhs_ident;
            let rhs_type = &val.signature.rhs_type;
            let op_type = &val.signature.op_type;

            let expr = &val.expr;

            quote! {
                impl #implgen #path<#rhs_ref #rhs_type> for #lhs_ref #lhs_type #wheregen {
                    type Output = #op_type;

                    fn #ident(self, rhs: #rhs_ref #rhs_type) -> Self::Output {
                        #[allow(clippy::redundant_closure_call)]
                        (|#lhs_ident: #lhs_ref #lhs_type, #rhs_ident: #rhs_ref #rhs_type| { #expr })(self, rhs)
                    }
                }
            }
        }

        let lhs = self.signature.lhs_ref.is_some();
        let rhs = self.signature.rhs_ref.is_some();
        let some = Some(Default::default());
        let none = None;

        match (lhs, rhs) {
            | (true, true) => {
                tokens.extend(get_impl(self, some, some));
                tokens.extend(get_impl(self, some, none));
                tokens.extend(get_impl(self, none, some));
                tokens.extend(get_impl(self, none, none));
            },
            | (true, false) => {
                tokens.extend(get_impl(self, some, none));
                tokens.extend(get_impl(self, none, none));
            },
            | (false, true) => {
                tokens.extend(get_impl(self, none, some));
                tokens.extend(get_impl(self, none, none));
            },
            | (false, false) => {
                tokens.extend(get_impl(self, none, none));
            },
        }
    }
}

impl ToTokens for OpsImplStdUnary {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        fn get_impl(val: &OpsImplStdUnary, lhs_ref: Option<Token![&]>) -> TokenStream {
            let (ident, path) = match get_std_path_unary(&val.ident) {
                | Ok(val) => val,
                | Err(err) => {
                    return err.into_compile_error();
                },
            };

            let generics = val.generics.as_ref().map(|val| val.split_for_impl());
            let (implgen, wheregen) = match generics {
                | Some((implgen, _, wheregen)) => (Some(implgen), wheregen),
                | None => (None, None),
            };

            let lhs_ident = &val.signature.lhs_ident;
            let lhs_type = &val.signature.lhs_type;
            let op_type = &val.signature.op_type;

            let expr = &val.expr;

            quote! {
                impl #implgen #path for #lhs_ref #lhs_type #wheregen {
                    type Output = #op_type;

                    fn #ident(self) -> Self::Output {
                        #[allow(clippy::redundant_closure_call)]
                        (|#lhs_ident: #lhs_ref #lhs_type| { #expr })(self)
                    }
                }
            }
        }

        let lhs = self.signature.lhs_ref.is_some();
        let some = Some(Default::default());
        let none = None;

        match lhs {
            | true => {
                tokens.extend(get_impl(self, some));
                tokens.extend(get_impl(self, none));
            },
            | false => {
                tokens.extend(get_impl(self, none));
            },
        }
    }
}

#[proc_macro]
pub fn ops_impl_std(stream: TokenStreamStd) -> TokenStreamStd {
    const ERROR: &str = "You must specify one of the identifiers: `@mut`, `@bin`, `@un`";

    let raw = parse_macro_input!(stream as OpsRaw);

    match raw.id.as_str() {
        | "@mut" => {
            let body = raw.body;
            let ops = parse2::<OpsImplStdMutable>(body);

            match ops {
                | Ok(val) => quote! { #val }.into(),
                | Err(err) => err.to_compile_error().into(),
            }
        },
        | "@bin" => {
            let body = raw.body;
            let ops = parse2::<OpsImplStdBinary>(body);

            match ops {
                | Ok(val) => quote! { #val }.into(),
                | Err(err) => err.to_compile_error().into(),
            }
        },
        | "@un" => {
            let body = raw.body;
            let ops = parse2::<OpsImplStdUnary>(body);

            match ops {
                | Ok(val) => quote! { #val }.into(),
                | Err(err) => err.to_compile_error().into(),
            }
        },
        | _ => Error::new(Span::call_site(), ERROR).to_compile_error().into(),
    }
}

#[proc_macro]
pub fn ops_impl(_stream: TokenStreamStd) -> TokenStreamStd {
    todo!()
}

#[proc_macro]
pub fn ops_impl_auto(_stream: TokenStreamStd) -> TokenStreamStd {
    todo!()
}

fn get_std_path_mut(ident: &Ident) -> syn::Result<(Ident, Path)> {
    let (ident, path) = match ident.to_string().as_str() {
        | "add" => Ok(("add_assign", "std::ops::AddAssign")),
        | "sub" => Ok(("sub_assign", "std::ops::SubAssign")),
        | "mul" => Ok(("mul_assign", "std::ops::MulAssign")),
        | "div" => Ok(("div_assign", "std::ops::DivAssign")),
        | "rem" => Ok(("rem_assign", "std::ops::RemAssign")),
        | "bitor" => Ok(("bitor_assign", "std::ops::BitOrAssign")),
        | "bitand" => Ok(("bitand_assign", "std::ops::BitAndAssign")),
        | "bitxor" => Ok(("bitxor_assign", "std::ops::BitXorAssign")),
        | "shl" => Ok(("shl_assign", "std::ops::ShlAssign")),
        | "shr" => Ok(("shr_assign", "std::ops::ShrAssign")),
        | _ => Err(Error::new(
            Span::call_site(),
            format!(
                "Invalid `ident` for operation: {}. Expected: add, sub, mul, div, rem, bitor, bitand, bitxor, shl, shr",
                ident
            ),
        )),
    }?;

    Ok((parse_str::<Ident>(ident)?, parse_str::<Path>(path)?))
}

fn get_std_path_binary(ident: &Ident) -> syn::Result<(Ident, Path)> {
    let str = match ident.to_string().as_str() {
        | "add" => Ok("std::ops::Add"),
        | "sub" => Ok("std::ops::Sub"),
        | "mul" => Ok("std::ops::Mul"),
        | "div" => Ok("std::ops::Div"),
        | "rem" => Ok("std::ops::Rem"),
        | "bitor" => Ok("std::ops::BitOr"),
        | "bitand" => Ok("std::ops::BitAnd"),
        | "bitxor" => Ok("std::ops::BitXor"),
        | "shl" => Ok("std::ops::Shl"),
        | "shr" => Ok("std::ops::Shr"),
        | _ => Err(Error::new(
            Span::call_site(),
            format!(
                "Invalid `ident` for operation: {}. Expected: add, sub, mul, div, rem, bitor, bitand, bitxor, shl, shr",
                ident
            ),
        )),
    }?;

    Ok((ident.clone(), parse_str::<Path>(str)?))
}

fn get_std_path_unary(ident: &Ident) -> syn::Result<(Ident, Path)> {
    let str = match ident.to_string().as_str() {
        | "neg" => Ok("std::ops::Neg"),
        | "not" => Ok("std::ops::Not"),
        | _ => Err(Error::new(
            Span::call_site(),
            format!("Invalid `ident` for operation: {}. Expected: neg, not", ident),
        )),
    }?;

    Ok((ident.clone(), parse_str::<Path>(str)?))
}
