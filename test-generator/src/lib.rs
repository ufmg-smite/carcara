use proc_macro::TokenStream;
use proc_macro2::Literal;
use quote::quote;
use std::ffi::OsStr;
use syn::{parse_macro_input, spanned::Spanned};

#[proc_macro_attribute]
pub fn from_dir(args: TokenStream, input: TokenStream) -> TokenStream {
    let original_input = input.clone();

    let args = parse_macro_input!(args as syn::AttributeArgs);
    if args.is_empty() || args.len() > 2 {
        return TokenStream::from(
            syn::Error::new(
                proc_macro2::Span::call_site(),
                "expected between one and two arguments",
            )
            .into_compile_error(),
        );
    }
    let arg = args.first().unwrap();
    let syn::NestedMeta::Lit(syn::Lit::Str(arg)) = arg else {
        return TokenStream::from(
            syn::Error::new(arg.span(), "macro argument must be string literal")
                .into_compile_error(),
        );
    };
    let arg = arg.value();
    let is_ignore = if args.len() > 1 {
        match &args[1] {
            syn::NestedMeta::Meta(syn::Meta::Path(path)) if path.is_ident("ignore") => true,
            _ => {
                return TokenStream::from(
                    syn::Error::new(args[1].span(), "invalid argument").into_compile_error(),
                )
            }
        }
    } else {
        false
    };

    let func = parse_macro_input!(input as syn::ItemFn);
    if func.sig.inputs.len() != 1 {
        return TokenStream::from(
            syn::Error::new(func.span(), "function must have exactly one argument")
                .into_compile_error(),
        );
    }
    let func_ident = func.sig.ident;

    let mut streams: Vec<TokenStream> = Vec::new();
    streams.push(original_input);

    for entry in walkdir::WalkDir::new(&arg) {
        let Ok(entry) = entry else { continue };

        if entry.file_type().is_file() && entry.path().extension() == Some(OsStr::new("proof")) {
            let path = entry.path().to_str().unwrap();
            let new_ident = {
                let path = path.strip_prefix(&arg).unwrap().strip_prefix('/').unwrap();
                let path = path.strip_suffix(".proof").unwrap();
                let path = path.replace(|c: char| !c.is_ascii_alphanumeric() && c != '_', "_");
                syn::Ident::new(&format!("{}_{}", func_ident, path), func_ident.span())
            };
            let arg = Literal::string(path);
            if is_ignore {
                streams.push(quote! { #[ignore] }.into());
            }
            streams.push(
                quote! {
                    #[test]
                    #[allow(warnings)]
                    fn #new_ident() {
                        #func_ident(#arg)
                    }
                }
                .into(),
            )
        }
    }

    TokenStream::from_iter(streams)
}
