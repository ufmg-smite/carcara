use proc_macro::TokenStream;
use proc_macro2::Literal;
use quote::quote;
use std::ffi::OsStr;
use syn::{parse_macro_input, spanned::Spanned};

// TODO: Add argument to control whether generated tests should be `#[ignore]` or not
#[proc_macro_attribute]
pub fn from_dir(args: TokenStream, input: TokenStream) -> TokenStream {
    let original_input = input.clone();

    let args = parse_macro_input!(args as syn::AttributeArgs);
    if args.len() != 1 {
        return TokenStream::from(
            syn::Error::new(
                proc_macro2::Span::call_site(),
                "expected exactly one argument",
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

    for entry in walkdir::WalkDir::new(arg.value()) {
        let Ok(entry) = entry else { continue };

        if entry.file_type().is_file() && entry.path().extension() == Some(OsStr::new("proof")) {
            let path = entry.path().to_str().unwrap();
            let new_name = format!(
                "{}_{}",
                func_ident,
                path.replace(|c: char| !c.is_ascii_alphanumeric() && c != '_', "_")
            );
            let new_ident = syn::Ident::new(&new_name, func_ident.span());
            let arg = Literal::string(path);
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
