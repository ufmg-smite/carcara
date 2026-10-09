use proc_macro::TokenStream;
use proc_macro2::Literal;
use quote::quote;
use std::ffi::OsStr;
use syn::{parse_macro_input, spanned::Spanned};

#[proc_macro_attribute]
pub fn from_dir(args: TokenStream, input: TokenStream) -> TokenStream {
    let original_input = input.clone();

    let mut arg: Option<syn::LitStr> = None;
    let mut is_ignore = false;
    let parser = syn::meta::parser(|meta| {
        if meta.path.is_ident("path") {
            arg = Some(meta.value()?.parse()?);
            Ok(())
        } else if meta.path.is_ident("ignore") {
            is_ignore = true;
            Ok(())
        } else {
            Err(meta.error("unsupported argument"))
        }
    });
    parse_macro_input!(args with parser);
    let arg = arg.expect("no path given").value();

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

        if entry.file_type().is_file() && entry.path().extension() == Some(OsStr::new("alethe")) {
            let path = entry.path().to_str().unwrap();
            let new_ident = {
                let path = path.strip_prefix(&arg).unwrap().strip_prefix('/').unwrap();
                let path = path.strip_suffix(".alethe").unwrap();
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
                        #func_ident(::std::path::Path::new(#arg))
                    }
                }
                .into(),
            )
        }
    }

    TokenStream::from_iter(streams)
}
