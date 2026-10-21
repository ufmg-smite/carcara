mod custom_operators;
mod match_term;
mod version_string;

use proc_macro::TokenStream;
use quote::quote;
use syn::{DataStruct, DeriveInput, parse_macro_input};

/// Reads a custom-operator TOML config file and expands to a `CustomOperator` enum and impl.
#[proc_macro]
pub fn custom_operators(input: TokenStream) -> TokenStream {
    custom_operators::custom_operators(input)
}

#[proc_macro]
pub fn match_term(input: TokenStream) -> TokenStream {
    match_term::match_term(input)
}

#[proc_macro]
pub fn get_op_variant(input: TokenStream) -> TokenStream {
    let input = input.to_string();
    match_term::op_to_variant(&input).into()
}

#[proc_macro]
pub fn get_param_op_variant(input: TokenStream) -> TokenStream {
    let input = input.to_string();
    match_term::param_op_to_variant(&input).into()
}

#[proc_macro_derive(GenerateSetters, attributes(skip_setter, const_setters))]
pub fn generate_setters(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let struct_name = &ast.ident;
    let generics = &ast.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let const_modifier = if ast.attrs.iter().any(|a| a.path().is_ident("const_setters")) {
        quote! { const }
    } else {
        quote! {}
    };

    let syn::Data::Struct(DataStruct { fields, .. }) = &ast.data else {
        panic!("can only be used with a struct")
    };
    let generated_setters = fields.iter().map(|f| {
        let field_name = f.ident.clone().expect("expected the field to have a name");
        let ty = f.ty.clone();
        let doc = f.attrs.iter().filter(|v| v.meta.path().is_ident("doc"));

        if f.attrs.iter().any(|a| a.path().is_ident("skip_setter")) {
            quote! {}
        } else {
            quote! {
                #(#doc)*
                #[inline(always)]
                pub #const_modifier fn #field_name(mut self, val: #ty) -> Self {
                    self.#field_name = val;
                    self
                }
            }
        }
    });

    quote! {
        impl #impl_generics #struct_name #ty_generics #where_clause {
            #(#generated_setters)*
        }
    }
    .into()
}

/// Generates a version string for Carcara.
#[proc_macro]
pub fn version_string(input: TokenStream) -> TokenStream {
    version_string::version_string(input)
}
