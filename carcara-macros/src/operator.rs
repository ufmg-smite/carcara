use proc_macro::TokenStream;
use proc_macro2::{Ident, TokenStream as TokenStream2};
use quote::quote;
use std::path::Path;

/// A parsed `operators.toml` file.
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct OperatorsConfig {
    #[serde(default)]
    operator: Vec<OperatorEntry>,
}

/// One `[[operator]]` entry parsed from the config file.
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct OperatorEntry {
    name: String,
    #[serde(default)]
    variant: Option<String>,
    #[serde(default)]
    params: Vec<String>,
    return_type: SortExpr,
    #[serde(default)]
    arg_types: Vec<SortExpr>,
}

/// A sort in the config file: either a sort name (`"Int"`) or a list representing a sort
/// application (`["Set", "Int"]`).
#[derive(serde::Deserialize)]
#[serde(
    untagged,
    expecting = "a sort name or a list of sorts, like `[\"Set\", \"Int\"]`"
)]
enum SortExpr {
    Name(String),
    App(Vec<SortExpr>),
}

impl SortExpr {
    /// Returns `true` if `name` occurs anywhere in this sort.
    fn mentions(&self, name: &str) -> bool {
        match self {
            SortExpr::Name(n) => n == name,
            SortExpr::App(items) => items.iter().any(|s| s.mentions(name)),
        }
    }
}

impl std::fmt::Display for SortExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SortExpr::Name(name) => write!(f, "{name}"),
            SortExpr::App(items) => match items.as_slice() {
                [] => write!(f, "()"),
                [head, tail @ ..] => {
                    write!(f, "({head}")?;
                    for arg in tail {
                        write!(f, " {arg}")?;
                    }
                    write!(f, ")")
                }
            },
        }
    }
}

/// Maps a built-in sort name to the tokens for its `SortSig` variant, or `None` if it isn't one.
fn builtin_sort_tokens(name: &str) -> Option<TokenStream2> {
    Some(match name {
        "Bool" => quote! { SortSig::Bool },
        "Int" => quote! { SortSig::Int },
        "Real" => quote! { SortSig::Real },
        "String" => quote! { SortSig::String },
        "RegLan" => quote! { SortSig::RegLan },
        "UnitTuple" => quote! { SortSig::Tuple(&[]) },
        _ => return None,
    })
}

/// Maps a supported sort to the tokens for its `SortSig`, panicking on an unknown sort.
fn sort_tokens(sort: &SortExpr, entry: &OperatorEntry) -> TokenStream2 {
    let op_name = &entry.name;
    match sort {
        SortExpr::Name(name) => match entry.params.iter().position(|p| p == name) {
            Some(i) => quote! { SortSig::Var(#i) },
            None => builtin_sort_tokens(name)
                .unwrap_or_else(|| panic!("unknown sort `{name}` for operator `{op_name}`")),
        },
        SortExpr::App(items) => match items.as_slice() {
            [SortExpr::Name(head), args @ ..] => match (head.as_str(), args) {
                ("Array", [a, b]) => {
                    let [a, b] = [a, b].map(|s| sort_tokens(s, entry));
                    quote! { SortSig::Array(&#a, &#b) }
                }
                ("Set", [a]) => {
                    let a = sort_tokens(a, entry);
                    quote! { SortSig::Set(&#a) }
                }
                ("Tuple", [_, ..]) => {
                    let args = args.iter().map(|s| sort_tokens(s, entry));
                    quote! { SortSig::Tuple(&[#(#args),*]) }
                }
                ("Array" | "Set" | "Tuple", _) => {
                    panic!("wrong number of arguments in sort `{sort}` for operator `{op_name}`")
                }
                _ => panic!(
                    "unknown sort constructor `{head}` in sort `{sort}` for operator `{op_name}`"
                ),
            },
            _ => panic!("invalid sort `{sort}` for operator `{op_name}`"),
        },
    }
}

/// Derives a `PascalCase` identifier from an operator name, e.g. `str.to_lower` -> `StrToLower`.
fn pascal_case_ident(name: &str) -> String {
    name.split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|segment| !segment.is_empty())
        .map(|segment| {
            let mut chars = segment.chars();
            let first = chars.next().expect("segment is non-empty");
            first.to_ascii_uppercase().to_string() + chars.as_str()
        })
        .collect()
}

struct Operators {
    names: Vec<String>,
    idents: Vec<Ident>,
    sigs: Vec<TokenStream2>,
}

fn load_operators(path: &Path) -> Operators {
    let content = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read `{}`: {e}", path.display()));
    let config: OperatorsConfig = toml::from_str(&content)
        .unwrap_or_else(|e| panic!("failed to parse `{}`: {e}", path.display()));
    let mut seen_idents = std::collections::HashSet::new();
    let mut names = Vec::new();
    let mut idents = Vec::new();
    let mut sigs = Vec::new();

    for entry in &config.operator {
        let name = &entry.name;
        let ident = entry
            .variant
            .clone()
            .unwrap_or_else(|| pascal_case_ident(name));
        let ident: Ident = syn::parse_str(&ident).unwrap_or_else(|_| {
            panic!("`{ident}` is not a valid variant name for operator `{name}`")
        });
        if !seen_idents.insert(ident.clone()) {
            panic!("duplicate operator identifier `{ident}`");
        }

        let mut seen_params = std::collections::HashSet::new();
        for param in &entry.params {
            if builtin_sort_tokens(param).is_some()
                || matches!(param.as_str(), "Array" | "Set" | "Tuple")
            {
                panic!("sort parameter `{param}` of operator `{name}` shadows a built-in sort");
            }
            if !seen_params.insert(param) {
                panic!("duplicate sort parameter `{param}` for operator `{name}`");
            }
            if !entry.arg_types.iter().any(|t| t.mentions(param)) {
                panic!(
                    "sort parameter `{param}` of operator `{name}` must occur in `arg_types`, \
                    otherwise it can't be inferred",
                );
            }
        }

        let return_sort = sort_tokens(&entry.return_type, entry);
        let arg_sorts = entry.arg_types.iter().map(|t| sort_tokens(t, entry));
        let params = &entry.params;
        let sig = quote! {
            OperatorSig {
                name: #name,
                params: &[#(#params),*],
                arg_sorts: &[#(#arg_sorts),*],
                return_sort: #return_sort,
            }
        };
        names.push(name.clone());
        idents.push(ident);
        sigs.push(sig.clone());
    }

    Operators { names, idents, sigs }
}

fn get_variant_name_attr(variant: &syn::Variant) -> String {
    let ident = &variant.ident;
    variant
        .attrs
        .iter()
        .find(|a| a.path().is_ident("name"))
        .unwrap_or_else(|| panic!("missing `name` attribute for variant {ident}"))
        .parse_args::<syn::LitStr>()
        .unwrap_or_else(|e| panic!("invalid `name` attribute for variant {ident}: {e}"))
        .value()
}

pub fn extend_operator_enum(config_path: &Path, mut enum_item: syn::ItemEnum) -> TokenStream {
    let path_str = config_path.to_str().unwrap();
    let enum_name = &enum_item.ident;
    let extra_operators = load_operators(config_path);
    let sigs = extra_operators.sigs;
    let extra_idents = extra_operators.idents;

    let all_names: Vec<_> = enum_item
        .variants
        .iter()
        .map(get_variant_name_attr)
        .chain(extra_operators.names.iter().cloned())
        .collect();
    let all_idents: Vec<_> = enum_item
        .variants
        .iter()
        .map(|v| &v.ident)
        .chain(&extra_idents)
        .cloned()
        .collect();

    let mut seen_names = std::collections::HashMap::new();
    for (name, ident) in all_names.iter().zip(&all_idents) {
        if let Some(prev) = seen_names.insert(name, ident) {
            panic!("operator name `{name}` is used by both `{prev}` and `{ident}`");
        }
    }

    // We must remove the `name` attributes from the variants before generating the enum definition
    for variant in &mut enum_item.variants {
        variant.attrs.retain(|a| !a.path().is_ident("name"));
    }

    for (name, ident) in extra_operators.names.iter().zip(&extra_idents) {
        let doc = format!(" The `{name}` operator.");
        enum_item.variants.push(syn::parse_quote! {
            #[doc = #doc]
            #ident
        });
    }

    quote! {
        // `include_str!` registers the config as a tracked input, since `tracked_path` is unstable.
        #[doc(hidden)]
        const _OPERATORS_TOML: &str = include_str!(#path_str);

        #enum_item

        impl #enum_name {
            fn raw_sig(self) -> Option<&'static OperatorSig> {
                match self {
                    #(#enum_name::#extra_idents => Some(&#sigs),)*
                    _ => None,
                }
            }
        }

        impl std::str::FromStr for #enum_name {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    #(#all_names => Ok(#enum_name::#all_idents),)*
                    _ => Err(()),
                }
            }
        }

        impl std::fmt::Display for #enum_name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    #(#enum_name::#all_idents => write!(f, #all_names),)*
                }
            }
        }
    }
    .into()
}
