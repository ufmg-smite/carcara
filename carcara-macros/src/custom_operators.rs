use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::parse_macro_input;

/// A parsed `custom_operators.toml` file.
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct CustomOperatorsConfig {
    #[serde(default)]
    operator: Vec<CustomOperatorEntry>,
}

/// One `[[operator]]` entry parsed from the config file.
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct CustomOperatorEntry {
    name: String,
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
fn sort_tokens(sort: &SortExpr, entry: &CustomOperatorEntry) -> TokenStream2 {
    let op_name = &entry.name;
    match sort {
        SortExpr::Name(name) => match entry.params.iter().position(|p| p == name) {
            Some(i) => quote! { SortSig::Var(#i) },
            None => builtin_sort_tokens(name)
                .unwrap_or_else(|| panic!("unknown sort `{name}` for custom operator `{op_name}`")),
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
                ("Array" | "Set" | "Tuple", _) => panic!(
                    "wrong number of arguments in sort `{sort}` for custom operator `{op_name}`"
                ),
                _ => panic!(
                    "unknown sort constructor `{head}` in sort `{sort}` for custom operator \
                    `{op_name}`"
                ),
            },
            _ => panic!("invalid sort `{sort}` for custom operator `{op_name}`"),
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

pub fn custom_operators(input: TokenStream) -> TokenStream {
    let relative_path = parse_macro_input!(input as syn::LitStr).value();

    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set");
    let full_path = std::path::Path::new(&manifest_dir).join(&relative_path);
    let full_path_str = full_path.to_str().expect("config path is not valid UTF-8");

    let content = std::fs::read_to_string(&full_path)
        .unwrap_or_else(|e| panic!("failed to read `{}`: {e}", full_path.display()));
    let config: CustomOperatorsConfig = toml::from_str(&content)
        .unwrap_or_else(|e| panic!("failed to parse `{}`: {e}", full_path.display()));

    let mut seen_names = std::collections::HashSet::new();
    let mut seen_idents = std::collections::HashSet::new();
    let mut variant_idents = Vec::new();
    let mut names = Vec::new();
    let mut sig_exprs = Vec::new();

    for entry in &config.operator {
        if !seen_names.insert(entry.name.clone()) {
            panic!("duplicate custom operator name `{}`", entry.name);
        }

        let ident_str = pascal_case_ident(&entry.name);
        if ident_str.is_empty() {
            panic!(
                "custom operator name `{}` does not yield a valid identifier",
                entry.name
            );
        }
        if !seen_idents.insert(ident_str.clone()) {
            panic!(
                "custom operators `{}` and a previous entry both derive the identifier `{ident_str}`",
                entry.name,
            );
        }

        let mut seen_params = std::collections::HashSet::new();
        for param in &entry.params {
            if builtin_sort_tokens(param).is_some()
                || matches!(param.as_str(), "Array" | "Set" | "Tuple")
            {
                panic!(
                    "sort parameter `{param}` of custom operator `{}` shadows a built-in sort",
                    entry.name,
                );
            }
            if !seen_params.insert(param) {
                panic!(
                    "duplicate sort parameter `{param}` for custom operator `{}`",
                    entry.name,
                );
            }
            if !entry.arg_types.iter().any(|t| t.mentions(param)) {
                panic!(
                    "sort parameter `{param}` of custom operator `{}` must occur in `arg_types`, \
                    otherwise it can't be inferred",
                    entry.name,
                );
            }
        }

        let return_sort = sort_tokens(&entry.return_type, entry);
        let arg_sorts: Vec<_> = entry
            .arg_types
            .iter()
            .map(|t| sort_tokens(t, entry))
            .collect();
        let name = &entry.name;
        let params = &entry.params;

        sig_exprs.push(quote! {
            OperatorSig {
                name: #name,
                params: &[#(#params),*],
                arg_sorts: &[#(#arg_sorts),*],
                return_sort: #return_sort,
            }
        });
        names.push(name.clone());
        variant_idents.push(format_ident!("{}", ident_str));
    }

    let num_operators = variant_idents.len();

    quote! {
        // `include_str!` registers the config as a tracked input, since `tracked_path` is unstable.
        #[doc(hidden)]
        const _CUSTOM_OPERATORS_TOML: &str = include_str!(#full_path_str);

        /// A custom operator, defined via `custom_operators.toml`.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum CustomOperator {
            #(#variant_idents),*
        }

        impl CustomOperator {
            /// All custom operators, in declaration order.
            pub const ALL: &'static [CustomOperator] = &[
                #(CustomOperator::#variant_idents),*
            ];

            /// Looks up a custom operator by name, returning `None` if it isn't one.
            pub fn lookup(name: &str) -> Option<Self> {
                match name {
                    #(#names => Some(CustomOperator::#variant_idents),)*
                    _ => None,
                }
            }

            /// Returns this operator's type signature.
            pub fn sig(self) -> &'static OperatorSig {
                static SIGS: [OperatorSig; #num_operators] = [
                    #(#sig_exprs),*
                ];
                &SIGS[self as usize]
            }
        }
    }
    .into()
}
