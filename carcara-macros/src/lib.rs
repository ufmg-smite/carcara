extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::{Delimiter, Ident, Spacing, TokenStream as TokenStream2, TokenTree};
use quote::{format_ident, quote};
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input, Expr, Token,
};

// Represents the full macro input: '<pattern> = <expr>'
struct Input {
    pattern: TokenTree,
    expr: Expr,
}

impl Parse for Input {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let pattern: TokenTree = input.parse()?;
        input.parse::<Token![=]>()?;
        let expr: Expr = input.parse()?;
        Ok(Input { pattern, expr })
    }
}

// Internal representation of the s-expression pattern.
// Pat::Variadic carries a generated Ident so the captured slice can appear
// as an element in the flat output tuple (e.g. '(and ...)' -> Some(args_slice)).
#[derive(Debug, Clone)]
enum Pat {
    True,
    False,
    EmptyString,
    Literal(u64),
    FreeVar(Ident),
    // Carries a generated name that will hold the captured &[Rc<Term>] slice.
    Variadic(Ident),
    Op { op: String, args: Vec<Pat> },
    ParamOp { op: String, op_args: Vec<Pat>, args: Vec<Pat> },
    // Represents (forall ... body), (exists ... body), (choice ... body).
    // Always captures a 'bindings' variable followed by whatever 'inner' captures.
    Binder { binder: String, inner: Box<Pat> },
}

impl Pat {
    /// Collects all free variables in depth-first, left-to-right order.
    /// This order determines the flat tuple returned by the macro.
    fn free_vars(&self) -> Vec<Ident> {
        match self {
            Pat::FreeVar(id) => vec![id.clone()],
            // Variadic contributes the slice ident as one element of the tuple.
            Pat::Variadic(id) => vec![id.clone()],
            Pat::Op { args, .. } => args.iter().flat_map(|p| p.free_vars()).collect(),
            Pat::ParamOp { op_args, args, .. } => op_args
                .iter()
                .chain(args.iter())
                .flat_map(|p| p.free_vars())
                .collect(),
            // Binder always yields 'bindings' first, then whatever the inner pattern captures.
            Pat::Binder { inner, .. } => {
                let mut vars = vec![format_ident!("bindings")];
                vars.extend(inner.free_vars());
                vars
            }
            _ => vec![],
        }
    }
}

// Reads an operator from a token slice.
// Multi-character operators like '<=', '>=', '=>' are two adjacent Punct tokens.
fn read_op(tokens: &[TokenTree]) -> (String, usize) {
    match &tokens[0] {
        TokenTree::Ident(id) => (id.to_string(), 1),
        TokenTree::Punct(p) => {
            if p.spacing() == Spacing::Joint {
                if let Some(TokenTree::Punct(p2)) = tokens.get(1) {
                    return (format!("{}{}", p.as_char(), p2.as_char()), 2);
                }
            }
            (p.as_char().to_string(), 1)
        }
        other => panic!("expected operator, found {:?}", other),
    }
}

// Recursively parses a TokenTree into a Pat.
// 'ctr' is used to generate unique idents for variadic captures.
fn parse_pat(tt: TokenTree, ctr: &mut usize) -> Pat {
    match tt {
        TokenTree::Ident(id) => match id.to_string().as_str() {
            "true"  => Pat::True,
            "false" => Pat::False,
            _       => Pat::FreeVar(id),
        },

        TokenTree::Literal(lit) => {
            let s = lit.to_string();
            if s == "\"\"" {
                Pat::EmptyString
            } else {
                let n: u64 = s.parse().unwrap_or_else(|_| {
                    panic!("unsupported literal in match_term_flat!: {s}")
                });
                Pat::Literal(n)
            }
        }

        TokenTree::Group(g) if g.delimiter() == Delimiter::Parenthesis => {
            let tokens: Vec<_> = g.stream().into_iter().collect();
            assert!(!tokens.is_empty(), "empty group in pattern");

            // Detect (forall ... body), (exists ... body), (choice ... body) - Binder pattern.
            // Expected shape: ident + dot + dot + dot + body (at least 5 tokens).
            if let TokenTree::Ident(id) = &tokens[0] {
                let name = id.to_string();
                if matches!(name.as_str(), "forall" | "exists" | "choice") {
                    assert!(
                        tokens.len() >= 5,
                        "binder pattern must be ({name} ... <body>)"
                    );
                    let inner_tt = tokens[tokens.len() - 1].clone();
                    return Pat::Binder {
                        binder: name,
                        inner: Box::new(parse_pat(inner_tt, ctr)),
                    };
                }
            }

            // Detect ((_ op op_args...) args...) - ParamOp pattern.
            // The '_' here is an Ident token, not a Punct.
            if let TokenTree::Group(inner) = &tokens[0] {
                if inner.delimiter() == Delimiter::Parenthesis {
                    let inner_tokens: Vec<_> = inner.stream().into_iter().collect();
                    if matches!(&inner_tokens[0], TokenTree::Ident(id) if id.to_string() == "_") {
                        let (op, op_len) = read_op(&inner_tokens[1..]);
                        let op_arg_tokens = &inner_tokens[1 + op_len..];
                        let op_args: Vec<Pat> = op_arg_tokens
                            .iter()
                            .cloned()
                            .map(|t| parse_pat(t, ctr))
                            .collect();
                        let args: Vec<Pat> = tokens[1..]
                            .iter()
                            .cloned()
                            .map(|t| parse_pat(t, ctr))
                            .collect();
                        return Pat::ParamOp { op, op_args, args };
                    }
                }
            }

            // Regular Op pattern - read op, then parse args.
            let (op, op_len) = read_op(&tokens);
            let rest = &tokens[op_len..];
            let mut args = Vec::new();
            let mut i = 0;
            while i < rest.len() {
                // Detect '...' - three consecutive '.' Punct tokens.
                if rest[i..].len() >= 3
                    && (0..3).all(|j| {
                        matches!(&rest[i + j], TokenTree::Punct(p) if p.as_char() == '.')
                    })
                {
                    // Generate a unique ident for this variadic capture.
                    *ctr += 1;
                    args.push(Pat::Variadic(format_ident!("__mt_variadic_{}", ctr)));
                    i += 3;
                    continue;
                }
                args.push(parse_pat(rest[i].clone(), ctr));
                i += 1;
            }
            Pat::Op { op, args }
        }

        other => panic!("unexpected token in pattern: {:?}", other),
    }
}

fn param_op_to_variant(op: &str) -> TokenStream2 {
    match op {
        "int_of"       => quote! { crate::ast::ParamOperator::BvIntOf },
        "bit_of"       => quote! { crate::ast::ParamOperator::BvBitOf },
        "int_to_bv"    => quote! { crate::ast::ParamOperator::IntToBv },
        "extract"      => quote! { crate::ast::ParamOperator::BvExtract },
        "zero_extend"  => quote! { crate::ast::ParamOperator::ZeroExtend },
        "sign_extend"  => quote! { crate::ast::ParamOperator::SignExtend },
        "rotate_left"  => quote! { crate::ast::ParamOperator::RotateLeft },
        "rotate_right" => quote! { crate::ast::ParamOperator::RotateRight },
        "repeat"       => quote! { crate::ast::ParamOperator::Repeat },
        other => panic!("unknown param operator in match_term_flat!: {other:?}"),
    }
}

fn op_to_variant(op: &str) -> TokenStream2 {
    match op {
        "not"      => quote! { crate::ast::Operator::Not },
        "=>"       => quote! { crate::ast::Operator::Implies },
        "and"      => quote! { crate::ast::Operator::And },
        "or"       => quote! { crate::ast::Operator::Or },
        "xor"      => quote! { crate::ast::Operator::Xor },
        "="        => quote! { crate::ast::Operator::Equals },
        "distinct" => quote! { crate::ast::Operator::Distinct },
        "ite"      => quote! { crate::ast::Operator::Ite },
        "+"        => quote! { crate::ast::Operator::Add },
        "-"        => quote! { crate::ast::Operator::Sub },
        "*"        => quote! { crate::ast::Operator::Mult },
        "div"      => quote! { crate::ast::Operator::IntDiv },
        "/"        => quote! { crate::ast::Operator::RealDiv },
        "mod"      => quote! { crate::ast::Operator::Mod },
        "<"        => quote! { crate::ast::Operator::LessThan },
        ">"        => quote! { crate::ast::Operator::GreaterThan },
        "<="       => quote! { crate::ast::Operator::LessEq },
        ">="       => quote! { crate::ast::Operator::GreaterEq },
        "to_real"  => quote! { crate::ast::Operator::ToReal },
        "cl"       => quote! { crate::ast::Operator::Cl },
        "delete"   => quote! { crate::ast::Operator::Delete },
        "bbterm"   => quote! { crate::ast::Operator::BvBbTerm },
        "pbbterm"  => quote! { crate::ast::Operator::BvPBbTerm },
        "bvnot"    => quote! { crate::ast::Operator::BvNot },
        "bvneg"    => quote! { crate::ast::Operator::BvNeg },
        "bvand"    => quote! { crate::ast::Operator::BvAnd },
        "bvor"     => quote! { crate::ast::Operator::BvOr },
        "bvxor"    => quote! { crate::ast::Operator::BvXor },
        "bvxnor"   => quote! { crate::ast::Operator::BvXNor },
        "bvcomp"   => quote! { crate::ast::Operator::BvComp },
        "bvadd"    => quote! { crate::ast::Operator::BvAdd },
        "bvmul"    => quote! { crate::ast::Operator::BvMul },
        "bvudiv"   => quote! { crate::ast::Operator::BvUDiv },
        "bvurem"   => quote! { crate::ast::Operator::BvURem },
        "bvshl"    => quote! { crate::ast::Operator::BvShl },
        "bvlshr"   => quote! { crate::ast::Operator::BvLShr },
        "concat"   => quote! { crate::ast::Operator::BvConcat },
        "bvuge"    => quote! { crate::ast::Operator::BvUGe },
        "bvugt"    => quote! { crate::ast::Operator::BvUGt },
        "bvule"    => quote! { crate::ast::Operator::BvULe },
        "bvult"    => quote! { crate::ast::Operator::BvULt },
        "bvsge"    => quote! { crate::ast::Operator::BvSGe },
        "bvsgt"    => quote! { crate::ast::Operator::BvSGt },
        "bvsle"    => quote! { crate::ast::Operator::BvSLe },
        "bvslt"    => quote! { crate::ast::Operator::BvSLt },
        "ubv_to_int" => quote! { crate::ast::Operator::UBvToInt },
        "sbv_to_int" => quote! { crate::ast::Operator::SBvToInt },
        "strconcat" => quote! { crate::ast::Operator::StrConcat },
        "strsubstr" => quote! { crate::ast::Operator::Substring },
        "strlen"    => quote! { crate::ast::Operator::StrLen },
        "strinre"   => quote! { crate::ast::Operator::StrInRe },
        "reinter"   => quote! { crate::ast::Operator::ReIntersection },
        other => panic!("unknown operator in match_term_flat!: {other:?}"),
    }
}

// Builds nested 'if let' matching code using continuation-passing style.
// 'inner' is the innermost code (the return value), and each recursive call
// wraps it in another layer of matching.
fn gen_match(
    pat: &Pat,
    var: &TokenStream2,
    inner: TokenStream2,
    ctr: &mut usize,
) -> TokenStream2 {
    match pat {
        Pat::True => quote! {
            if (#var).is_bool_true() { #inner } else { None }
        },
        Pat::False => quote! {
            if (#var).is_bool_false() { #inner } else { None }
        },
        Pat::EmptyString => quote! {
            if (#var).is_empty_string() { #inner } else { None }
        },
        Pat::Literal(n) => quote! {
            if (#var).as_number().is_some_and(|i| i == #n) { #inner } else { None }
        },
        Pat::FreeVar(id) => quote! {
            { let #id = #var; #inner }
        },
        // Variadic as a standalone pattern: bind the value directly.
        // In practice this is only reached when the variadic is the sole arg of an Op,
        // which is handled as a special case in the Op arm below.
        Pat::Variadic(id) => quote! {
            { let #id = #var; #inner }
        },
        Pat::Op { op, args } => {
            let variant = op_to_variant(op);

            // Special case: sole variadic arg - capture entire args slice directly.
            // We cannot use 'if let [single_arg] = slice' here because the slice
            // can have any length. Instead, just bind the whole slice.
            if args.len() == 1 {
                if let Pat::Variadic(var_id) = &args[0] {
                    *ctr += 1;
                    let args_ident = format_ident!("__mt_args_{}", ctr);
                    return quote! {
                        if let crate::ast::Term::Op(#variant, #args_ident) = (#var).as_ref() {
                            let #var_id = #args_ident.as_slice();
                            #inner
                        } else {
                            None
                        }
                    };
                }
            }

            // Normal fixed-arity case.
            let n = args.len();
            let arg_idents: Vec<Ident> = (0..n)
                .map(|_| {
                    *ctr += 1;
                    format_ident!("__mt_arg_{}", ctr)
                })
                .collect();
            *ctr += 1;
            let args_vec = format_ident!("__mt_args_{}", ctr);

            // Build the continuation right-to-left so that the leftmost
            // argument is the outermost binding (correct DFS order).
            let mut body = inner;
            for (sub_pat, arg_id) in args.iter().zip(arg_idents.iter()).rev() {
                let v = quote! { #arg_id };
                body = gen_match(sub_pat, &v, body, ctr);
            }

            quote! {
                if let crate::ast::Term::Op(#variant, #args_vec) = (#var).as_ref() {
                    if let [#(#arg_idents),*] = #args_vec.as_slice() {
                        #body
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        }
        Pat::ParamOp { op, op_args, args } => {
            let variant = param_op_to_variant(op);
            let n_op  = op_args.len();
            let n_arg = args.len();

            let op_arg_idents: Vec<Ident> = (0..n_op).map(|_| {
                *ctr += 1;
                format_ident!("__mt_arg_{}", ctr)
            }).collect();
            *ctr += 1;
            let op_args_vec = format_ident!("__mt_args_{}", ctr);

            let arg_idents: Vec<Ident> = (0..n_arg).map(|_| {
                *ctr += 1;
                format_ident!("__mt_arg_{}", ctr)
            }).collect();
            *ctr += 1;
            let args_vec = format_ident!("__mt_args_{}", ctr);

            // Build continuation right-to-left: regular args first (innermost), then op_args.
            // This ensures op_args appear before args in the final flat tuple, matching
            // the left-to-right DFS order of the pattern ((_ op i j) a b) -> (i, j, a, b).
            let mut body = inner;
            for (sub_pat, arg_id) in args.iter().zip(arg_idents.iter()).rev() {
                let v = quote! { #arg_id };
                body = gen_match(sub_pat, &v, body, ctr);
            }
            for (sub_pat, arg_id) in op_args.iter().zip(op_arg_idents.iter()).rev() {
                let v = quote! { #arg_id };
                body = gen_match(sub_pat, &v, body, ctr);
            }

            quote! {
                if let crate::ast::Term::ParamOp {
                    op: #variant,
                    op_args: #op_args_vec,
                    args: #args_vec,
                } = (#var).as_ref() {
                    if let [#(#op_arg_idents),*] = #op_args_vec.as_slice() {
                        if let [#(#arg_idents),*] = #args_vec.as_slice() {
                            #body
                        } else { None }
                    } else { None }
                } else { None }
            }
        }
        // Rename destructured field to 'inner_pat' to avoid conflict with the
        // 'inner' parameter of gen_match (which is the continuation TokenStream2).
        Pat::Binder { binder, inner: inner_pat } => {
            let binder_variant = match binder.as_str() {
                "forall" => quote! { crate::ast::Binder::Forall },
                "exists" => quote! { crate::ast::Binder::Exists },
                "choice" => quote! { crate::ast::Binder::Choice },
                other    => panic!("unknown binder in match_term_flat!: {other}"),
            };

            *ctr += 1;
            let inner_var = format_ident!("__mt_arg_{}", ctr);
            // 'bindings' is a fixed name, matching the contract of the original match_term!
            let bindings_var = format_ident!("bindings");

            // Recursively generate matching for the body of the binder,
            // passing 'inner' (the continuation) as the innermost code.
            let body = gen_match(inner_pat, &quote! { #inner_var }, inner, ctr);

            quote! {
                if let crate::ast::Term::Binder(#binder_variant, #bindings_var, #inner_var) =
                    (#var).as_ref()
                {
                    #body
                } else {
                    None
                }
            }
        }
    }
}

#[proc_macro]
pub fn match_term_flat(input: TokenStream) -> TokenStream {
    let Input { pattern, expr } = parse_macro_input!(input as Input);

    // Single counter shared between parse_pat (for variadic idents) and gen_match
    // (for temporary arg idents). They use separate ranges so names never collide.
    let mut parse_ctr = 0usize;
    let pat = parse_pat(pattern, &mut parse_ctr);
    let free_vars = pat.free_vars();

    // Innermost code: return a flat tuple of all captured variables.
    let result = match free_vars.len() {
        0 => quote! { Some(()) },
        1 => { let v = &free_vars[0]; quote! { Some(#v) } }
        _ => quote! { Some((#(#free_vars),*)) },
    };

    let mut gen_ctr = 1000usize; // start at 1000 to avoid collisions with parse_ctr names
    let body = gen_match(&pat, &quote! { #expr }, result, &mut gen_ctr);

    quote! {{ #body }}.into()
}
