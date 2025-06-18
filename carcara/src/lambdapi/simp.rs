use try_match::match_ok;

use crate::ast::Constant;

use super::*;

pub fn translate_rare_simp(clause: &Vec<Rc<AletheTerm>>, args: &Vec<Rc<AletheTerm>>) -> Proof {
    let (rare_rule, args) = args.split_first().unwrap();

    let rule: String =
        unwrap_match!(**rare_rule, crate::ast::Term::Const(Constant::String(ref s)) => s.clone());

    //FIXME: bugging rule
    if rule == "bool-and-flatten" || rule == "bool-or-flatten" {
        return Proof(vec![ProofStep::Admit]);
    }

    let mut rewrites = match rule.as_str() {
        "bool-and-true" => translate_bool_and_true(args),
        "bool-or-false" => translate_bool_or_false(args),
        "bool-or-flatten" => translate_bool_or_flatten(args),
        "bool-and-flatten" => translate_bool_and_flatten(args),
        "bool-impl-elim" => translate_bool_impl_elim(args),
        "bool-and-de-morgan" => translate_bool_and_de_morgan(args),
        "bool-or-de-morgan" => translate_bool_or_de_morgan(args),
        "arith-poly-norm" => translate_arith_poly_norm(),
        "evaluate" => {
            let cl_first = clause.first().expect("evaluate can not be empty");
            match  match_term!((= l r) = cl_first) {
                Some((l, r)) if (r.is_bool_false() || r.is_bool_true())
                    && (
                    matches!(l.deref(), AletheTerm::Op(Operator::GreaterEq, _))
                    || matches!(l.deref(), AletheTerm::Op(Operator::LessEq, _))
                    || matches!(l.deref(), AletheTerm::Op(Operator::GreaterThan, _))
                    || matches!(l.deref(), AletheTerm::Op(Operator::LessThan, _))
                )
                => {
                    translate_evaluate_linear_arith()
                },
                Some((_l, r)) if (r.is_bool_false() || r.is_bool_true()) => {
                    translate_evaluate_bool()
                },
                Some(_) => {
                    translate_evaluate_eq_arith()
                }
                None => panic!("not well formed evaluate, expected t1 = t2"),
            }
        },
        r => {
            let args = args.into_iter().map(|term| term.into()).collect_vec();
            vec![ProofStep::Apply(Term::from(r), args, SubProofs(None))]
        }
    };

    Proof(lambdapi! {
        apply "∨ᵢ₁";
        inject(rewrites);
    })
}

/// Provide a proof term for `evaluate` rule that fold numeric constant.
/// For example:
/// ```
/// (step ti (cl (= (* -16 1) -16)) :rule rare_rewrite :args ("evaluate"))
/// ```
fn translate_evaluate_eq_arith() -> Vec<ProofStep> {
    lambdapi! {
        simplify;
        reflexivity;
    }
}

/// Provide a proof term for `evaluate` rule that fold numeric constant.
/// For example:
/// ```
/// (step tj (cl (= (>= 0 0) true)) :rule rare_rewrite :args ("evaluate"))
/// ```
fn translate_evaluate_linear_arith() -> Vec<ProofStep> {
    vec![ProofStep::Admit]
}

/// Provide a proof term for the `evaluate` rule that fold boolean constant.
/// For example:
/// ```
/// (step ti (cl (= (not true) false)) :rule rare_rewrite :args ("evaluate"))
/// ```
fn translate_evaluate_bool() -> Vec<ProofStep> {
    // lambdapi! {
    //     simplify;
    //     apply "prop_ext";
    //     why3;
    // }
    vec![ProofStep::Admit]
}

/// Use the RING solver to prove arith-poly-norm 
fn translate_arith_poly_norm() -> Vec<ProofStep> {
    // vec![
    //     ProofStep::Simplify,
    //     ProofStep::Rewrite(true, Some("[x in _ = x]".into()), Term::from("inj"), vec![],SubProofs(None)),
    //     ProofStep::Rewrite(true, Some("[x in x = _]".into()), Term::from("inj"), vec![],SubProofs(None)),
    //     ProofStep::Reflexivity
    // ]
    //FIXME: Ring has change for another method
    vec![ProofStep::Admit]
}

// /// Translate (define-rule* bool-or-false ((xs Bool :list) (ys Bool :list)) (or xs false ys) (or xs ys))
fn translate_bool_or_false(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    let args = args
        .into_iter()
        .map(|term| unwrap_match!(**term, AletheTerm::Op(Operator::RareList, ref l) => l))
        .collect_vec();

    // If `xs` or `ys` rare-list are empty then we can not use the lemma bool-or-false because it expect 2 arguments.
    // we will use the `or_identity_l` or `or_identity_r` in that cases, otherwise we can use bool-and-true.

    if args[0].is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        lambdapi! { rewrite "or_identity_l"; }
    } else if args[1].is_empty() {
        // argument `x` of and_identity_r lemma should be inferred by Lambdapi
        lambdapi! { rewrite "or_identity_r"; }
    } else {
        // let args: Vec<Term> = args
        //     .into_iter()
        //     .map(|terms| Term::from(AletheTerm::Op(Operator::RareList, terms.to_vec())))
        //     .collect_vec();
        // vec![ProofStep::Rewrite(None, Term::from("bool-or-false"), args)]
        lambdapi! { rewrite "or_identity_l"; }
    }
}

/// Translate the RARE rule:
/// `(define-rule* bool-and-true ((xs Bool :list) (ys Bool :list)) (and xs true ys) (and xs ys))`
fn translate_bool_and_true(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    let args = args
        .into_iter()
        .map(|term| unwrap_match!(**term, AletheTerm::Op(Operator::RareList, ref l) => l))
        .collect_vec();

    // If `xs` or `ys` rare-list are empty then we can not use the lemma bool-and-true because it expect 2 arguments.
    // we will use the `and_identity_l` or `and_identity_r` in that cases, otherwise we can use bool-and-true.

    if args[0].is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        lambdapi! { rewrite "and_identity_l"; }
    } else if args[1].is_empty() {
        // argument `x` of and_identity_r lemma should be inferred by Lambdapi
        lambdapi! { rewrite "and_identity_r"; }
    } else {
        let args: Vec<Term> = args
            .into_iter()
            .map(|terms| Term::from(AletheTerm::Op(Operator::RareList, terms.to_vec())))
            .collect_vec();
        vec![
            ProofStep::Rewrite(false, None, Term::from("bool-and-true"), args,SubProofs(None)),
            ProofStep::Reflexivity,
        ]
    }
}

fn translate_bool_impl_elim(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(false, None, Term::from("bool-impl-elim"), vec![],SubProofs(None)),
        ProofStep::Reflexivity,
    ]
}

// /// Translate the RARE rule:
// /// `(define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (or xs (or b ys) zs) (or xs b ys zs))`
fn translate_bool_or_flatten(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    let xs = 0;
    let zs = 3;

    let args_len = args
        .iter()
        .map(|term| {
            match_ok!(**term, AletheTerm::Op(Operator::RareList, ref l) => l.len())
                .or_else(|| Some(1))
                .expect("can not convert rare-list")
        })
        .collect_vec();

    if args_len[xs] == 0 {
        lambdapi! {  rewrite "left ∨_assoc";  }
    } else if args_len[zs] == 0 {
        vec![]
    } else {
        let args: Vec<Term> = args.into_iter().map(|term| term.into()).collect_vec();
        vec![
            ProofStep::Rewrite(false, None, Term::from("bool-or-flatten"), args,SubProofs(None)),
            ProofStep::Reflexivity,
        ]
    }
}

// // (define-rule* bool-and-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list)) (and xs (and b ys) zs) (and xs b ys zs))
fn translate_bool_and_flatten(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    let xs = 0;
    let zs = 3;

    let args_len = args
        .iter()
        .map(|term| {
            match_ok!(**term, AletheTerm::Op(Operator::RareList, ref l) => l.len())
                .or_else(|| Some(1))
                .expect("can not convert rare-list")
        })
        .collect_vec();

    if args_len[xs] == 0 {
        lambdapi! {  rewrite "left ∧_assoc";  }
    } else if args_len[zs] == 0 {
        vec![]
    } else {
        let args: Vec<Term> = args.into_iter().map(|term| term.into()).collect_vec();
        vec![
            ProofStep::Rewrite(false, None, Term::from("bool-and-flatten"), args,SubProofs(None)),
            ProofStep::Reflexivity,
        ]
    }
}

pub fn translate_simplify_step(rule: &str) -> Proof {
    match rule {
        "equiv_simplify" => translate_equiv_simplify(),
        "not_simplify" => translate_not_simplify(),
        "implies_simplify" => translate_implies_simplify(),
        "ite_simplify" => translate_ite_simplify(),
        "ac_simp" => translate_ac_simplify(),
        "all_simplify" => Proof(vec![ProofStep::Admit]),
        "bool_simplify" => Proof(vec![ProofStep::Admit]),
        "comp_simplify" => Proof(vec![ProofStep::Admit]),
        r => unimplemented!("{}", r),
    }
}

fn translate_equiv_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᵢ₁";
        simplify;
        eval "equiv_simplify";
    })
}

fn translate_not_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᵢ₁";
        simplify;
        eval "not_simplify";
    })
}

fn translate_implies_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᵢ₁";
        simplify;
        eval "implies_simplify";
    })
}

fn translate_ite_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᵢ₁";
        simplify;
        eval "ite_simplify";
    })
}

fn translate_ac_simplify() -> Proof {
    Proof(lambdapi! {
        apply "∨ᵢ₁";
        try [ rewrite "ac_simp_or"; ];
        try [ rewrite "ac_simp_and";  ];
        reflexivity;
    })
}

fn translate_bool_and_de_morgan(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    if matches!(args.last().unwrap().deref(), AletheTerm::Op(Operator::RareList, ref l) if l.len() == 0)
    {
        vec![apply!(id!("morgan₁"))]
    } else {
        let args_conv: Vec<Term> = args.into_iter().map(|t| Term::from(t)).collect_vec();
        // vec![ProofStep::Apply(
        //     id!("bool-and-de-morgan"),
        //     args_conv,
        //     SubProofs(None),
        // )]
        admit()
    }
}

fn translate_bool_or_de_morgan(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    if matches!(args.last().unwrap().deref(), AletheTerm::Op(Operator::RareList, ref l) if l.len() == 0)
    {
        vec![apply!(id!("morgan₂"))]
    } else {
        let args_conv: Vec<Term> = args.into_iter().map(|t| Term::from(t)).collect_vec();
        // vec![ProofStep::Apply(
        //     id!("bool-or-de-morgan"),
        //     args_conv,
        //     SubProofs(None),
        // )]
        admit()
    }
}
