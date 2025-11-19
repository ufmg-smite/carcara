use try_match::match_ok;

use crate::ast::Constant;

use super::*;

pub fn translate_rare_simp(
    clause: &Vec<Rc<AletheTerm>>,
    args: &Vec<Rc<AletheTerm>>,
    dag_terms: HashSet<String>,
) -> Proof {
    let (rare_rule, args) = args.split_first().unwrap();

    let rule: String =
        unwrap_match!(**rare_rule, crate::ast::Term::Const(Constant::String(ref s)) => s.clone());

    let mut simps: Vec<_> = if dag_terms.len() > 0 {
        dag_terms
            .into_iter()
            .map(|s| ProofStep::Simplify(vec![s.into()]))
            .collect_vec()
    } else {
        vec![]
    };

    let mut rewrites = match rule.as_str() {
        "bool-and-true" => translate_bool_and_true(args),
        "bool-or-false" => translate_bool_or_false(args),
        "bool-or-flatten" => translate_bool_or_flatten(),
        "bool-and-flatten" => translate_bool_and_flatten(args),
        "bool-impl-elim" => translate_bool_impl_elim(args),
        "bool-and-de-morgan" => translate_bool_and_de_morgan(args),
        "bool-or-de-morgan" => translate_bool_or_de_morgan(args),
        "bool-double-not-elim" => translate_bool_double_not_elim(),
        "bool-implies-or-distrib" => translate_bool_implies_or_distrib(args),
        "bool-impl-true1" => translate_bool_imp_true1(),
        "bool-impl-true2" => translate_bool_imp_true2(),
        "bool-impl-false1" => translate_bool_imp_false1(),
        "bool-impl-false2" => translate_bool_imp_false2(),
        "arith-poly-norm" => translate_arith_poly_norm(clause),
        "evaluate" => {
            let cl_first = clause.first().expect("evaluate can not be empty");
            match match_term!((= l r) = cl_first) {
                Some((l, r))
                    if (r.is_bool_false() || r.is_bool_true())
                        && (matches!(l.deref(), AletheTerm::Op(Operator::GreaterEq, _))
                            || matches!(l.deref(), AletheTerm::Op(Operator::LessEq, _))
                            || matches!(l.deref(), AletheTerm::Op(Operator::GreaterThan, _))
                            || matches!(l.deref(), AletheTerm::Op(Operator::LessThan, _))) =>
                {
                    translate_evaluate_linear_arith()
                }
                Some((_l, r)) if (r.is_bool_false() || r.is_bool_true()) => {
                    translate_evaluate_bool()
                }
                Some(_) => translate_evaluate_eq_arith(),
                None => panic!("not well formed evaluate, expected t1 = t2"),
            }
        }
        r => {
            let args = args.into_iter().map(|term| term.into()).collect_vec();
            vec![ProofStep::Apply(Term::from(r), args, SubProofs(None))]
        }
    };

    Proof(lambdapi! {
        apply "∨ᵢ₁";
        inject(simps);
        inject(rewrites);
    })
}

/// (define-rule bool-eq-true ((t Bool)) (= t true) t)
///
/// We translate it into:
/// ```text
/// simplify p_*;
/// rewrite ⊤=;
/// reflexivity;
/// ```
///
/// We simplify `p_*` all shared symbols otherwise the tactic `rewrite` does not work.
fn translate_bool_eq_true(dag_terms: HashSet<String>) -> Vec<ProofStep> {
    let mut proof = vec![];

    if dag_terms.len() > 0 {
        dag_terms
            .into_iter()
            .for_each(|s| proof.push(ProofStep::Simplify(vec![s.into()])));
    }

    proof.push(ProofStep::Rewrite(
        false,
        None,
        "⊤=".into(),
        vec![],
        SubProofs(None),
    ));
    proof.push(ProofStep::Reflexivity);

    proof
}

///(define-rule bool-eq-false ((t Bool)) (= t false) (not t))
///
/// We translate it into:
/// ```text
/// simplify p_*;
/// rewrite ⊥=;
/// reflexivity;
/// ```
///
/// We simplify `p_*` all shared symbols otherwise the tactic `rewrite` does not work.
fn translate_bool_eq_false(dag_terms: HashSet<String>) -> Vec<ProofStep> {
    let mut proof = vec![];

    if dag_terms.len() > 0 {
        dag_terms
            .into_iter()
            .for_each(|s| proof.push(ProofStep::Simplify(vec![s.into()])));
    }

    proof.push(ProofStep::Rewrite(
        false,
        None,
        "⊥=".into(),
        vec![],
        SubProofs(None),
    ));
    proof.push(ProofStep::Reflexivity);

    proof
}

/// (define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))
fn translate_bool_imp_false1() -> Vec<ProofStep> {
    let mut proof = vec![];

    proof.push(ProofStep::Rewrite(
        false,
        None,
        "⇒⊥".into(),
        vec![],
        SubProofs(None),
    ));
    proof.push(ProofStep::Reflexivity);

    proof
}

/// (define-rule bool-impl-false2 ((t Bool)) (=> false t) true)
fn translate_bool_imp_false2() -> Vec<ProofStep> {
    let mut proof = vec![];

    proof.push(ProofStep::Rewrite(
        false,
        None,
        "⊥⇒".into(),
        vec![],
        SubProofs(None),
    ));
    proof.push(ProofStep::Reflexivity);

    proof
}

/// (define-rule bool-impl-true1 ((t Bool)) (=> t true) true)
fn translate_bool_imp_true1() -> Vec<ProofStep> {
    let mut proof = vec![];

    proof.push(ProofStep::Rewrite(
        false,
        None,
        "⇒⊤".into(),
        vec![],
        SubProofs(None),
    ));
    proof.push(ProofStep::Reflexivity);

    proof
}

/// (define-rule bool-impl-true2 ((t Bool)) (=> true t) t)
fn translate_bool_imp_true2() -> Vec<ProofStep> {
    let mut proof = vec![];

    proof.push(ProofStep::Rewrite(
        false,
        None,
        "⊤⇒".into(),
        vec![],
        SubProofs(None),
    ));
    proof.push(ProofStep::Reflexivity);

    proof
}

/// (define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)
///
/// We translate it into:
/// ```text
/// simplify p_*;
/// rewrite ¬¬ₑ_eq;
/// reflexivity;
/// ```
///
/// We simplify `p_*` all shared symbols otherwise the tactic `rewrite` does not work.
fn translate_bool_double_not_elim() -> Vec<ProofStep> {
    let mut proof = vec![];

    proof.push(ProofStep::Rewrite(
        false,
        None,
        "¬¬ₑ_eq".into(),
        vec![],
        SubProofs(None),
    ));
    proof.push(ProofStep::Reflexivity);

    proof
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

/// In Alethe, arith_poly_norm is the arithmetical polynomial normalization rule.
/// It is used to justify steps where an arithmetic expression (a polynomial over integers, rationals, or reals) is rewritten into a canonical, normalized polynomial form. This usually involves:
///   * Flattening nested additions and multiplications
///   * Sorting terms in a fixed order (e.g., lexicographically by variable)
///   * Combining like terms (e.g., 2x + 3x → 5x)
///   * Normalizing coefficients (for rationals, ensuring a canonical denominator)
///   * Eliminating redundant constants or zero terms (e.g., x + 0 → x)
/// So, if a proof line in Alethe has justification `:rule arith_poly_norm`, it means the term was transformed into its canonical polynomial representation.
/// This ensures that arithmetic equalities like:
/// ```
/// (x + 1) + (2*x - 3) ≡ 3*x - 2
/// ```
///
/// We then would like to produce the script that re-use the normalise for `la_generic``.
/// Note that we need to reify left side first to re-use the reification map for the right side.
/// Otherwise, we can not prove the equality of expression such as `x + y ≡ y + x` because the reification map would be different (l = [x |-> 0, x |-> 1], r = [x |-> 1, x |-> 0]).
///
/// ```
/// have t50_t3 : π̇ (e1 = e2) ⟇ ▩) {
///     apply ∨ᵢ₁;
///     rewrite left  .[x in x = _] reify_correct;
///     set l ≔ (reify e1);
///     rewrite .[x in val x = _] eta_prod;
///     rewrite left .[x in _ = x] (reify_correct_withenv (l ₂));
///     rewrite .[x in _ = val x] eta_prod;
///     rewrite left .[x in x = _] norm_correct;
///     rewrite left .[x in _ = x] norm_correct;
///     reflexivity;
/// };
/// ```
fn translate_arith_poly_norm(clause: &Vec<Rc<AletheTerm>>) -> Vec<ProofStep> {
    let mut proof = vec![];

    let l_set_id = "l";

    // Encode: rewrite left  .[x in x = _] reify_correct;
    proof.push(ProofStep::Rewrite(
        true,
        Some("[x in x = _]".into()),
        Term::from("reify_correct"),
        vec![],
        SubProofs(None),
    ));

    // Encode: set l ≔ (reify e1);
    let (left, _) = match_term!((= l r) = clause[0]).expect("no equality");
    let e1: Term = Term::Terms(vec!["reify".into(), left.into()]);
    proof.push(ProofStep::Set(l_set_id.to_string(), e1));

    // Encode: rewrite .[x in val x = _] eta_prod;
    proof.push(ProofStep::Rewrite(
        false,
        Some("[x in val x = _]".into()),
        Term::from("eta_prod"),
        vec![],
        SubProofs(None),
    ));

    // Encode: rewrite left .[x in _ = x] (reify_correct_withenv (l ₂));
    proof.push(ProofStep::Rewrite(
        true,
        Some("[x in _ = x]".into()),
        Term::from("reify_correct_withenv"),
        vec![Term::from(format!("({} ₂)", l_set_id))],
        SubProofs(None),
    ));

    // Encode: rewrite .[x in _ = val x] eta_prod;
    proof.push(ProofStep::Rewrite(
        false,
        Some("[x in _ = val x]".into()),
        Term::from("eta_prod"),
        vec![],
        SubProofs(None),
    ));

    // Encode: rewrite left  .[x in x = _] norm_correct;
    proof.push(ProofStep::Rewrite(
        true,
        Some("[x in x = _]".into()),
        Term::from("norm_correct"),
        vec![],
        SubProofs(None),
    ));

    // Encode: rewrite left  .[x in _ = x] norm_correct;
    proof.push(ProofStep::Rewrite(
        true,
        Some("[x in _ = x]".into()),
        Term::from("norm_correct"),
        vec![],
        SubProofs(None),
    ));

    // Encode: reflexivity;
    proof.push(ProofStep::Reflexivity);

    proof
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
            ProofStep::Rewrite(
                false,
                None,
                Term::from("bool-and-true"),
                args,
                SubProofs(None),
            ),
            ProofStep::Reflexivity,
        ]
    }
}

fn translate_bool_impl_elim(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    vec![
        ProofStep::Rewrite(
            false,
            None,
            Term::from("bool-impl-elim"),
            vec![],
            SubProofs(None),
        ),
        ProofStep::Reflexivity,
    ]
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
            ProofStep::Rewrite(
                false,
                None,
                Term::from("bool-and-flatten"),
                args,
                SubProofs(None),
            ),
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

/// (define-rule* bool-and-de-morgan ((x Bool) (y Bool) (zs Bool :list))
///   (not (and x y zs))
///   (not (and y zs))
///   (or (not x) _))
///
/// eval #repeat (#rewrite morgan1);
///
/// We ignore arguments for this rule and take benefits of metatactics in Lambdapi.
fn translate_bool_and_de_morgan(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    vec![
        ProofStep::Eval(Term::Terms(vec![
            "#repeat".into(),
            "#rewrite".into(),
            "morgan1".into(),
        ])),
        ProofStep::Reflexivity,
    ]
}

/// ```text
/// (define-rule* bool-or-de-morgan ((x Bool) (y Bool) (zs Bool :list))
///   (not (or x y zs))
///   (not (or y zs))
///   (and (not x) _))
/// ```
///
/// Translate into:
/// `eval #repeat (#rewrite morgan1);`
///
/// We ignore arguments for this rule and take benefits of metatactics in Lambdapi.
fn translate_bool_or_de_morgan(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    vec![
        ProofStep::Eval(Term::Terms(vec![
            "#repeat".into(),
            "#rewrite".into(),
            "morgan2".into(),
        ])),
        ProofStep::Reflexivity,
    ]
}

/// ```text
/// (define-rule* bool-or-flatten ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list))
///     (or xs (or b ys) zs)
///     (or xs b ys zs))
/// ```
///
/// Translate into:
/// `eval #repeat (#rewrite morgan1);`
///
/// We ignore arguments for this rule and take benefits of metatactics in Lambdapi.
fn translate_bool_or_flatten() -> Vec<ProofStep> {
    vec![
        ProofStep::Eval(Term::Terms(vec![
            "#repeat".into(),
            "#rewrite".into(),
            "∨_assoc".into(),
        ])),
        ProofStep::Reflexivity,
    ]
}

/// ```text
///  (define-rule* bool-implies-or-distrib
///  ((y1 Bool) (y2 Bool) (ys Bool :list) (z Bool))
///      (=> (or y1 y2 ys) z)
///      (=> (or y2 ys) z)
///      (and (=> y1 z) _))
/// ```
fn translate_bool_implies_or_distrib(args: &[Rc<AletheTerm>]) -> Vec<ProofStep> {
    let mut proof = vec![];

    let y1: Term = args[0].clone().into();
    let y2: Term = args[1].clone().into();
    let ys = unwrap_match!(*args[2], AletheTerm::Op(Operator::RareList, ref l) => l);

    if ys.is_empty() {
        // argument `x` of and_identity_l lemma should be inferred by Lambdapi
        proof.push(ProofStep::Rewrite(
            false,
            None,
            "bool_implies_or_distrib".into(),
            vec![y1, y2],
            SubProofs(None),
        ));
    } else {
        let ys_term: Term = Term::from(AletheTerm::Op(Operator::RareList, ys.to_vec()));
        proof.push(ProofStep::Rewrite(
            false,
            None,
            "bool_implies_or_distrib_rec".into(),
            vec![y1, y2, ys_term],
            SubProofs(None),
        ));
    }

    proof.push(ProofStep::Reflexivity);

    proof
}
