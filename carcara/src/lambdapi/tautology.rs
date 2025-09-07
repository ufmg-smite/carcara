use super::*;
use crate::ast::{Constant, Operator, Rc, Term as AletheTerm};
use std::ops::Deref;

/// Generate the proof term for the rule `trans` e.g.
/// ```text
///  (assume h1 (= a b))
///  (assume h2 (= b c))
///  (assume h3 (= c d))
/// (step ti (cl (= a d)) :rule trans :premises (h1 h2 h3))
/// ```
///
/// sConstruct a proof term that compose n-1 application of the lemma `trans`
/// where n is the cardinality of the premises set. Given our example, we will
/// translate this proof step `ti` into `apply trans (h1 trans (h2 h3))`.
///
pub fn translate_trans(premises: &mut Vec<(String, &[Rc<AletheTerm>])>) -> TradResult<Proof> {
    // The elaborator can sometime optimise useless transitivity leting only a single hypothesis
    if premises.len() == 1 {
        let (premise_name, _) = premises.first().unwrap();
        return Ok(Proof(lambdapi! {
            apply @(premise_name);
        }));
    }

    let tn_t_succ_n = premises.drain(premises.len() - 2..).take(2).collect_vec();

    let first_trans = Term::Terms(vec![
        Term::from("trans"),
        Term::from(tn_t_succ_n[0].0.as_str()),
        Term::from(tn_t_succ_n[1].0.as_str()),
    ]);

    let proofterm = premises.into_iter().rev().fold(first_trans, |mut acc, p| {
        acc = Term::Terms(vec![Term::from("trans"), Term::from(p.0.as_str()), acc]);
        acc
    });

    let proofstep = vec![ProofStep::Apply(proofterm, vec![], SubProofs(None))];

    Ok(Proof(proofstep))
}

/// Construct the proof term for the rule `false`
/// ```text
/// (step ti (cl (not false)) :rule false)
/// ```
/// we directly apply the lemma `neg_⊥`.
///
///
pub fn translate_false() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        refine "neg_⊥";
    }))
}

/// Construct the proof term for the rule `implies`.
///
/// ```text
/// (assume h1 (=> a b))
/// (step t2 (cl (not a) b) :rule implies :premises (h1))
/// ```
///
/// We generate a proof term that use the lemma `implies` with the premise as parameter.
/// Following our example we should obtain: `apply (implies h1)`.
///
pub fn translate_implies(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "implies" (@unary_clause_to_prf(premise));
    }))
}

/// Construct the proof term for the rule `implies`.
///
/// ```text
/// (assume h1 (not (=> a b)))
/// (step t1 (cl a) :rule not_implies1 :premises (h1))
/// ```
///
/// We apply the direct corresponding lemma
///
pub fn translate_not_implies1(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "not_implies1" (@unary_clause_to_prf(premise));
    }))
}

/// Construct the proof term for the rule `implies`.
///
/// ```text
/// (assume h1 (not (=> a b)))
/// (step t1 (cl (not b)) :rule not_implies2 :premises (h1))
/// ```
///
/// We apply the direct corresponding lemma `not_implies2`
///
pub fn translate_not_implies2(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "not_implies2" (@unary_clause_to_prf(premise));
    }))
}

pub fn translate_refl() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        reflexivity;
    }))
}

pub fn translate_sym(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        symmetry;
        apply @unary_clause_to_prf(premise);
    }))
}

pub fn translate_not_symm(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        apply "not_symm" (@unary_clause_to_prf(premise));
    }))
}

/// Rule 30: and
/// 𝑖. ⊳  𝜑0 ∧ ⋯ ∧ 𝜑n (...)
/// 𝑗. ⊳  𝜑n          (and 𝑖) k
///
///
/// ```text
/// refine ∧ₑₙ k (𝜑0 ⸬ ... ⸬ 𝜑𝑛 ⸬ □) ⊤ᵢ i
/// ```
pub fn translate_and(
    premise: &(String, &[Rc<AletheTerm>]),
    args: &Vec<Rc<AletheTerm>>,
) -> TradResult<Proof> {
    //let mut proof = vec![];

    // position of 𝜑𝑘 in sequent i. ▷ ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛)
    let k = Term::Nat(
        args[0]
            .as_usize_err()
            .expect("missing index 𝑘 in :args")
            .try_into()
            .unwrap(),
    );

    // get 𝜑0 ∧ ⋯ ∧ 𝜑n from i
    let conj_list = Term::Alethe(LTerm::List(List(
        match_term_err!((and ...) = premise.1.first().unwrap())
            .unwrap()
            .iter()
            .rev()
            .map(|t| t.into())
            .collect_vec(),
    )));

    let premise_id = premise.0.to_string().into(); // i

    Ok(Proof(vec![ProofStep::Refine(
        "∧ₑₙ".into(),
        vec![k, conj_list, intro_top(), premise_id],
        SubProofs(None),
    )]))

    // Ok(Proof(vec![apply!("∨ᵢ₁".into()), projections]))
}

/// Rule not_or:
/// i. ▷ ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛)
/// j. ▷ ¬𝜑𝑘
///
/// We solve this with this script:
/// ```text
/// refine not_or Stdlib.Nat._1 (𝜑1 ⸬ ... ⸬ 𝜑𝑛 ⸬ □)) ⊤ᵢ _;
/// simplify;
/// refine fold_⇒ _;
/// eval #repeat_or_id_r;
/// refine (π̇ₗ Goal);
/// ```
pub fn translate_not_or(
    premise: &(String, &[Rc<AletheTerm>]),
    args: &Vec<Rc<AletheTerm>>,
) -> TradResult<Proof> {
    let mut proof = vec![];

    // position of 𝜑𝑘 in sequent i. ▷ ¬(𝜑1 ∨ ⋯ ∨ 𝜑𝑛)
    let k = Term::Nat(
        args[0]
            .as_usize_err()
            .expect("missing index 𝑘 in :args")
            .try_into()
            .unwrap(),
    );

    // get 𝜑1 ∨ ⋯ ∨ 𝜑𝑛 from i
    let disj_list = List(
        match_term_err!((not (or ...)) = premise.1.first().unwrap())
            .unwrap()
            .iter()
            .rev()
            .map(|t| t.into())
            .collect_vec(),
    );

    proof.push(ProofStep::Refine(
        "not_or".into(),
        vec![
            k,
            Term::Alethe(LTerm::List((disj_list))),
            intro_top(),
            underscore!(),
        ],
        SubProofs(None),
    ));

    proof.push(ProofStep::Simplify(vec![]));

    proof.push(ProofStep::Refine(
        "fold_⇒".into(),
        vec![underscore!()],
        SubProofs(None),
    ));

    proof.push(ProofStep::Eval("#repeat_or_id_r".into()));

    proof.push(ProofStep::Refine(
        unary_clause_to_prf(&premise.0),
        vec![],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

/// Rule 32: or
/// transform a disjunction into a clause
/// 𝑖. ⊳ 𝜑1 ∨ ... ∨ 𝜑n    (...)
/// j. 𝜑1 , ... , 𝜑n.     (or i)
///
/// But in our case i will have the form `(𝜑1 ∨ ... ∨ 𝜑n) ⟇ ▩`
///
/// ```text
/// refine ∨ₑₙ (𝜑0 ⸬ ... ⸬ 𝜑𝑛 ⸬ □) _
/// simplify;
/// eval #repeat_or_id_r;
/// apply (π̇ₗ i)
/// ```
#[inline]
pub fn translate_or(premise: &(String, &[Rc<AletheTerm>])) -> TradResult<Proof> {
    let mut proof = vec![];

    // get 𝜑1 ∨ ⋯ ∨ 𝜑𝑛 from i
    let disj_list = Term::Alethe(LTerm::List(List(
        match_term_err!((or ...) = premise.1.first().unwrap())
            .unwrap()
            .iter()
            .rev()
            .map(|t| t.into())
            .collect_vec(),
    )));

    let i =  unary_clause_to_prf(premise.0.as_ref());

    proof.push(ProofStep::Refine(
        "∨ₑₙ".into(),
        vec![disj_list, underscore!()],
        SubProofs(None),
    ));

    proof.push(ProofStep::Simplify(vec![]));
    proof.push(ProofStep::Eval(Term::from("#repeat_or_id_r")));
    proof.push(ProofStep::Refine(i,vec![] ,SubProofs(None)));

    Ok(Proof(proof))
}

/// Rule not_and
/// i. ▷ ¬(𝜑1 ∧ … ∧ 𝜑𝑛)
/// j. ▷ ¬𝜑1, … , ¬𝜑𝑛
///
/// We want to produce the script:
///
///```
/// refine not_and (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) (π̇ₗ i);
///```
pub fn translate_not_and(clause: &[Rc<AletheTerm>], premise: &str) -> TradResult<Proof> {
    let mut proof = vec![];

    // collect the list 𝜑1, ... 𝜑𝑛 from the clause ¬𝜑1, … , ¬𝜑𝑛
    let conj_list = List(
        clause
            .iter()
            .rev()
            .map(|t| {
                let phi = match_term_err!((not phi) = t).unwrap();
                phi.into()
            })
            .collect_vec(),
    );

    proof.push(ProofStep::Refine(
        Term::from("not_and"),
        vec![
            Term::Alethe(LTerm::List(conj_list)),
            unary_clause_to_prf(premise),
        ],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

/// Rule (𝜑1 ∧ ⋯ ∧ 𝜑𝑛), ¬𝜑1, … , ¬𝜑𝑛
/// we want to produce the script:
/// ```
/// refine and_neg (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) _;
/// simplify;
/// eval #repeat_or_id_r;
/// reflexivity
/// ```
pub fn translate_and_neg(clause: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut proof = vec![];

    // values 𝜑1 ∧ ⋯ ∧ 𝜑𝑛 as List
    let conj_list = unwrap_match!(clause[0].deref(), AletheTerm::Op(Operator::And, e) => {
        List(e.iter().rev().map(|t| t.into()).collect_vec())
    });

    proof.push(ProofStep::Refine(
        Term::TermId("and_neg".into()),
        vec![Term::Alethe(LTerm::List(conj_list)), Term::Underscore],
        SubProofs(None),
    ));
    proof.push(ProofStep::Simplify(vec![]));
    proof.push(ProofStep::Eval(Term::from("#repeat_or_id_r")));
    proof.push(ProofStep::Reflexivity);
    Ok(Proof(proof))
}

/// Rule and_pos: ¬(𝜑1 ∧ … ∧ 𝜑𝑛), 𝜑𝑘
/// we want to produce the script:
/// ```
/// refine and_pos k (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) ⊤ᵢ;
/// ```
pub fn translate_and_pos(
    clause: &[Rc<AletheTerm>],
    args: &Vec<Rc<AletheTerm>>,
) -> TradResult<Proof> {
    let mut proof = vec![];

    let conj_list = List(
        match_term_err!((not (and ...)) = &clause[0])
            .unwrap()
            .iter()
            .rev()
            .map(|t| t.into())
            .collect_vec(),
    );

    let k = args[0].as_usize_err().unwrap();

    proof.push(ProofStep::Refine(
        Term::from("and_pos"),
        vec![
            Term::Nat(k as u32),
            Term::Alethe(LTerm::List(conj_list)),
            intro_top(),
        ],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

/// Rule  or_neg (𝜑1 ∨ … ∨ 𝜑𝑛), ¬ 𝜑𝑘
/// we want to produce the script:
/// ```
/// apply sym_clause;
/// refine or_neg k (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) _ ⊤ᵢ;
/// simplify;
/// eval #repeat_or_id_r;
/// reflexivity
/// ```
pub fn translate_or_neg(
    clause: &[Rc<AletheTerm>],
    args: &Vec<Rc<AletheTerm>>,
) -> TradResult<Proof> {
    let mut proof = vec![];

    let disj_list = List(
        match_term_err!((or ...) = &clause[0])
            .unwrap()
            .iter()
            .rev()
            .map(|t| t.into())
            .collect_vec(),
    );

    let k = args[0].as_usize_err().unwrap();

    proof.push(ProofStep::Apply(
        Term::from("sym_clause"),
        vec![],
        SubProofs(None),
    ));

    proof.push(ProofStep::Refine(
        Term::from("or_neg"),
        vec![
            Term::Nat(k as u32),
            Term::Alethe(LTerm::List(disj_list)),
            Term::Underscore,
            intro_top(),
        ],
        SubProofs(None),
    ));

    proof.push(ProofStep::Simplify(vec![]));
    proof.push(ProofStep::Eval(Term::from("#repeat_or_id_r")));

    proof.push(ProofStep::Reflexivity);

    Ok(Proof(proof))
}

#[inline]
pub fn translate_auto_rewrite(rule: &str) -> TradResult<Proof> {
    Ok(Proof(vec![
        ProofStep::Apply(Term::TermId(rule.into()), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]))
}

fn propositional_or_cong(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    fn cong_tree(premises: &[(String, &[Rc<AletheTerm>])]) -> Proof {
        match premises.split_first() {
            Some((p, rest)) if !rest.is_empty() => {
                let p_proof = Proof(vec![ProofStep::Apply(
                    Term::from(p.0.as_str()),
                    vec![],
                    SubProofs(None),
                )]);
                Proof(vec![ProofStep::Apply(
                    Term::from("cong_or"),
                    vec![],
                    SubProofs(Some(vec![p_proof, cong_tree(rest)])),
                )])
            }
            Some((p, [])) => Proof(vec![ProofStep::Apply(
                Term::from(p.0.as_str()),
                vec![],
                SubProofs(None),
            )]),
            _ => unreachable!("we should stop when rest is empty"),
        }
    }

    Ok(cong_tree(premises))
}

fn propositional_and_cong(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    fn cong_tree(premises: &[(String, &[Rc<AletheTerm>])]) -> Proof {
        match premises.split_first() {
            Some((p, rest)) if !rest.is_empty() => {
                let p_proof = Proof(vec![ProofStep::Apply(
                    Term::from(p.0.as_str()),
                    vec![],
                    SubProofs(None),
                )]);
                Proof(vec![ProofStep::Apply(
                    Term::from("cong_and"),
                    vec![],
                    SubProofs(Some(vec![p_proof, cong_tree(rest)])),
                )])
            }
            Some((p, [])) => Proof(vec![ProofStep::Apply(
                Term::from(p.0.as_str()),
                vec![],
                SubProofs(None),
            )]),
            _ => unreachable!("we should stop when rest is empty"),
        }
    }

    Ok(cong_tree(premises))
}

fn ite_cong(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    let premises = premises
        .into_iter()
        .map(|p| unary_clause_to_prf(p.0.as_str()))
        .collect_vec();

    Ok(proof!(ProofStep::Apply(
        "ite_cong".into(),
        premises,
        SubProofs(None)
    )))
}

fn propositional_cong(
    symbol: Term,
    arity: usize,
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    if arity == 1 {
        let premise = premises
            .first()
            .map(|p| unary_clause_to_prf(p.0.as_str()))
            .expect("Missing premise");

        Ok(Proof(lambdapi! {
            apply "∨ᵢ₁";
            inject(vec![ProofStep::Apply(Term::from("feq"), vec![ symbol, premise ], SubProofs(None))]);
        }))
    } else {
        match symbol {
            Term::TermId(s) if s == "(∨)" => propositional_or_cong(premises),
            Term::TermId(s) if s == "(∧)" => propositional_and_cong(premises),
            _ => {
                // Case `iff`, `=>` ...
                let premises_rev = premises.iter().rev().collect_vec();
                let (left, right) = premises_rev.split_at(2);

                let feq_first = Term::Terms(vec![
                    Term::from("feq2"),
                    symbol.clone(),
                    unary_clause_to_prf(left[1].0.as_str()),
                    unary_clause_to_prf(left[0].0.as_str()),
                ]);

                let feq = right.into_iter().fold(feq_first, |acc, (hyp, _)| {
                    Term::Terms(vec![
                        Term::from("feq2"),
                        symbol.clone(),
                        unary_clause_to_prf(hyp),
                        acc,
                    ])
                });

                Ok(Proof(lambdapi! {
                    apply "∨ᵢ₁";
                    inject(vec![ProofStep::Apply(feq, vec![], SubProofs(None))]);
                }))
            }
        }
    }
}

fn application_cong(
    symbol: Term,
    arity: usize,
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    let feq_name = if arity > 1 {
        Term::from(format!("feq{}", arity))
    } else {
        Term::from("feq")
    };

    let mut args = vec![symbol];

    let mut hyps = premises
        .into_iter()
        .map(|p| unary_clause_to_prf(p.0.as_str()))
        .collect_vec();

    args.append(&mut hyps);

    let feq = ProofStep::Apply(feq_name, args, SubProofs(None));

    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        inject(vec![feq]);
    }))
}

/// Construct the proof term for the rule `cong`
/// The cong rule is applied on any n-ary function symbol `f` of appropriate sort.
/// Therefore, first we collect information about the sort of `f`, its arguments and its arity by looking at the clause and number of premises.
/// The application of cong on f: A₁ ... Aₙ → Set` are translated with the lemma feqₙ where `n` is the arity of `f`.
/// The application of cong on `or` and `and` operator are translated by composing the lemma `cong_or` (`cong_and` respectively).
/// For the operators `(imp a b)` and `(not a)` we apply the lemma feq₂ and (`feq` respectively) since we can quantify over propositions with `ο`.
pub fn translate_cong(
    clause: &[Rc<AletheTerm>],
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    let (operator, symbol, arity) = unwrap_match!(clause[0].deref(), AletheTerm::Op(Operator::Equals, ts) => {
        match (&*ts[0], &*ts[1]) {
            (AletheTerm::App(f, args) , AletheTerm::App(g, _)) if f == g => (None, Term::from((*f).clone()),  args.len()),
            (AletheTerm::Op(f, args) , AletheTerm::Op(g, _)) if f == g => (Some(f), Term::from(*f), args.len()),
            _ => unreachable!()
        }
    });

    if matches!(operator, Some(Operator::Ite)) {
        ite_cong(premises)
    } else if operator.is_some() {
        propositional_cong(symbol, arity, premises)
    } else {
        application_cong(symbol, arity, premises)
    }
}

/// Translate the rule ite1
/// ```text
/// i. ▷ (ite 𝜑1 𝜑2 𝜑3)
/// j. ▷ 𝜑1, 𝜑3
/// ```
/// Since 𝜑2 does not appear in `j` clause we need to pass
///
pub fn translate_ite1(premise: &(String, &[Rc<AletheTerm>])) -> TradResult<Proof> {
    let term_ite = premise.1.first().expect("could not find ite term");
    if let [_c, t, _e, ..] =
        unwrap_match!(term_ite.deref(), AletheTerm::Op(Operator::Ite, cte) => cte.as_slice() )
    {
        Ok(proof!(
            apply!("ite1".into(), { underscore!(), t.into() , underscore!(), unary_clause_to_prf(&premise.0) } )
        ))
    } else {
        Err(TranslatorError::PremisesError)
    }
}

/// Translate the rule ite2:
/// ```text
/// i. ▷ (ite 𝜑1 𝜑2 𝜑3)
/// j. ▷ ¬ 𝜑1, 𝜑2
/// ```
///
pub fn translate_ite2(premise: &(String, &[Rc<AletheTerm>])) -> TradResult<Proof> {
    let term_ite = premise.1.first().expect("could not find ite term");
    if let [_c, _t, e, ..] =
        unwrap_match!(term_ite.deref(), AletheTerm::Op(Operator::Ite, cte) => cte.as_slice() )
    {
        Ok(proof!(
            apply!("ite2".into(), { underscore!(), underscore!(), e.into(), unary_clause_to_prf(&premise.0) } )
        ))
    } else {
        Err(TranslatorError::PremisesError)
    }
}

pub fn translate_simple_tautology(
    rule: &str,
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    Ok(Proof(vec![ProofStep::Apply(
        translate_rule_name(rule),
        premises
            .into_iter()
            .map(|(name, _)| Term::TermId(name.to_string()))
            .collect_vec(),
        SubProofs(None),
    )]))
}

/// Construct the proof term to validate forall_inst rule.
/// Considering the example below:
/// ```text
/// (step tᵢ (cl (or (not (forall ((x S) (y T)) (P y x )))
/// (P b (f a))
/// :rule forall_inst :args ((f a) b)
/// ```
///
/// We will translate `forall_inst` changing the or (not a) b into an implication.
/// Passing the left handside into the hypothesis and then applying
/// n-|args| times forall eliminator.
///
/// NOTE: The convertion of arguments do not use the context for sharing the symbol for now.
///
/// Thus, the example is translated into the proof script:
/// ```text
/// have tᵢ: (((¬ (`∀ ((x: τ S) (y: τ T)) (P y x ))) ∨ (P b (f a))) ⟇ ▩) {
///     apply ∨ᵢ₁;
///     apply imply_to_or;  
///     assume H;
///     apply H b (f a)
/// }
/// ```
pub fn translate_forall_inst(args: &Vec<Rc<AletheTerm>>) -> TradResult<Proof> {
    let mut hyp = vec![Term::from("H")];

    hyp.append(&mut args.into_iter().map(Term::from).collect_vec());

    let mut forall_elims = Term::Terms(hyp);

    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        apply "imply_to_or";
        assume [H]; //FIXME: use hyp instead
        refine (forall_elims);
    }))
}

pub fn translate_sko_forall() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        apply "sko_forall";
        assume [x H];
        rewrite "H";
        reflexivity;
    }))
}

#[cfg(test)]
mod tests_tautolog {
    use super::*;
    use crate::lambdapi::test_macros::*;
    use crate::parser::{self, parse_instance};

    #[test]
    fn test_transitivity_translation() {
        let problem: &[u8] = b"
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun d () T)
            (declare-fun e () T)
        ";
        let proof = b"
            (assume h1 (= a b))
            (assume h2 (= b c))
            (assume h3 (= c d))
            (step t1 (cl (= a d)) :rule trans :premises (h1 h2 h3))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(4, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate trans");

        assert_eq!(4, res.len());

        let t1 = res.last().unwrap().clone();

        assert_eq!(
            t1,
            Command::Symbol(
                None,
                "t1".into(),
                vec![],
                cl!(eq!(bid!("a"), bid!("d"))),
                Some(proof!(apply!(terms!(
                    id!("trans"),
                    id!("h1"),
                    terms!(id!("trans"), id!("h2"), id!("h3"))
                ))))
            )
        );
    }

    #[test]
    fn test_cong_or_translation() {
        let problem: &[u8] = b"
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
            (declare-fun e () Bool)
            (declare-fun f () Bool)
            (declare-fun g () Bool)
            (declare-fun h () Bool)
        ";
        let proof = b"
            (assume h1 (= a e))
            (assume h2 (= b f))
            (assume h3 (= c g))
            (assume h4 (= d h))
            (step t3 (cl (= (or a b c d) (or e f g h))) :rule cong :premises (h1 h2 h3 h4))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(5, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate cong");

        assert_eq!(5, res.len());

        let t3 = res.last().unwrap().clone();

        let cmd = Command::Symbol(
            None,
            "t3".into(),
            vec![],
            cl!(eq!(
                or![id!("a"), id!("b"), id!("c"), id!("d"),],
                or![id!("e"), id!("f"), id!("g"), id!("h"),]
            )),
            Some(proof!(apply!(
                cong_or,
                {},
                [
                    apply!(h1),
                    apply!(
                        cong_or,
                        {},
                        [apply!(h2), apply!(cong_or, {}, [apply!(h3), apply!(h4)]),]
                    )
                ]
            ))),
        );

        assert_eq!(t3, cmd);
    }

    #[test]
    fn test_cong_and_translation() {
        let problem: &[u8] = b"
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
            (declare-fun e () Bool)
            (declare-fun f () Bool)
            (declare-fun g () Bool)
            (declare-fun h () Bool)
        ";
        let proof = b"
            (assume h1 (= a e))
            (assume h2 (= b f))
            (assume h3 (= c g))
            (assume h4 (= d h))
            (step t3 (cl (= (and a b c d) (and e f g h))) :rule cong :premises (h1 h2 h3 h4))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(5, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate cong");

        assert_eq!(5, res.len());

        let t3 = res.last().unwrap().clone();

        let cmd = Command::Symbol(
            None,
            "t3".into(),
            vec![],
            cl!(eq!(
                and![id!("a"), id!("b"), id!("c"), id!("d"),],
                and![id!("e"), id!("f"), id!("g"), id!("h"),]
            )),
            Some(proof!(apply!(
                cong_and,
                {},
                [
                    apply!(h1),
                    apply!(
                        cong_and,
                        {},
                        [apply!(h2), apply!(cong_and, {}, [apply!(h3), apply!(h4)]),]
                    )
                ]
            ))),
        );

        assert_eq!(t3, cmd);
    }

    #[test]
    fn test_cong_not_translation() {
        let problem: &[u8] = b"
            (declare-fun a () Bool)
            (declare-fun b () Bool)
        ";
        let proof = b"
            (assume h1 (= a b))
            (step t3 (cl (= (not a) (not b))) :rule cong :premises (h1))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate cong");

        assert_eq!(2, res.len());

        let t3 = res.last().unwrap().clone();

        let cmd = Command::Symbol(
            None,
            "t3".into(),
            vec![],
            cl!(eq!(not!(id!("a")), not!(id!("b")))),
            Some(proof!(
                apply!(id!("∨ᵢ₁")),
                apply!(
                    id!("feq"),
                    { id!("(¬)"), unary_clause_to_prf("h1") }
                )
            )),
        );

        assert_eq!(t3, cmd);
    }

    #[test]
    fn test_cong_imp_translation() {
        let problem: &[u8] = b"
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
        ";
        let proof = b"
            (assume h1 (= a c))
            (assume h2 (= b d))
            (step t3 (cl (= (=> a b) (=> c d))) :rule cong :premises (h1 h2))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(3, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate cong");

        assert_eq!(3, res.len());

        let t3 = res.last().unwrap().clone();

        let cmd = Command::Symbol(
            None,
            "t3".into(),
            vec![],
            cl!(eq!(imp!(id!("a"), id!("b")), imp!(id!("c"), id!("d")))),
            Some(proof!(
                apply!(id!("∨ᵢ₁")),
                apply!(terms![
                    id!("feq2"),
                    id!("(⇒)"),
                    unary_clause_to_prf("h1"),
                    unary_clause_to_prf("h2")
                ])
            )),
        );

        assert_eq!(t3, cmd);
    }

    #[test]
    fn test_forall_inst_translation() {
        let problem: &[u8] = b"
            (declare-sort S 0)
            (declare-sort T 0)
            (declare-fun a () S)
            (declare-fun b () T)
            (declare-fun f (S) S)
            (declare-fun P (T S) Bool)
        ";
        let proof = b"
            (step t1 (cl (or (not (forall ((x S) (y T)) (P y x ))) (P b (f a)))) :rule forall_inst :args ((f a) b))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(1, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate forall_inst");

        assert_eq!(1, res.len());

        let t1 = res.last().unwrap().clone();

        let cmd_expected = Command::Symbol(
            None,
            "t1".into(),
            vec![],
            cl!(or!(
                not!(forall!(
                    [(id!("x"), tau("S".into())), (id!("y"), tau("T".into()))],
                    Term::Terms(vec![id!("P"), id!("y"), id!("x")])
                )),
                Term::Terms(vec![
                    id!("P"),
                    id!("b"),
                    Term::Terms(vec![id!("f"), id!("a")])
                ])
            )),
            Some(proof!(
                apply!(id!("∨ᵢ₁")),
                apply!(id!("imply_to_or")),
                assume!(H),
                apply!(id!(""), {
                    terms!(id!("H"), terms!(id!("f"), id!("a")), id!("b"),),
                })
            )),
        );

        assert_eq!(t1, cmd_expected);
    }

    #[test]
    fn test_ite1() {
        let problem: &[u8] = b"
            (declare-sort U 0)
            (declare-fun a() U)
            (declare-fun b() U)
            (declare-fun p(U) Bool)
        ";
        let proof = b"
            (step t1 (cl (ite (p a) (= b (ite (p a) b a)) (= a (ite (p a) b a)))) :rule hole)
            (step t2 (cl (p a) (= a (ite (p a) b a))) :rule ite1 :premises (t1))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate forall_inst");

        assert_eq!(2, res.len());

        let t2 = res.last().unwrap().clone();

        let t = eq!(
            id!("b"),
            terms!(id!("ite"), terms!(id!("p"), id!("a")), id!("b"), id!("a"))
        );

        let cmd_expected = Command::Symbol(
            None,
            "t2".into(),
            vec![],
            cl!(
                terms![id!("p"), id!("a")],
                eq!(
                    id!("a"),
                    terms!(id!("ite"), terms!(id!("p"), id!("a")), id!("b"), id!("a"))
                )
            ),
            Some(proof!(
                apply!(id!("ite1"), { underscore!(),  t,  underscore!(), unary_clause_to_prf("t1") } )
            )),
        );

        assert_eq!(t2, cmd_expected);
    }

    #[test]
    fn test_ite2() {
        let problem: &[u8] = b"
            (declare-sort U 0)
            (declare-fun a() U)
            (declare-fun b() U)
            (declare-fun p(U) Bool)
        ";
        let proof = b"
            (step t1 (cl (ite (p a) (= b (ite (p a) b a)) (= a (ite (p a) b a)))) :rule hole)
            (step t2 (cl (not (p a)) (= b (ite (p a) b a))) :rule ite2 :premises (t1))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate forall_inst");

        assert_eq!(2, res.len());

        let t2 = res.last().unwrap().clone();

        let e = eq!(
            id!("a"),
            terms!(id!("ite"), terms!(id!("p"), id!("a")), id!("b"), id!("a"))
        );

        let cmd_expected = Command::Symbol(
            None,
            "t2".into(),
            vec![],
            cl!(
                not!(Term::Terms(vec![id!("p"), id!("a")])),
                eq!(
                    id!("b"),
                    terms!(id!("ite"), terms!(id!("p"), id!("a")), id!("b"), id!("a"))
                )
            ),
            Some(proof!(
                apply!(id!("ite2"), { underscore!(),  underscore!(),  e, unary_clause_to_prf("t1") } )
            )),
        );

        assert_eq!(t2, cmd_expected);
    }

    #[test]
    fn test_and_translation1() {
        let problem: &[u8] = b"
            (declare-sort U 0)
            (declare-fun a() U)
            (declare-fun b() U)
            (declare-fun c() U)
            (declare-fun p(U) Bool)
        ";
        let proof = b"
            (step t1 (cl (and (p a) (p b) (p c))) :rule hole)
            (step t2 (cl (p b)) :rule and :premises (t1) :args (1))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate and");

        assert_eq!(2, res.len());

        let t2 = res.last().unwrap().clone();

        let t1 = unary_clause_to_prf("t1");

        let cmd_expected = Command::Symbol(
            None,
            "t2".into(),
            vec![],
            cl!(terms!(id!("p"), id!("b"))),
            Some(proof!(
                apply!(id!("∨ᵢ₁")),
                apply!(id!("∧ₑ₁"), { terms!(id!("∧ₑ₂"), t1) })
            )),
        );

        assert_eq!(t2, cmd_expected)
    }

    #[test]
    fn test_and_translation2() {
        let problem: &[u8] = b"
            (declare-sort U 0)
            (declare-fun a() U)
            (declare-fun b() U)
            (declare-fun c() U)
            (declare-fun p(U) Bool)
        ";
        let proof = b"
            (step t1 (cl (and (p a) (p b) (p c))) :rule hole)
            (step t2 (cl (p a)) :rule and :premises (t1) :args (0))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate and");

        assert_eq!(2, res.len());

        let t2 = res.last().unwrap().clone();

        let t1 = unary_clause_to_prf("t1");

        let cmd_expected = Command::Symbol(
            None,
            "t2".into(),
            vec![],
            cl!(terms!(id!("p"), id!("a"))),
            Some(proof!(apply!(id!("∨ᵢ₁")), apply!(id!("∧ₑ₁"), { t1 }))),
        );

        assert_eq!(t2, cmd_expected)
    }

    #[test]
    fn test_and_translation3() {
        let problem: &[u8] = b"
            (declare-sort U 0)
            (declare-fun a() U)
            (declare-fun b() U)
            (declare-fun c() U)
            (declare-fun d() U)
            (declare-fun p(U) Bool)
        ";
        let proof = b"
            (step t1 (cl (and (p a) (p b) (p c) (p d))) :rule hole)
            (step t2 (cl (p d)) :rule and :premises (t1) :args (3))
        ";
        let (_, proof, _) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(&mut Context::default(), &mut proof.iter(), |id, t, ps| {
            Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
        })
        .expect("translate and");

        assert_eq!(2, res.len());

        let t2 = res.last().unwrap().clone();

        let t1 = unary_clause_to_prf("t1");

        let cmd_expected = Command::Symbol(
            None,
            "t2".into(),
            vec![],
            cl!(terms!(id!("p"), id!("d"))),
            Some(proof!(
                apply!(id!("∨ᵢ₁")),
                ProofStep::Apply(
                    terms!(
                        id!("∧ₑ₂"),
                        terms!(id!("∧ₑ₂"), terms!(id!("∧ₑ₂"), t1.clone()))
                    ),
                    vec![],
                    SubProofs(None)
                ),
            )),
        );

        assert_eq!(t2, cmd_expected)
    }
}
