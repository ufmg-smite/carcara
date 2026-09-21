// The per-rule handlers deliberately share a uniform fallible signature
// (`TradResult<Proof>`) so the rule dispatch stays regular and handlers can gain real
// error paths (replacing the remaining `todo!`/`expect` panics) without signature churn.
#![allow(clippy::unnecessary_wraps)]

use super::*;
use crate::{
    ast::{Operator, Rc, Term as AletheTerm, match_term_err},
    terms, underscore,
};
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

    let proofterm = premises.iter_mut().rev().fold(first_trans, |mut acc, p| {
        acc = Term::Terms(vec![Term::from("trans"), Term::from(p.0.as_str()), acc]);
        acc
    });

    let proofstep = vec![ProofStep::Apply(proofterm, SubProofs(None))];

    Ok(Proof(proofstep))
}

/// Construct the proof term for the rule `false`
/// ```text
/// (step ti (cl (not false)) :rule false)
/// ```
/// we directly apply the lemma `neg_⊥`.
///
///
/// Translate the `true` rule (▷ ⊤). Without a dedicated case the rule name would resolve to
/// the Boolean constant `true` of Stdlib.Bool instead of a proof of `π ⊤`.
pub fn translate_true() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        refine "⊤ᵢ";
    }))
}

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

/// Rule 12: `not_symm`
/// i. `¬(𝑡1 ≈ 𝑡2)`
/// j. `¬(𝑡2 ≈ 𝑡1)`
///     
///
/// /// is translated into the script:
/// ```text
/// refine not_symm [[i]];
/// ```
pub fn translate_not_symm(premise: &str) -> TradResult<Proof> {
    let mut proof = vec![];
    proof.push(ProofStep::Apply(Term::from("∨ᵢ₁"), SubProofs(None)));
    proof.push(ProofStep::Refine(
        terms![Term::from("not_symm"), ..vec![unary_clause_to_prf(premise)],],
        SubProofs(None),
    ));
    Ok(Proof(proof))
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
    args: &[Rc<AletheTerm>],
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
            .map(std::convert::Into::into)
            .collect_vec(),
    )));

    let premise_id = premise.0.clone().into(); // i

    Ok(Proof(vec![ProofStep::Refine(
        terms!["∧ₑₙ".into(), ..vec![k, conj_list, intro_top(), premise_id],],
        SubProofs(None),
    )]))

    // Ok(Proof(vec![apply!("∨ᵢ₁".into()), projections]))
}

/// Rule `not_or`:
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
    args: &[Rc<AletheTerm>],
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
            .map(std::convert::Into::into)
            .collect_vec(),
    );

    proof.push(ProofStep::Refine(
        terms![
            "not_or".into(),
            ..vec![
                k,
                Term::Alethe(LTerm::List(disj_list)),
                intro_top(),
                underscore!(),
            ]
        ],
        SubProofs(None),
    ));

    proof.push(ProofStep::Simplify(vec![]));

    proof.push(ProofStep::Refine(
        terms!["fold_⇒".into(), ..vec![underscore!()],],
        SubProofs(None),
    ));

    proof.push(ProofStep::Eval("#repeat_or_id_r".into()));

    proof.push(ProofStep::Refine(
        unary_clause_to_prf(&premise.0),
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
            .map(std::convert::Into::into)
            .collect_vec(),
    )));

    let i = unary_clause_to_prf(premise.0.as_ref());

    proof.push(ProofStep::Refine(
        terms!["∨ₑₙ".into(), ..vec![disj_list, underscore!()]],
        SubProofs(None),
    ));

    proof.push(ProofStep::Simplify(vec![]));
    proof.push(ProofStep::Eval(Term::from("#repeat_or_id_r")));
    proof.push(ProofStep::Refine(i, SubProofs(None)));

    Ok(Proof(proof))
}

/// Rule `not_and`
/// i. ▷ ¬(𝜑1 ∧ … ∧ 𝜑𝑛)
/// j. ▷ ¬𝜑1, … , ¬𝜑𝑛
///
/// We want to produce the script:
///
///```text
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
        terms![
            Term::from("not_and"),
            Term::Alethe(LTerm::List(conj_list)),
            unary_clause_to_prf(premise),
        ],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

/// Rule (𝜑1 ∧ ⋯ ∧ 𝜑𝑛), ¬𝜑1, … , ¬𝜑𝑛
/// we want to produce the script:
/// ```text
/// refine and_neg (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) _;
/// simplify;
/// eval #repeat_or_id_r;
/// reflexivity
/// ```
pub fn translate_and_neg(clause: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut proof = vec![];

    // values 𝜑1 ∧ ⋯ ∧ 𝜑𝑛 as List
    let conj_list = unwrap_match!(clause[0].deref(), AletheTerm::Op(Operator::And, e) => {
        List(e.iter().rev().map(std::convert::Into::into).collect_vec())
    });

    proof.push(ProofStep::Refine(
        terms![
            Term::TermId("and_neg".into()),
            ..vec![Term::Alethe(LTerm::List(conj_list)), Term::Underscore],
        ],
        SubProofs(None),
    ));
    proof.push(ProofStep::Simplify(vec![]));
    proof.push(ProofStep::Eval(Term::from("#repeat_or_id_r")));
    proof.push(ProofStep::Reflexivity);
    Ok(Proof(proof))
}

/// Rule `and_pos`: ¬(𝜑1 ∧ … ∧ 𝜑𝑛), 𝜑𝑘
/// we want to produce the script:
/// ```text
/// refine and_pos k (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) ⊤ᵢ;
/// ```
pub fn translate_and_pos(clause: &[Rc<AletheTerm>], args: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut proof = vec![];

    let conj_list = List(
        match_term_err!((not (and ...)) = &clause[0])
            .unwrap()
            .iter()
            .rev()
            .map(std::convert::Into::into)
            .collect_vec(),
    );

    let k = args[0].as_usize_err().unwrap();

    proof.push(ProofStep::Refine(
        terms![
            Term::from("and_pos"),
            ..vec![
                Term::Nat(k as u32),
                Term::Alethe(LTerm::List(conj_list)),
                intro_top(),
            ]
        ],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

/// Rule  `or_neg` (𝜑1 ∨ … ∨ 𝜑𝑛), ¬ 𝜑𝑘
/// we want to produce the script:
/// ```text
/// apply sym_clause;
/// refine or_neg k (𝜑1 ⸬ … ⸬ 𝜑𝑛 ⸬ □) _ ⊤ᵢ;
/// simplify;
/// eval #repeat_or_id_r;
/// reflexivity
/// ```
pub fn translate_or_neg(clause: &[Rc<AletheTerm>], args: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut proof = vec![];

    let disj_list = List(
        match_term_err!((or ...) = &clause[0])
            .unwrap()
            .iter()
            .rev()
            .map(std::convert::Into::into)
            .collect_vec(),
    );

    let k = args[0].as_usize_err().unwrap();

    proof.push(ProofStep::Apply(Term::from("sym_clause"), SubProofs(None)));

    proof.push(ProofStep::Refine(
        terms![
            Term::from("or_neg"),
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

fn propositional_or_cong(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    fn cong_tree(premises: &[(String, &[Rc<AletheTerm>])]) -> Proof {
        match premises.split_first() {
            Some((p, rest)) if !rest.is_empty() => {
                let p_proof = Proof(vec![ProofStep::Apply(
                    Term::from(p.0.as_str()),
                    SubProofs(None),
                )]);
                Proof(vec![ProofStep::Apply(
                    Term::from("cong_or"),
                    SubProofs(Some(vec![p_proof, cong_tree(rest)])),
                )])
            }
            Some((p, [])) => Proof(vec![ProofStep::Apply(
                Term::from(p.0.as_str()),
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
                    SubProofs(None),
                )]);
                Proof(vec![ProofStep::Apply(
                    Term::from("cong_and"),
                    SubProofs(Some(vec![p_proof, cong_tree(rest)])),
                )])
            }
            Some((p, [])) => Proof(vec![ProofStep::Apply(
                Term::from(p.0.as_str()),
                SubProofs(None),
            )]),
            _ => unreachable!("we should stop when rest is empty"),
        }
    }

    Ok(cong_tree(premises))
}

fn ite_cong(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    let premises = premises
        .iter()
        .map(|p| unary_clause_to_prf(p.0.as_str()))
        .collect_vec();

    Ok(proof!(ProofStep::Apply(
        terms!["ite_cong".into(), ..premises,],
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
            inject(vec![ProofStep::Apply(terms![Term::from("feq"), symbol, premise], SubProofs(None))]);
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

                let feq = right.iter().fold(feq_first, |acc, (hyp, _)| {
                    Term::Terms(vec![
                        Term::from("feq2"),
                        symbol.clone(),
                        unary_clause_to_prf(hyp),
                        acc,
                    ])
                });

                Ok(Proof(lambdapi! {
                    apply "∨ᵢ₁";
                    inject(vec![ProofStep::Apply(feq, SubProofs(None))]);
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
        .iter()
        .map(|p| unary_clause_to_prf(p.0.as_str()))
        .collect_vec();

    args.append(&mut hyps);

    let feq = ProofStep::Apply(terms![feq_name, ..args], SubProofs(None));

    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        inject(vec![feq]);
    }))
}

/// Construct the proof term for the rule `cong`
/// The cong rule is applied on any n-ary function symbol `f` of appropriate sort.
/// Therefore, first we collect information about the sort of `f`, its arguments and its arity by looking at the clause and number of premises.
/// The application of cong on `f: A₁ ... Aₙ → Set` are translated with the lemma feqₙ where `n` is the arity of `f`.
/// The application of cong on `or` and `and` operator are translated by composing the lemma `cong_or` (`cong_and` respectively).
/// For the operators `(imp a b)` and `(not a)` we apply the lemma feq₂ and (`feq` respectively) since we can quantify over propositions with `ο`.
pub fn translate_cong(
    clause: &[Rc<AletheTerm>],
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    let (operator, symbol, f_args, g_args) = unwrap_match!(clause[0].deref(), AletheTerm::Op(Operator::Equals, ts) => {
        match (&*ts[0], &*ts[1]) {
            (AletheTerm::App(f, f_args) , AletheTerm::App(g, g_args)) if f == g => (None, Term::from((*f).clone()), f_args, g_args),
            (AletheTerm::Op(f, f_args) , AletheTerm::Op(g, g_args)) if f == g => (Some(f), Term::from(*f), f_args, g_args),
            _ => unreachable!()
        }
    });
    let arity = f_args.len();

    // The Alethe `cong` rule does not require a premise for pairs of arguments that are
    // syntactically equal, and cvc5 omits them. The Lambdapi lemmas expect one proof per
    // argument, so we justify those pairs with local reflexivity hypotheses, pairing the
    // premises with the arguments exactly like the checker does.
    let mut refl_steps = Vec::new();
    let mut full_premises: Vec<(String, &[Rc<AletheTerm>])> = Vec::with_capacity(arity);
    let mut remaining = premises.iter().peekable();
    for (k, (f_arg, g_arg)) in f_args.iter().zip(g_args).enumerate() {
        let justified = remaining.peek().is_some_and(|(_, premise)| {
            premise.first().is_some_and(|t| {
                matches!(t.deref(), AletheTerm::Op(Operator::Equals, ts)
                    if (&ts[0] == f_arg && &ts[1] == g_arg) || (&ts[0] == g_arg && &ts[1] == f_arg))
            })
        });
        if justified || f_arg != g_arg {
            full_premises.push(remaining.next().expect("cong: missing premise").clone());
        } else {
            let name = format!("cong_refl_{}", k);
            let goal = Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(vec![
                Term::Alethe(LTerm::Eq(
                    Box::new(Term::from(f_arg)),
                    Box::new(Term::from(g_arg)),
                )),
            ])))));
            refl_steps.push(ProofStep::Have(
                name.clone(),
                goal,
                lambdapi! {
                    apply "⟇ᵢ₁'";
                    reflexivity;
                },
            ));
            full_premises.push((name, std::slice::from_ref(f_arg)));
        }
    }

    let Proof(cong_steps) = if matches!(operator, Some(Operator::Ite)) {
        ite_cong(&full_premises)?
    } else if operator.is_some() {
        propositional_cong(symbol, arity, &full_premises)?
    } else {
        application_cong(symbol, arity, &full_premises)?
    };

    refl_steps.extend(cong_steps);
    Ok(Proof(refl_steps))
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

/// Translate the cvc5-specific `and_intro` rule: from the unit premises 𝜑1, …, 𝜑n, conclude
/// (and 𝜑1 … 𝜑n). Conjunction is right-nested in Lambdapi, so the proof term is
/// `⟇ᵢ₁' (∧ᵢ (π̇ₗ p1) (∧ᵢ (π̇ₗ p2) (… (π̇ₗ pn))))`.
pub fn translate_and_intro(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    if premises.is_empty() || premises.iter().any(|(_, clause)| clause.len() != 1) {
        return Err(TranslatorError::PremisesError);
    }

    let conjunction = premises
        .iter()
        .rev()
        .map(|(id, _)| unary_clause_to_prf(id))
        .reduce(|acc, premise| terms![Term::from("∧ᵢ"), premise, acc])
        .unwrap();

    Ok(Proof(vec![ProofStep::Refine(
        terms![Term::from("⟇ᵢ₁'"), conjunction],
        SubProofs(None),
    )]))
}

pub fn translate_simple_tautology(
    rule: &str,
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    Ok(Proof(vec![ProofStep::Apply(
        terms![
            translate_rule_name(rule),
            ..premises
                .iter()
                .map(|(name, _)| Term::TermId(name.clone()))
                .collect_vec()
        ],
        SubProofs(None),
    )]))
}

/// Construct the proof term to validate `forall_inst` rule.
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
pub fn translate_forall_inst(args: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut hyp = vec![Term::from("H")];

    hyp.append(&mut args.iter().map(Term::from).collect_vec());

    let forall_elims = Term::Terms(hyp);

    Ok(Proof(lambdapi! {
        apply "∨ᵢ₁";
        apply "imply_to_or";
        assume [H]; //FIXME: use hyp instead
        refine (forall_elims);
    }))
}

pub fn translate_sko_forall() -> TradResult<Proof> {
    // Ok(Proof(lambdapi! {
    //     apply "∨ᵢ₁";
    //     apply "sko_forall";
    //     assume [x H];
    //     rewrite "H";
    //     reflexivity;
    // }))
    Ok(Proof(admit()))
}

/// Rule 9 contraction:
///```text
/// 𝑖. ⊳ 𝑙1, ... , 𝑙n    (...)
/// 𝑗. ⊳  𝑙𝑘1, ... , 𝑙kn (contraction i)
///```
///
/// Removes duplicated literal and does not reorder the literals.
///
/// ```text
///   assume we have i: π̇ (𝑙𝑘1, ... , 𝑙kn)
///
///   have H : π (⟇_to_∨_rw 𝑙1, ... , 𝑙n = ⟇_to_∨_rw 𝑙𝑘1, ... , 𝑙kn) {
///     set r ≔ reify_cl 𝑙1, ... , 𝑙n;
///     change π (den (r ₂) (r ₁) = ⟇_to_∨_rw 𝑙𝑘1, ... , 𝑙kn);
///     rewrite left contraction_correct;
///     reflexivity
///   };
///   refine subst_equiv_clause (𝑙1, ... , 𝑙n) (𝑙𝑘1, ... , 𝑙kn)  H i
/// end;
/// ```
pub fn translate_contraction(
    clause: &[Rc<AletheTerm>],
    premise: &(String, &[Rc<AletheTerm>]),
) -> TradResult<Proof> {
    let mut proof = vec![];

    let i = premise.0.clone().into();

    let i_cl = Term::Alethe(LTerm::Clauses(
        premise.1.iter().map(Into::into).collect_vec(),
    ));

    let j_cl = Term::Alethe(LTerm::Clauses(clause.iter().map(Into::into).collect_vec()));

    // reify_i represents reify_cl 𝑙1, ... , 𝑙n
    let reify_i = Term::Terms(vec!["reify_cl".into(), i_cl.clone()]);

    let alias_reify_i = "ir";

    proof.push(ProofStep::Set(alias_reify_i.into(), reify_i.clone()));

    // conv_i represents ⟇_to_∨_rw 𝑙1, ... , 𝑙n
    let conv_i = Term::Terms(vec!["⟇_to_∨_rw".into(), i_cl.clone()]);

    // conv_j represents ⟇_to_∨_rw 𝑙𝑘1, ... , 𝑙kn
    let conv_j = Term::Terms(vec!["⟇_to_∨_rw".into(), j_cl.clone()]);

    // π (⟇_to_∨_rw 𝑙1, ... , 𝑙n = ⟇_to_∨_rw 𝑙𝑘1, ... , 𝑙kn)
    let goal_contra = Term::Alethe(LTerm::ClassicProof(Box::new(Term::Alethe(LTerm::Eq(
        Box::new(conv_i.clone()),
        Box::new(conv_j.clone()),
    )))));

    let have_id = "H";

    // π (den (r ₂) (r ₁) = ⟇_to_∨_rw 𝑙1, ... , 𝑙n);
    let change = ProofStep::Change(Term::Alethe(LTerm::ClassicProof(Box::new(Term::Alethe(
        LTerm::Eq(
            Box::new(Term::Terms(vec![
                "den".into(),
                Term::Terms(vec![alias_reify_i.into(), "₂".into()]),
                Term::Terms(vec![alias_reify_i.into(), "₁".into()]),
            ])),
            Box::new(conv_j.clone()),
        ),
    )))));

    //   have eq : π (⟇_to_∨_rw 𝑙1, ... , 𝑙n = ⟇_to_∨_rw 𝑙1, ... , 𝑙n) {
    //     set r ≔ ...;
    //     change ...;
    //   };
    proof.push(ProofStep::Have(
        have_id.to_owned(),
        goal_contra,
        vec![
            change,
            ProofStep::Rewrite(
                true,
                None,
                "contraction_correct".into(),
                vec![],
                SubProofs(None),
            ),
            ProofStep::Reflexivity,
        ],
    ));

    proof.push(ProofStep::Refine(
        terms!["subst_equiv_clause".into(), i_cl, j_cl, have_id.into(), i],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

/// Rule 13: `la_disequality`
/// `𝑡1 ≈ 𝑡2 ∨ ¬(𝑡1 ≤ 𝑡2) ∨ ¬(𝑡2 ≤ 𝑡1)`
///
/// is translated into the script:
///
/// ```text
/// refine la_disequality t1 t2;
/// ```
pub fn translate_la_disequality(clause: &[Rc<AletheTerm>]) -> TradResult<Proof> {
    let mut proof = vec![];

    let eq_t1_t2 = match_term_err!((or ...) = &clause[0])
        .unwrap()
        .first()
        .unwrap();

    let (t1, t2): (Term, Term) = match_term_err!((= t1 t2) = eq_t1_t2)
        .map(|(t1, t2)| (t1.into(), t2.into()))
        .expect("No equality found in la_disequality?");

    proof.push(ProofStep::Refine(
        terms!["la_disequality".into(), t1, t2],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}

#[cfg(test)]
mod tests_tautolog {
    use super::*;
    use crate::terms;
    use crate::translation::lambdapi::test_macros::*;

    #[test]
    fn test_transitivity_translation() {
        let problem = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun d () T)
            (declare-fun e () T)
        ";
        let proof = "
            (assume h1 (= a b))
            (assume h2 (= b c))
            (assume h3 (= c d))
            (step t1 (cl (= a d)) :rule trans :premises (h1 h2 h3))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(4, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
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
        let problem = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
            (declare-fun e () Bool)
            (declare-fun f () Bool)
            (declare-fun g () Bool)
            (declare-fun h () Bool)
        ";
        let proof = "
            (assume h1 (= a e))
            (assume h2 (= b f))
            (assume h3 (= c g))
            (assume h4 (= d h))
            (step t3 (cl (= (or a b c d) (or e f g h))) :rule cong :premises (h1 h2 h3 h4))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(5, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
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
        let problem = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
            (declare-fun e () Bool)
            (declare-fun f () Bool)
            (declare-fun g () Bool)
            (declare-fun h () Bool)
        ";
        let proof = "
            (assume h1 (= a e))
            (assume h2 (= b f))
            (assume h3 (= c g))
            (assume h4 (= d h))
            (step t3 (cl (= (and a b c d) (and e f g h))) :rule cong :premises (h1 h2 h3 h4))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(5, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
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
        let problem = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
        ";
        let proof = "
            (assume h1 (= a b))
            (step t3 (cl (= (not a) (not b))) :rule cong :premises (h1))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
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
        let problem = "
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (declare-fun c () Bool)
            (declare-fun d () Bool)
        ";
        let proof = "
            (assume h1 (= a c))
            (assume h2 (= b d))
            (step t3 (cl (= (=> a b) (=> c d))) :rule cong :premises (h1 h2))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(3, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
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
    fn test_ite1() {
        let problem = "
            (declare-sort U 0)
            (declare-fun a() U)
            (declare-fun b() U)
            (declare-fun p(U) Bool)
        ";
        let proof = "
            (step t1 (cl (ite (p a) (= b (ite (p a) b a)) (= a (ite (p a) b a)))) :rule hole)
            (step t2 (cl (p a) (= a (ite (p a) b a))) :rule ite1 :premises (t1))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
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
        let problem = "
            (declare-sort U 0)
            (declare-fun a() U)
            (declare-fun b() U)
            (declare-fun p(U) Bool)
        ";
        let proof = "
            (step t1 (cl (ite (p a) (= b (ite (p a) b a)) (= a (ite (p a) b a)))) :rule hole)
            (step t2 (cl (not (p a)) (= b (ite (p a) b a))) :rule ite2 :premises (t1))
        ";
        let (_, proof, _, mut pool) = parse_test_instance(problem, proof).unwrap();

        assert_eq!(2, proof.commands.len());

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            &mut pool,
            |id, t, ps| Command::Symbol(None, normalize_name(id), vec![], t, ps.map(Proof)),
        )
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
}
