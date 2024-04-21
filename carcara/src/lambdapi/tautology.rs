use std::iter;

use super::*;
use crate::ast::{Operator, Rc, Term as AletheTerm};

pub fn translate_trans(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    let mut rewrites = premises
        .into_iter()
        .map(|(id, _)| {
            inline_lambdapi! {
                rewrite [unary_clause_to_prf(id.as_str())];
            }
        })
        .collect_vec();

    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        inject(rewrites);
        reflexivity;
    }))
}

pub fn translate_false() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        apply "neg_⊥";
    }))
}

pub fn translate_implies(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "implies" (@unary_clause_to_prf(premise));
    }))
}

pub fn translate_not_implies1(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "not_implies1" (@unary_clause_to_prf(premise));
    }))
}

pub fn translate_not_implies2(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "not_implies2" (@unary_clause_to_prf(premise));
    }))
}

pub fn translate_not_and(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "not_and" (@unary_clause_to_prf(premise));
        reflexivity;
    }))
}

pub fn translate_refl() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        reflexivity;
    }))
}

pub fn translate_sym(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        symmetry;
        apply @unary_clause_to_prf(premise);
    }))
}

pub fn translate_not_symm(premise: &str) -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        apply "not_symm" (@unary_clause_to_prf(premise));
    }))
}

/// FIXME: admitted for now
pub fn translate_and(_premise: &(String, &[Rc<AletheTerm>])) -> TradResult<Proof> {
    // let mut conjonctions_vec = unwrap_match!(premise.1.first().unwrap().deref(), AletheTerm::Op(Operator::And, args) => args)
    //     .into_iter()
    //     .map(From::from)
    //     .collect_vec();

    // conjonctions_vec.push(Term::Alethe(LTerm::True));

    // let conjonctions = Term::Alethe(LTerm::NAnd(conjonctions_vec));

    // let t_i = premise.0.clone();

    // Ok(Proof(lambdapi! {
    //     apply "and" (@conjonctions)
    //     {  reflexivity; }
    //     { apply t_i; };
    // }))
    Ok(Proof(vec![ProofStep::Admit]))
}

pub fn translate_not_or(premise: &(String, &[Rc<AletheTerm>])) -> TradResult<Proof> {
    let apply_identity = Proof(vec![ProofStep::Apply(
        Term::TermId("identity_⊥".into()),
        vec![Term::from(premise.0.clone())],
        SubProofs(None),
    )]);
    let reflexivity = Proof(vec![ProofStep::Reflexivity]);

    let disjunctions = unwrap_match!(premise.1.first().unwrap().deref(), AletheTerm::Op(Operator::Not, args) => args)
        .into_iter()
        .map(From::from)
        .collect_vec();

    Ok(Proof(vec![ProofStep::Apply(
        Term::TermId("not_or".into()),
        vec![Term::Terms(disjunctions)],
        SubProofs(Some(vec![apply_identity, reflexivity])),
    )]))
}

/// FIXME: admitted for now
#[inline]
pub fn translate_or(_premise_id: &str) -> TradResult<Proof> {
    // Ok(Proof(vec![ProofStep::Apply(
    //     Term::TermId("π̇ₗ".into()),
    //     vec![Term::TermId(premise_id.into())],
    //     SubProofs(None),
    // )]))
    Ok(Proof(vec![ProofStep::Admit]))
}

#[inline]
pub fn translate_auto_rewrite(rule: &str) -> TradResult<Proof> {
    Ok(Proof(vec![
        ProofStep::Apply(Term::TermId(rule.into()), vec![], SubProofs(None)),
        ProofStep::Reflexivity,
    ]))
}

fn propositional_disjunction_cong(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    let premises_len = premises.len();

    let premises = premises
        .into_iter()
        .map(|p| unary_clause_to_prf(p.0.as_str()))
        .collect_vec();

    // generate the rewrites
    let mut rewrites: Vec<ProofStep> = premises
        .into_iter()
        .enumerate()
        .map(|(index, premise)| {
            let mut subexpr_pattern = iter::repeat(Term::Underscore)
                .take(premises_len)
                .collect_vec();
            subexpr_pattern
                .get_mut(index)
                .map(|t| *t = Term::from("x"))
                .unwrap();

            let pattern_disjunction = Term::Alethe(LTerm::NOr(subexpr_pattern));

            let pattern = format!("[ x in {} ]", pattern_disjunction);

            ProofStep::Rewrite(Some(pattern), premise, vec![])
        })
        .collect_vec();

    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        inject(rewrites);
        reflexivity;
    }))
}

fn propositional_conjunction_cong(premises: &[(String, &[Rc<AletheTerm>])]) -> TradResult<Proof> {
    let premises_len = premises.len();

    let premises = premises
        .into_iter()
        .map(|p| unary_clause_to_prf(p.0.as_str()))
        .collect_vec();

    // generate the rewrites
    let mut rewrites: Vec<ProofStep> = premises
        .into_iter()
        .enumerate()
        .map(|(index, premise)| {
            let mut subexpr_pattern = iter::repeat(Term::Underscore)
                .take(premises_len)
                .collect_vec();
            subexpr_pattern
                .get_mut(index)
                .map(|t| *t = Term::from("x"))
                .unwrap();

            let pattern_disjunction = Term::Alethe(LTerm::NAnd(subexpr_pattern));

            let pattern = format!("[ x in {} ]", pattern_disjunction);

            ProofStep::Rewrite(Some(pattern), premise, vec![])
        })
        .collect_vec();

    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        inject(rewrites);
        reflexivity;
    }))
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
            apply "∨ᶜᵢ₁";
            inject(vec![ProofStep::Apply(Term::from("feqᶜ"), vec![ symbol, premise ], SubProofs(None))]);
        }))
    } else {
        match symbol {
            Term::TermId(s) if s == "(∨ᶜ)" => propositional_disjunction_cong(premises),
            Term::TermId(s) if s == "(∧ᶜ)" => propositional_conjunction_cong(premises),
            _ => {
                let premises_rev = premises.iter().rev().collect_vec();
                let (left, right) = premises_rev.split_at(2);

                let feq_first = Term::Terms(vec![
                    Term::from("feq2ᶜ"),
                    symbol.clone(),
                    unary_clause_to_prf(left[1].0.as_str()),
                    unary_clause_to_prf(left[0].0.as_str()),
                ]);

                let feq = right.into_iter().fold(feq_first, |acc, (hyp, _)| {
                    Term::Terms(vec![
                        Term::from("feq2ᶜ"),
                        symbol.clone(),
                        unary_clause_to_prf(hyp),
                        acc,
                    ])
                });

                Ok(Proof(lambdapi! {
                    apply "∨ᶜᵢ₁";
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
        Term::from(format!("feq{}ᶜ", arity))
    } else {
        Term::from("feqᶜ")
    };

    let mut args = vec![symbol];

    let mut hyps = premises
        .into_iter()
        .map(|p| unary_clause_to_prf(p.0.as_str()))
        .collect_vec();

    args.append(&mut hyps);

    let feq = ProofStep::Apply(feq_name, args, SubProofs(None));

    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        inject(vec![feq]);
    }))
}

pub fn translate_cong(
    clause: &[Rc<AletheTerm>],
    premises: &[(String, &[Rc<AletheTerm>])],
) -> TradResult<Proof> {
    let (is_operator, symbol, arity) = unwrap_match!(clause[0].deref(), AletheTerm::Op(Operator::Equals, ts) => {
        match (&*ts[0], &*ts[1]) {
            (AletheTerm::App(f, args) , AletheTerm::App(g, _)) if f == g => (false, Term::from((*f).clone()),  args.len()),
            (AletheTerm::Op(f, args) , AletheTerm::Op(g, _)) if f == g => (true, Term::from(*f), args.len()),
            _ => unreachable!()
        }
    });

    if is_operator {
        propositional_cong(symbol, arity, premises)
    } else {
        application_cong(symbol, arity, premises)
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

pub fn translate_forall_inst(args: &[ProofArg]) -> TradResult<Proof> {
    let hyp = Term::from("H");

    // The term Term::from("H") is related to assume [H];
    let init_forall_elim = Term::Terms(vec![
        Term::from("∀ᶜₑ"),
        unwrap_match!(args.first(), Some(ProofArg::Assign(_, t)) => t.into()),
        hyp,
    ]);

    let forall_elims = args.into_iter().skip(1).fold(init_forall_elim, |acc, arg| {
        Term::Terms(vec![
            Term::from("∀ᶜₑ"),
            unwrap_match!(arg, ProofArg::Assign(_, t) => t.into()),
            acc,
        ])
    });

    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        apply "imply_to_or";
        apply "⇒ᶜᵢ";
        assume [H]; //FIXME: use hyp instead
        apply "" (@forall_elims);
    }))
}

pub fn translate_sko_forall() -> TradResult<Proof> {
    Ok(Proof(lambdapi! {
        apply "∨ᶜᵢ₁";
        apply "sko_forall";
        assume [x H];
        rewrite "H";
        reflexivity;
    }))
}
