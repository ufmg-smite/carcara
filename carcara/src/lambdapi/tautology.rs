use super::*;
use crate::ast::{Operator, Rc, Term as AletheTerm};
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
        apply "∨ᶜᵢ₁";
        apply "neg_⊥";
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
            Term::TermId(s) if s == "(∨ᶜ)" => propositional_or_cong(premises),
            Term::TermId(s) if s == "(∧ᶜ)" => propositional_and_cong(premises),
            _ => {
                // Case `iff`, `=>` ...
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

/// Construct the proof term for the rule `cong`
/// The cong rule is applied on any n-ary function symbol `f` of appropriate sort.
/// Therefore, first we collect information about the sort of `f`, its arguments and its arity by looking at the clause and number of premises.
/// The application of cong on f: A₁ ... Aₙ → Set` are translated with the lemma feqₙᶜ where `n` is the arity of `f`.
/// The application of cong on `or` and `and` operator are translated by composing the lemma `cong_or` (`cong_and` respectively).
/// For the operators `(imp a b)` and `(not a)` we apply the lemma feq₂ᶜ and (`feqᶜ` respectively) since we can quantify over propositions with `ο`.
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

pub fn translate_forall_inst(_args: &Vec<Rc<AletheTerm>>) -> TradResult<Proof> {
    Ok(Proof(admit()))
    // let hyp = Term::from("H");

    // // The term Term::from("H") is related to assume [H];
    // let init_forall_elim = Term::Terms(vec![
    //     Term::from("∀ᶜₑ"),
    //     unwrap_match!(args.first(), Some(ProofArg::Assign(_, t)) => t.into()),
    //     hyp,
    // ]);

    // let forall_elims = args.into_iter().skip(1).fold(init_forall_elim, |acc, arg| {
    //     Term::Terms(vec![
    //         Term::from("∀ᶜₑ"),
    //         unwrap_match!(arg, ProofArg::Assign(_, t) => t.into()),
    //         acc,
    //     ])
    // });

    // Ok(Proof(lambdapi! {
    //     apply "∨ᶜᵢ₁";
    //     apply "imply_to_or";
    //     apply "⇒ᶜᵢ";
    //     assume [H]; //FIXME: use hyp instead
    //     apply "" (@forall_elims);
    // }))
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

#[cfg(test)]
mod tests_tautolog {
    use super::*;
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

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            0,
            |id, t, ps| {
                Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
            },
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

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            0,
            |id, t, ps| {
                Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
            },
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
                [
                    apply!(h1),
                    apply!(
                        cong_or,
                        [apply!(h2), apply!(cong_or, [apply!(h3), apply!(h4)]),]
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

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            0,
            |id, t, ps| {
                Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
            },
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
                [
                    apply!(h1),
                    apply!(
                        cong_and,
                        [apply!(h2), apply!(cong_and, [apply!(h3), apply!(h4)]),]
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

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            0,
            |id, t, ps| {
                Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
            },
        )
        .expect("translate cong");

        assert_eq!(2, res.len());

        let t3 = res.last().unwrap().clone();

        let cmd = Command::Symbol(
            None,
            "t3".into(),
            vec![],
            cl!(eq!(Box::new(not!(id!("a"))), Box::new(not!(id!("b"))))),
            Some(proof!(
                apply!(id!("∨ᶜᵢ₁")),
                ProofStep::Apply(
                    id!("feqᶜ"),
                    vec![id!("(¬)"), unary_clause_to_prf("h1")],
                    SubProofs(None)
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

        let res = translate_commands(
            &mut Context::default(),
            &mut proof.iter(),
            0,
            |id, t, ps| {
                Command::Symbol(None, normalize_name(id), vec![], t, ps.map(|ps| Proof(ps)))
            },
        )
        .expect("translate cong");

        assert_eq!(3, res.len());

        let t3 = res.last().unwrap().clone();

        let cmd = Command::Symbol(
            None,
            "t3".into(),
            vec![],
            cl!(eq!(
                Box::new(imp!(id!("a"), id!("b"))),
                Box::new(imp!(id!("c"), id!("d")))
            )),
            Some(proof!(
                apply!(id!("∨ᶜᵢ₁")),
                apply!(terms![
                    id!("feq2ᶜ"),
                    id!("(⇒ᶜ)"),
                    unary_clause_to_prf("h1"),
                    unary_clause_to_prf("h2")
                ])
            )),
        );

        assert_eq!(t3, cmd);
    }
}
