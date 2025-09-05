
use rug::Integer;

use super::*;
use crate::ast::{Constant, Operator, Rc, Term as AletheTerm};

#[derive(Debug, PartialEq)]
enum Op {
    Eq,
    Lt,
    Gt,
    Ge,
    Le,
}

fn op_into_operator(op: &Op) -> Operator {
    match op {
        Op::Eq => Operator::Equals,
        Op::Ge => Operator::GreaterEq,
        Op::Gt => Operator::GreaterThan,
        Op::Lt => Operator::LessThan,
        Op::Le => Operator::LessEq,
    }
}

#[derive(Debug)]
struct ReifiedInequality {
    lhs: Rc<AletheTerm>,
    rhs: Rc<AletheTerm>,
    op: Op,
    neg: bool,
    name: String,
}

fn inequalitie_with_alias_name(i: &ReifiedInequality) -> AletheTerm {
    let op: Operator = op_into_operator(&i.op);
    let lhs = Rc::new(AletheTerm::Const(Constant::String(format!("{}l", i.name))));
    let rhs = Rc::new(AletheTerm::Const(Constant::String(format!("{}r", i.name))));

    let ine = AletheTerm::Op(op, vec![lhs, rhs]);

    if i.neg {
        AletheTerm::Op(Operator::Not, vec![Rc::new(ine)])
    } else {
        ine
    }
}

pub fn gen_proof_la_generic(
    clause: &[Rc<AletheTerm>],
    args: &Vec<Rc<AletheTerm>>,
) -> Vec<ProofStep> {
    let inequalities: Vec<ReifiedInequality> = get_inequalities_from_clause(clause);

    let la_clause = clause
        .iter()
        //.map(|i| inequalitie_with_alias_name(i))
        .map(Term::from)
        .collect_vec();

    // let sets = inequalities.iter().fold(vec![], |mut sets, i| {
    //     sets.push(ProofStep::Set(format!("{}l", i.name), i.lhs.clone().into()));
    //     sets.push(ProofStep::Set(format!("{}r", i.name), i.rhs.clone().into()));
    //     sets
    // });

    let mut proof_la = vec![ProofStep::Apply(
        Term::from("∨ᵢ₁"),
        vec![],
        SubProofs(None),
    )];

    proof_la.append(&mut la_generic(inequalities, args).unwrap().0);

    let id_temp_proof = String::from("Hla");

    let ring_computation_proof = ProofStep::Have(
        id_temp_proof.clone(),
        Term::Alethe(LTerm::Proof(Box::new(Term::Alethe(LTerm::Clauses(vec![
            Term::Alethe(LTerm::NOr(la_clause)),
        ]))))),
        proof_la,
    );

    let mut proof: Vec<ProofStep> = vec![];

    proof.append(&mut vec![
        ring_computation_proof,
        ProofStep::Simplify(vec![]),
        ProofStep::Rewrite(false, None, "or_identity_r".into(), vec![], SubProofs(None)),
        ProofStep::Apply(unary_clause_to_prf(&id_temp_proof), vec![], SubProofs(None)),
    ]);

    proof
}

fn get_inequalities_from_clause(clause: &[Rc<AletheTerm>]) -> Vec<ReifiedInequality> {
    clause
        .into_iter()
        .enumerate()
        .map(|(i, t)| match t.deref() {
            AletheTerm::Op(Operator::Equals, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Eq,
                neg: false,
                name: format!("H{}", i),
            },
            AletheTerm::Op(Operator::LessEq, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Le,
                neg: false,
                name: format!("H{}", i),
            },
            AletheTerm::Op(Operator::LessThan, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Lt,
                neg: false,
                name: format!("H{}", i),
            },
            AletheTerm::Op(Operator::GreaterThan, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Gt,
                neg: false,
                name: format!("H{}", i),
            },
            AletheTerm::Op(Operator::GreaterEq, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Ge,
                neg: false,
                name: format!("H{}", i),
            },
            AletheTerm::Op(Operator::Not, t) => match t.first().unwrap().deref() {
                AletheTerm::Op(Operator::Equals, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Eq,
                    neg: true,
                    name: format!("H{}", i),
                },
                AletheTerm::Op(Operator::LessEq, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Le,
                    neg: true,
                    name: format!("H{}", i),
                },
                AletheTerm::Op(Operator::LessThan, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Lt,
                    neg: true,
                    name: format!("H{}", i),
                },
                AletheTerm::Op(Operator::GreaterThan, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Gt,
                    neg: true,
                    name: format!("H{}", i),
                },
                AletheTerm::Op(Operator::GreaterEq, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Ge,
                    neg: true,
                    name: format!("H{}", i),
                },
                _ => unreachable!(),
            },
            _ => unreachable!(),
        })
        .collect_vec()
}

fn sum_hyps(prefix: &str, suffix: &str, start: usize, end: usize) -> String {
    let s = (start..end)
        .into_iter()
        .map(|i| format!("{}{}{}", prefix, i, suffix))
        .collect_vec();
    s.join(" + ")
}

// TODO: Maybe optmise this function to reduce allocation?
fn visit_arith_term(term: &AletheTerm) -> HashSet<AletheTerm> {
    match term {
        func @ AletheTerm::App(f, args) => HashSet::from([func.clone()]),
        AletheTerm::Op(_f, args) => args
            .into_iter()
            .map(|a| visit_arith_term(&a))
            .reduce(|acc, e| acc.union(&e).cloned().collect())
            .unwrap_or(HashSet::new()),
        var @ AletheTerm::Var(_, _) => HashSet::from([var.clone()]),
        _ => HashSet::new(),
    }
}

fn la_generic(
    inequalities: Vec<ReifiedInequality>,
    args: &Vec<Rc<AletheTerm>>,
) -> TradResult<Proof> {
    let mut inequalities = inequalities;

    // let env_map_aletheterm: HashSet<AletheTerm> = inequalities
    //     .iter()
    //     .map(|i| {
    //         visit_arith_term(&i.lhs)
    //             .union(&visit_arith_term(&i.rhs))
    //             .cloned()
    //             .collect()
    //     })
    //     .reduce(|acc: HashSet<_>, e| acc.union(&e).cloned().collect())
    //     .unwrap_or(HashSet::new());

    //let env_map_as_vec: Vec<_> = env_map_aletheterm.iter().cloned().collect();
    //let env_map = env_map_as_vec.into_iter().map(Term::from).collect_vec(); 

    // We create alias to make generation of the proof easily
    // inequalities.iter_mut().for_each(|i| {
    //     i.lhs = Rc::new(AletheTerm::Const(Constant::String(format!("{}l", i.name))));
    //     i.rhs = Rc::new(AletheTerm::Const(Constant::String(format!("{}r", i.name))));
    // });

    let args = args
        .into_iter()
        .map(|a| match a.deref() {
            AletheTerm::Const(c) => c,
            _ => unreachable!(),
        })
        .collect_vec();

    // step 1: negates the literal
    // If 𝜑 = s1 > s2, then let 𝜑 ∶= s1 ≤ s2.
    // If 𝜑 = s1 ≥ s2 , then let 𝜑 ∶= s1 < s2 .
    // If 𝜑 = s1 < s2 , then let 𝜑 ∶= s1 ≥ s2 .
    // If 𝜑 = s1 ≤ s2 , then let 𝜑 ∶= s1 > s2 .
    //FIXME: only done for Eq for now
    // let mut step1 = vec![];

    let mut step1 = inequalities
        .iter()
        .enumerate()
        .filter(|(i, l)| l.neg == false && l.op != Op::Eq)
        .map(|(i, l)| {
            let mut pattern: Vec<String> = vec!["_".to_string(); inequalities.len()];
            pattern[i] = "x".to_string();
            let pattern_with_or: String =
                itertools::intersperse(pattern.into_iter(), " ∨ ".to_string()).collect();
            match l.op {
                Op::Lt => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    "Zlt_not_ge".into(),
                    vec![],
                    SubProofs(None)
                ),
                Op::Le => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    "Zle_not_gt".into(),
                    vec![],
                    SubProofs(None)
                ),
                Op::Ge => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    "Zge_not_lt".into(),
                    vec![],
                    SubProofs(None)
                ),
                Op::Gt => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    "Zgt_not_le".into(),
                    vec![],
                    SubProofs(None)
                ),
                _ => todo!(),
            }
        })
        .collect_vec();

    for i in inequalities.iter_mut() {
        if i.neg == false {
            i.op = match i.op {
                Op::Eq => Op::Eq,
                Op::Lt => Op::Ge,
                Op::Le => Op::Gt,
                Op::Gt => Op::Le,
                Op::Ge => Op::Lt,
            };
            i.neg = true; // the literal have been negate
        }
    }

    //println!("Step 1 {:?}", inequalities);

    // Step normalize < and ≤. The algorithm expect to work only with ⋈ = { >, = , ≥ }
    // If 𝜑 = a < b then 𝜑 = ~ a > ~ b
    // If 𝜑 = a ≤ b then 𝜑 = ~ a ≥ ~ b
    let mut normalize_step = vec![];

    for i in inequalities.iter_mut() {
        if i.op == Op::Lt {
            i.lhs = Rc::new(AletheTerm::Op(Operator::Sub, vec![i.lhs.clone()]));
            i.rhs = Rc::new(AletheTerm::Op(Operator::Sub, vec![i.rhs.clone()]));
            i.op = Op::Gt;
            normalize_step.push(ProofStep::Try(Box::new(ProofStep::Rewrite(
                false,
                None,
                "Zinv_lt_eq".into(),
                vec![],
                SubProofs(None)
            ))));
        }
        if i.op == Op::Le {
            i.lhs = Rc::new(AletheTerm::Op(Operator::Sub, vec![i.lhs.clone()]));
            i.rhs = Rc::new(AletheTerm::Op(Operator::Sub, vec![i.rhs.clone()]));
            i.op = Op::Ge;
            normalize_step.push(ProofStep::Try(Box::new(ProofStep::Rewrite(
                false,
                None,
                "Zinv_le_eq".into(),
                vec![],
                SubProofs(None)
            ))));
        }
    }

    //println!("Step Normalize {:?}", inequalities);

    // step 3:
    let mut step3 = inequalities
        .iter()
        .map(|i| match i.op {
            Op::Eq => ProofStep::Rewrite(
                false,
                None,
                "Z_diff_eq_Z0_eq".into(),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
                SubProofs(None)
            ),
            Op::Ge => ProofStep::Rewrite(
                false,
                None,
                "Z_diff_geq_Z0_eq".into(),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
                SubProofs(None)
            ),
            Op::Gt => ProofStep::Rewrite(
                false,
                None,
                "Z_diff_gt_Z0_eq".into(),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
                SubProofs(None)
            ),
            _ => unreachable!(),
        })
        .collect_vec();

    for i in inequalities.iter_mut() {
        i.lhs = Rc::new(AletheTerm::Op(
            Operator::Sub,
            vec![i.lhs.clone(), i.rhs.clone()],
        ));
        i.rhs = Rc::new(AletheTerm::Const(Constant::Integer(Integer::from(0))));
    }

    //println!("Step 3 {:?}", inequalities);

    // Now 𝜑 has the form s1 ⋈ d. If all variables in s1 are integer sorted: replace ⋈ d according to the table below.
    let mut step4 = inequalities
        .iter()
        .filter(|i| matches!(i.op, Op::Gt))
        .map(|i| {
            ProofStep::Rewrite(
                false,
                None,
                "Zgt_le_succ_r_eq".into(),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
                SubProofs(None)
            )
        })
        .collect_vec();

    for i in inequalities.iter_mut() {
        if i.op == Op::Gt {
            i.rhs = Rc::new(AletheTerm::Op(
                Operator::Add,
                vec![
                    i.rhs.clone(),
                    Rc::new(AletheTerm::Const(Constant::Integer(Integer::from(1)))),
                ],
            ));
            i.op = Op::Ge;
        }
    }

    //println!("Step 4 {:?}", inequalities);

    // step 5
    // If ⋈ is ≈ replace l with i ∈ 0..m by
    // ∑ a × ci × ti ≈ a × d,
    // otherwise replace it by ∑ |a| × ci × ti ≈ |a| × d.
    let mut step5 = vec![];
    let mut rw_args = inequalities
        .iter()
        .zip(args.iter())
        .map(|(i, c)| match i {
            ReifiedInequality { lhs, rhs, op: Op::Eq, .. } => {
                let c: Integer = match c {
                    Constant::Integer(i) => i.clone(),
                    Constant::Real(r) => r.clone().into_numer_denom().0,
                    _ => unreachable!(),
                };
                let lhs = Term::from(lhs);
                let rhs = Term::from(rhs);
                ProofStep::Rewrite(
                    false,
                    None,
                    "Zmult_eq_compat_eq".into(),
                    vec![Term::Int(c.clone()), lhs.into(), rhs.into()],
                    SubProofs(None)
                )
            }
            ReifiedInequality { lhs, rhs, .. } => {
                let c: Integer = match c {
                    Constant::Integer(i) => i.clone(),
                    Constant::Real(r) => r.clone().into_numer_denom().0.clone(),
                    _ => unreachable!(),
                };
                let lhs = Term::from(lhs);
                let rhs = Term::from(rhs);
                ProofStep::Rewrite(
                    false,
                    None,
                    "Zmult_ge_compat_eq".into(),
                    vec![Term::Int(c.clone()), lhs.into(), rhs.into()],
                    SubProofs(None)
                )
            }
        })
        .collect_vec();
    step5.append(&mut rw_args);

    for (i, arg) in inequalities.iter_mut().zip(args.into_iter()) {
        let c = match arg.to_owned() {
            Constant::Integer(c) => c,
            Constant::Real(c) => c.into_numer_denom().0,
            _ => unreachable!(),
        };
        i.lhs = Rc::new(AletheTerm::Op(
            Operator::Mult,
            vec![
                Rc::new(AletheTerm::Const(Constant::Integer(c.clone()))),
                i.lhs.clone(),
            ],
        ));
        i.rhs = Rc::new(AletheTerm::Op(
            Operator::Mult,
            vec![
                Rc::new(AletheTerm::Const(Constant::Integer(c))),
                i.rhs.clone(),
            ],
        ));
    }

    step5.push(ProofStep::Try(Box::new(ProofStep::Rewrite(
        false,
        None,
        "Z_eq_antisym".into(),
        vec![],
        SubProofs(None)
    ))));

    // Step 2 If 𝜑 = ¬(s1 ⋈ s2), then let 𝜑 ∶= s2 ⋈ s2. We interpret this step as moving literals in the context
    let mut step2 = inequalities
        .iter()
        .enumerate()
        .map(|(counter, _)| {
            vec![
                //rewrite imp_eq_or; assume H1;
                ProofStep::Rewrite(false, None, "imp_eq_or".into(), vec![], SubProofs(None)),
                ProofStep::Assume(vec![format!("H{}", counter)]),
            ]
        })
        .collect_vec();
    step2.pop();
    step2.append(&mut vec![vec![
        ProofStep::Assume(vec![format!("H{}", step2.len())]),
    ]]);

    // Finally, the sum of the resulting literals is trivially contradictory.
    // The sum on the left-hand side is 0 and the right-hand side is > 0 (or ≥ 0 if ⋈ is >).
    //let sum =  inequalities.iter().(|acc, c.| acc = AletheTerm::Op(Operator::Add, );
    let mut sets = inequalities
        .iter()
        .enumerate()
        .map(|(counter, i)| {
            vec![
                ProofStep::Set(format!("H{}l'", counter), i.lhs.clone().into()),
                ProofStep::Set(format!("H{}r'", counter), i.rhs.clone().into()),
            ]
        })
        .collect_vec()
        .concat();

    let ine_len = inequalities.len();

    //HACK: to be faster we generate the goal has a constant string
    let left_sum = Term::from(
        sum_hyps("H", "l'", 0, ine_len), // inequalities
                                         //     .iter()
                                         //     .enumerate()
                                         //     .map(|(i, _)| format!("H{}l'", i))
                                         //     .join(" + "),
    );

    let right_sum = Term::from(
        // inequalities
        //     .iter()
        //     .enumerate()
        //     .map(|(i, _)| format!("H{}r'", i))
        //    .join(" + "),
        sum_hyps("H", "r'", 0, ine_len),
    );

    let left_prefix = "l";
    let right_prefix = "r";

    sets.push(ProofStep::Set(left_prefix.to_string(), left_sum));
    sets.push(ProofStep::Set(right_prefix.to_string(), right_sum));

    let left_prefix_term = Term::from(left_prefix);
    let right_prefix_term = Term::from(right_prefix);

    //FIXME: support also Gt and Eq
    let final_sum = Term::Terms(vec![
        left_prefix_term.clone(),
        Term::from("≥"),
        right_prefix_term.clone(),
    ]);

    // We want to generate (Zsum_geq_s H0l' H0r' (H1l' + H2l') (H1r' + H2r') H0 (Zsum_geq_s H1l' H1r' H2l' H2r' H1 H2));
    let mut pack: Term = Term::Terms(vec![
        "Zsum_geq_s".into(),
        format!("H{}l'", ine_len - 2).into(),
        format!("H{}r'", ine_len - 2).into(),
        format!("H{}l'", ine_len - 1).into(),
        format!("H{}r'", ine_len - 1).into(),
        format!("H{}", ine_len - 2).into(),
        format!("H{}", ine_len - 1).into(),
    ]);
    inequalities
        .iter()
        .enumerate()
        .rev()
        .skip(2)
        .for_each(|(i, _)| {
            pack = Term::Terms(vec![
                "Zsum_geq_s".into(),
                format!("H{}l'", i).into(),
                format!("H{}r'", i).into(),
                Term::Terms(vec![Term::from(sum_hyps("H", "l'", i + 1, ine_len))]),
                Term::Terms(vec![Term::from(sum_hyps("H", "r'", i + 1, ine_len))]),
                format!("H{}", i).into(),
                pack.clone(),
            ])
        });

    let sum_hyp_name = "sum";

    let contradiction = ProofStep::Have(
        sum_hyp_name.to_string(),
        Term::Alethe(LTerm::ClassicProof(Box::new(final_sum))),
        vec![
            ProofStep::Refine(pack, vec![], SubProofs(None)),
        ],
    );

    let mut proof = vec![];

    proof.append(&mut step1);
    proof.append(&mut normalize_step);
    proof.append(&mut step3);
    proof.append(&mut step4);
    proof.append(&mut step5);
    proof.append(&mut step2.concat());
    proof.append(&mut sets);


    proof.push(contradiction);

    proof.push(ProofStep::Refine(Term::from(sum_hyp_name),vec![Term::Underscore], SubProofs(None)));
    
    proof.push(ProofStep::Rewrite(true, None, Term::from("reify_correct"), vec![left_prefix_term.clone()], SubProofs(None)));
    proof.push(ProofStep::Rewrite(true, None, Term::from("reify_correct"), vec![right_prefix_term.clone()], SubProofs(None)));


    let left_prefix_p = format!("{}'", left_prefix);
    let right_prefix_p = format!("{}'", right_prefix);

    proof.push(ProofStep::Set(left_prefix_p.clone(), Term::Terms(vec![Term::from("reify"), left_prefix_term.clone()])));
    proof.push(ProofStep::Set(right_prefix_p.clone(), Term::Terms(vec![Term::from("reify"), right_prefix_term.clone()])));

    let left_prefix_term = Term::from(left_prefix_p.clone());
    let right_prefix_term = Term::from(right_prefix_p.clone());

    proof.push(ProofStep::Rewrite(false, None, Term::from("eta_prod"), vec![left_prefix_term.clone()],SubProofs(None)));
    proof.push(ProofStep::Rewrite(false, None, Term::from("eta_prod"), vec![right_prefix_term.clone()],SubProofs(None)));

    proof.push(ProofStep::Rewrite(true, None, Term::from("norm_correct"), vec![
        Term::Terms(vec![left_prefix_term.clone(), Term::from("₁")]),
        Term::Terms(vec![left_prefix_term, Term::from("₂")]),
        Term::Underscore,
    ],SubProofs(Some(vec![
        Proof(vec![ ProofStep::Refine(intro_top(), vec![], SubProofs(None)) ]),
        Proof(vec![ ProofStep::Refine(intro_top(), vec![], SubProofs(None)) ]),
    ]))));

    Ok(Proof(proof))
}
