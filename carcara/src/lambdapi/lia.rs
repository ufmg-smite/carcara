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

#[derive(Debug)]
struct ReifiedInequality {
    lhs: Rc<AletheTerm>,
    rhs: Rc<AletheTerm>,
    op: Op,
    neg: bool,
}

pub fn la_generic(clause: &[Rc<AletheTerm>], args: &Vec<Rc<AletheTerm>>) -> TradResult<Proof> {
    let mut inequalities = clause
        .into_iter()
        .map(|t| match t.deref() {
            AletheTerm::Op(Operator::Equals, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Eq,
                neg: false,
            },
            AletheTerm::Op(Operator::LessEq, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Le,
                neg: false,
            },
            AletheTerm::Op(Operator::LessThan, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Lt,
                neg: false,
            },
            AletheTerm::Op(Operator::GreaterThan, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Gt,
                neg: false,
            },
            AletheTerm::Op(Operator::GreaterEq, xs) => ReifiedInequality {
                lhs: xs[0].clone(),
                rhs: xs[1].clone(),
                op: Op::Ge,
                neg: false,
            },
            AletheTerm::Op(Operator::Not, t) => match t.first().unwrap().deref() {
                AletheTerm::Op(Operator::Equals, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Eq,
                    neg: true,
                },
                AletheTerm::Op(Operator::LessEq, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Le,
                    neg: true,
                },
                AletheTerm::Op(Operator::LessThan, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Lt,
                    neg: true,
                },
                AletheTerm::Op(Operator::GreaterThan, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Gt,
                    neg: true,
                },
                AletheTerm::Op(Operator::GreaterEq, xs) => ReifiedInequality {
                    lhs: xs[0].clone(),
                    rhs: xs[1].clone(),
                    op: Op::Ge,
                    neg: true,
                },
                _ => unreachable!(),
            },
            _ => unreachable!(),
        })
        .collect_vec();

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

    let step1 = inequalities
        .iter()
        .enumerate()
        .filter(|(i, l)| l.neg == false && l.op != Op::Eq)
        .map(|(i, l)| {
            let mut pattern: Vec<String> = vec!["_".to_string(); inequalities.len()];
            pattern[i] = "x".to_string();
            let pattern_with_or: String =
                itertools::intersperse(pattern.into_iter(), " ∨ᶜ ".to_string()).collect();
            match l.op {
                Op::Lt => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    id!("Zlt_not_ge"),
                    vec![],
                ),
                Op::Le => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    id!("Zle_not_gt"),
                    vec![],
                ),
                Op::Ge => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    id!("Zge_not_lt"),
                    vec![],
                ),
                Op::Gt => ProofStep::Rewrite(
                    false,
                    Some(format!("[x in {}]", pattern_with_or)),
                    id!("Zgt_not_le"),
                    vec![],
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

    println!("Step 1 {:?}", inequalities);

    // Step normalize < and ≤. The algorithm expect to work only with ⋈ = { >, = , ≥ }
    // If 𝜑 = a < b then 𝜑 = ~ a > ~ b
    // If 𝜑 = a ≤ b then 𝜑 = ~ a ≥ ~ b
    let mut normalize_step = vec![
        ProofStep::Try(Box::new(ProofStep::Rewrite(
            false,
            None,
            id!("Zinv_lt_eq"),
            vec![],
        ))),
        ProofStep::Try(Box::new(ProofStep::Rewrite(
            false,
            None,
            id!("Zinv_le_eq"),
            vec![],
        ))),
    ];

    for i in inequalities.iter_mut() {
        if i.op == Op::Lt {
            i.lhs = Rc::new(AletheTerm::Op(Operator::Sub, vec![i.lhs.clone()]));
            i.rhs = Rc::new(AletheTerm::Op(Operator::Sub, vec![i.rhs.clone()]));
            i.op = Op::Gt;
        }
        if i.op == Op::Le {
            i.lhs = Rc::new(AletheTerm::Op(Operator::Sub, vec![i.lhs.clone()]));
            i.rhs = Rc::new(AletheTerm::Op(Operator::Sub, vec![i.rhs.clone()]));
            i.op = Op::Ge;
        }
    }

    println!("Step Normalize {:?}", inequalities);

    // step 3:
    let mut step3 = inequalities
        .iter()
        .map(|i| match i.op {
            Op::Eq => ProofStep::Rewrite(
                false,
                None,
                id!("Z_diff_eq_Z0_eq"),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
            ),
            Op::Ge => ProofStep::Rewrite(
                false,
                None,
                id!("Z_diff_geq_Z0_eq"),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
            ),
            Op::Gt => ProofStep::Rewrite(
                false,
                None,
                id!("Z_diff_gt_Z0_eq"),
                vec![i.lhs.clone().into(), i.rhs.clone().into()],
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

    println!("Step 3 {:?}", inequalities);

    // Now 𝜑 has the form s1 ⋈ d. If all variables in s1 are integer sorted: replace ⋈ d according to the table below.
    let mut step4 = inequalities
    .iter()
    .filter(|i| matches!(i.op, Op::Gt))
    .map(|i| 
        ProofStep::Rewrite(false, None, id!("Zgt_le_succ_r_eq"), vec![i.lhs.clone().into(), i.rhs.clone().into()])
    ).collect_vec();


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

    println!("Step 4 {:?}", inequalities);

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
                let c = match c {
                    Constant::Integer(c) => c,
                    Constant::Real(c) => &c.clone().into_numer_denom().0,
                    _ => unreachable!(),
                };
                let lhs = Term::from(lhs);
                let rhs = Term::from(rhs);
                ProofStep::Rewrite(
                    false,
                    None,
                    id!("Zmult_eq_compat_eq"),
                    vec![Term::Int(c.clone()), lhs.into(), rhs.into()],
                )
            }
            ReifiedInequality { lhs, rhs, .. } => {
                let c = match c {
                    Constant::Integer(c) => c,
                    Constant::Real(c) => &c.clone().into_numer_denom().0,
                    _ => unreachable!(),
                };
                let lhs = Term::from(lhs);
                let rhs = Term::from(rhs);
                ProofStep::Rewrite(
                    false,
                    None,
                    id!("Zmult_ge_compat_eq"),
                    vec![Term::Int(c.clone()), lhs.into(), rhs.into()],
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
        id!("Z_eq_antisym"),
        vec![],
    ))));

    // Step 2 If 𝜑 = ¬(s1 ⋈ s2), then let 𝜑 ∶= s2 ⋈ s2. We interpret this step as moving literals in the context
    let mut step2 = inequalities
        .iter()
        .enumerate()
        .map(|(counter, _)| {
            vec![
                //rewrite imp_eq_or; apply ⇒ᶜᵢ; assume H1;
                ProofStep::Rewrite(false, None, id!("imp_eq_or"), vec![]),
                ProofStep::Apply(Term::from("⇒ᶜᵢ"), vec![], SubProofs(None)),
                ProofStep::Assume(vec![format!("H{}", counter)]),
            ]
        })
        .collect_vec();
    step2.pop();
    step2.append(&mut vec![vec![
        ProofStep::Apply(Term::from("¬ᶜᵢ"), vec![], SubProofs(None)),
        ProofStep::Assume(vec![format!("H{}", step2.len())]),
    ]]);

    // Finally, the sum of the resulting literals is trivially contradictory.
    // The sum on the left-hand side is 0 and the right-hand side is > 0 (or ≥ 0 if ⋈ is >).
    //let sum =  inequalities.iter().(|acc, c.| acc = AletheTerm::Op(Operator::Add, );
    let sets = inequalities
        .iter()
        .enumerate()
        .map(|(counter, i)| {
            vec![
                ProofStep::Set(format!("H{}lhs", counter), i.lhs.clone().into()),
                ProofStep::Set(format!("H{}rhs", counter), i.rhs.clone().into()),
            ]
        })
        .collect_vec();

    //HACK: to be faster we generate the goal has a constant string
    let left_sum = inequalities
        .iter()
        .enumerate()
        .map(|(c, _)| format!("H{}lhs", c))
        .collect_vec();
    let left_sum = left_sum.join(" + ");
    let right_sum = inequalities
        .iter()
        .enumerate()
        .map(|(c, _)| format!("H{}rhs", c))
        .collect_vec();
    let right_sum = right_sum.join(" + ");

    let final_sum = Term::from(AletheTerm::Op(
        Operator::GreaterEq,
        vec![
            Rc::new(AletheTerm::Const(Constant::String(left_sum))),
            Rc::new(AletheTerm::Const(Constant::String(right_sum))),
        ],
    ));

    let mut pack: Term = Term::Terms(vec![id!("Zsum_geq_s"), id!("H0"), id!("H1")]);
    inequalities.iter().enumerate().skip(2).for_each(|(i, _)| {
        pack = Term::Terms(vec![
            id!("Zsum_geq_s"),
            pack.clone(),
            format!("H{}", i).into(),
        ])
    });

    let final_sum_have = ProofStep::Have(
        "Hsum".to_string(),
        Term::Alethe(LTerm::ClassicProof(Box::new(final_sum))),
        vec![ProofStep::Apply(pack, vec![], SubProofs(None))],
    );

    let mut proof = step1;
    proof.append(&mut normalize_step);
    proof.append(&mut step3);
    proof.append(&mut step4);
    proof.append(&mut step5);
    proof.append(&mut step2.concat());
    proof.append(&mut sets.concat());
    proof.push(final_sum_have);
    proof.push(ProofStep::Apply(
        "completude_lia".into(),
        vec![underscore!(), underscore!(), id!("Hsum")],
        SubProofs(None),
    ));

    Ok(Proof(proof))
}
