use super::*;
use crate::{ast::*, checker::error::CheckerError};

pub fn ite_intro(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.clause.len(), 1);
    let mut ids = IdHelper::new(&step.id);
    let mut polyeq = Polyeq::new().mod_reordering(true);
    let (root_term, right_side) = match_term_err!((= t u) = &step.clause[0])?;

    if polyeq.eq(root_term, right_side) {
        return Ok(
            PolyeqElaborator::new(&mut ids, step.depth, false).elaborate(
                pool,
                root_term.clone(),
                right_side.clone(),
            ),
        );
    }

    let us = match_term_err!((and ...) = right_side)?;

    // Construct the expected right-hand side
    let expected_us = us[1..].iter().map(|u_i| {
        let (cond, (a, b), (c, d)) = match_term!((ite cond (= a b) (= c d)) = u_i).unwrap();
        let mut is_valid = |r_1, s_1, r_2, s_2| {
            // s_1 == s_2 == (ite cond r_1 r_2)
            if polyeq.eq(s_1, s_2) {
                if let Some((a, b, c)) = match_term!((ite a b c) = s_1) {
                    return polyeq.eq(a, cond) && polyeq.eq(b, r_1) && polyeq.eq(c, r_2);
                }
            }
            false
        };

        let [r_1, r_2] = if is_valid(a, b, c, d) {
            [a, c]
        } else if is_valid(b, a, c, d) {
            [b, c]
        } else if is_valid(a, b, d, c) {
            [a, d]
        } else if is_valid(b, a, d, c) {
            [b, d]
        } else {
            unreachable!()
        };

        let s = build_term!(pool, (ite {cond.clone()} {r_1.clone()} {r_2.clone()}));
        build_term!(pool, (ite {cond.clone()} (= {s.clone()} {r_1.clone()}) (= {s} {r_2.clone()})))
    });
    let expected_us: Vec<_> = std::iter::once(root_term.clone())
        .chain(expected_us)
        .collect();
    let fixed_right_side = pool.add(Term::Op(Operator::And, expected_us));

    // If the right_side is already correct, we don't need to elaborate anything
    if *right_side == fixed_right_side {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    let new_ite_intro_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![build_term!(pool, (= {root_term.clone()} {fixed_right_side.clone()}))],
        rule: "ite_intro".to_owned(),
        ..StepNode::default()
    }));
    let polyeq_step = PolyeqElaborator::new(&mut ids, step.depth, false).elaborate(
        pool,
        fixed_right_side.clone(),
        right_side.clone(),
    );
    let trans_step = Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "trans".to_owned(),
        premises: vec![new_ite_intro_step, polyeq_step],
        ..StepNode::default()
    }));
    Ok(trans_step)
}
