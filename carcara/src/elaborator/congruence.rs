use super::{add_symm_step, IdHelper};
use crate::{
    ast::*,
    checker::error::CheckerError,
    utils::{DedupIterator, MultiSet},
};
use std::collections::HashSet;

fn build_eq_symm_step(
    pool: &mut PrimitivePool,
    a: &Rc<Term>,
    b: &Rc<Term>,
    id: String,
    depth: usize,
) -> Rc<ProofNode> {
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth,
        clause: vec![
            build_term!(pool, (= (= {a.clone()} {b.clone()}) (= {b.clone()} {a.clone()}))),
        ],
        rule: "eq_symmetric".to_owned(),
        ..StepNode::default()
    }))
}

fn check_cong<'a, I: IntoIterator<Item = &'a Rc<Term>>>(
    premises: &[(&Rc<Term>, &Rc<Term>)],
    f_args: I,
    g_args: I,
    mut flipped: Option<&mut [bool]>,
) -> bool {
    let mut premises = premises.iter().enumerate().peekable();

    for (f_arg, g_arg) in f_args.into_iter().zip(g_args) {
        let expected = (f_arg.as_ref(), g_arg.as_ref());
        match premises.peek() {
            // If the next premise can justify that the arguments are equal, we consume it. We
            // prefer consuming the premise even if the arguments are directly equal
            Some((_, (t, u))) if expected == (t, u) => {
                premises.next();
            }
            Some((i, (t, u))) if expected == (u, t) => {
                if let Some(flipped) = &mut flipped {
                    flipped[*i] = true;
                }
                premises.next();
            }

            // If the arguments are directly equal, we simply continue to the next pair of
            // arguments
            _ if f_arg == g_arg => (),

            // If the arguments are not directly equal, we needed a premise that can justify
            // their equality, so now we return false
            _ => return false,
        }
    }

    // At the end, all premises must have been consumed
    premises.next().is_none()
}

fn term_args(term: &Rc<Term>) -> &[Rc<Term>] {
    match term.as_ref() {
        Term::App(_, args) | Term::Op(_, args) | Term::ParamOp { args, .. } => args,
        _ => panic!(),
    }
}

pub fn cong(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.clause.len(), 1);
    assert!(!step.premises.is_empty());

    let (f, g) = match_term_err!((= f g) = &step.clause[0])?;

    // Sometimes, `cong` is used to derive an equality between identical terms. We can turn these
    // steps into `refl` steps, removing the unnecessary premises
    if f == g {
        return Ok(Rc::new(ProofNode::Step(StepNode {
            rule: "refl".to_owned(),
            premises: vec![],
            ..step.clone()
        })));
    }

    let step =
        if let (Some(fs), Some(gs)) = (match_term!((= f1 f2) = f), match_term!((= g1 g2) = g)) {
            // If it's a congruence between two equalities, we need to take some extra care
            elaborate_cong_between_equalities(pool, step, fs, gs)?
        } else {
            flip_needed_premises(pool, step.clone())
        };
    Ok(Rc::new(ProofNode::Step(step)))
}

fn flip_needed_premises(pool: &mut PrimitivePool, step: StepNode) -> StepNode {
    let (f, g) = match_term!((= f g) = &step.clause[0]).unwrap();
    let [f_args, g_args] = [f, g].map(term_args);
    let premises: Vec<_> = step
        .premises
        .iter()
        .map(|p| match_term!((= a b) = p.clause()[0]).unwrap())
        .collect();
    let mut flipped = vec![false; premises.len()];
    let is_valid = check_cong(&premises, f_args, g_args, Some(&mut flipped));
    assert!(is_valid);

    if flipped.iter().any(|f| *f) {
        let mut ids = IdHelper::new(&step.id);
        let new_premises: Vec<_> = step
            .premises
            .iter()
            .zip(flipped)
            .map(|(p, flip)| {
                if flip {
                    add_symm_step(pool, p, ids.next_id())
                } else {
                    p.clone()
                }
            })
            .collect();
        StepNode { premises: new_premises, ..step }
    } else {
        step
    }
}

fn elaborate_cong_between_equalities(
    pool: &mut PrimitivePool,
    step: &StepNode,
    (f1, f2): (&Rc<Term>, &Rc<Term>),
    (g1, g2): (&Rc<Term>, &Rc<Term>),
) -> Result<StepNode, CheckerError> {
    // At this point, we know there are either one or two premises
    assert!(step.premises.len() <= 2);

    // Similar to the `refl` case, sometimes `cong` is used to derive `(= (= a b) (= b a))`. In this
    // case, we turn the step into a `eq_symmetric` step, without any premise
    if f1 == g2 && f2 == g1 {
        return Ok(StepNode {
            rule: "eq_symmetric".to_owned(),
            premises: vec![],
            ..step.clone()
        });
    }

    let premises: Vec<_> = step
        .premises
        .iter()
        .map(|p| match_term!((= a b) = p.clause()[0]).unwrap())
        .collect();

    let mut ids = IdHelper::new(&step.id);
    if check_cong(&premises, [f1, f2], [g1, g2], None) {
        // None are flipped, everything is good
        Ok(flip_needed_premises(pool, step.clone()))
    } else if check_cong(&premises, [f2, f1], [g1, g2], None) {
        // f is flipped
        let eq_symm_step = build_eq_symm_step(pool, f1, f2, ids.next_id(), step.depth);
        let cong_step = StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![
                build_term!(pool, (= (= {f2.clone()} {f1.clone()}) (= {g1.clone()} {g2.clone()}))),
            ],
            rule: "cong".to_owned(),
            premises: step.premises.clone(),
            ..StepNode::default()
        };
        let cong_step = Rc::new(ProofNode::Step(flip_needed_premises(pool, cong_step)));
        let trans_step = StepNode {
            id: step.id.clone(),
            depth: step.depth,
            clause: step.clause.clone(),
            rule: "trans".to_owned(),
            premises: vec![eq_symm_step, cong_step],
            ..StepNode::default()
        };
        Ok(trans_step)
    } else if check_cong(&premises, [f1, f2], [g2, g1], None) {
        // g is flipped
        let eq_symm_step = build_eq_symm_step(pool, g2, g1, ids.next_id(), step.depth);
        let cong_step = StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![
                build_term!(pool, (= (= {f1.clone()} {f2.clone()}) (= {g2.clone()} {g1.clone()}))),
            ],
            rule: "cong".to_owned(),
            premises: step.premises.clone(),
            ..StepNode::default()
        };
        let cong_step = Rc::new(ProofNode::Step(flip_needed_premises(pool, cong_step)));
        let trans_step = StepNode {
            id: step.id.clone(),
            depth: step.depth,
            clause: step.clause.clone(),
            rule: "trans".to_owned(),
            premises: vec![cong_step, eq_symm_step],
            ..StepNode::default()
        };
        Ok(trans_step)
    } else if check_cong(&premises, [f2, f1], [g2, g1], None) {
        // Both are flipped. This can only happen if there are two premises
        assert_eq!(step.premises.len(), 2);

        // In this case, we can just reverse the order of the premises
        let mut new_step = step.clone();
        new_step.premises.reverse();
        Ok(flip_needed_premises(pool, new_step))
    } else {
        // the step is invalid
        unreachable!()
    }
}

pub fn eq_congruent(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert!(step.clause.len() >= 2);

    let premises: Vec<_> = step.clause[..step.clause.len() - 1]
        .iter()
        .map(|term| match_term!((not (= t u)) = term).unwrap())
        .collect();

    let (f, g) = match_term_err!((= f g) = step.clause.last().unwrap())?;
    let [f_args, g_args] = [f, g].map(term_args);

    let mut flipped = vec![false; premises.len()];
    let is_valid = check_cong(&premises, f_args, g_args, Some(&mut flipped));
    assert!(is_valid);

    if !flipped.iter().any(|f| *f) {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    // If there are any flipped premises, we need to change the `eq_congruent` step's conclusion to
    // fix them, and then reconstruct the original conclusion. The general idea is to, for each
    // flipped premise `(not (= u t))`, add an `eq_symmetric` step concluding `(= (= u t) (= t u))`,
    // and use `equiv1` to turn that into `(cl (not (= u t)) (= t u))`. Then, we resolve the fixed
    // `eq_congruent` step with this `equiv1` step to replace the flipped premise, and reach the
    // original conclusion after a reordering.
    //
    // The annoying case is when there are duplicate flipped premises. Then, we must take extra
    // care to make sure the resolution step is still valid. We must:
    // - first apply a `contraction` to the `eq_congruent` step before resolution,
    // - omit the `eq_symmetric`/`equiv1` construction for duplicate premises,
    // - omit these duplicates in the `resolution` conclusion,
    // - and add a `weakening` step to get back the conclusion with duplicates.

    let mut ids = IdHelper::new(&step.id);

    // (1) First, we build the fixed `eq_congruent` step, possibly applying a `contraction` if there
    // are duplicate premises.
    let fixed_eq_congruent_step = {
        let fixed_conclusion: Vec<_> = premises
            .iter()
            .zip(&flipped)
            .map(|(&(t, u), flipped)| if *flipped { (u, t) } else { (t, u) })
            .map(|(t, u)| build_term!(pool, (not (= {t.clone()} {u.clone()}))))
            .chain(std::iter::once(step.clause.last().unwrap().clone()))
            .collect();

        let contracted: Vec<_> = fixed_conclusion.iter().dedup().cloned().collect();
        let needs_contraction = contracted.len() != fixed_conclusion.len();

        let eq_congruent = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: fixed_conclusion,
            rule: "eq_congruent".to_owned(),
            ..StepNode::default()
        }));

        if needs_contraction {
            Rc::new(ProofNode::Step(StepNode {
                id: ids.next_id(),
                depth: step.depth,
                clause: contracted,
                rule: "contraction".to_owned(),
                premises: vec![eq_congruent],
                ..StepNode::default()
            }))
        } else {
            eq_congruent
        }
    };

    let mut seen_premises = HashSet::new();
    let mut resolution_premises = vec![fixed_eq_congruent_step];
    let mut resolution_args = Vec::new();

    // (2) Then, we construct `eq_symmetric`/`equiv1` steps for each unique flipped premise.
    for (&(u, t), _) in premises
        .iter()
        .zip(&flipped)
        .filter(|(_, flipped)| **flipped)
    {
        // The resolution step we are building would not work with duplicate premises, so we must
        // skip them. This will be fixed later with a weakening step.
        if !seen_premises.insert((u.clone(), t.clone())) {
            continue;
        }

        let t_eq_u = build_term!(pool, (= {t.clone()} {u.clone()}));
        let u_eq_t = build_term!(pool, (= {u.clone()} {t.clone()}));
        let eq_symmetric = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![build_term!(pool, (= {u_eq_t.clone()} {t_eq_u.clone()}))],
            rule: "eq_symmetric".to_owned(),
            ..StepNode::default()
        }));
        let equiv_1 = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![build_term!(pool, (not { u_eq_t })), t_eq_u.clone()],
            rule: "equiv1".to_owned(),
            premises: vec![eq_symmetric],
            ..StepNode::default()
        }));
        resolution_premises.push(equiv_1);
        resolution_args.extend([t_eq_u, pool.bool_false()]);
    }

    // (3) Next, we create the resolution step.
    let resolution_clause: Vec<_> = {
        flipped.push(false); // Add an extra `false` for the conclusion term

        // The conclusion of the resolution step will be, first, all terms which are not flipped
        // premises
        step.clause
            .iter()
            .enumerate()
            .filter(|(i, _)| !flipped[*i])
            // ...followed by the flipped premises, which are added by resolution
            .chain(step.clause.iter().enumerate().filter(|(i, _)| flipped[*i]))
            .map(|(_, t)| t.clone())
            .dedup() // ...with duplicates removed
            .collect()
    };

    // If there are any duplicate premises, they were omitted in the resolution clause. We will add
    // them back with a `weakening` step.
    let needs_weakening = step.clause.len() != resolution_clause.len();
    let resolution = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: resolution_clause,
        rule: "resolution".to_owned(),
        premises: resolution_premises,
        args: resolution_args,
        ..StepNode::default()
    }));

    // (4) If needed, we apply `weakening` to add back the duplicate premises.
    let weakened = if needs_weakening {
        // we have to make sure that the terms added by weakening are at the end of the clause
        let mut missing: MultiSet<_> = step.clause.iter().collect();
        for term in resolution.clause() {
            assert!(missing.get(&term) != 0);
            missing.remove(term);
        }
        let mut clause = resolution.clause().to_vec();
        clause.extend(missing.into_iter().cloned());

        Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause,
            rule: "weakening".to_owned(),
            premises: vec![resolution],
            ..StepNode::default()
        }))
    } else {
        resolution
    };

    // (5) Finally, we apply a reordering to get back the original clause.
    Ok(Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "reordering".to_owned(),
        premises: vec![weakened],
        ..StepNode::default()
    })))
}
