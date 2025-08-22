use super::IdHelper;
use crate::{ast::*, checker::error::CheckerError};

fn check_cong(
    premises: &[(&Rc<Term>, &Rc<Term>)],
    f_args: [&Rc<Term>; 2],
    g_args: [&Rc<Term>; 2],
) -> bool {
    let mut premises = premises.iter().peekable();

    for (f_arg, g_arg) in f_args.into_iter().zip(g_args) {
        let expected = (f_arg.as_ref(), g_arg.as_ref());
        match premises.peek() {
            // If the next premise can justify that the arguments are equal, we consume it. We
            // prefer consuming the premise even if the arguments are directly equal
            Some((t, u)) if expected == (t, u) || expected == (u, t) => {
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

pub fn cong(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.clause.len(), 1);
    assert!(!step.premises.is_empty());

    let unchanged = || Ok(Rc::new(ProofNode::Step(step.clone())));

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

    let (Term::Op(Operator::Equals, f_args), Term::Op(Operator::Equals, g_args)) =
        (f.as_ref(), g.as_ref())
    else {
        return unchanged();
    };

    let ([f1, f2], [g1, g2]) = (f_args.as_slice(), g_args.as_slice()) else {
        return unchanged();
    };
    // At this point, we know there are either one or two premises
    assert!(step.premises.len() <= 2);

    // Similar to the `refl` case, sometimes `cong` is used to derive `(= (= a b) (= b a))`. In this
    // case, we turn the step into a `eq_symmetric` step, without any premise
    if f1 == g2 && f2 == g1 {
        return Ok(Rc::new(ProofNode::Step(StepNode {
            rule: "eq_symmetric".to_owned(),
            premises: vec![],
            ..step.clone()
        })));
    }

    let premises: Vec<_> = step
        .premises
        .iter()
        .map(|p| match_term!((= a b) = p.clause()[0]).unwrap())
        .collect();

    let mut ids = IdHelper::new(&step.id);
    if check_cong(&premises, [f1, f2], [g1, g2]) {
        // None are flipped, everything is good
        unchanged()
    } else if check_cong(&premises, [f2, f1], [g1, g2]) {
        // f is flipped
        let eq_symm_step = build_eq_symm_step(pool, f1, f2, ids.next_id(), step.depth);
        let cong_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![
                build_term!(pool, (= (= {f2.clone()} {f1.clone()}) (= {g1.clone()} {g2.clone()}))),
            ],
            rule: "cong".to_owned(),
            premises: step.premises.clone(),
            ..StepNode::default()
        }));
        let trans_step = Rc::new(ProofNode::Step(StepNode {
            id: step.id.clone(),
            depth: step.depth,
            clause: step.clause.clone(),
            rule: "trans".to_owned(),
            premises: vec![eq_symm_step, cong_step],
            ..StepNode::default()
        }));
        Ok(trans_step)
    } else if check_cong(&premises, [f1, f2], [g2, g1]) {
        // g is flipped
        let eq_symm_step = build_eq_symm_step(pool, g2, g1, ids.next_id(), step.depth);
        let cong_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![
                build_term!(pool, (= (= {f1.clone()} {f2.clone()}) (= {g2.clone()} {g1.clone()}))),
            ],
            rule: "cong".to_owned(),
            premises: step.premises.clone(),
            ..StepNode::default()
        }));
        let trans_step = Rc::new(ProofNode::Step(StepNode {
            id: step.id.clone(),
            depth: step.depth,
            clause: step.clause.clone(),
            rule: "trans".to_owned(),
            premises: vec![cong_step, eq_symm_step],
            ..StepNode::default()
        }));
        Ok(trans_step)
    } else if check_cong(&premises, [f2, f1], [g2, g1]) {
        // Both are flipped. This can only happen if there are two premises
        assert_eq!(step.premises.len(), 2);

        // In this case, we can just reverse the order of the premises
        let mut new_step = step.clone();
        new_step.premises.reverse();
        Ok(Rc::new(ProofNode::Step(new_step)))
    } else {
        // the step is invalid
        unreachable!()
    }
}
