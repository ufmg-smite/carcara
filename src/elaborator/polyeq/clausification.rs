use super::{IdHelper, PolyeqElaborator};
use crate::{
    ast::{
        ContextStack, Operator, ProofNode, Rc, Sort, StepNode, Term, build_term, match_term,
        match_term_err,
        pool::{PrimitivePool, TermPool},
    },
    checker::{apply_bfun_elim, error::CheckerError},
    elaborator::error::ElaborationError,
};
use indexmap::IndexMap;

fn is_flipped(term: &Rc<Term>, a: &Rc<Term>, b: &Rc<Term>) -> bool {
    let diseq_args = match_term!((not (= x y)) = term).unwrap();
    diseq_args != (a, b)
}

/// The elimination `distinct_elim` specifies, obtained by traversing
/// `got` alongside the pairs of `args` and rebuilding only the
/// disequalities that are flipped. If there isn't any, the function
/// returns `None`.
fn canonical_elimination(
    pool: &mut PrimitivePool,
    args: &[Rc<Term>],
    got: &Rc<Term>,
) -> Option<Rc<Term>> {
    match args {
        [] | [_] => unreachable!(),
        [a, b] => is_flipped(got, a, b).then(|| {
            let (a, b) = (a.clone(), b.clone());
            build_term!(pool, (not (= {a} {b})))
        }),
        // special case where rhs is `false`, so there can't be flipped diseqs
        _ if pool.sort(&args[0]).as_ref() == &Sort::Bool => None,
        _ => {
            let n = args.len();
            let mut conjuncts = match_term!((and ...) = got).unwrap().to_vec();
            assert_eq!(conjuncts.len(), n * (n - 1) / 2);
            let mut flipped = false;
            let mut k = 0;
            for i in 0..n {
                for j in (i + 1)..n {
                    if is_flipped(&conjuncts[k], &args[i], &args[j]) {
                        let (a, b) = (args[i].clone(), args[j].clone());
                        conjuncts[k] = build_term!(pool, (not (= {a} {b})));
                        flipped = true;
                    }
                    k += 1;
                }
            }
            flipped.then(|| pool.add(Term::Op(Operator::And, conjuncts)))
        }
    }
}

/// The `distinct_elim` checker accepts each disequality in either
/// orientation, which is not how the rule is specified. The step is
/// changed to generate the expected order.
pub fn distinct_elim(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    assert_eq!(step.clause.len(), 1);
    let (distinct, got) = match_term_err!((= d s) = &step.clause[0])?;
    let args = match_term_err!((distinct ...) = distinct)?;

    let (distinct, got, args) = (distinct.clone(), got.clone(), args.to_vec());
    let Some(expected) = canonical_elimination(pool, &args, &got) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };

    let mut ids = IdHelper::new(&step.id);
    let canonical_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![build_term!(pool, (= {distinct.clone()} {expected.clone()}))],
        rule: "distinct_elim".to_owned(),
        ..StepNode::default()
    }));
    let bridge = PolyeqElaborator::new(&mut ids, step.depth, false).elaborate(pool, expected, got);
    Ok(Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "trans".to_owned(),
        premises: vec![canonical_step, bridge],
        ..StepNode::default()
    })))
}

pub fn bfun_elim(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    assert_eq!(step.premises.len(), 1);
    assert_eq!(step.clause.len(), 1);
    let psi = &step.premises[0].clause()[0];
    let expected = apply_bfun_elim(pool, psi, &mut IndexMap::new()).map_err(CheckerError::from)?;
    let got = &step.clause[0];

    if *got == expected {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    let mut ids = IdHelper::new(&step.id);
    let polyeq_step = PolyeqElaborator::new(&mut ids, step.depth, false).elaborate(
        pool,
        expected.clone(),
        got.clone(),
    );
    let equiv1_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![build_term!(pool, (not {expected.clone()})), got.clone()],
        rule: "equiv1".to_owned(),
        premises: vec![polyeq_step],
        ..StepNode::default()
    }));
    let new_bfun_elim_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![expected.clone()],
        rule: "bfun_elim".to_owned(),
        premises: step.premises.clone(),
        ..StepNode::default()
    }));
    let resolution_step = Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "resolution".to_owned(),
        premises: vec![equiv1_step, new_bfun_elim_step],
        args: vec![expected, pool.bool_false()],
        ..StepNode::default()
    }));
    Ok(resolution_step)
}
