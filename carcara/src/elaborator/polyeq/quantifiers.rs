use super::*;
use crate::{ast::*, checker::error::CheckerError};
use indexmap::IndexMap;

pub fn forall_inst(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.clause.len(), 1);

    let (quantified, substituted) =
        match_term_err!((or (not quantified) result) = &step.clause[0])?;
    let (bindings, original) = match_term_err!((forall ... original) = quantified)?;

    assert_eq!(step.args.len(), bindings.len());

    // iterate over the bindings and arguments simultaneously, building the substitution
    let substitution: IndexMap<_, _> = bindings
        .iter()
        .zip(&step.args)
        .map(|((var_name, sort), value)| {
            assert_eq!(sort, &pool.sort(value));
            let var = pool.add(Term::new_var(var_name, sort.clone()));
            (var.clone(), value.clone())
        })
        .collect();
    let mut substitution = Substitution::new(pool, substitution)?;

    // Equalities may be reordered, and the application of the substitution might rename bound
    // variables, so we need to compare for alpha-equivalence here
    let expected = substitution.apply(pool, original);

    if *substituted == expected {
        // There was no polyeq needed, so we return the step unchanged
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    // Given that the original forall_inst step has conclusion (cl (or (not quant)) p'), where
    // quant is the forall term, and p' is an alpha-equivalent mutation of the expected term p, the
    // elaboration will have the following shape:
    //
    // (step t1.t1 (cl (= p p')) :rule hole) ; polyequality elaboration
    // (step t1.t2 (cl (= (or (not quant) p) (or (not quant) p'))) :rule cong :premises (t1.t1))
    // (step t1.t3 (cl (not (or (not quant) p)) (or (not quant) p')) :rule equiv1 :premises (t1.t2))
    // (step t1.t4 (cl (or (not quant) p)) :rule forall_inst) ; easy-to-check forall_inst step
    // (step t1 (cl (or (not quant) p')) :rule resolution
    //     :premises (t1.t3 t1.t4) :args ((or (not quant) p) false))
    let mut ids = IdHelper::new(&step.id);
    let p_prime = substituted;
    let p = expected;

    // (cl (= p p'))
    let polyeq_step = {
        let is_alpha_equivalence = !Polyeq::new().mod_reordering(true).eq(&p, p_prime);

        PolyeqElaborator::new(&mut ids, step.depth, is_alpha_equivalence).elaborate(
            pool,
            p.clone(),
            p_prime.clone(),
        )
    };

    let or_term = build_term!(pool, (or (not {quantified.clone()}) {p.clone()}));
    let or_term_prime = build_term!(pool, (or (not {quantified.clone()}) {p_prime.clone()}));

    // (cl (= (or (not quant) p) (or (not quant) p')))
    let cong_step = {
        Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![build_term!(pool, (= {or_term.clone()} {or_term_prime.clone()}))],
            rule: "cong".to_owned(),
            premises: vec![polyeq_step],
            ..StepNode::default()
        }))
    };

    // (cl (not (or (not quant) p)) (or (not quant) p'))
    let equiv1_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![
            build_term!(pool, (not {or_term.clone()})),
            or_term_prime.clone(),
        ],
        rule: "equiv1".to_owned(),
        premises: vec![cong_step],
        ..StepNode::default()
    }));

    // (cl (or (not quant) p))
    let forall_inst_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![or_term.clone()],
        rule: "forall_inst".to_owned(),
        args: step.args.clone(),
        ..StepNode::default()
    }));

    // (cl (or (not quant) p'))
    let resolution_step = Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: vec![or_term_prime],
        rule: "resolution".to_owned(),
        premises: vec![equiv1_step, forall_inst_step],
        args: vec![or_term, pool.bool_false()],
        ..StepNode::default()
    }));

    Ok(resolution_step)
}
