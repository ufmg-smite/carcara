use super::*;
use crate::{
    ast::*,
    utils::{DedupIterator, HashMapStack},
};

pub(super) struct PolyeqElaborator<'a> {
    ids: &'a mut IdHelper,
    root_depth: usize,
    cache: HashMapStack<(Rc<Term>, Rc<Term>), Rc<ProofNode>>,
    checker: PolyeqComparator,
    context: Option<ContextStack>,
}

impl<'a> PolyeqElaborator<'a> {
    pub fn new(id_helper: &'a mut IdHelper, root_depth: usize, is_alpha_equivalence: bool) -> Self {
        Self {
            ids: id_helper,
            root_depth,
            cache: HashMapStack::new(),
            checker: PolyeqComparator::new(true, is_alpha_equivalence, false),
            context: is_alpha_equivalence.then(ContextStack::new),
        }
    }

    /// Takes two terms that are equal modulo reordering of equalities, and returns a premise that
    /// proves their equality.
    pub fn elaborate(
        &mut self,
        pool: &mut dyn TermPool,
        a: Rc<Term>,
        b: Rc<Term>,
    ) -> Rc<ProofNode> {
        let key = (a, b);
        if let Some(p) = self.cache.get(&key) {
            return p.clone();
        }
        // We have to do this to avoid moving `a` and `b` when calling `self.cache.get`
        let (a, b) = key.clone();
        let result = self.elaborate_impl(pool, a, b);
        self.cache.insert(key, result.clone());
        result
    }

    fn elaborate_impl(
        &mut self,
        pool: &mut dyn TermPool,
        a: Rc<Term>,
        b: Rc<Term>,
    ) -> Rc<ProofNode> {
        if self.directly_eq(pool, &a, &b) {
            let id = self.ids.next_id();
            return add_refl_step(pool, a, b, id, self.depth());
        }

        if let Some((a_left, a_right)) = match_term!((= x y) = a) {
            if let Some((b_left, b_right)) = match_term!((= x y) = b) {
                if self.polyeq(pool, a_left, b_right) && self.polyeq(pool, a_right, b_left) {
                    let [a_left, a_right, b_left, b_right] =
                        [a_left, a_right, b_left, b_right].map(Clone::clone);
                    return self.flip_equality(pool, (a, a_left, a_right), (b, b_left, b_right));
                }
            }
        }

        match (a.as_ref(), b.as_ref()) {
            (Term::App(a_func, a_args), Term::App(b_func, b_args)) => {
                assert_eq!(a_func, b_func);
                assert_eq!(a_args.len(), b_args.len());
                self.build_cong(pool, (&a, &b), (a_args, b_args))
            }
            (Term::Op(a_op, a_args), Term::Op(b_op, b_args)) => {
                assert_eq!(a_op, b_op);
                assert_eq!(a_args.len(), b_args.len());
                self.build_cong(pool, (&a, &b), (a_args, b_args))
            }

            // Since `choice` and `lambda` terms are not in the SMT-LIB standard, they cannot appear
            // in the premises of a proof, so we would never need to elaborate polyequalities that
            // use these terms.
            (Term::Binder(b @ (Binder::Choice | Binder::Lambda), _, _), _)
            | (_, Term::Binder(b @ (Binder::Choice | Binder::Lambda), _, _)) => {
                log::error!("Trying to elaborate polyequality between `{b}` terms");
                panic!()
            }
            (Term::Binder(a_q, a_bindings, a_inner), Term::Binder(b_q, b_bindings, b_inner)) => {
                assert_eq!(a_q, b_q);

                let args: Vec<_> = match &mut self.context {
                    None => {
                        assert_eq!(a_bindings, b_bindings);

                        let variable_args = a_bindings.iter().cloned().map(AnchorArg::Variable);

                        let assign_args = a_bindings.iter().map(|(name, sort)| {
                            let value = pool.add(Term::new_var(name, sort.clone()));
                            AnchorArg::Assign((name.clone(), sort.clone()), value)
                        });

                        variable_args.chain(assign_args).collect()
                    }
                    Some(c) => {
                        let a_sorts = a_bindings.iter().map(|(_, sort)| sort);
                        assert!(a_sorts.eq(b_bindings.iter().map(|(_, sort)| sort)));

                        let variable_args = a_bindings
                            .iter()
                            .chain(b_bindings)
                            .dedup()
                            .cloned()
                            .map(AnchorArg::Variable);

                        let assign_args =
                            a_bindings.iter().zip(b_bindings).map(|((name, sort), b)| {
                                AnchorArg::Assign(
                                    (name.clone(), sort.clone()),
                                    pool.add(b.clone().into()),
                                )
                            });

                        let args: Vec<_> = variable_args.chain(assign_args).collect();
                        c.push(&args);
                        args
                    }
                };

                self.open_subproof();
                let previous = self.create_bind_subproof(pool, (a_inner.clone(), b_inner.clone()));

                if let Some(c) = &mut self.context {
                    c.pop();
                }
                let last_step = StepNode {
                    id: String::new(), // this will be overwritten later
                    depth: self.depth(),
                    clause: vec![build_term!(pool, (= {a.clone()} {b.clone()}))],
                    rule: "bind".to_owned(),
                    previous_step: Some(previous),
                    ..Default::default()
                };
                self.close_subproof(args, last_step)
            }

            (Term::Let(a_bindings, a_inner), Term::Let(b_bindings, b_inner)) => {
                assert_eq!(a_bindings.len(), b_bindings.len());

                let args: Vec<_> = a_bindings
                    .iter()
                    .map(|(name, value)| AnchorArg::Variable((name.clone(), pool.sort(value))))
                    .collect();

                self.open_subproof();

                // The values of the binding lists in the `let` terms may not be syntactically
                // identical, in which case we need to prove their equality so the `bind_let` step
                // is valid.
                let premises = a_bindings
                    .iter()
                    .zip(b_bindings)
                    .filter_map(|(a, b)| {
                        assert_eq!(a.0, b.0);
                        if a.1 == b.1 {
                            None
                        } else {
                            Some(self.elaborate(pool, a.1.clone(), b.1.clone()))
                        }
                    })
                    .collect();

                let previous = self.create_bind_subproof(pool, (a_inner.clone(), b_inner.clone()));
                let last_step = StepNode {
                    id: String::new(), // this will be overwritten later
                    depth: self.depth(),
                    clause: vec![build_term!(pool, (= {a.clone()} {b.clone()}))],
                    rule: "bind_let".to_owned(),
                    premises,
                    args: Vec::new(),
                    discharge: Vec::new(),
                    previous_step: Some(previous),
                };
                self.close_subproof(args, last_step)
            }
            _ => panic!("terms not equal!"),
        }
    }

    fn depth(&mut self) -> usize {
        self.root_depth + self.cache.height() - 1
    }

    /// Returns `true` if the terms are directly equal, modulo application of the current context.
    fn directly_eq(&mut self, pool: &mut dyn TermPool, a: &Rc<Term>, b: &Rc<Term>) -> bool {
        match &mut self.context {
            Some(c) => c.apply(pool, a) == *b,
            None => a == b,
        }
    }

    /// Returns `true` if the terms are equal modulo reordering of inequalities, and modulo
    /// application of the current context.
    fn polyeq(&mut self, pool: &mut dyn TermPool, a: &Rc<Term>, b: &Rc<Term>) -> bool {
        match &mut self.context {
            Some(c) => Polyeq::eq(&mut self.checker, &c.apply(pool, a), b),
            None => Polyeq::eq(&mut self.checker, a, b),
        }
    }

    fn build_cong(
        &mut self,
        pool: &mut dyn TermPool,
        (a, b): (&Rc<Term>, &Rc<Term>),
        (a_args, b_args): (&[Rc<Term>], &[Rc<Term>]),
    ) -> Rc<ProofNode> {
        let clause = vec![build_term!(pool, (= {a.clone()} {b.clone()}))];
        let premises = a_args
            .iter()
            .zip(b_args)
            .filter_map(|(a, b)| {
                if a == b {
                    None
                } else {
                    Some(self.elaborate(pool, a.clone(), b.clone()))
                }
            })
            .collect();

        Rc::new(ProofNode::Step(StepNode {
            id: self.ids.next_id(),
            depth: self.depth(),
            clause,
            rule: "cong".to_owned(),
            premises,
            ..Default::default()
        }))
    }

    fn flip_equality(
        &mut self,
        pool: &mut dyn TermPool,
        (a, a_left, a_right): (Rc<Term>, Rc<Term>, Rc<Term>),
        (b, b_left, b_right): (Rc<Term>, Rc<Term>, Rc<Term>),
    ) -> Rc<ProofNode> {
        // Let's define:
        //     a := (= x y)
        //     b := (= y' x')
        // The simpler case that we have to consider is when x equals x' and y equals y'
        // (syntactically), that is, if we just flip the b equality, the terms will be
        // syntactically equal. In this case, we can simply introduce an `equiv_simplify` step that
        // derives `(= (= x y) (= y x))`.
        //
        // The more complex case happens when x is equal to x', but they are not syntactically
        // identical, or the same is true with y and y'. This can happen if they are equal modulo
        // reordering of equalities, or if they are equal modulo the application of the current
        // context (in the case of alpha equivalence).
        //
        // In this case, we need to elaborate the polyequality between x and x' (or y and y'), and
        // from that, prove that `(= (= x y) (= y' x'))`. We do that by first proving that
        // `(= x x')` (1) and `(= y y')` (2). Then, we introduce a `cong` step that uses (1) and (2)
        // to show that `(= (= x y) (= x' y'))` (3). After that, we add an `equiv_simplify` step
        // that derives `(= (= x' y') (= y' x'))` (4). Finally, we introduce a `trans` step with
        // premises (3) and (4) that proves `(= (= x y) (= y' x'))`. The general format looks like
        // this:
        //
        //     ...
        //     (step t1 (cl (= x x')) ...)
        //     ...
        //     (step t2 (cl (= y y')) ...)
        //     (step t3 (cl (= (= x y) (= x' y'))) :rule cong :premises (t1 t2))
        //     (step t4 (cl (= (= x' y') (= y' x'))) :rule equiv_simplify)
        //     (step t5 (cl (= (= x y) (= y' x'))) :rule trans :premises (t3 t4))
        //
        // If x equals x' syntactically, we can omit the derivation of step `t1`, and remove that
        // premise from step `t3`. We can do the same with step `t2` if y equals y' syntactically.
        // Of course, if both x == x' and y == y', we fallback to the simpler case, where we only
        // need to introduce an `equiv_simplify` step.

        // Simpler case
        if a_left == b_right && a_right == b_left {
            return Rc::new(ProofNode::Step(StepNode {
                id: self.ids.next_id(),
                depth: self.depth(),
                clause: vec![build_term!(pool, (= {a} {b}))],
                rule: "equiv_simplify".to_owned(),
                ..Default::default()
            }));
        }

        // To create the `cong` step that derives `(= (= x y) (= x' y'))`, we use the `build_cong`
        // method. This method also creates the steps that prove `(= x x')` and `(= y y')`, if
        // needed.
        let flipped_b = build_term!(pool, (= {b_right.clone()} {b_left.clone()}));
        let cong_step = self.build_cong(
            pool,
            (&a, &flipped_b),
            (&[a_left, a_right], &[b_right, b_left]),
        );

        // It might be the case that `x'` is syntactically equal to `y'`, which would mean that we
        // are adding an `equiv_simplify` step to prove a reflexivity step. This is not valid
        // according to the `equiv_simplify` specification, so we must change the rule to `refl` in
        // this case.
        let rule = if b == flipped_b {
            "refl".to_owned()
        } else {
            "equiv_simplify".to_owned()
        };
        let equiv_step = Rc::new(ProofNode::Step(StepNode {
            id: self.ids.next_id(),
            depth: self.depth(),
            clause: vec![build_term!(pool, (= {flipped_b} {b.clone()}))],
            rule,
            ..Default::default()
        }));

        Rc::new(ProofNode::Step(StepNode {
            id: self.ids.next_id(),
            depth: self.depth(),
            clause: vec![build_term!(pool, (= {a} {b}))],
            rule: "trans".to_owned(),
            premises: vec![cong_step, equiv_step],
            ..Default::default()
        }))
    }

    fn open_subproof(&mut self) {
        self.cache.push_scope();
        self.ids.push();
    }

    fn close_subproof(&mut self, args: Vec<AnchorArg>, mut last_step: StepNode) -> Rc<ProofNode> {
        self.cache.pop_scope();
        self.ids.pop();

        // We overwrite the last step id to be correct in relation to the outer subproof
        last_step.id = self.ids.next_id();

        Rc::new(ProofNode::Subproof(SubproofNode {
            last_step: Rc::new(ProofNode::Step(last_step)),
            args,
            outbound_premises: Vec::new(), // TODO: recompute outbound premises
        }))
    }

    /// Creates the subproof for a `bind` or `bind_let` step, used to derive the equality of
    /// quantifier or `let` terms. This assumes the subproof has already been opened.
    fn create_bind_subproof(
        &mut self,
        pool: &mut dyn TermPool,
        inner_equality: (Rc<Term>, Rc<Term>),
    ) -> Rc<ProofNode> {
        let (a, b) = inner_equality;

        let inner_eq = self.elaborate(pool, a.clone(), b.clone());

        // The inner equality step may be skipped if it was already derived before. In this case,
        // the end step must have something to implicitly reference, so we must add a step that
        // copies that clause to inside the subproof. We do that with a dummy `reordering` step.
        if inner_eq.as_step().is_some_and(|s| s.depth == self.depth()) {
            inner_eq
        } else {
            let clause = vec![build_term!(pool, (= {a} {b}))];
            Rc::new(ProofNode::Step(StepNode {
                id: self.ids.next_id(),
                depth: self.depth(),
                clause,
                rule: "reordering".to_owned(),
                premises: vec![inner_eq],
                ..Default::default()
            }))
        }
    }
}
