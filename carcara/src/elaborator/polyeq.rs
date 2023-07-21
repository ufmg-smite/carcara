use super::*;
use crate::{
    ast::*,
    utils::{DedupIterator, HashMapStack},
};

pub struct PolyeqElaborator<'a> {
    inner: &'a mut Elaborator,
    root_id: &'a str,
    cache: HashMapStack<(Rc<Term>, Rc<Term>), (usize, usize)>,
    checker: PolyeqComparator,
    context: Option<ContextStack>,
}

impl<'a> PolyeqElaborator<'a> {
    pub fn new(inner: &'a mut Elaborator, root_id: &'a str, is_alpha_equivalence: bool) -> Self {
        Self {
            inner,
            root_id,
            cache: HashMapStack::new(),
            checker: PolyeqComparator::new(true, is_alpha_equivalence),
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
    ) -> (usize, usize) {
        // TODO: Make this method return an error instead of panicking if the terms aren't equal

        let key = (a, b);
        if let Some(p) = self.cache.get(&key) {
            return *p;
        }
        // We have to do this to avoid moving `a` and `b` when calling `self.cache.get`
        let (a, b) = key.clone();
        let result = self.elaborate_impl(pool, a, b);
        self.cache.insert(key, result);
        result
    }

    fn elaborate_impl(
        &mut self,
        pool: &mut dyn TermPool,
        a: Rc<Term>,
        b: Rc<Term>,
    ) -> (usize, usize) {
        if self.directly_eq(pool, &a, &b) {
            let id = self.inner.get_new_id(self.root_id);
            return self.inner.add_refl_step(pool, a, b, id);
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

            (Term::Quant(a_q, a_bindings, a_inner), Term::Quant(b_q, b_bindings, b_inner)) => {
                assert_eq!(a_q, b_q);

                let (variable_args, assignment_args) = match &mut self.context {
                    None => {
                        assert_eq!(a_bindings, b_bindings);
                        let assignment_args: Vec<_> = a_bindings
                            .iter()
                            .map(|x| {
                                let var = x.0.clone();
                                let term = pool.add(x.clone().into());
                                (var, term)
                            })
                            .collect();

                        (a_bindings.to_vec(), assignment_args)
                    }
                    Some(c) => {
                        assert!(a_bindings
                            .iter()
                            .map(|(_, sort)| sort)
                            .eq(b_bindings.iter().map(|(_, sort)| sort)));
                        let variable_args: Vec<_> = a_bindings
                            .iter()
                            .chain(b_bindings)
                            .dedup()
                            .cloned()
                            .collect();

                        let assigment_args: Vec<_> = a_bindings
                            .iter()
                            .zip(b_bindings)
                            .map(|((a_var, _), b)| (a_var.clone(), pool.add(b.clone().into())))
                            .collect();

                        c.push(pool, &assigment_args, &variable_args).unwrap();
                        (variable_args, assigment_args)
                    }
                };

                self.open_subproof();
                self.create_bind_subproof(pool, (a_inner.clone(), b_inner.clone()));

                if let Some(c) = &mut self.context {
                    c.pop();
                }
                self.close_subproof(
                    assignment_args,
                    variable_args,
                    ProofStep {
                        id: String::new(),
                        clause: vec![build_term!(pool, (= {a.clone()} {b.clone()}))],
                        rule: "bind".to_owned(),
                        premises: Vec::new(),
                        args: Vec::new(),
                        discharge: Vec::new(),
                    },
                )
            }

            (Term::Let(a_bindings, a_inner), Term::Let(b_bindings, b_inner)) => {
                assert_eq!(a_bindings.len(), b_bindings.len());

                let variable_args: Vec<_> = a_bindings
                    .iter()
                    .map(|(name, value)| {
                        let sort = pool.sort(value).as_ref().clone();
                        (name.clone(), pool.add(sort))
                    })
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

                self.create_bind_subproof(pool, (a_inner.clone(), b_inner.clone()));
                self.close_subproof(
                    Vec::new(),
                    variable_args,
                    ProofStep {
                        id: String::new(),
                        clause: vec![build_term!(pool, (= {a.clone()} {b.clone()}))],
                        rule: "bind_let".to_owned(),
                        premises,
                        args: Vec::new(),
                        discharge: Vec::new(),
                    },
                )
            }

            // Since `choice` and `lambda` terms are not in the SMT-LIB standard, they cannot appear
            // in the premises of a proof, so we would never need to elaborate polyequalities that
            // use these terms.
            (Term::Choice(_, _), Term::Choice(_, _)) => {
                log::error!("Trying to elaborate polyequality between `choice` terms");
                panic!()
            }
            (Term::Lambda(_, _), Term::Lambda(_, _)) => {
                log::error!("Trying to elaborate polyequality between `lambda` terms");
                panic!()
            }
            _ => panic!("terms not equal!"),
        }
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
    ) -> (usize, usize) {
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
        let id = self.inner.get_new_id(self.root_id);
        let step = ProofStep {
            id,
            clause,
            rule: "cong".to_owned(),
            premises,
            args: Vec::new(),
            discharge: Vec::new(),
        };
        self.inner.add_new_step(step)
    }

    fn flip_equality(
        &mut self,
        pool: &mut dyn TermPool,
        (a, a_left, a_right): (Rc<Term>, Rc<Term>, Rc<Term>),
        (b, b_left, b_right): (Rc<Term>, Rc<Term>, Rc<Term>),
    ) -> (usize, usize) {
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
            let step = ProofStep {
                id: self.inner.get_new_id(self.root_id),
                clause: vec![build_term!(pool, (= {a} {b}))],
                rule: "equiv_simplify".to_owned(),
                premises: Vec::new(),
                args: Vec::new(),
                discharge: Vec::new(),
            };
            return self.inner.add_new_step(step);
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

        let id = self.inner.get_new_id(self.root_id);
        let equiv_step = self.inner.add_new_step(ProofStep {
            id,
            clause: vec![build_term!(pool, (= {flipped_b} {b.clone()}))],
            rule: "equiv_simplify".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        });

        let id = self.inner.get_new_id(self.root_id);
        self.inner.add_new_step(ProofStep {
            id,
            clause: vec![build_term!(pool, (= {a} {b}))],
            rule: "trans".to_owned(),
            premises: vec![cong_step, equiv_step],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    }

    fn open_subproof(&mut self) {
        self.cache.push_scope();
        self.inner.open_accumulator_subproof();
    }

    fn close_subproof(
        &mut self,
        assignment_args: Vec<(String, Rc<Term>)>,
        variable_args: Vec<SortedVar>,
        end_step: ProofStep,
    ) -> (usize, usize) {
        self.cache.pop_scope();
        self.inner.close_accumulator_subproof(
            assignment_args,
            variable_args,
            end_step,
            self.root_id,
        )
    }

    /// Creates the subproof for a `bind` or `bind_let` step, used to derive the equality of
    /// quantifier or `let` terms. This assumes the accumulator subproof has already been opened.
    fn create_bind_subproof(
        &mut self,
        pool: &mut dyn TermPool,
        inner_equality: (Rc<Term>, Rc<Term>),
    ) {
        let (a, b) = inner_equality;

        let inner_eq = self.elaborate(pool, a.clone(), b.clone());

        // The inner equality step may be skipped if it was already derived before. In this case,
        // the end step must have something to implicitly reference, so we must add a step that
        // copies that clause to inside the subproof. We do that with a dummy `reordering` step.
        if self.inner.accumulator.top_frame_len() == 0 {
            let id = self.inner.get_new_id(self.root_id);
            let clause = vec![build_term!(pool, (= {a} {b}))];
            self.inner.add_new_command(
                ProofCommand::Step(ProofStep {
                    id,
                    clause,
                    rule: "reordering".to_owned(),
                    premises: vec![inner_eq],
                    args: Vec::new(),
                    discharge: Vec::new(),
                }),
                true,
            );
        }
    }
}
