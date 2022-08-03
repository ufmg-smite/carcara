use super::*;
use crate::ast::*;
use ahash::AHashMap;

pub struct DeepEqElaborator<'a> {
    inner: &'a mut Elaborator,
    root_id: &'a str,
    cache: AHashMap<(Rc<Term>, Rc<Term>), (usize, usize)>,
    checker: DeepEqualityChecker,
}

impl<'a> DeepEqElaborator<'a> {
    pub fn new(inner: &'a mut Elaborator, root_id: &'a str) -> Self {
        let cache = AHashMap::new();
        let checker = DeepEqualityChecker::new(true, false);
        Self { inner, root_id, cache, checker }
    }

    /// Takes two terms that are equal modulo reordering of equalities, and returns a premise that
    /// proves their equality.
    pub fn elaborate(&mut self, pool: &mut TermPool, a: Rc<Term>, b: Rc<Term>) -> (usize, usize) {
        // TODO: Make this method return an error instead of panicking if the terms aren't equal

        let key = (a, b);
        if let Some(p) = self.cache.get(&key) {
            return *p;
        }
        // We have to do this to avoid moving `a` and `b` when calling `self.cache.get`
        let (a, b) = key;

        if a == b {
            let id = self.inner.get_new_id(self.root_id);
            return self.inner.add_refl_step(pool, a, id);
        }

        if let Some((a_left, a_right)) = match_term!((= x y) = a) {
            if let Some((b_left, b_right)) = match_term!((= x y) = b) {
                if DeepEq::eq(&mut self.checker, a_left, b_right)
                    && DeepEq::eq(&mut self.checker, a_right, b_left)
                {
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
                assert_eq!(a_bindings, b_bindings);
                let variable_args = a_bindings.as_slice().to_vec();
                let assignment_args = a_bindings
                    .iter()
                    .map(|x| {
                        let var = x.0.clone();
                        let term = pool.add_term(x.clone().into());
                        (var, term)
                    })
                    .collect();

                self.inner.open_accumulator_subproof();

                let inner_eq = self.elaborate(pool, a_inner.clone(), b_inner.clone());
                if self.inner.accumulator.top_frame_len() == 0 {
                    // The inner equality step may be skipped if it was already derived before. In
                    // this case, the end step must have something to implicitly reference, so we
                    // must add a step that copies that clause to inside the subproof. We do that
                    // with a dummy `reordering` step.
                    let id = self.inner.get_new_id(self.root_id);
                    let clause = vec![build_term!(pool, (= {a_inner.clone()} {b_inner.clone()}))];
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

                let id = self.inner.get_new_id(self.root_id);
                let clause = vec![build_term!(pool, (= {a.clone()} {b.clone()}))];
                let end_step = ProofStep {
                    id,
                    clause,
                    rule: "bind".to_owned(),
                    premises: Vec::new(),
                    args: Vec::new(),
                    discharge: Vec::new(),
                };
                self.inner
                    .close_accumulator_subproof(assignment_args, variable_args, end_step)
            }

            // TODO: To elaborate equalities that use `let` terms, we will need to add a new rule
            // called `bind_let`, similar to `bind`, that can introduce `let` binders
            (Term::Let(_, _), Term::Let(_, _)) => todo!(),

            // Since `choice` and `lambda` terms are not in the SMT-LIB standard, they cannot appear
            // in the premises of a proof, so we would never need to elaborate deep equalities that
            // use these terms.
            (Term::Choice(_, _), Term::Choice(_, _)) => {
                log::error!("Trying to elaborate deep equality between `choice` terms");
                panic!()
            }
            (Term::Lambda(_, _), Term::Lambda(_, _)) => {
                log::error!("Trying to elaborate deep equality between `lambda` terms");
                panic!()
            }
            _ => panic!("terms not equal!"),
        }
    }

    fn build_cong(
        &mut self,
        pool: &mut TermPool,
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
            rule: "cong".into(),
            premises,
            args: Vec::new(),
            discharge: Vec::new(),
        };
        self.inner.add_new_step(step)
    }

    fn flip_equality(
        &mut self,
        pool: &mut TermPool,
        (a, a_left, a_right): (Rc<Term>, Rc<Term>, Rc<Term>),
        (b, b_left, b_right): (Rc<Term>, Rc<Term>, Rc<Term>),
    ) -> (usize, usize) {
        // Let's define:
        //     a := (= x y),
        //     b := (= z w)
        // The simpler case that we have to consider is when `x` equals `w` and `y` equals `z`
        // (syntactically), that is, if we just flip the `b` equality, the terms will be
        // syntactically equal. In this case, we can simply introduce a `refl` step that derives
        // `(= (= x y) (= y x))`.
        //
        // The more complex case happens when `x` is equal to `w` modulo reordering of equalities,
        // but they are not syntactically equal, or the same is true with `y` and `z`. In this case,
        // we need to elaborate the deep equality between `x` and `w` (or `y` and `z`), and from
        // that, prove that `(= (= x y) (= z w))`. We do that by first proving that `(= x w)` (1)
        // and `(= y z)` (2). Then, we introduce a `cong` step that uses (1) and (2) to show that
        // `(= (= x y) (= w z))` (3). After that, we add a `refl` step that derives
        // `(= (= w z) (= z w))` (4). Finally, we introduce a `trans` step with premises (3) and (4)
        // that proves `(= (= x y) (= z w))`. The general format looks like this:
        //
        //     ...
        //     (step t1 (cl (= x w)) ...)
        //     ...
        //     (step t2 (cl (= y z)) ...)
        //     (step t3 (cl (= (= x y) (= w z))) :rule cong :premises (t1 t2))
        //     (step t4 (cl (= (= w z) (= z w))) :rule refl)
        //     (step t5 (cl (= (= x y) (= z w))) :rule trans :premises (t3 t4))
        //
        // If `x` equals `w` syntactically, we can omit the derivation of step `t1`, and remove that
        // premise from step `t3`. We can do the same with step `t2` if `y` equals `z`
        // syntactically. Of course, if both `x` == `w` and `y` == `z`, we fallback to the simpler
        // case, where we only need to introduce a `refl` step.
        //
        // Note that in both cases we are using `refl` steps to prove that `(= (= x y) (= y x))`.
        // Checking these steps still requires deep equality modulo reordering of equalities, even
        // though it only requires checking to a very shallow depth. This somewhat defeats the
        // purpose of elaboration, so it may be changed in the future.

        let mut cong_premises = Vec::new();
        if a_left != b_right {
            cong_premises.push(self.elaborate(pool, a_left, b_right.clone()));
        }
        if a_right != b_left {
            cong_premises.push(self.elaborate(pool, a_right, b_left.clone()));
        }

        // Both `a_left == b_right` and `a_right == b_left`, so we are in the simpler case
        if cong_premises.is_empty() {
            let step = ProofStep {
                id: self.inner.get_new_id(self.root_id),
                clause: vec![build_term!(pool, (= {a} {b}))],
                rule: "refl".into(),
                premises: Vec::new(),
                args: Vec::new(),
                discharge: Vec::new(),
            };
            return self.inner.add_new_step(step);
        }

        let b_flipped = build_term!(pool, (= {b_right} {b_left}));
        let clause = vec![build_term!(pool, (= {a.clone()} {b_flipped.clone()}))];
        let id = self.inner.get_new_id(self.root_id);
        let cong_step = self.inner.add_new_step(ProofStep {
            id,
            clause,
            rule: "cong".into(),
            premises: cong_premises,
            args: Vec::new(),
            discharge: Vec::new(),
        });

        let clause = vec![build_term!(pool, (= {b_flipped} {b.clone()}))];
        let id = self.inner.get_new_id(self.root_id);
        let refl_step = self.inner.add_new_step(ProofStep {
            id,
            clause,
            rule: "refl".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        });

        let clause = vec![build_term!(pool, (= {a} {b}))];
        let id = self.inner.get_new_id(self.root_id);
        self.inner.add_new_step(ProofStep {
            id,
            clause,
            rule: "trans".into(),
            premises: vec![cong_step, refl_step],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    }
}
