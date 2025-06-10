use crate::translation::eunoia::eunoia_ast::*;

/// Definition of Alethe in Eunoia, following [AletheInAlf](https://github.com/cvc5/aletheinalf/).
use std::string::String;

// TODO: THIS IS ONLY DONE TO AVOID THE COMPLEXITIES OF DECLARING
// AND DEALING WITH GLOBALS IN RUST.
pub struct AletheTheory {
    // Built-in operators.
    pub cl: Symbol,
    // To represent the empty clause.
    pub empty_cl: Symbol,
    pub ite: Symbol,

    // Logical operators.
    pub and: Symbol,
    pub not: Symbol,
    pub or: Symbol,

    // Arithmetic
    pub add: Symbol,
    pub sub: Symbol,
    pub mult: Symbol,
    pub int_div: Symbol,
    pub real_div: Symbol,

    // Comparison.
    pub eq: Symbol,
    pub lt: Symbol,
    pub le: Symbol,
    pub gt: Symbol,
    pub ge: Symbol,

    // Rules' names.
    // TODO: order this
    pub let_rule: Symbol,
    pub equiv_pos2: Symbol,
    pub bind: Symbol,
    pub refl: Symbol,
    pub subproof: Symbol,
    pub forall_inst: Symbol,
    pub la_generic: Symbol,
    pub discard_context: Symbol,
    pub onepoint: Symbol,
    pub sko_ex: Symbol,
    pub cong_variadic: Symbol,
    pub cong_nary: Symbol,

    // Context representation and manipulation.
    pub ctx: Symbol,
    // To bind variables in a context.
    pub var: Symbol,

    // Binders.
    pub let_binder: Symbol,
    pub forall_binder: Symbol,
    pub exists_binder: Symbol,
    pub choice_binder: Symbol,

    // VarList constructors
    pub varlist_cons: Symbol,
    pub varlist_nil: Symbol,
}

impl AletheTheory {
    pub fn new() -> Self {
        AletheTheory {
            cl: String::from("@cl"),
            empty_cl: String::from("@empty_cl"),
            ite: String::from("ite"),

            // Logical operators.
            and: String::from("and"),
            or: String::from("or"),
            not: String::from("not"),

            // Arithemtic
            add: String::from("+"),
            sub: String::from("-"),
            mult: String::from("*"),
            int_div: String::from("div"),
            real_div: String::from("/"),

            // Comparison.
            eq: String::from("="),
            lt: String::from("<"),
            le: String::from("<="),
            gt: String::from(">"),
            ge: String::from(">="),

            // Rules' names.
            let_rule: String::from("let_elim"),
            refl: String::from("refl"),
            equiv_pos2: String::from("equiv_pos2"),
            subproof: String::from("subproof"),
            forall_inst: String::from("forall_inst"),
            bind: String::from("bind"),
            la_generic: String::from("la_generic"),
            discard_context: String::from("discard_context"),
            onepoint: String::from("onepoint"),
            sko_ex: String::from("sko_ex"),
            cong_variadic: String::from("cong_variadic"),
            cong_nary: String::from("cong_nary"),

            // Context representation and manipulation.
            ctx: String::from("@ctx"),
            var: String::from("@var"),

            // Binders.
            let_binder: String::from("@let"),
            forall_binder: String::from("forall"),
            exists_binder: String::from("exists"),
            choice_binder: String::from("choice"),

            // VarList constructors
            varlist_cons: String::from("@varlist"),
            varlist_nil: String::from("@varlist.nil"),
        }
    }

    // Utilities to help in the translation of steps that use specific rules.

    // Helps in extracting the lhs and rhs of a conclusion clause of
    // the form (@cl ("=", t1, t2)).
    // PRE: {conclusion is an EunoiaTerm of the form (@cl ("=", t1, t2)) }
    pub fn extract_eq_lhs_rhs(&self, conclusion: &EunoiaTerm) -> (EunoiaTerm, EunoiaTerm) {
        match conclusion {
            // TODO: just assuming that cl and clause are correct
            EunoiaTerm::App(cl, clause) => match clause.as_slice() {
                [EunoiaTerm::App(eq, lhs_rhs)] => match lhs_rhs.as_slice() {
                    [lhs, rhs] => {
                        assert!(*cl == self.cl);
                        assert!(*eq == self.eq);
                        (lhs.clone(), rhs.clone())
                    }

                    _ => panic!(),
                },

                _ => panic!(),
            },

            _ => {
                panic!();
            }
        }
    }

    // Helps in extracting the consequent of an implication in the form
    // (@cl (not p1 or p2)).
    // PRE: {conclusion is an EunoiaTerm of the form (@cl (not p1 or p2)) }
    pub fn extract_consequent(&self, conclusion: &EunoiaTerm) -> EunoiaTerm {
        match conclusion {
            // @cl
            EunoiaTerm::App(cl, disjuncts) => match disjuncts.as_slice() {
                [.., consequent] => {
                    // NOTE: not checking the structure of remaining disjuncts
                    assert!(*cl == self.cl);
                    consequent.clone()
                }

                _ => {
                    println!("Actual conclusion: {:?}", conclusion);
                    panic!()
                }
            },

            _ => {
                panic!();
            }
        }
    }

    pub fn extract_cl_disjuncts(&self, conclusion: &EunoiaTerm) -> Vec<EunoiaTerm> {
        match conclusion {
            // @cl
            EunoiaTerm::App(cl, disjuncts) => {
                assert!(*cl == self.cl);
                disjuncts.clone()
            }

            _ => {
                println!("Actual term: {:?}", conclusion);
                panic!()
            }
        }
    }

    // Helps in extracting the top-level operator applied in a unit-clause of
    // the form (@cl ("=", f t1 ..., f t2 ...)).
    // PRE: {conclusion is an EunoiaTerm of the form (@cl ("=", f t1 ..., f t2 ...)) }
    fn extract_top_level_op(&self, conclusion: &EunoiaTerm) -> String {
        let (lhs, rhs) = self.extract_eq_lhs_rhs(conclusion);

        match (lhs, rhs) {
            // TODO: just assuming that cl and clause are correct
            (EunoiaTerm::App(f1, ..), EunoiaTerm::App(f2, ..)) => {
                if *f1 == *f2 {
                    f1
                } else {
                    // { *f1 != *f2 }
                    panic!();
                }
            }

            _ => {
                // Pre not satisfied
                panic!();
            }
        }
    }

    // Determines which congruence rule should be applied, considering the
    // given conclusion.
    // PRE: {conclusion is an EunoiaTerm of the form (@cl ("=", f t1 ..., f t2 ...)) }
    pub fn select_cong_rule(&self, conclusion: &EunoiaTerm) -> String {
        let op = self.extract_top_level_op(conclusion);

        let cong_rule: String = if op == self.cl
            || op == self.or
            || op == self.and
            || op == self.add
            || op == self.mult
        {
            self.cong_variadic.clone()
        } else {
            self.cong_nary.clone()
        };

        cong_rule
    }
}

impl Default for AletheTheory {
    fn default() -> Self {
        AletheTheory::new()
    }
}
