use crate::translation::eunoia::ast::*;
/// Definition of Alethe in Eunoia, following [AletheInAlf](https://github.com/cvc5/aletheinalf/).
// NOTE: THIS IS ONLY DONE TO AVOID THE COMPLEXITIES OF DECLARING
// AND DEALING WITH GLOBALS IN RUST.
pub struct AletheTheory {
    // Built-in operators.
    pub cl: &'static str,
    // To represent the empty clause.
    pub empty_cl: &'static str,

    // Logical operators.
    pub and: &'static str,
    pub not: &'static str,
    pub or: &'static str,
    pub xor: &'static str,
    pub implies: &'static str,
    pub ite: &'static str,

    // Arithmetic
    pub add: &'static str,
    pub sub: &'static str,
    pub mult: &'static str,
    pub int_div: &'static str,
    pub real_div: &'static str,

    // Comparison.
    pub eq: &'static str,
    pub lt: &'static str,
    pub le: &'static str,
    pub gt: &'static str,
    pub ge: &'static str,

    // Rules' names.
    // TODO: order this
    pub let_rule: &'static str,
    pub equiv_pos2: &'static str,
    pub bind: &'static str,
    pub bind_let: &'static str,
    pub refl: &'static str,
    pub subproof: &'static str,
    pub forall_inst: &'static str,
    pub la_generic: &'static str,
    pub la_mult_neg: &'static str,
    pub discard_context: &'static str,
    pub onepoint: &'static str,
    pub sko_ex: &'static str,
    pub cong: &'static str,

    // Context representation and manipulation.
    pub ctx: &'static str,
    // To bind variables in a context.
    pub var: &'static str,

    // Binders.
    pub let_binder: &'static str,
    pub forall_binder: &'static str,
    pub exists_binder: &'static str,
    pub choice_binder: &'static str,

    // VarList constructors
    pub varlist_cons: &'static str,
    pub varlist_nil: &'static str,
}

impl AletheTheory {
    pub fn new() -> Self {
        AletheTheory {
            cl: "@cl",
            empty_cl: "@empty_cl",

            // Logical operators.
            and: "and",
            or: "or",
            not: "not",
            xor: "xor",
            implies: "=>",
            ite: "ite",

            // Arithemtic
            add: "+",
            sub: "-",
            mult: "*",
            int_div: "div",
            real_div: "/",

            // Comparison.
            eq: "=",
            lt: "<",
            le: "<=",
            gt: ">",
            ge: ">=",

            // Rules' names.
            let_rule: "let_elim",
            refl: "refl",
            equiv_pos2: "equiv_pos2",
            subproof: "subproof",
            forall_inst: "forall_inst",
            bind: "bind",
            bind_let: "bind_let",
            la_generic: "la_generic",
            la_mult_neg: "la_mult_neg",
            discard_context: "discard_context",
            onepoint: "onepoint",
            sko_ex: "sko_ex",
            cong: "cong",

            // Context representation and manipulation.
            ctx: "@ctx",
            var: "@var",

            // Binders.
            let_binder: "@let",
            forall_binder: "forall",
            exists_binder: "exists",
            choice_binder: "choice",

            // VarList constructors
            varlist_cons: "@varlist",
            varlist_nil: "@varlist.nil",
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
}

impl Default for AletheTheory {
    fn default() -> Self {
        AletheTheory::new()
    }
}
