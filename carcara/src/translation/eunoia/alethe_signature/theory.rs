use crate::translation::eunoia::ast::*;

// NOTE: THIS IS ONLY DONE TO AVOID THE COMPLEXITIES OF DECLARING
// AND DEALING WITH GLOBALS IN RUST.

/// Definition of Alethe in Eunoia, following [AletheInEunoia](https://github.com/cvc5/AletheInEunoia).
/// Serves as an additional layer of abstraction for the current compiler to
/// interact with the internals of our current main mechanization in Eunoia.
pub struct AletheTheory {
    // Path to each file of the current AletheInEunoia mechanization.
    pub mechanization_files: Vec<String>,

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
    pub resolution: &'static str,
    pub sko_ex: &'static str,
    pub cong: &'static str,

    // Context representation and manipulation.
    pub ctx: &'static str,
    // To bind variables in a context.
    pub var: &'static str,
    // Name of the assumption that refers to the last introduced context.
    pub ctx_assumption: &'static str,

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
    pub fn new(eunoia_mech: &str) -> Self {
        AletheTheory {
            // Build paths to current mechanization files.
            mechanization_files: vec![
                // Theories
                format!("{}/theories/theory.eo", eunoia_mech),
                // Rules
                format!("{}/rules/alethe.eo", eunoia_mech),
                format!("{}/rules/tautologies.eo", eunoia_mech),
                format!("{}/rules/rare_rules.eo", eunoia_mech),
                // Programs
                format!("{}/programs/programs.eo", eunoia_mech),
                format!("{}/programs/arith.eo", eunoia_mech),
            ],

            // Clauses.
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
            let_rule: "let",
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
            resolution: "resolution",
            sko_ex: "sko_ex",
            cong: "cong",

            // Context representation and manipulation.
            ctx: "@ctx",
            var: "@var",
            ctx_assumption: "context",

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

    /// Helps in extracting the lhs and rhs of a conclusion clause of
    /// the form (@cl ("=", t1, t2)).
    /// PRE: {conclusion is an `EunoiaTerm` of the form (@cl ("=", t1, t2)) }
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

    /// Helps in extracting the consequent of an implication in the form
    /// (@cl (not p1 or p2)).
    /// PRE: {conclusion is an `EunoiaTerm` of the form (@cl (not p1 or p2)) }
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

    pub fn rule_receives_premises(&self, rule: &String) -> bool {
        match rule {
            rule if rule == self.let_rule => true,

            rule if rule == self.bind_let => true,

            rule if rule == self.bind => true,

            rule if rule == self.subproof => true,

            rule if rule == self.onepoint => true,

            rule if rule == self.sko_ex => true,

            _ => false,
        }
    }

    pub fn rule_receives_varying_arguments(&self, rule: &String) -> bool {
        match rule {
            // The coefficients are one single argument.  This means they
            // must be be wrapped in a single function call using an n-ary
            // function.
            rule if rule == self.la_generic => true,

            // It receives the pivots.
            rule if rule == self.resolution => true,

            rule if rule == self.forall_inst => true,

            _ => false,
        }
    }
}
