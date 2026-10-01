//! Lambdapi tactics DSL embedded within Rust macros.
//!
//! This module provides a domain-specific language (DSL) for writing Lambdapi proof tactics
//! directly in Rust code. The DSL is implemented using Rust's macro system and allows
//! writing proof scripts in a syntax that closely resembles native Lambdapi tactic syntax.
//!
//! Inspired by the paper: [A DSL embedded in Rust](https://kyleheadley.github.io/PHDWebsite/traitlang-IFL18-draftsubmit.pdf) of Kyle Headley.
//!
//! # Example
//!
//! ```ignore
//! lambdapi! {
//!     assume [a b c];
//!     rewrite lemma1 (arg1) (arg2);
//!     apply theorem;
//!     reflexivity;
//!     end;
//! }
//! ```

/// Macro for constructing Lambdapi `Term`
///
/// This macro provides various patterns for building terms:
/// - `_` produces [`Term::Underscore`]
/// - `or ident` produces a disjunction term
/// - `and ident` produces a conjunction term
/// - `left => right` produces an implication
/// - `f(args...)` produces function application
/// - `@expr` allows embedding arbitrary Rust expressions that evaluate to [`Term`]
/// - Identifiers are converted via [`Term::from`]
///
/// # Examples
///
/// ```ignore
/// make_term![_]                    // Underscore
/// make_term![a => b]               // Implication
/// make_term![f(x y z)]             // Function application
/// make_term![@some_rust_expr]      // Embed expression
/// ```
macro_rules! make_term {
    ( ($( $args:tt ) +) ) => { make_term![  $( $args) + ] };
    (_) => { Term::Underscore };
    (or $i:ident) => { Term::Alethe(LTerm::NOr($i)) };
    (and $i:ident) => { Term::Alethe(LTerm::NAnd($i)) };
    ($l:tt => $r:tt) => { Term::Alethe(LTerm::Implies(Box::new(make_term![$l]) ,  Box::new(make_term![$r]))) };
    ( $f:tt ( $( $args:tt ) + ) ) => { Term::Terms(vec![  make_term![$f], $( make_term![$args] ) , + ]) };
    ( @$( $exp:tt )+ ) => { $( $exp )+  };
    ($f:tt) => { Term::from($f) };
}

pub(crate) use make_term;

/// Macro for creating inline Lambdapi proof fragments.
///
/// This macro wraps a sequence of tactic calls and returns a single `ProofStep`
/// Useful for embedding small proof fragments within larger proof scripts.
///
/// # Example
///
/// ```ignore
/// let step = inline_lambdapi! {
///     reflexivity;
/// };
/// ```
macro_rules! inline_lambdapi {
    ($($tokens:tt)+) => {
        {
            lambdapi_wrapper!(
                begin
                    $($tokens)+
                end;
            ).pop().unwrap()
        }
    }
}

pub(crate) use inline_lambdapi;

/// Core macro for parsing and translating Lambdapi tactics into Rust `ProofStep` objects.
///
/// This macro implements a recursive descent parser that matches Lambdapi tactic syntax
/// and constructs the corresponding Rust proof step data structures. It accumulates
/// proof steps in a vector (`$steps`) and recursively processes the remaining tactics.
///
/// # Supported tactics:
///
/// - `simplify;` - Simplification tactic
/// - `why3;` - Why3 solver invocation
/// - `symmetry;` - Symmetry rule
/// - `reflexivity;` - Reflexivity rule
/// - `eval term;` - Evaluate a term
/// - `refine term;` - Refinement with a term
/// - `apply term;` - Apply a theorem/lemma
/// - `apply term (args...);` - Apply with arguments
/// - `apply term (args...) { subproof };` - Apply with subproofs
/// - `have ident : (goal) { proof };` - Local hypothesis
/// - `assume [idents...];` - Assume variables
/// - `try [tactics];` - Try a tactic sequence
/// - `rewrite term (args...);` - Rewrite using a lemma
/// - `{ code_block };` - Embed Rust code block
/// - `inject(expr);` - Inject proof steps from expression
/// - `admit;` - Admit the goal (incomplete proof)
/// - `end;` - End of proof script
///
/// # Arguments:
///
/// - `$steps` - Mutable vector accumulating `ProofStep`
/// - Remaining tokens represent the tactic sequence to parse
macro_rules! tactic {
    ($steps:ident, simplify; $($body:tt)*) => { $steps.push(ProofStep::Simplify(vec![])) ; tactic![ $steps, $( $body )* ] };
    ($steps:ident, why3; $($body:tt)*) => { $steps.push(ProofStep::Why3) ; tactic![ $steps, $( $body )* ] };
    ($steps:ident, symmetry; $($body:tt)*) => { $steps.push(ProofStep::Symmetry) ; tactic![ $steps, $( $body )* ] };
    ($steps:ident, reflexivity; $($body:tt)*) => { $steps.push(ProofStep::Reflexivity) ; tactic![ $steps, $( $body )* ] };
    ($steps:ident, eval $i:tt; $($body:tt)+) => {
        $steps.push(ProofStep::Eval(Term::from($i)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, eval @$e:expr; $($body:tt)+) => {
        $steps.push(ProofStep::Eval(make_term![$e]));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, refine $i:tt; $($body:tt)+) => {
        $steps.push(ProofStep::Refine(Term::from($i), SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, refine @$e:expr; $($body:tt)+) => {
        $steps.push(ProofStep::Refine(make_term![$e], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    // Apply tactic with identifier (no arguments)
    ($steps:ident, apply $i:tt; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(Term::from($i), SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    // Apply tactic with expression
    ($steps:ident, apply @$e:expr; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(make_term![$e], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    // Apply tactic with single argument
    ($steps:ident, apply $i:tt $arg:tt; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(terms![Term::from($i), ..vec![ make_term![$arg] ]], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    // Apply tactic with multiple arguments in parentheses
    ($steps:ident, apply $i:tt  $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    // Apply tactic with arguments and subproofs
    ($steps:ident, apply $i:tt  $( ( $($args:tt) + ) ) * $( { $($subproof:tt) * } ) + ; $($body:tt)+) => {
        let mut sub_proofs: Vec<Proof> = Vec::new();

        $(
            {
                let sub_proof = lambdapi_wrapper!{ begin $( $subproof )* end; };
                sub_proofs.push(Proof(sub_proof));
            }
        )*;

        $steps.push(ProofStep::Apply(Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(Some(sub_proofs))));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, have $i:tt : ( $($goal:tt) + ) {  $( $body_have:tt )+  }  ; $($body:tt)*) => {
        let have_body: Vec<ProofStep> = lambdapi!{ $( $body_have )+ };
        $steps.push(ProofStep::Have(stringify!($i).to_string(), make_term![  $( $goal )+ ] ,have_body))  ; tactic![ $steps, $( $body )* ]
    };
    ($steps:ident, assume [$($id:tt)+] ; $($body:tt)*) => {
        let mut ids: Vec<String> = Vec::new();

        $(
            ids.push(stringify!($id).to_string());
        )+

        $steps.push(ProofStep::Assume(ids));
        tactic![ $steps, $(  $body )* ]
    };
    ($steps:ident, try [ $($id:tt)+ ] ; $($body:tt)*) => {
        let step = inline_lambdapi![ $( $id )+ ];

        $steps.push(ProofStep::Try(Box::new(step)));
        tactic![ $steps, $(  $body )* ]
    };
    ($steps:ident, rewrite [$($i:tt)+] $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Rewrite(None, $($i)+, vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, rewrite .$pattern:tt $i:tt  $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Rewrite(false, Some($pattern.to_string()), Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, rewrite $i:tt  $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Rewrite(false, None, Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, $code:block ; $($body:tt)*) => {  $steps.append(&mut $code) ; tactic![ $steps, $(  $body )* ]  };
    ($steps:ident, inject($code:expr) ; $($body:tt)*) => {  $steps.append(&mut $code) ; tactic![ $steps, $(  $body )* ]  };
    ($steps:ident, admit; $($body:tt)*) => { $steps.push(ProofStep::Admit)  ; tactic![ $steps, $(  $body )* ]  };
    ($steps:ident, end;) => { };
}

pub(crate) use tactic;

macro_rules! lambdapi_wrapper {
    (begin $($body:tt)+) => {
        #[allow(clippy::vec_init_then_push)]
        {
            let mut steps: Vec<ProofStep> = vec![];
            tactic![ steps, $( $body )+ ] ; steps
        }
    };
}

pub(crate) use lambdapi_wrapper;

/// Main entry point macro for writing Lambdapi proof scripts.
///
/// This macro provides the user-facing API for the DSL. It automatically wraps
/// the proof script with `begin`/`end` markers and returns a vector of `ProofStep`.
///
/// # Example
///
/// ```ignore
/// let proof_steps = lambdapi! {
///     assume [x y];
///     have eq_comm : (x = y => y = x) {
///         assume [h];
///         symmetry;
///         apply h;
///         reflexivity;
///     };
///     apply eq_comm;
///     end;
/// };
/// ```
macro_rules! lambdapi {
    ($($body:tt)+) => { { lambdapi_wrapper!{ begin $($body)+ end; } } };
}

pub(crate) use lambdapi;
