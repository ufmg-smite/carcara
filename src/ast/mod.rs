//! The abstract syntax tree (AST) for the Alethe proof format.
//!
//! This module also contains various utilities for manipulating Alethe proofs and terms.

mod context;
mod evaluate;
mod iter;
mod macros;
mod node;
mod polyeq;
pub mod pool;
pub mod printer; // TODO improve API
mod problem;
mod proof;
pub mod rare_rules;
mod rc;
mod sort;
mod substitution;
mod term;
#[cfg(test)]
mod tests;

pub use evaluate::Value;
pub use iter::ProofIter;
pub use node::{ProofNode, ProofNodeForest, StepNode, SubproofNode};
pub use polyeq::{Polyeq, PolyeqComparable, PolyeqConfig, alpha_equiv, polyeq};
pub use problem::{Problem, ProblemPrelude};
pub use proof::{AnchorArg, Proof, ProofCommand, ProofStep, Subproof};
pub use rc::Rc;
pub use sort::Sort;
pub use substitution::{SortSubstitution, Substitution, SubstitutionError};
pub use term::{
    Binder, BindingList, Constant, MatchCase, MatchPattern, NaryCase, Operator, ParamOperator,
    QualifiedOperator, SortedVar, Term,
};

pub(crate) use carcara_macros::match_term;
pub(crate) use context::ContextStack;
pub(crate) use macros::{build_term, impl_str_conversion_traits, match_term_err};

#[cfg(test)]
pub(crate) use node::compare_forests;
#[cfg(test)]
pub(crate) use node::compare_nodes;
