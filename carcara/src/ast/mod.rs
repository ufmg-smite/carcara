//! The abstract syntax tree (AST) for the Alethe proof format.
//!
//! This module also contains various utilities for manipulating Alethe proofs and terms.

#[macro_use]
mod macros;
mod context;
mod iter;
mod node;
mod polyeq;
pub mod pool;
pub(crate) mod printer;
mod problem;
mod proof;
pub mod rare_rules;
mod rc;
mod substitution;
mod term;
#[cfg(test)]
mod tests;

pub use context::{Context, ContextStack};
pub use iter::ProofIter;
pub use node::{ProofNode, ProofNodeForest, StepNode, SubproofNode};
pub use polyeq::{alpha_equiv, polyeq, Polyeq, PolyeqComparable, PolyeqConfig};
pub use pool::{PrimitivePool, TermPool};
pub use printer::{print_proof, write_asserts, write_proof_to_dest, USE_SHARING_IN_TERM_DISPLAY};
pub use problem::*;
pub use proof::*;
pub use rc::Rc;
pub use substitution::{Substitution, SubstitutionError};
pub use term::{Binder, BindingList, Constant, Operator, ParamOperator, Sort, SortedVar, Term};

#[cfg(test)]
pub(crate) use node::compare_forests;
#[cfg(test)]
pub(crate) use node::compare_nodes;
