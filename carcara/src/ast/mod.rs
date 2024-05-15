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
mod proof;
mod rc;
mod substitution;
mod term;
#[cfg(test)]
mod tests;

pub use context::{Context, ContextStack};
pub use iter::ProofIter;
pub use node::{proof_list_to_node, proof_node_to_list, ProofNode, StepNode, SubproofNode};
pub use polyeq::{alpha_equiv, polyeq, polyeq_mod_nary, tracing_polyeq_mod_nary};
pub use pool::{PrimitivePool, TermPool};
pub use printer::{print_proof, USE_SHARING_IN_TERM_DISPLAY};
pub use proof::*;
pub use rc::Rc;
pub use substitution::{Substitution, SubstitutionError};
pub use term::{Binder, BindingList, Constant, Operator, ParamOperator, Sort, SortedVar, Term};

pub(crate) use polyeq::{Polyeq, PolyeqComparator};

/// The prelude of an SMT-LIB problem instance.
///
/// This stores the sort declarations, function declarations and the problem's logic string.
#[derive(Debug, Clone, Default)]
pub struct ProblemPrelude {
    /// The sort declarations, each represented by its name and arity.
    pub(crate) sort_declarations: Vec<(String, usize)>,

    /// The function declarations, each represented by its name and body.
    pub(crate) function_declarations: Vec<(String, Rc<Term>)>,

    /// The problem's logic string, if it exists.
    pub(crate) logic: Option<String>,
}
