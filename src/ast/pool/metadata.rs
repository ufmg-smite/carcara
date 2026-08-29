use indexmap::IndexSet;

use crate::ast::{pool::Pool, *};

pub struct Metadata {
    pub sort: Rc<Sort>,
    pub free_vars: IndexSet<Rc<Term>>,
    pub choice_subterms: Option<IndexSet<Rc<Term>>>, // Computed lazily
}

impl Metadata {
    pub fn new(pool: &mut Pool, term: &Rc<Term>) -> Self {
        Self {
            sort: todo!(),
            free_vars: todo!(),
            choice_subterms: None,
        }
    }
}
