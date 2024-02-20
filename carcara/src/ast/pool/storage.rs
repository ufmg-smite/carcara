//* The behaviour of the term pool could be modeled by a hash map from `Term` to `Rc<Term>`, but
//* that would require allocating two copies of each term, one in the key of the hash map, and one
//* inside the `Rc`. Instead, we store a hash set of `Rc<Term>`s, combining the key and the value
//* into a single object. We access this hash set using a `&Term`, and if the entry is present, we
//* clone it; otherwise, we allocate a new `Rc`.

use crate::ast::*;
use std::borrow::Borrow;

/// Since `ast::Rc` intentionally implements hashing and equality by reference (instead of by
/// value), we cannot safely implement `Borrow<Term>` for `Rc<Term>`, so we cannot access a
/// `HashSet<Rc<Term>>` using a `&Term` as a key. To go around that, we use this struct that wraps
/// an `Rc<Term>` and that re-implements hashing and equality by value, meaning we can implement
/// `Borrow<Term>` for it, and use it as the contents of the hash set instead.
#[derive(Debug, Clone, Eq)]
struct ByValue(Rc<Term>);

impl PartialEq for ByValue {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref() == other.0.as_ref()
    }
}

impl Hash for ByValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.as_ref().hash(state);
    }
}

impl Borrow<Term> for ByValue {
    fn borrow(&self) -> &Term {
        self.0.as_ref()
    }
}

#[derive(Debug, Clone, Default)]
pub struct Storage(IndexSet<ByValue>);

impl Storage {
    pub fn add(&mut self, term: Term) -> Rc<Term> {
        // If the `hash_set_entry` feature was stable, this would be much simpler to do using
        // `get_or_insert_with` (and would avoid rehashing the term)
        match self.0.get(&term) {
            Some(t) => t.0.clone(),
            None => {
                let result = Rc::new(term);
                self.0.insert(ByValue(result.clone()));
                result
            }
        }
    }

    pub fn get(&self, term: &Term) -> Option<&Rc<Term>> {
        self.0.get(term).map(|t| &t.0)
    }

    // This method is only necessary for the hash consing tests
    #[cfg(test)]
    pub fn into_vec(self) -> Vec<Rc<Term>> {
        self.0.into_iter().map(|ByValue(t)| t).collect()
    }
}
