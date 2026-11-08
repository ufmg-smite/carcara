//* The behaviour of the term pool could be modeled by a hash map from `Term` to `Rc<Term>`, but
//* that would require allocating two copies of each term, one in the key of the hash map, and one
//* inside the `Rc`. Instead, we store a hash set of `Rc<Term>`s, combining the key and the value
//* into a single object. We access this hash set using a `&Term`, and if the entry is present, we
//* clone it; otherwise, we allocate a new `Rc`.

use crate::ast::*;
use hashbrown::{HashTable, hash_table::Entry};
use std::hash::{BuildHasher, Hash};

/// A hash-consing enforcing storage of objects.
///
/// This struct stores objects ensuring that identical object are only allocated once, and hands out
/// [`ast::Rc`] handles to those allocations.
#[derive(Debug, Clone)]
pub struct Storage<T> {
    table: HashTable<Rc<T>>,
    hasher: rapidhash::fast::RandomState,
}

impl<T> Default for Storage<T> {
    fn default() -> Self {
        Self {
            table: HashTable::new(),
            hasher: Default::default(),
        }
    }
}

impl<T: Hash + Eq> Storage<T> {
    /// Takes an object and returns a possibly newly allocated `Rc` that references it.
    ///
    /// If the object was not originally in the storage, it is added to it. Otherwise, this method
    /// just returns an `Rc` pointing to the existing allocation.
    pub fn add(&mut self, object: T) -> Rc<T> {
        let hasher = &self.hasher;
        let hash = hasher.hash_one(&object);
        let eq = |o: &Rc<T>| o.as_ref() == &object;
        match self.table.entry(hash, eq, |o| hasher.hash_one(o.as_ref())) {
            Entry::Occupied(entry) => entry.get().clone(),
            Entry::Vacant(entry) => {
                // SAFETY: We have just checked that the object does not exist in the pool, so we can
                // create a new allocation.
                let result = unsafe { Rc::new_raw(object) };
                entry.insert(result.clone());
                result
            }
        }
    }

    /// Reserves capacity for at least `additional` more objects.
    pub fn reserve(&mut self, additional: usize) {
        let hasher = &self.hasher;
        self.table
            .reserve(additional, |o| hasher.hash_one(o.as_ref()));
    }

    /// Returns a reference to the allocation of `object` stored in `self`, if it is present.
    pub fn get(&self, object: &T) -> Option<&Rc<T>> {
        let hash = self.hasher.hash_one(object);
        self.table.find(hash, |o| o.as_ref() == object)
    }

    // This method is only necessary for the hash consing tests
    #[cfg(test)]
    pub fn into_vec(self) -> Vec<Rc<T>> {
        self.table.into_iter().collect()
    }
}
