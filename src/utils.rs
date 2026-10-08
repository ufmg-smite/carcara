use crate::ast::{Binder, BindingList, Operator, Rc, Sort, Term};
use indexmap::{IndexMap, IndexSet};
use rapidhash::{HashMapExt, RapidHashMap};
use rug::Integer;
use std::{
    borrow::Borrow,
    fmt,
    hash::{Hash, Hasher},
    ops,
};

/// Returns `true` if the character is a valid symbol character in the SMT-LIB and Alethe formats.
pub fn is_symbol_character(ch: char) -> bool {
    match ch {
        ch if ch.is_ascii_alphanumeric() => true,
        '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '~' | '&' | '^' | '<'
        | '>' | '@' => true,
        _ => false,
    }
}

/// An iterator that removes duplicate elements from `iter`. This will yield the elements in
/// `iter` in order, skipping elements that have already been seen before.
pub struct Dedup<T, I> {
    seen: IndexSet<T>,
    iter: I,
}

impl<T, I> Iterator for Dedup<T, I>
where
    T: Clone + Hash + Eq,
    I: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let got = self.iter.next()?;
            let is_new = self.seen.insert(got.clone());
            if is_new {
                return Some(got);
            }
        }
    }
}

/// An iterator extension trait that provides the [`dedup`](DedupIterator::dedup) method.
///
/// This trait is implemented for all iterators.
pub trait DedupIterator<T> {
    /// Creates an iterator that skips duplicate elements.
    fn dedup(self) -> Dedup<T, Self>
    where
        Self: Sized;
}

impl<T, I: Iterator<Item = T>> DedupIterator<T> for I {
    fn dedup(self) -> Dedup<T, Self>
    where
        Self: Sized,
    {
        Dedup { seen: IndexSet::new(), iter: self }
    }
}

/// A wrapper around a value that caches its hash, so that the wrapped value only needs to be
/// hashed once.
///
/// The hash is computed when the `HashCache` is created, and after that hashing will only write
/// that cached hash instead of hashing the wrapped value. This is useful when you need to hash the
/// same value multiple times, for example when it is used as a key in a [`HashMapStack`].
pub struct HashCache<T> {
    hash: u64,
    value: T,
}

impl<T: PartialEq> PartialEq for HashCache<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T: Eq> Eq for HashCache<T> {}

impl<T: Hash> Hash for HashCache<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

impl<T: Eq + Hash> HashCache<T> {
    /// Creates a new `HashCache`, computing and storing the hash of `value`.
    pub fn new(value: T) -> Self {
        let mut hasher = rapidhash::fast::RapidHasher::default_const();
        value.hash(&mut hasher);
        Self { hash: hasher.finish(), value }
    }

    /// Consumes the `HashCache`, returning the wrapped value.
    pub fn unwrap(self) -> T {
        self.value
    }
}

impl<T> AsRef<T> for HashCache<T> {
    fn as_ref(&self) -> &T {
        &self.value
    }
}

/// A stack of hash maps, used as a symbol table.
///
/// Values are inserted into the topmost scope, and lookups search scopes from the top down,
/// returning the first value found.
#[derive(Debug, Clone)]
pub struct HashMapStack<K, V> {
    scopes: Vec<RapidHashMap<K, V>>,
}

impl<K, V> HashMapStack<K, V> {
    /// Creates an empty `HashMapStack`, containing a single empty scope.
    pub fn new() -> Self {
        Self { scopes: vec![RapidHashMap::new()] }
    }

    /// Returns the number of scopes in the stack.
    pub fn height(&self) -> usize {
        self.scopes.len()
    }

    /// Returns `true` if every scope in the stack is empty.
    pub fn is_empty(&self) -> bool {
        self.scopes.iter().all(RapidHashMap::is_empty)
    }

    /// Clears the `HashMapStack`, removing all entries and popping all scopes except the base
    /// scope.
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// Clears the top scope in the stack.
    pub fn clear_top(&mut self) {
        if let Some(top) = self.scopes.last_mut() {
            top.clear();
        }
    }

    /// Pushes a new, empty scope onto the stack.
    pub fn push_scope(&mut self) {
        self.scopes.push(RapidHashMap::new());
    }

    /// Pops the topmost scope from the stack.
    ///
    /// # Panics
    ///
    /// Panics if the stack contains only one scope, since the last scope cannot be popped.
    pub fn pop_scope(&mut self) {
        match self.scopes.len() {
            0 => unreachable!(),
            1 => panic!("trying to pop last scope in `HashMapStack`"),
            _ => {
                self.scopes.pop().unwrap();
            }
        }
    }
}

impl<K: Eq + Hash, V> HashMapStack<K, V> {
    /// Searches for the value bound to `key`, starting from the topmost scope.
    ///
    /// Returns the value from the first scope found that binds `key`, or `None` if no scope does.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        // Note: If there are a lot of scopes in the symbol table, this can be a big performance
        // bottleneck. As currently implemented, this function needs to hash the key once for every
        // scope. The ideal way of solving this would be to hash the key once, and reuse that hash
        // to access the entry in each scope. To do that, we could use the `HashMap::raw_entry`
        // method, but it is currently nightly-only. Another way to mitigate this issue is to use
        // the `HashCache<T>` struct to wrap the key values in the symbol table. This allows the key
        // to only be hashed once, and that value is stored and reused in the struct.
        self.scopes.iter().rev().find_map(|scope| scope.get(key))
    }

    /// Like [`get`](HashMapStack::get), but also returns the depth of the scope in which the key
    /// was found, where `0` is the bottommost scope.
    pub fn get_with_depth<Q>(&self, key: &Q) -> Option<(usize, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.scopes
            .iter()
            .enumerate()
            .rev()
            .find_map(|(depth, scope)| scope.get(key).map(|v| (depth, v)))
    }

    /// Like [`get`](HashMapStack::get), but only searches the topmost scope.
    pub fn get_top<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.scopes.last().unwrap().get(key)
    }

    /// Inserts a key-value pair into the topmost scope.
    pub fn insert(&mut self, key: K, value: V) {
        self.scopes.last_mut().unwrap().insert(key, value);
    }

    /// Retains from the top scope only elements specified by the predicate.
    ///
    /// This does not change any scope besides the topmost one.
    pub fn retain_top<F: FnMut(&K, &mut V) -> bool>(&mut self, f: F) {
        self.scopes.last_mut().unwrap().retain(f);
    }
}

impl<K, V> Default for HashMapStack<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Eq + Hash, V> std::iter::Extend<(K, V)> for HashMapStack<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        self.scopes.last_mut().unwrap().extend(iter);
    }
}

/// A multiset (or bag): a collection that counts how many times each element occurs.
#[derive(Debug, Clone)]
pub struct MultiSet<T>(pub IndexMap<T, usize>);

impl<T> Default for MultiSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> MultiSet<T> {
    /// Creates a new, empty `MultiSet`.
    pub fn new() -> Self {
        MultiSet(IndexMap::new())
    }

    /// Returns the number of distinct elements in the multiset.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the multiset is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// The result of comparing two multisets with [`MultiSet::symmetric_difference`].
pub enum MultiSetDifference<'a, T> {
    /// The two multisets contain the same elements with the same multiplicities.
    None,

    /// The element occurs fewer times in `self` than in the other multiset.
    Missing(&'a T),

    /// The element occurs more times in `self` than in the other multiset.
    Extra(&'a T),
}

impl<T: Hash + Eq> MultiSet<T> {
    /// Returns the number of times `value` occurs in the multiset, or `0` if it is not present.
    pub fn get<Q>(&self, value: &Q) -> usize
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.0.get(value).copied().unwrap_or_default()
    }

    /// Returns a mutable reference to the number of times `value` occurs in the multiset, inserting
    /// an entry with count `0` if `value` is not present.
    pub fn get_mut(&mut self, value: T) -> &mut usize {
        self.0.entry(value).or_default()
    }

    /// Returns `true` if `value` is contained at least once in the multiset.
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.get(value) > 0
    }

    /// Inserts `value` into the multiset once, returning the new count for `value`.
    pub fn insert(&mut self, value: T) -> usize {
        self.insert_n(value, 1)
    }

    /// Inserts `n` copies of `value` into the multiset, returning the new count for `value`.
    pub fn insert_n(&mut self, value: T, n: usize) -> usize {
        if n == 0 {
            return self.get(&value);
        }
        let v = self.get_mut(value);
        *v += n;
        *v
    }

    /// Removes `value` from the multiset once, returning the remaining count for `value`.
    pub fn remove(&mut self, value: &T) -> usize {
        self.remove_n(value, 1)
    }

    /// Removes up to `n` copies of `value` from the multiset, returning the remaining count.
    pub fn remove_n(&mut self, value: &T, n: usize) -> usize {
        if self.get(value) <= n {
            self.0.swap_remove(value);
            0
        } else {
            let v = &mut self.0[value];
            *v -= n;
            *v
        }
    }

    /// Returns the first element that distinguishes this multiset from `other`.
    ///
    /// More precisely, this returns `MultiSetDifference::Extra` if some element occurs more times
    /// in `self` than in `other`, `MultiSetDifference::Missing` if some element occurs fewer
    /// times in `self` than in `other`, and `MultiSetDifference::None` if the two multisets are
    /// identical.
    pub fn symmetric_difference<'a>(&'a self, other: &'a Self) -> MultiSetDifference<'a, T> {
        for (item, &count) in &self.0 {
            let other_count = other.get(item);
            if count > other_count {
                return MultiSetDifference::Extra(item);
            } else if count < other_count {
                return MultiSetDifference::Missing(item);
            }
        }

        for (item, &count) in &other.0 {
            let self_count = self.get(item);
            if self_count > count {
                return MultiSetDifference::Extra(item);
            } else if self_count < count {
                return MultiSetDifference::Missing(item);
            }
        }

        MultiSetDifference::None
    }
}

impl<T: Hash + Eq> PartialEq for MultiSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Hash + Eq> FromIterator<T> for MultiSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut mset = MultiSet::new();
        for i in iter {
            mset.insert(i);
        }
        mset
    }
}

impl<T: Clone> MultiSet<T> {
    /// Returns an iterator that yields each element of the multiset as many times as it occurs.
    pub fn into_iter(self) -> impl Iterator<Item = T> {
        // I use a custom `into_iter` method instead of implementing `IntoIterator` because the
        // actual iterator type I use can't be named (because of the closure), which `IntoIterator`
        // requires.
        self.0
            .into_iter()
            .flat_map(|(item, count)| std::iter::repeat_n(item, count))
    }
}

impl<T: Eq + Hash> std::iter::Extend<T> for MultiSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for elem in iter {
            self.insert(elem);
        }
    }
}

/// A range type with a nice `Display` implementation, to be used in error messages.
#[derive(Debug)]
pub struct Range(Option<usize>, Option<usize>);

impl Range {
    /// Returns `true` if `n` is contained in the range.
    pub fn contains(&self, n: usize) -> bool {
        self.0.as_ref().is_none_or(|bound| n >= *bound)
            && self.1.as_ref().is_none_or(|bound| n <= *bound)
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Range(Some(a), Some(b)) if a == b => write!(f, "{}", a),
            Range(Some(a), Some(b)) => write!(f, "between {} and {}", a, b),
            Range(Some(a), None) => write!(f, "at least {}", a),
            Range(None, Some(b)) => write!(f, "up to {}", b),
            Range(None, None) => write!(f, "any number of"),
        }
    }
}

impl From<usize> for Range {
    fn from(n: usize) -> Self {
        Self(Some(n), Some(n))
    }
}

impl From<ops::Range<usize>> for Range {
    fn from(r: ops::Range<usize>) -> Self {
        Self(Some(r.start), Some(r.end - 1))
    }
}

impl From<ops::RangeFrom<usize>> for Range {
    fn from(r: ops::RangeFrom<usize>) -> Self {
        Self(Some(r.start), None)
    }
}

impl From<ops::RangeFull> for Range {
    fn from(_: ops::RangeFull) -> Self {
        Self(None, None)
    }
}

impl From<ops::RangeTo<usize>> for Range {
    fn from(r: ops::RangeTo<usize>) -> Self {
        Self(None, Some(r.end - 1))
    }
}

/// Provides a pretty displayable name for a type.
pub trait TypeName {
    /// The type's displayable name.
    const NAME: &'static str;
}

impl TypeName for Rc<Term> {
    const NAME: &'static str = "term";
}

impl TypeName for Rc<Sort> {
    const NAME: &'static str = "sort";
}

impl TypeName for Binder {
    const NAME: &'static str = "binder";
}

impl<T> TypeName for BindingList<T> {
    const NAME: &'static str = "binding list";
}

impl TypeName for Integer {
    const NAME: &'static str = "integer";
}

impl TypeName for Operator {
    const NAME: &'static str = "operator";
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbol_character() {
        for ch in "aZ09+-/*=%?!.$_~&^<>@".chars() {
            assert!(is_symbol_character(ch));
        }
        for ch in "() \"|:;#',é".chars() {
            assert!(!is_symbol_character(ch));
        }
    }

    #[test]
    fn test_dedup() {
        let got: Vec<_> = [3, 1, 3, 2, 1, 3].into_iter().dedup().collect();
        assert_eq!(got, [3, 1, 2]);

        let got: Vec<i32> = std::iter::empty().dedup().collect();
        assert!(got.is_empty());
    }

    #[test]
    fn test_hash_cache() {
        fn hash_of<T: Hash>(value: &T) -> u64 {
            let mut hasher = rapidhash::fast::RapidHasher::default_const();
            value.hash(&mut hasher);
            hasher.finish()
        }

        let a = HashCache::new("foo".to_owned());
        let b = HashCache::new("foo".to_owned());
        let c = HashCache::new("bar".to_owned());
        assert!(a == b);
        assert!(a != c);
        assert_eq!(hash_of(&a), hash_of(&b));
        assert_eq!(a.as_ref(), "foo");
        assert_eq!(c.unwrap(), "bar");
    }

    #[test]
    fn test_hash_map_stack() {
        let mut stack = HashMapStack::new();
        assert_eq!(stack.height(), 1);
        assert!(stack.is_empty());

        stack.insert("x", 1);
        stack.insert("y", 2);
        assert!(!stack.is_empty());

        // Inner scopes shadow outer ones
        stack.push_scope();
        stack.insert("x", 10);
        assert_eq!(stack.height(), 2);
        assert_eq!(stack.get("x"), Some(&10));
        assert_eq!(stack.get("y"), Some(&2));
        assert_eq!(stack.get("z"), None);
        assert_eq!(stack.get_with_depth("x"), Some((1, &10)));
        assert_eq!(stack.get_with_depth("y"), Some((0, &2)));
        assert_eq!(stack.get_top("x"), Some(&10));
        assert_eq!(stack.get_top("y"), None);

        // Popping a scope restores the outer bindings
        stack.pop_scope();
        assert_eq!(stack.height(), 1);
        assert_eq!(stack.get("x"), Some(&1));

        // `clear_top`, `retain_top` and `extend` only touch the top scope
        stack.push_scope();
        stack.extend([("a", 3), ("b", 4), ("c", 5)]);
        stack.retain_top(|_, v| *v % 2 == 1);
        assert_eq!(stack.get_top("a"), Some(&3));
        assert_eq!(stack.get_top("b"), None);
        assert_eq!(stack.get_top("c"), Some(&5));
        stack.clear_top();
        assert_eq!(stack.get_top("a"), None);
        assert_eq!(stack.get("x"), Some(&1));
        assert_eq!(stack.height(), 2);

        // `clear` removes everything, including the extra scopes
        stack.clear();
        assert_eq!(stack.height(), 1);
        assert!(stack.is_empty());
    }

    #[test]
    #[should_panic(expected = "trying to pop last scope")]
    fn test_hash_map_stack_pop_last_scope() {
        let mut stack: HashMapStack<i32, i32> = HashMapStack::new();
        stack.pop_scope();
    }

    #[test]
    fn test_multiset() {
        let mut set = MultiSet::new();
        assert!(set.is_empty());

        assert_eq!(set.insert('a'), 1);
        assert_eq!(set.insert('a'), 2);
        assert_eq!(set.insert_n('b', 3), 3);
        assert_eq!(set.insert_n('c', 0), 0);
        assert_eq!(set.len(), 2); // Inserting zero copies doesn't add an entry
        assert_eq!(set.get(&'a'), 2);
        assert_eq!(set.get(&'c'), 0);
        assert!(set.contains(&'b'));
        assert!(!set.contains(&'c'));

        assert_eq!(set.remove(&'a'), 1);
        assert_eq!(set.remove_n(&'b', 2), 1);
        // Removing more copies than there are removes the entry entirely
        assert_eq!(set.remove_n(&'b', 5), 0);
        assert!(!set.contains(&'b'));
        assert_eq!(set.len(), 1);
        assert_eq!(set.remove(&'z'), 0);

        *set.get_mut('d') += 2;
        assert_eq!(set.get(&'d'), 2);
    }

    #[test]
    fn test_multiset_iteration_and_equality() {
        let set: MultiSet<_> = "abacab".chars().collect();
        assert_eq!(set.get(&'a'), 3);
        assert_eq!(set.get(&'b'), 2);
        assert_eq!(set.get(&'c'), 1);

        let mut items: Vec<_> = set.clone().into_iter().collect();
        items.sort();
        assert_eq!(items, ['a', 'a', 'a', 'b', 'b', 'c']);

        // Equality doesn't depend on insertion order
        let other: MultiSet<_> = "bcaaab".chars().collect();
        assert!(set == other);
        let different: MultiSet<_> = "abcab".chars().collect();
        assert!(set != different);

        let mut extended: MultiSet<_> = "ab".chars().collect();
        extended.extend("aacb".chars());
        assert!(extended == set);
    }

    #[test]
    fn test_multiset_symmetric_difference() {
        fn diff(a: &str, b: &str) -> Option<(bool, char)> {
            let (a, b): (MultiSet<_>, MultiSet<_>) = (a.chars().collect(), b.chars().collect());
            match a.symmetric_difference(&b) {
                MultiSetDifference::None => None,
                MultiSetDifference::Missing(c) => Some((false, *c)),
                MultiSetDifference::Extra(c) => Some((true, *c)),
            }
        }

        assert_eq!(diff("", ""), None);
        assert_eq!(diff("aab", "aba"), None);
        assert_eq!(diff("aab", "ab"), Some((true, 'a')));
        assert_eq!(diff("ab", "aab"), Some((false, 'a')));
        // Elements that only occur in the second multiset are found in the second loop
        assert_eq!(diff("ab", "abc"), Some((false, 'c')));
        assert_eq!(diff("abc", "ab"), Some((true, 'c')));
    }

    #[test]
    fn test_range() {
        let cases: [(Range, &[usize], &[usize], &str); 5] = [
            (3.into(), &[3], &[2, 4], "3"),
            ((2..5).into(), &[2, 3, 4], &[1, 5], "between 2 and 4"),
            ((2..).into(), &[2, 3, 100], &[0, 1], "at least 2"),
            ((..3).into(), &[0, 1, 2], &[3, 4], "up to 2"),
            ((..).into(), &[0, 1, 100], &[], "any number of"),
        ];
        for (range, inside, outside, display) in cases {
            for &n in inside {
                assert!(range.contains(n));
            }
            for &n in outside {
                assert!(!range.contains(n));
            }
            assert_eq!(range.to_string(), display);
        }

        // A single-element `a..a + 1` range is displayed like a single number
        assert_eq!(Range::from(4..5).to_string(), "4");
    }
}
