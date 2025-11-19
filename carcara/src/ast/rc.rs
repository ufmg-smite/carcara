//! This module implements a variant of `Rc` where equality and hashing are done by reference.

use std::{fmt, hash::Hash, ops::Deref, sync};

/// A wrapper for `std::rc::Rc` where equality and hashing are done by reference, instead of by
/// value.
///
/// This means that two `Rc`s will not be considered equal and won't have the same hash value unless
/// they point to the same allocation. This has the advantage that equality and hashing can be done
/// in constant time, even for recursive structures.
///
/// The Carcara parser makes use of hash consing, meaning that each term is only allocated once,
/// even if it appears multiple times in the proof. This means that if we want to compare two terms
/// for equality, we only need to compare them by reference, since if they are equal they will point
/// to the same allocation. However, `std::rc::Rc` implements `PartialEq` by comparing the inner
/// values for equality. If we simply used this implementation, each equality comparison would need
/// to traverse the terms recursively, which would be prohibitively expensive. Instead, this wrapper
/// overrides the `PartialEq` implementation to compare the pointers directly, allowing for constant
/// time equality comparisons.
///
/// Similarly, when inserting terms in a hash map or set, we can also just hash the pointers
/// instead of recursively hashing the inner value (as `std::rc::Rc`'s `Hash` implementation does).
/// Therefore, this wrapper also overrides the implementation of the `Hash` trait.
///
/// Note: when using this struct, it's important to avoid constructing terms with `Rc::new` and
/// instead prefer to construct them by adding them to a `TermPool`. This is because `Rc::new` will
/// create a brand new allocation for that term, instead of reusing the existing allocation if that
/// term was already added to the pool. Two indentical terms created independently with `Rc::new`
/// will not compare as equal.
///
/// # Examples
///
/// ```
/// # use carcara::ast::Rc;
/// let a = Rc::new(5);
/// let b = Rc::new(5);
/// assert_ne!(a, b);
///
/// let c = a.clone();
/// assert_eq!(a, c);
/// ```
///
/// While `a` and `b` have the same contents, they are not considered equal. However, since `c` was
/// created by cloning `a`, they point to the same allocation, and are thus considered equal. The
/// same thing happens with their hash values:
///
/// ```
/// # use carcara::ast::Rc;
/// # use std::collections::HashSet;
/// # let a = Rc::new(5);
/// # let b = Rc::new(5);
/// # let c = a.clone();
/// let mut set = HashSet::new();
/// set.insert(a);
/// assert!(!set.contains(&b));
/// assert!(set.contains(&c));
/// ```
#[derive(Eq)]
pub struct Rc<T: ?Sized>(sync::Arc<T>);

// If we simply `#[derive(Clone)]`, it would require that the type parameter `T` also implements
// `Clone`, even though it is of course not needed. For more info, see:
// https://github.com/rust-lang/rust/issues/26925
impl<T: ?Sized> Clone for Rc<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: ?Sized> PartialEq for Rc<T> {
    fn eq(&self, other: &Self) -> bool {
        sync::Arc::ptr_eq(&self.0, &other.0)
    }
}

impl<T: ?Sized> Hash for Rc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        sync::Arc::as_ptr(&self.0).hash(state);
    }
}

impl<T: ?Sized> Deref for Rc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

// Note: Since `Eq` and `Hash` are implemented differently for `Rc<T>` than they are for `T`, we
// _cannot_ implement `Borrow<T>` for `Rc<T>`
impl<T: ?Sized> AsRef<T> for Rc<T> {
    fn as_ref(&self) -> &T {
        self.0.as_ref()
    }
}

impl<T, const N: usize> Rc<[T; N]> {
    /// Converts an `Rc` of an array into an `Rc` of a slice.
    pub fn to_rc_of_slice(self) -> Rc<[T]> {
        Rc(self.0 as _)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl<T> Rc<T> {
    /// Constructs a new `Rc<T>`.
    ///
    /// # Safety
    /// This method allows you to create an arbitrary new `Rc` for an object. The `PartialEq` and
    /// `Hash` implementations of `Rc` expect that identical objects share the same allocation.
    /// In the case of `Term`s, this preserves the property of hash-consing, and is enforced by
    /// the term pool. When this property is broken, you observe weird behaviors like identical
    /// terms comparing as different, or multiple identical terms being inserted in the same
    /// `HashMap`/`HashSet`.
    ///
    /// In most cases, instead of using this method, you should use add the raw term into a term
    /// pool, using `TermPool::add`; or clone the `Rc<Term>` from an existing allocation, if it
    /// exists. Unless you know what you are doing, prefer one of those options instead of using
    /// this method.
    pub(super) unsafe fn new_raw(value: T) -> Self {
        #[allow(clippy::disallowed_methods)]
        Self(sync::Arc::new(value))
    }

    /// Similar to [`std::rc::Rc::strong_count`].
    pub fn strong_count(this: &Self) -> usize {
        sync::Arc::strong_count(&this.0)
    }
}
