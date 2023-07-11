//! This module implements a variant of `Rc` where equality and hashing are done by reference.

/// An `Rc` where equality and hashing are done by reference, instead of by value.
///
/// This means that two `Rc`s will not be considered equal and won't have the same hash value unless
/// they point to the same allocation. This has the advantage that equality and hashing can be done
/// in constant time, even for recursive structures.
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
pub type Rc<T> = MyArc::Rc<T>;

#[allow(non_snake_case, dead_code)]
mod MyArc {
    use std::{fmt, hash::Hash, ops::Deref, sync};

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

    // Implements `From<U>` for every `U` that can be converted into an `rc::Rc<T>`
    impl<T: ?Sized, U> From<U> for Rc<T>
    where
        sync::Arc<T>: From<U>,
    {
        fn from(inner: U) -> Self {
            Self(inner.into())
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
        pub fn new(value: T) -> Self {
            #[allow(clippy::disallowed_methods)]
            Self(sync::Arc::new(value))
        }

        /// Similar to [`std::rc::Rc::strong_count`].
        pub fn strong_count(this: &Self) -> usize {
            sync::Arc::strong_count(&this.0)
        }
    }
}
