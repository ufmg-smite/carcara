use std::{fmt, hash::Hash, ops::Deref, rc};

/// An `Rc` where equality and hashing are done by reference, instead of by value
#[derive(Eq)]
pub struct Rc<T: ?Sized>(rc::Rc<T>);

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
        rc::Rc::ptr_eq(&self.0, &other.0)
    }
}

impl<T: ?Sized> Hash for Rc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        rc::Rc::as_ptr(&self.0).hash(state);
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
    rc::Rc<T>: From<U>,
{
    fn from(inner: U) -> Self {
        Self(inner.into())
    }
}

impl<T, const N: usize> Rc<[T; N]> {
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
    pub fn new(value: T) -> Self {
        #[allow(clippy::disallowed_method)]
        Self(rc::Rc::new(value))
    }
}
