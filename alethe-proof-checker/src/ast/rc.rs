use std::{
    borrow::Borrow,
    fmt::{self, Debug},
    hash::Hash,
    ops::Deref,
    rc,
};

/// An `Rc` where equality and hashing are done by reference, instead of by value
#[derive(Clone, Eq)]
pub struct Rc<T>(rc::Rc<T>);

impl<T> PartialEq for Rc<T> {
    fn eq(&self, other: &Self) -> bool {
        rc::Rc::ptr_eq(&self.0, &other.0)
    }
}

impl<T> Hash for Rc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        rc::Rc::as_ptr(&self.0).hash(state)
    }
}

impl<T> Deref for Rc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<T> AsRef<T> for Rc<T> {
    fn as_ref(&self) -> &T {
        self.0.as_ref()
    }
}

impl<T> Borrow<T> for Rc<T> {
    fn borrow(&self) -> &T {
        self.0.as_ref()
    }
}

impl<T> From<T> for Rc<T> {
    fn from(value: T) -> Self {
        Rc::new(value)
    }
}

impl<T: Debug> Debug for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl<T> Rc<T> {
    pub fn new(value: T) -> Self {
        #[allow(clippy::disallowed_method)]
        Self(rc::Rc::new(value))
    }
}
