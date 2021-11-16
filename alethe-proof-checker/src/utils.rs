use crate::ast::{BindingList, Quantifier, Rc, Term};
use ahash::AHashSet;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::{hash::Hash, ops};

/// An enum that can hold one of two types. Similar to `Result`, but doesn't imply that one of the
/// variants is "better" than the other.
pub enum Either<T, U> {
    Left(T),
    Right(U),
}

/// An iterator that removes duplicate elements from `iter`. This will yield the elements in
/// `iter` in order, skipping elements that have already been seen before.
pub struct Dedup<T, I> {
    seen: AHashSet<T>,
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
        Dedup { seen: AHashSet::new(), iter: self }
    }
}

/// A trait that implements addition and multiplication operations on `BigRational`s that don't
/// reduce the fractions. This makes them much faster than the implementations of the `Add` and
/// `Mul` traits, but may lead to errors when using methods that assume that the fractions are
/// reduced.
pub trait RawOps {
    fn raw_add(&self, other: &Self) -> Self;

    fn raw_mul(&self, other: &Self) -> Self;
}

impl RawOps for BigRational {
    fn raw_add(&self, other: &Self) -> Self {
        let denom = self.denom().abs() * other.denom().abs();
        let numer_a = self.numer() * other.denom().abs();
        let numer_b = other.numer() * self.denom().abs();
        Self::new_raw(numer_a + numer_b, denom)
    }

    fn raw_mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            Self::zero()
        } else if self.is_one() {
            other.clone()
        } else if other.is_one() {
            self.clone()
        } else {
            let numer = self.numer() * other.numer();
            let denom = self.denom() * other.denom();
            Self::new_raw(numer, denom)
        }
    }
}

// TODO: Document this struct
#[derive(Debug)]
pub struct Range(Option<usize>, Option<usize>);

impl Range {
    pub fn to_text(&self) -> String {
        match self {
            Range(Some(a), Some(b)) if a == b => format!("{}", a),
            Range(Some(a), Some(b)) => format!("between {} and {}", a, b),
            Range(Some(a), None) => format!("at least {}", a),
            Range(None, Some(b)) => format!("up to {}", b),
            Range(None, None) => "any number of".into(),
        }
    }

    pub fn contains(&self, n: usize) -> bool {
        self.0.map_or(true, |bound| n >= bound) && self.1.map_or(true, |bound| n <= bound)
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

/// Provides a pretty displayable name for a type. For example, the type name for `Rc<Term>` is
/// "term".
pub trait TypeName {
    const NAME: &'static str;
}

impl TypeName for Rc<Term> {
    const NAME: &'static str = "term";
}

impl TypeName for Quantifier {
    const NAME: &'static str = "quantifier";
}

impl TypeName for BindingList {
    const NAME: &'static str = "binding list";
}
