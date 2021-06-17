use super::{ByRefRc, Term};
use std::{collections::HashSet, iter};

pub struct Subterms<'a> {
    visited: HashSet<&'a Term>,
    inner: SubtermsInner<'a>,
}

impl<'a> Subterms<'a> {
    pub fn new(root: &'a Term) -> Self {
        Self {
            visited: HashSet::new(),
            inner: SubtermsInner::new(root),
        }
    }
}

impl<'a> Iterator for Subterms<'a> {
    type Item = &'a Term;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next(&mut self.visited)
    }
}

struct SubtermsInner<'a> {
    root: &'a Term,
    visited_root: bool,
    current: Option<Box<Self>>,
    children: Box<dyn Iterator<Item = &'a ByRefRc<Term>> + 'a>,
}

impl<'a> SubtermsInner<'a> {
    fn new(root: &'a Term) -> Self {
        let children: Box<dyn Iterator<Item = _>> = match root {
            Term::App(f, args) => Box::new(iter::once(f).chain(args.iter())),
            Term::Op(_, args) => Box::new(args.iter()),
            Term::Quant(_, _, t) => Box::new(iter::once(t)),
            _ => Box::new(iter::empty()),
        };
        Self {
            root,
            visited_root: false,
            current: None,
            children,
        }
    }

    fn next(&mut self, visited: &mut HashSet<&'a Term>) -> Option<&'a Term> {
        if !self.visited_root {
            self.current = self.next_child(visited);
            self.visited_root = true;
            return Some(self.root);
        }
        let current = self.current.as_mut()?;
        if let Some(t) = current.next(visited) {
            visited.insert(t);
            Some(t)
        } else {
            self.current = self.next_child(visited);
            self.next(visited)
        }
    }

    fn next_child(&mut self, visited: &mut HashSet<&'a Term>) -> Option<Box<Self>> {
        self.children
            .find(|t| !visited.contains(t.as_ref()))
            .map(|t| Box::new(SubtermsInner::new(t.as_ref())))
    }
}
