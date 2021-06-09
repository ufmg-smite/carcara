use super::*;
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
        match current.next(visited) {
            Some(t) => {
                visited.insert(t);
                Some(t)
            }
            None => {
                self.current = self.next_child(visited);
                self.next(visited)
            }
        }
    }

    fn next_child(&mut self, visited: &mut HashSet<&'a Term>) -> Option<Box<Self>> {
        self.children
            .find(|t| !visited.contains(t.as_ref()))
            .map(|t| Box::new(SubtermsInner::new(t.as_ref())))
    }
}

pub struct FreeVars<'a> {
    root: &'a Term,
    visited_root: bool,
    bound_vars: HashSet<&'a str>,
    inner: iter::Flatten<Box<dyn Iterator<Item = Box<Self>> + 'a>>,
}

impl<'a> FreeVars<'a> {
    pub fn new(root: &'a Term) -> Self {
        // Unlike `Subterms`, this struct iterates through the term without skipping already seen
        // subterms, meaning it traverses it as tree, and not as a DAG. That is necessary beacause
        // a variable that may be free in one subterm may not be free in another identical subterm,
        // depending on where in appears. For example, consider the following term:
        //
        //     (and (forall ((a Int)) (= a 0)) (= a 0))
        //
        // The "a" variable is bound in the first appearance of the (= a 0) subterm, but it is free
        // when that subterm appears again, outside the "forall" term.
        let mut bound_vars = HashSet::new();
        let children: Box<dyn Iterator<Item = _>> = match root {
            Term::App(f, args) => Box::new(
                iter::once(f)
                    .chain(args.iter())
                    .map(|t| Box::new(t.free_vars())),
            ),
            Term::Op(_, args) => Box::new(args.iter().map(|t| Box::new(t.free_vars()))),
            Term::Quant(_, bindings, t) => {
                for (var, _) in bindings {
                    bound_vars.insert(var.as_str());
                }
                Box::new(iter::once(Box::new(t.free_vars())))
            }
            _ => Box::new(iter::empty()),
        };
        Self {
            root,
            visited_root: false,
            bound_vars,
            inner: children.flatten(),
        }
    }
}

impl<'a> Iterator for FreeVars<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.visited_root {
            self.visited_root = true;
            if let Some(var) = self.root.try_as_var() {
                return Some(var);
            }
        }

        loop {
            let got = self.inner.next()?;
            if !self.bound_vars.contains(got) {
                return Some(got);
            }
        }
    }
}
