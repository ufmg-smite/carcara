use carcara::ast::{
    Binder, MatchCase, Operator, ParamOperator, QualifiedOperator, Rc, Sort, SortedVar, Term,
};
use owo_colors::OwoColorize;
use rapidhash::{HashMapExt, RapidHashMap};
use std::fmt;

pub enum TermDiff {
    Identical(Rc<Term>),

    // For terms that share no structure, e.g. `1` and `x`, or terms with incompatible head
    // variants, e.g. a binder and a `match` terms.
    Different(Rc<Term>, Rc<Term>),

    App(UnaryDiff<Applicand>, Vec<ArgDiff>),

    Binder(UnaryDiff<Binder>, Vec<ElemDiff<SortedVar>>, Box<TermDiff>),

    Let(Vec<ElemDiff<(String, Rc<Term>)>>, Box<TermDiff>),

    Match(Box<TermDiff>, Vec<ElemDiff<MatchCase>>),
}

fn indent(f: &mut fmt::Formatter, level: usize) -> fmt::Result {
    const INDENT_UNIT: &str = "  ";
    for _ in 0..level {
        write!(f, "{}", INDENT_UNIT)?;
    }
    Ok(())
}

impl TermDiff {
    fn print(&self, f: &mut fmt::Formatter, level: usize) -> fmt::Result {
        match self {
            TermDiff::Identical(term) => write!(f, "{}", term),
            TermDiff::Different(l, r) => {
                writeln!(f, "{}", l.red())?;
                indent(f, level)?;
                write!(f, "{}", r.green())
            }
            TermDiff::App(func, args) => {
                match func {
                    UnaryDiff::Identical(func) => writeln!(f, "({}", func)?,
                    UnaryDiff::Different(l, r) => {
                        writeln!(f, "(")?;
                        indent(f, level + 1)?;
                        writeln!(f, "{}", l.red())?;
                        indent(f, level + 1)?;
                        writeln!(f, "{}", r.green())?
                    }
                }
                for a in args {
                    a.print(f, level + 1)?;
                }
                indent(f, level)?;
                write!(f, ")")
            }
            TermDiff::Binder(binder, bindings, inner) => {
                match binder {
                    UnaryDiff::Identical(b) => writeln!(f, "({}", b)?,
                    UnaryDiff::Different(l, r) => {
                        writeln!(f, "(")?;
                        indent(f, level + 1)?;
                        writeln!(f, "{}", l.red())?;
                        indent(f, level + 1)?;
                        writeln!(f, "{}", r.green())?
                    }
                }

                indent(f, level + 1)?;
                ElemDiff::print_multiple(f, bindings, level + 1, |(var, sort)| {
                    format!("({} {})", var, sort)
                })?;

                indent(f, level + 1)?;
                inner.print(f, level + 1)?;
                writeln!(f)?;
                indent(f, level)?;
                write!(f, ")")
            }
            TermDiff::Let(assignments, inner) => {
                writeln!(f, "(let")?;

                indent(f, level + 1)?;
                ElemDiff::print_multiple(f, assignments, level + 1, |(var, value)| {
                    format!("({} {})", var, value)
                })?;

                indent(f, level + 1)?;
                inner.print(f, level + 1)?;
                writeln!(f)?;
                indent(f, level)?;
                write!(f, ")")
            }
            TermDiff::Match(inner, cases) => {
                writeln!(f, "(match")?;

                indent(f, level + 1)?;
                inner.print(f, level + 1)?;
                writeln!(f)?;

                indent(f, level + 1)?;
                ElemDiff::print_multiple(f, cases, level + 1, |case| {
                    format!("({} {})", case.pattern, case.body)
                })?;

                indent(f, level)?;
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for TermDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.print(f, 0)
    }
}

pub enum UnaryDiff<T> {
    Identical(T),
    Different(T, T),
}

impl<T: PartialEq> UnaryDiff<T> {
    fn new(l: T, r: T) -> Self {
        if l == r {
            UnaryDiff::Identical(l)
        } else {
            UnaryDiff::Different(l, r)
        }
    }
}

#[derive(PartialEq)]
pub enum Applicand {
    Func(Rc<Term>),
    Op(Operator),
    ParamOp(ParamOperator, Vec<Rc<Term>>),
    AsOp(QualifiedOperator, Rc<Sort>),
}

impl fmt::Display for Applicand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Applicand::Func(func) => write!(f, "{}", func),
            Applicand::Op(op) => write!(f, "{}", op),
            Applicand::ParamOp(op, args) => {
                write!(f, "(_ {}", op)?;
                for a in args {
                    write!(f, " {}", a)?;
                }
                write!(f, ")")
            }
            Applicand::AsOp(op, sort) => write!(f, "(as {} {})", op, sort),
        }
    }
}

pub enum ArgDiff {
    Matching(TermDiff),
    NovelLeft(Rc<Term>),
    NovelRight(Rc<Term>),
}

impl ArgDiff {
    fn print(&self, f: &mut fmt::Formatter, level: usize) -> fmt::Result {
        indent(f, level)?;

        match self {
            ArgDiff::Matching(inner) => {
                inner.print(f, level)?;
                writeln!(f)
            }
            ArgDiff::NovelLeft(t) => writeln!(f, "{}", t.red()),
            ArgDiff::NovelRight(t) => writeln!(f, "{}", t.green()),
        }
    }
}

pub enum ElemDiff<T> {
    Identical(T),
    NovelLeft(T),
    NovelRight(T),
}

impl<T> ElemDiff<T> {
    fn print(&self, f: &mut fmt::Formatter, display: fn(&T) -> String) -> fmt::Result {
        match self {
            ElemDiff::Identical(inner) => write!(f, "{}", display(inner)),
            ElemDiff::NovelLeft(inner) => write!(f, "{}", display(inner).red()),
            ElemDiff::NovelRight(inner) => write!(f, "{}", display(inner).green()),
        }
    }

    fn print_multiple(
        f: &mut fmt::Formatter,
        elems: &[Self],
        level: usize,
        display: fn(&T) -> String,
    ) -> fmt::Result {
        if elems.is_empty() {
            writeln!(f, "()")
        } else if elems.iter().all(|e| matches!(e, ElemDiff::Identical(_))) {
            write!(f, "(")?;
            elems[0].print(f, display)?;
            for e in &elems[1..] {
                write!(f, " ")?;
                e.print(f, display)?;
            }
            writeln!(f, ")")
        } else {
            writeln!(f, "(")?;
            for e in elems {
                indent(f, level + 1)?;
                e.print(f, display)?;
                writeln!(f)?;
            }
            indent(f, level)?;
            writeln!(f, ")")
        }
    }
}

fn as_application(t: &Rc<Term>) -> (Applicand, &[Rc<Term>]) {
    match t.as_ref() {
        Term::App(f, args) => (Applicand::Func(f.clone()), args),
        Term::Op(op, args) => (Applicand::Op(*op), args),
        Term::ParamOp { op, op_args, args } => (Applicand::ParamOp(*op, op_args.clone()), args),
        Term::AsOp(op, sort, args) => (Applicand::AsOp(*op, sort.clone()), args),
        _ => unreachable!(),
    }
}

pub fn diff(l: &Rc<Term>, r: &Rc<Term>) -> TermDiff {
    match (l.as_ref(), r.as_ref()) {
        _ if l == r => TermDiff::Identical(l.clone()),

        // match on App
        (
            Term::App(_, _) | Term::Op(_, _) | Term::ParamOp { .. } | Term::AsOp(..),
            Term::App(_, _) | Term::Op(_, _) | Term::ParamOp { .. } | Term::AsOp(..),
        ) => {
            let (l, r) = (as_application(l), as_application(r));
            let head = UnaryDiff::new(l.0, r.0);
            let args = diff_args(l.1, r.1);
            TermDiff::App(head, args)
        }

        // match directly
        (Term::Binder(l_binder, l_list, l_inner), Term::Binder(r_binder, r_list, r_inner)) => {
            TermDiff::Binder(
                UnaryDiff::new(*l_binder, *r_binder),
                diff_elems(l_list, r_list),
                Box::new(diff(l_inner, r_inner)),
            )
        }
        (Term::Let(l_list, l_inner), Term::Let(r_list, r_inner)) => {
            TermDiff::Let(diff_elems(l_list, r_list), Box::new(diff(l_inner, r_inner)))
        }
        (Term::Match(l, l_cases), Term::Match(r, r_cases)) => {
            TermDiff::Match(Box::new(diff(l, r)), diff_elems(l_cases, r_cases))
        }

        // different heads
        _ => TermDiff::Different(l.clone(), r.clone()),
    }
}

fn diff_args(mut left: &[Rc<Term>], mut right: &[Rc<Term>]) -> Vec<ArgDiff> {
    shortest_path(left, right)
        .into_iter()
        .map(|m| match m {
            Move::NovelLeft => {
                let l = left.split_off_first().unwrap();
                ArgDiff::NovelLeft(l.clone())
            }
            Move::NovelRight => {
                let r = right.split_off_first().unwrap();
                ArgDiff::NovelRight(r.clone())
            }
            Move::Matching => {
                let l = left.split_off_first().unwrap();
                let r = right.split_off_first().unwrap();
                ArgDiff::Matching(diff(l, r))
            }
        })
        .collect()
}

fn diff_elems<T>(mut left: &[T], mut right: &[T]) -> Vec<ElemDiff<T>>
where
    T: Diffable + Clone,
{
    shortest_path(left, right)
        .into_iter()
        .map(|m| match m {
            Move::NovelLeft => {
                let l = left.split_off_first().unwrap();
                ElemDiff::NovelLeft(l.clone())
            }
            Move::NovelRight => {
                let r = right.split_off_first().unwrap();
                ElemDiff::NovelRight(r.clone())
            }
            Move::Matching => {
                let l = left.split_off_first().unwrap();
                let r = right.split_off_first().unwrap();
                assert!(l == r);
                ElemDiff::Identical(l.clone())
            }
        })
        .collect()
}

trait Diffable: PartialEq {
    fn matching_cost(left: &Self, right: &Self) -> Option<usize> {
        if left == right { Some(1) } else { None }
    }
}

impl Diffable for Rc<Term> {
    fn matching_cost(left: &Self, right: &Self) -> Option<usize> {
        if left == right {
            return Some(1);
        }
        match (left.as_ref(), right.as_ref()) {
            (
                Term::App(..) | Term::Op(..) | Term::ParamOp { .. } | Term::AsOp(..),
                Term::App(..) | Term::Op(..) | Term::ParamOp { .. } | Term::AsOp(..),
            )
            | (Term::Binder(..), Term::Binder(..))
            | (Term::Let(..), Term::Let(..))
            | (Term::Match(..), Term::Match(..)) => Some(100),
            _ => None,
        }
    }
}

// While we could technically recurse into sorts, we currently don't
impl Diffable for Rc<Sort> {}
impl Diffable for SortedVar {}
impl Diffable for (String, Rc<Term>) {}
impl Diffable for MatchCase {}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
enum Move {
    NovelLeft,
    NovelRight,
    Matching,
}

fn shortest_path<T: Diffable>(left: &[T], right: &[T]) -> Vec<Move> {
    #[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
    struct Vertex {
        // indices into the left, right slices
        l: usize,
        r: usize,
    }

    struct Reached(Vertex, usize, Move);

    impl PartialEq for Reached {
        fn eq(&self, other: &Self) -> bool {
            // We have to implement it like this to make sure the `Ord` implementation is a total
            // order
            self.1 == other.1
        }
    }

    impl Eq for Reached {}

    impl PartialOrd for Reached {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }

    impl Ord for Reached {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.1.cmp(&other.1).reverse()
        }
    }

    if left.is_empty() && right.is_empty() {
        return Vec::new();
    }

    let mut heap = std::collections::BinaryHeap::new();
    heap.push(Reached(Vertex { l: 0, r: 0 }, 0, Move::Matching));

    let mut traversed: RapidHashMap<Vertex, Move> = RapidHashMap::new();

    let last = loop {
        let Reached(v, cost, m) = heap.pop().unwrap();
        if traversed.contains_key(&v) {
            continue;
        }
        traversed.insert(v, m);

        if v.l == left.len() && v.r == right.len() {
            break (v, m);
        }

        if v.l < left.len() {
            let new_v = Vertex { l: v.l + 1, r: v.r };
            heap.push(Reached(new_v, cost + 300, Move::NovelLeft));
        }
        if v.r < right.len() {
            let new_v = Vertex { l: v.l, r: v.r + 1 };
            heap.push(Reached(new_v, cost + 300, Move::NovelRight));
        }
        if v.l < left.len()
            && v.r < right.len()
            && let Some(edge_cost) = Diffable::matching_cost(&left[v.l], &right[v.r])
        {
            let new_v = Vertex { l: v.l + 1, r: v.r + 1 };
            heap.push(Reached(new_v, cost + edge_cost, Move::Matching));
        }
    };
    let mut moves = vec![];
    let mut curr = last.0;
    while curr.l > 0 || curr.r > 0 {
        let m = traversed[&curr];
        moves.push(m);
        curr = match m {
            Move::NovelLeft => Vertex { l: curr.l - 1, r: curr.r },
            Move::NovelRight => Vertex { l: curr.l, r: curr.r - 1 },
            Move::Matching => Vertex { l: curr.l - 1, r: curr.r - 1 },
        }
    }
    moves.reverse();
    moves
}
