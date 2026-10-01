use carcara::ast::{
    Binder, MatchCase, Operator, ParamOperator, QualifiedOperator, Rc, Sort, SortedVar, Term,
};
use owo_colors::{OwoColorize, Style};
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
    indent_with_char(f, level, ' ')
}

fn indent_with_char<C: fmt::Display>(
    f: &mut fmt::Formatter,
    level: usize,
    indicator_char: C,
) -> fmt::Result {
    const INDENT_UNIT: &str = "  ";
    write!(f, "{}", indicator_char)?;
    for _ in 0..level {
        write!(f, "{}", INDENT_UNIT)?;
    }
    Ok(())
}

fn addition<T>(f: &mut fmt::Formatter, t: T, level: usize, use_colors: bool) -> fmt::Result
where
    T: fmt::Display,
{
    let c = if use_colors {
        Style::new().green().bold()
    } else {
        Style::new()
    };
    indent_with_char(f, level, '+'.style(c))?;
    writeln!(f, "{}", t.style(c))
}

fn removal<T>(f: &mut fmt::Formatter, t: T, level: usize, use_colors: bool) -> fmt::Result
where
    T: fmt::Display,
{
    let c = if use_colors {
        Style::new().red().bold()
    } else {
        Style::new()
    };
    indent_with_char(f, level, '-'.style(c))?;
    writeln!(f, "{}", t.style(c))
}

fn plain<T>(f: &mut fmt::Formatter, t: T, level: usize) -> fmt::Result
where
    T: fmt::Display,
{
    indent(f, level)?;
    writeln!(f, "{}", t)
}

impl TermDiff {
    pub fn display(&self, use_colors: bool) -> impl fmt::Display {
        struct DisplayTermDiff<'a>(&'a TermDiff, bool);

        impl fmt::Display for DisplayTermDiff<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0.print(f, 0, self.1)
            }
        }

        DisplayTermDiff(self, use_colors)
    }

    fn print(&self, f: &mut fmt::Formatter, level: usize, use_colors: bool) -> fmt::Result {
        match self {
            TermDiff::Identical(term) => plain(f, term, level),
            TermDiff::Different(l, r) => {
                removal(f, l, level, use_colors)?;
                addition(f, r, level, use_colors)
            }
            TermDiff::App(func, args) => {
                match func {
                    UnaryDiff::Identical(func) => {
                        indent(f, level)?;
                        writeln!(f, "({}", func)?;
                    }
                    UnaryDiff::Different(l, r) => {
                        plain(f, "(", level)?;
                        removal(f, l, level + 1, use_colors)?;
                        addition(f, r, level + 1, use_colors)?;
                    }
                }
                for a in args {
                    a.print(f, level + 1, use_colors)?;
                }
                plain(f, ")", level)
            }
            TermDiff::Binder(binder, bindings, inner) => {
                match binder {
                    UnaryDiff::Identical(b) => {
                        indent(f, level)?;
                        writeln!(f, "({}", b)?;
                    }
                    UnaryDiff::Different(l, r) => {
                        plain(f, "(", level)?;
                        removal(f, l, level + 1, use_colors)?;
                        addition(f, r, level + 1, use_colors)?;
                    }
                }

                ElemDiff::print_multiple(
                    f,
                    bindings,
                    |(var, sort)| format!("({} {})", var, sort),
                    level + 1,
                    use_colors,
                )?;

                inner.print(f, level + 1, use_colors)?;

                plain(f, ")", level)
            }
            TermDiff::Let(assignments, inner) => {
                plain(f, "(let", level)?;

                ElemDiff::print_multiple(
                    f,
                    assignments,
                    |(var, value)| format!("({} {})", var, value),
                    level + 1,
                    use_colors,
                )?;

                inner.print(f, level + 1, use_colors)?;

                plain(f, ")", level)
            }
            TermDiff::Match(inner, cases) => {
                plain(f, "(match", level)?;

                inner.print(f, level + 1, use_colors)?;

                ElemDiff::print_multiple(
                    f,
                    cases,
                    |case| format!("({} {})", case.pattern, case.body),
                    level + 1,
                    use_colors,
                )?;

                plain(f, ")", level)
            }
        }
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
    fn print(&self, f: &mut fmt::Formatter, level: usize, use_colors: bool) -> fmt::Result {
        match self {
            ArgDiff::Matching(inner) => inner.print(f, level, use_colors),
            ArgDiff::NovelLeft(t) => removal(f, t, level, use_colors),
            ArgDiff::NovelRight(t) => addition(f, t, level, use_colors),
        }
    }
}

pub enum ElemDiff<T> {
    Identical(T),
    NovelLeft(T),
    NovelRight(T),
}

impl<T> ElemDiff<T> {
    fn inner(&self) -> &T {
        match self {
            ElemDiff::Identical(inner)
            | ElemDiff::NovelLeft(inner)
            | ElemDiff::NovelRight(inner) => inner,
        }
    }

    fn print_multiple(
        f: &mut fmt::Formatter,
        elems: &[Self],
        display: fn(&T) -> String,
        level: usize,
        use_colors: bool,
    ) -> fmt::Result {
        indent(f, level)?;
        if elems.is_empty() {
            writeln!(f, "()")
        } else if elems.iter().all(|e| matches!(e, ElemDiff::Identical(_))) {
            write!(f, "({}", display(elems[0].inner()))?;
            for e in &elems[1..] {
                write!(f, " {}", display(e.inner()))?;
            }
            writeln!(f, ")")
        } else {
            writeln!(f, "(")?;
            for e in elems {
                match e {
                    ElemDiff::Identical(inner) => plain(f, display(inner), level + 1)?,
                    ElemDiff::NovelLeft(inner) => {
                        removal(f, display(inner), level + 1, use_colors)?
                    }
                    ElemDiff::NovelRight(inner) => {
                        addition(f, display(inner), level + 1, use_colors)?
                    }
                }
            }
            plain(f, ")", level)
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
