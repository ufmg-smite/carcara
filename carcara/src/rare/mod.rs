use indexmap::{IndexMap, IndexSet};
use rug::Integer;

use crate::{
    ast::{rare_rules::RewriteTerm, Operator, Rc, Sort, Term, TermPool},
    build_equation, pseudo_term,
};

#[derive(Debug, Default)]
struct RewriteContext {
    cache: IndexMap<Rc<Term>, Rc<Term>>,
    in_progress: IndexSet<Rc<Term>>,
}

pub fn get_rules() -> Vec<(RewriteTerm, RewriteTerm)> {
    // For each n-ary (right-assoc-nil) operator we need, in this order:
    //   flatten   `(Op (RareList ..x..)) ~> (Op x)`  -- splice a rare list into the parent
    //   singleton `(Op x) ~> x`                       -- a one-argument application is its argument
    //   empty     `(Op) ~> <nil>`                     -- the operator's nil terminator
    // The flatten rule MUST precede the singleton rule: `check_rewrites` returns the first
    // matching rule, and `(Op x)` also matches `(Op (RareList ..))`, so without flatten-first a
    // single rare-list argument would be wrongly collapsed instead of spliced.
    //
    // Bitvector n-ary operators have width-dependent nil terminators that cannot be written as a
    // static constant, so they only get flatten + singleton rules here; the empty -> nil case is
    // synthesized from the operand width in `finish_op` / `bv_nil`.
    vec![
        build_equation!((RareList ..x..) ~> x),
        // Booleans
        build_equation!((And (RareList ..x..)) ~> (And x)),
        build_equation!((Or (RareList ..x..)) ~> (Or x)),
        build_equation!((And x) ~> x),
        build_equation!((Or x) ~> x),
        build_equation!((Or true) ~> true),
        build_equation!((And false) ~> false),
        // Arithmetic
        build_equation!((Add (RareList ..x..)) ~> (Add x)),
        build_equation!((Add x) ~> x),
        build_equation!((Add) ~> 0),
        build_equation!((Mult (RareList ..x..)) ~> (Mult x)),
        build_equation!((Mult x) ~> x),
        build_equation!((Mult) ~> 1),
        // Strings
        build_equation!((StrConcat (RareList ..x..)) ~> (StrConcat x)),
        build_equation!((StrConcat x) ~> x),
        build_equation!((StrConcat) ~> ""),
        // Regular expressions
        // re.++ has nil `(str.to_re "")`, which is not a zero-argument term, so we omit its empty
        // rule and keep only flatten + singleton; an empty re.++ does not arise from those.
        build_equation!((ReConcat (RareList ..x..)) ~> (ReConcat x)),
        build_equation!((ReConcat x) ~> x),
        build_equation!((ReUnion (RareList ..x..)) ~> (ReUnion x)),
        build_equation!((ReUnion x) ~> x),
        build_equation!((ReUnion) ~> (ReNone)),
        build_equation!((ReIntersection (RareList ..x..)) ~> (ReIntersection x)),
        build_equation!((ReIntersection x) ~> x),
        build_equation!((ReIntersection) ~> (ReAll)),
        // Bitvectors (empty -> nil handled in `finish_op`/`bv_nil`)
        build_equation!((BvAnd (RareList ..x..)) ~> (BvAnd x)),
        build_equation!((BvAnd x) ~> x),
        build_equation!((BvOr (RareList ..x..)) ~> (BvOr x)),
        build_equation!((BvOr x) ~> x),
        build_equation!((BvXor (RareList ..x..)) ~> (BvXor x)),
        build_equation!((BvXor x) ~> x),
        build_equation!((BvAdd (RareList ..x..)) ~> (BvAdd x)),
        build_equation!((BvAdd x) ~> x),
        build_equation!((BvMul (RareList ..x..)) ~> (BvMul x)),
        build_equation!((BvMul x) ~> x),
        build_equation!((BvConcat (RareList ..x..)) ~> (BvConcat x)),
        build_equation!((BvConcat x) ~> x),
    ]
}

#[derive(Debug, Clone)]
enum Trace<T1, T2> {
    Term(T1),
    ManyTerm(T2),
}

type TraceRef<'a> = Trace<&'a Rc<Term>, &'a Vec<Rc<Term>>>;
type TraceOwned = Trace<Rc<Term>, Vec<Rc<Term>>>;

#[inline]
fn match_meta_terms<'a, 'b>(
    term: &'a Rc<Term>,
    rule: &'b RewriteTerm,
    traces: &'b mut IndexMap<String, TraceRef<'a>>,
) -> Option<&'b mut IndexMap<String, TraceRef<'a>>>
where
    'a: 'b,
{
    match rule {
        RewriteTerm::ManyEq(op, var) => match term.as_ref() {
            Term::Op(op_, rest_) if op == op_ => {
                traces.insert((*var).to_owned(), Trace::ManyTerm(rest_));
                Some(traces)
            }
            _ => None,
        },
        RewriteTerm::OperatorEq(op, rest) => match term.as_ref() {
            Term::Op(op_, rest_) if op == op_ => {
                if rest_.len() != rest.len() {
                    return None;
                }

                let mut rest = rest.iter();
                let mut traces = Some(traces);
                for param in rest_ {
                    let rule = rest.next().unwrap();
                    traces = match_meta_terms(param, rule, traces.unwrap());
                    traces.as_ref()?;
                }
                traces
            }
            _ => None,
        },
        RewriteTerm::VarEqual(var) => {
            traces.insert((*var).to_owned(), Trace::Term(term));
            Some(traces)
        }
        RewriteTerm::Const(c) => match term.as_ref() {
            Term::Const(c_) if c == c_ => Some(traces),
            _ => None,
        },
    }
}

#[inline]
fn reconstruct_meta_terms<'a>(
    pool: &mut dyn TermPool,
    rule: &'a RewriteTerm,
    traces: &IndexMap<String, TraceRef<'a>>,
) -> TraceOwned {
    match rule {
        RewriteTerm::ManyEq(_, _) => unreachable!(),
        RewriteTerm::OperatorEq(op, params) => {
            let mut args = vec![];
            for param in params {
                let k = reconstruct_meta_terms(pool, param, traces);
                match k {
                    Trace::Term(term) => args.push(term.clone()),
                    Trace::ManyTerm(terms) => args.extend(terms.iter().cloned()),
                }
            }
            Trace::Term(pool.add(Term::Op(*op, args)))
        }
        RewriteTerm::VarEqual(var) => {
            let trace = traces.get(*var).unwrap();
            match trace {
                Trace::Term(t) => Trace::Term((*t).clone()),
                Trace::ManyTerm(t) => Trace::ManyTerm((*t).clone()),
            }
        }
        RewriteTerm::Const(c) => Trace::Term(pool.add(Term::Const((*c).clone()))),
    }
}

fn check_rewrites(
    pool: &mut dyn TermPool,
    term: &Rc<Term>,
    rules: &[(RewriteTerm, RewriteTerm)],
) -> Option<TraceOwned> {
    for rule in rules {
        let mut traces = IndexMap::new();
        let lhs = &rule.0;
        if let Some(traces) = match_meta_terms(term, lhs, &mut traces) {
            return Some(reconstruct_meta_terms(pool, &rule.1, traces));
        }
    }
    None
}

fn rewrite_arg_for_parent(
    pool: &mut dyn TermPool,
    arg: &Rc<Term>,
    rules: &[(RewriteTerm, RewriteTerm)],
    ctx: &mut RewriteContext,
) -> Vec<Rc<Term>> {
    if let Some(trace) = check_rewrites(pool, arg, rules) {
        match trace {
            Trace::Term(t) => {
                if t == *arg {
                    vec![t]
                } else {
                    vec![rewrite_meta_terms_inner(pool, t, rules, ctx)]
                }
            }
            Trace::ManyTerm(subs) => match arg.as_ref() {
                Term::Op(Operator::RareList, _) => subs,
                _ => vec![arg.clone()],
            },
        }
    } else {
        vec![rewrite_meta_terms_inner(pool, arg.clone(), rules, ctx)]
    }
}

fn rewrite_arguments(
    pool: &mut dyn TermPool,
    args: &[Rc<Term>],
    rules: &[(RewriteTerm, RewriteTerm)],
    ctx: &mut RewriteContext,
) -> Vec<Rc<Term>> {
    let mut flattened = Vec::new();
    for arg in args {
        flattened.extend(rewrite_arg_for_parent(pool, arg, rules, ctx));
    }

    let mut normalized = Vec::with_capacity(flattened.len());
    for arg in flattened {
        let rewritten = rewrite_meta_terms_inner(pool, arg.clone(), rules, ctx);
        if rewritten == arg {
            normalized.push(arg);
        } else {
            normalized.push(rewritten);
        }
    }
    normalized
}

/// When an n-ary bitvector operator's argument list has become empty after flattening (every
/// argument was an empty rare list), synthesize its width-dependent nil terminator:
///   bvadd / bvor / bvxor -> 0,  bvand -> all ones (2^m - 1),  bvmul -> 1,  concat -> empty bv.
///
/// Returns `None` when `op` is not an n-ary bitvector operator, the argument list is non-empty,
/// or the operand width cannot be recovered (e.g. a bare `(bvand)` with no operands). In the
/// last case the term is intentionally left un-normalized rather than guessing a width, so the
/// downstream equality check fails loudly instead of fabricating a wrong nil.
fn bv_nil_if_empty(
    pool: &mut dyn TermPool,
    op: Operator,
    original_args: &[Rc<Term>],
    new_args: &[Rc<Term>],
) -> Option<Rc<Term>> {
    if !new_args.is_empty() {
        return None;
    }
    // concat's nil is the zero-width empty bitvector; it needs no operand width.
    if op == Operator::BvConcat {
        return Some(pool.add(Term::new_bv(0, 0)));
    }
    let width = bv_operand_width(pool, original_args)?;
    let nil = match op {
        Operator::BvAdd | Operator::BvOr | Operator::BvXor => Term::new_bv(0, width),
        Operator::BvMul => Term::new_bv(1, width),
        Operator::BvAnd => Term::new_bv((Integer::from(1) << width) - 1, width),
        _ => return None,
    };
    Some(pool.add(nil))
}

/// Recover the bit width of an n-ary bitvector operator from its pre-flatten arguments. A rare
/// list argument is looked through to its first element, since after flattening the operator has
/// no arguments left to take the width from.
fn bv_operand_width(pool: &mut dyn TermPool, original_args: &[Rc<Term>]) -> Option<usize> {
    for arg in original_args {
        let probe = match arg.as_ref() {
            Term::Op(Operator::RareList, elems) => elems.first()?,
            _ => arg,
        };
        let sort = pool.sort(probe);
        if let Some(Sort::BitVec(width)) = sort.as_sort() {
            return Some(*width);
        }
    }
    None
}

fn rewrite_meta_terms_inner(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    rules: &[(RewriteTerm, RewriteTerm)],
    ctx: &mut RewriteContext,
) -> Rc<Term> {
    if let Some(cached) = ctx.cache.get(&term) {
        return cached.clone();
    }
    if !ctx.in_progress.insert(term.clone()) {
        return term;
    }

    let result = match term.as_ref() {
        Term::Var(_, _) => term.clone(),
        Term::Const(_) => term.clone(),
        Term::Sort(_) => term.clone(),

        Term::App(f, args) => {
            let f_prime = rewrite_meta_terms_inner(pool, f.clone(), rules, ctx);
            let new_args = rewrite_arguments(pool, args, rules, ctx);
            let new_term = pool.add(Term::App(f_prime, new_args));
            if new_term != term {
                rewrite_meta_terms_inner(pool, new_term, rules, ctx)
            } else {
                new_term
            }
        }

        Term::Op(op, args) => {
            if let Some(trace) = check_rewrites(pool, &term, rules) {
                match trace {
                    Trace::Term(t) => {
                        if t == term {
                            t
                        } else {
                            rewrite_meta_terms_inner(pool, t, rules, ctx)
                        }
                    }
                    Trace::ManyTerm(_) => {
                        let new_args = rewrite_arguments(pool, args, rules, ctx);
                        if let Some(nil) = bv_nil_if_empty(pool, *op, args, &new_args) {
                            nil
                        } else {
                            let new_term: Rc<Term> = pool.add(Term::Op(*op, new_args));
                            if new_term != term {
                                rewrite_meta_terms_inner(pool, new_term, rules, ctx)
                            } else {
                                new_term
                            }
                        }
                    }
                }
            } else {
                let new_args = rewrite_arguments(pool, args, rules, ctx);
                if let Some(nil) = bv_nil_if_empty(pool, *op, args, &new_args) {
                    nil
                } else {
                    let new_term = pool.add(Term::Op(*op, new_args));
                    if check_rewrites(pool, &new_term, rules).is_some() {
                        rewrite_meta_terms_inner(pool, new_term, rules, ctx)
                    } else {
                        new_term
                    }
                }
            }
        }

        Term::Binder(binder, bindings, body) => {
            let new_body = rewrite_meta_terms_inner(pool, body.clone(), rules, ctx);
            pool.add(Term::Binder(*binder, bindings.clone(), new_body))
        }

        Term::Let(bindings, body) => {
            let new_body = rewrite_meta_terms_inner(pool, body.clone(), rules, ctx);
            pool.add(Term::Let(bindings.clone(), new_body))
        }

        Term::ParamOp { op, op_args, args } => {
            let new_op_args = op_args
                .iter()
                .map(|op_arg| rewrite_meta_terms_inner(pool, op_arg.clone(), rules, ctx))
                .collect::<Vec<_>>();
            let new_args = args
                .iter()
                .map(|arg| rewrite_meta_terms_inner(pool, arg.clone(), rules, ctx))
                .collect::<Vec<_>>();
            pool.add(Term::ParamOp {
                op: *op,
                op_args: new_op_args,
                args: new_args,
            })
        }
    };

    ctx.in_progress.shift_remove(&term);
    ctx.cache.insert(term, result.clone());
    result
}

pub fn rewrite_meta_terms(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    rules: &[(RewriteTerm, RewriteTerm)],
) -> Rc<Term> {
    let mut ctx = RewriteContext::default();
    rewrite_meta_terms_inner(pool, term, rules, &mut ctx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::PrimitivePool, parser::*};

    fn run_test(definitions: &str, original: &str, rule: (RewriteTerm, RewriteTerm), result: &str) {
        let mut pool = PrimitivePool::new();
        let mut parser = Parser::new(&mut pool, Config::new(), definitions.as_bytes()).unwrap();
        parser.parse_problem().unwrap();

        let [original, result] = [original, result].map(|s| {
            parser.reset(s.as_bytes()).unwrap();
            parser.parse_term().unwrap()
        });

        let got = rewrite_meta_terms(&mut pool, original, &[rule]);

        assert_eq!(&result, &got);
    }

    macro_rules! run_tests {
        (
            definitions = $defs:literal,
            $($original:literal [$rule:expr] => $result:literal,)*
        ) => {{
            let definitions = $defs;
            $(run_test(definitions, $original, $rule, $result);)*
        }};
    }

    #[test]
    fn test_substitutions() {
        run_tests! {
            definitions = "
            (declare-const v Bool)
        ",
            "(not (not (not true)))" [build_equation!((Not (Not x)) ~> x)] => "(not true)",
            "(or true)" [build_equation!((Or true) ~> true)] => "true",

        }
    }

    use crate::ast::Constant;

    fn rare_list(pool: &mut PrimitivePool, elems: Vec<Rc<Term>>) -> Rc<Term> {
        pool.add(Term::Op(Operator::RareList, elems))
    }

    fn op(pool: &mut PrimitivePool, op: Operator, args: Vec<Rc<Term>>) -> Rc<Term> {
        pool.add(Term::Op(op, args))
    }

    fn int(pool: &mut PrimitivePool, value: i32) -> Rc<Term> {
        pool.add(Term::Const(Constant::Integer(Integer::from(value))))
    }

    fn bv(pool: &mut PrimitivePool, value: i32, width: usize) -> Rc<Term> {
        pool.add(Term::new_bv(value, width))
    }

    fn normalize(pool: &mut PrimitivePool, term: Rc<Term>) -> Rc<Term> {
        rewrite_meta_terms(pool, term, &get_rules())
    }

    #[test]
    fn test_nary_list_flatten_and_singleton() {
        let mut pool = PrimitivePool::new();

        // Flatten a rare list into its n-ary parent (and do NOT collapse a multi-element list).
        let (a, b, c) = (int(&mut pool, 1), int(&mut pool, 2), int(&mut pool, 3));
        let list = rare_list(&mut pool, vec![a.clone(), b.clone()]);
        let term = op(&mut pool, Operator::Add, vec![list, c.clone()]);
        let expected = op(&mut pool, Operator::Add, vec![a.clone(), b.clone(), c]);
        assert_eq!(expected, normalize(&mut pool, term));

        // A singleton rare list collapses to its element (flatten-before-singleton ordering).
        let list = rare_list(&mut pool, vec![a.clone()]);
        let term = op(&mut pool, Operator::Add, vec![list]);
        assert_eq!(a, normalize(&mut pool, term));

        // Strings: a trailing empty list disappears, leaving the singleton, which collapses.
        let s = pool.add(Term::Const(Constant::String("ab".to_owned())));
        let empty = rare_list(&mut pool, vec![]);
        let term = op(&mut pool, Operator::StrConcat, vec![s.clone(), empty]);
        assert_eq!(s, normalize(&mut pool, term));
    }

    #[test]
    fn test_nary_empty_to_nil() {
        let mut pool = PrimitivePool::new();

        // Arithmetic empties fold to the additive / multiplicative identity.
        let empty = rare_list(&mut pool, vec![]);
        let term = op(&mut pool, Operator::Add, vec![empty]);
        let zero = int(&mut pool, 0);
        assert_eq!(zero, normalize(&mut pool, term));

        let empty = rare_list(&mut pool, vec![]);
        let term = op(&mut pool, Operator::Mult, vec![empty]);
        let one = int(&mut pool, 1);
        assert_eq!(one, normalize(&mut pool, term));

        // Regex empties fold to re.none / re.all (zero-argument operators).
        let empty = rare_list(&mut pool, vec![]);
        let term = op(&mut pool, Operator::ReUnion, vec![empty]);
        let re_none = op(&mut pool, Operator::ReNone, vec![]);
        assert_eq!(re_none, normalize(&mut pool, term));

        let empty = rare_list(&mut pool, vec![]);
        let term = op(&mut pool, Operator::ReIntersection, vec![empty]);
        let re_all = op(&mut pool, Operator::ReAll, vec![]);
        assert_eq!(re_all, normalize(&mut pool, term));
    }

    #[test]
    fn test_bv_nary_flatten_and_singleton() {
        let mut pool = PrimitivePool::new();
        let (a, b, c) = (bv(&mut pool, 1, 4), bv(&mut pool, 2, 4), bv(&mut pool, 3, 4));

        // Flatten a rare list of bitvectors into its parent (not collapsed to a singleton).
        let list = rare_list(&mut pool, vec![a.clone(), b.clone()]);
        let term = op(&mut pool, Operator::BvAdd, vec![list, c.clone()]);
        let expected = op(&mut pool, Operator::BvAdd, vec![a.clone(), b.clone(), c]);
        assert_eq!(expected, normalize(&mut pool, term));

        // A singleton bitvector list collapses to its element.
        let list = rare_list(&mut pool, vec![a.clone()]);
        let term = op(&mut pool, Operator::BvAdd, vec![list]);
        assert_eq!(a, normalize(&mut pool, term));
    }

    #[test]
    fn test_bv_nil_synthesis() {
        // Width-dependent nil construction. The all-empty rewrite state that would trigger this
        // through `normalize` cannot itself carry a width, so exercise the helper directly with a
        // (non-empty originals, empty result) pair to verify the per-operator nil values.
        let mut pool = PrimitivePool::new();
        let probe = bv(&mut pool, 5, 4);
        let originals = vec![rare_list(&mut pool, vec![probe])];
        let empty: Vec<Rc<Term>> = vec![];

        let add_nil = bv_nil_if_empty(&mut pool, Operator::BvAdd, &originals, &empty).unwrap();
        assert_eq!(bv(&mut pool, 0, 4), add_nil);
        let mul_nil = bv_nil_if_empty(&mut pool, Operator::BvMul, &originals, &empty).unwrap();
        assert_eq!(bv(&mut pool, 1, 4), mul_nil);
        let and_nil = bv_nil_if_empty(&mut pool, Operator::BvAnd, &originals, &empty).unwrap();
        assert_eq!(bv(&mut pool, 15, 4), and_nil); // all ones at width 4

        // concat needs no operand width: its nil is the zero-width empty bitvector.
        let cat_nil = bv_nil_if_empty(&mut pool, Operator::BvConcat, &empty, &empty).unwrap();
        assert_eq!(bv(&mut pool, 0, 0), cat_nil);

        // Non-empty result -> no synthesis; unrecoverable width -> None.
        assert!(bv_nil_if_empty(&mut pool, Operator::BvAdd, &originals, &originals).is_none());
        assert!(bv_nil_if_empty(&mut pool, Operator::BvAnd, &empty, &empty).is_none());
    }
}
