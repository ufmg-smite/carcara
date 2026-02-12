use indexmap::IndexMap;

use crate::{
    ast::{rare_rules::RewriteTerm, Operator, Rc, Term, TermPool},
    build_equation, pseudo_term,
};

pub fn get_rules() -> Vec<(RewriteTerm, RewriteTerm)> {
    vec![
        build_equation!((RareList ..x..) ~> x),
        build_equation!((And (RareList ..x..)) ~> (And x)),
        build_equation!((Or (RareList ..x..)) ~> (Or x)),
        build_equation!((And x) ~> x),
        build_equation!((Or x) ~> x),
        build_equation!((Or true) ~> true),
        build_equation!((And false) ~> false)
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
) -> Vec<Rc<Term>> {
    if let Some(trace) = check_rewrites(pool, arg, rules) {
        match trace {
            Trace::Term(t) => {
                if t == *arg {
                    vec![t]
                } else {
                    vec![rewrite_meta_terms(pool, t, rules)]
                }
            }
            Trace::ManyTerm(subs) => match arg.as_ref() {
                Term::Op(Operator::RareList, _) => subs,
                _ => vec![arg.clone()],
            },
        }
    } else {
        vec![rewrite_meta_terms(pool, arg.clone(), rules)]
    }
}

fn rewrite_arguments(
    pool: &mut dyn TermPool,
    args: &[Rc<Term>],
    rules: &[(RewriteTerm, RewriteTerm)],
) -> Vec<Rc<Term>> {
    let mut flattened = Vec::new();
    for arg in args {
        flattened.extend(rewrite_arg_for_parent(pool, arg, rules));
    }

    let mut normalized = Vec::with_capacity(flattened.len());
    for arg in flattened {
        let rewritten = rewrite_meta_terms(pool, arg.clone(), rules);
        if rewritten == arg {
            normalized.push(arg);
        } else {
            normalized.push(rewritten);
        }
    }
    normalized
}

pub fn rewrite_meta_terms(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    rules: &[(RewriteTerm, RewriteTerm)],
) -> Rc<Term> {
    match term.as_ref() {
        Term::Var(_, _) => term.clone(),
        Term::Const(_) => term.clone(),
        Term::Sort(_) => term.clone(),

        Term::App(f, args) => {
            let f_prime = rewrite_meta_terms(pool, f.clone(), rules);
            let new_args = rewrite_arguments(pool, args, rules);
            let new_term = pool.add(Term::App(f_prime, new_args));
            if new_term != term {
                return rewrite_meta_terms(pool, new_term, rules);
            }

            new_term
        }

        Term::Op(op, args) => {
            if let Some(trace) = check_rewrites(pool, &term, rules) {
                match trace {
                    Trace::Term(t) => {
                        if t == term {
                            t
                        } else {
                            rewrite_meta_terms(pool, t, rules)
                        }
                    }
                    Trace::ManyTerm(_) => {
                        let new_args = rewrite_arguments(pool, args, rules);
                        let new_term: Rc<Term> = pool.add(Term::Op(*op, new_args));
                        if new_term != term {
                            return rewrite_meta_terms(pool, new_term, rules);
                        }

                        new_term
                    }
                }
            } else {
                let new_args = rewrite_arguments(pool, args, rules);
                let new_term = pool.add(Term::Op(*op, new_args));
                if check_rewrites(pool, &new_term, rules).is_some() {
                    return rewrite_meta_terms(pool, new_term, rules);
                }

                new_term
            }
        }

        Term::Binder(binder, bindings, body) => {
            let new_body = rewrite_meta_terms(pool, body.clone(), rules);
            pool.add(Term::Binder(*binder, bindings.clone(), new_body))
        }

        Term::Let(bindings, body) => {
            let new_body = rewrite_meta_terms(pool, body.clone(), rules);
            pool.add(Term::Let(bindings.clone(), new_body))
        }

        Term::ParamOp { op, op_args, args } => {
            let new_op_args = op_args
                .iter()
                .map(|op_arg| rewrite_meta_terms(pool, op_arg.clone(), rules))
                .collect::<Vec<_>>();
            let new_args = args
                .iter()
                .map(|arg| rewrite_meta_terms(pool, arg.clone(), rules))
                .collect::<Vec<_>>();
            pool.add(Term::ParamOp {
                op: *op,
                op_args: new_op_args,
                args: new_args,
            })
        }
    }
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
}
