use std::collections::{hash_map::DefaultHasher, HashMap};
use std::hash::{Hash, Hasher};

use indexmap::{IndexMap, IndexSet};

use crate::ast::{match_term, Operator, Rc, Sort, Term, TermPool};

pub fn clauses_to_or(pool: &mut dyn TermPool, clauses: &[Rc<Term>]) -> Option<Rc<Term>> {
    if clauses.is_empty() {
        return None;
    }

    if clauses.len() == 1 {
        return Some(clauses[0].clone());
    }

    Some(pool.add(Term::Op(Operator::Or, clauses.to_vec())))
}

pub fn get_equational_terms(term: &Rc<Term>) -> Option<(Operator, &Rc<Term>, &Rc<Term>)> {
    if let Some((lhs, rhs)) = match_term!((= x y) = term) {
        return Some((Operator::Equals, lhs, rhs));
    }
    if let Some((lhs, rhs)) = match_term!((distinct x y) = term) {
        return Some((Operator::Distinct, lhs, rhs));
    }
    None
}

#[inline]
pub fn str_to_u64(input: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    input.hash(&mut hasher);
    hasher.finish()
}

pub fn collect_vars(root: &Rc<Term>, collect_functions: bool) -> IndexMap<String, Rc<Term>> {
    fn visit(term: &Rc<Term>, acc: &mut IndexMap<String, Rc<Term>>, collect_functions: bool) {
        match &**term {
            Term::Const(_) | Term::Sort(_) => {}

            Term::Var(name, sort) => {
                if !collect_functions {
                    if let Some(Sort::Function(_)) = sort.as_sort() {
                        return;
                    }
                }
                // If we are not collecting functions, or if the
                // keep the first sort we see for a given identifier
                acc.entry(name.clone()).or_insert_with(|| sort.clone());
            }

            Term::App(fun, args) => {
                visit(fun, acc, collect_functions);
                for arg in args {
                    visit(arg, acc, collect_functions);
                }
            }

            Term::Op(_, args) => {
                for arg in args {
                    visit(arg, acc, collect_functions);
                }
            }

            Term::Binder(_, bindings, body) => {
                // Traverse each binder declaration (identifier + sort) …
                for (id, sort) in bindings {
                    acc.entry(id.clone()).or_insert_with(|| sort.clone());
                    visit(sort, acc, collect_functions);
                }
                // … and then its body.
                visit(body, acc, collect_functions);
            }

            Term::Let(bindings, body) => {
                for (id, sort) in bindings {
                    acc.entry(id.clone()).or_insert_with(|| sort.clone());
                    visit(sort, acc, collect_functions);
                }
                visit(body, acc, collect_functions);
            }

            Term::Match(term, patterns) => {
                visit(term, acc, collect_functions);
                for (bindings, pattern, result) in patterns {
                    for (id, sort) in bindings {
                        acc.entry(id.clone()).or_insert_with(|| sort.clone());
                        visit(sort, acc, collect_functions);
                    }
                    visit(pattern, acc, collect_functions);
                    visit(result, acc, collect_functions);
                }
            }

            Term::ParamOp { op_args, args, .. } => {
                for t in op_args.iter().chain(args) {
                    visit(t, acc, collect_functions);
                }
            }
        }
    }

    let mut map = IndexMap::<String, Rc<Term>>::new();
    visit(root, &mut map, collect_functions);
    map.into_iter().collect()
}

pub fn collect_subterms(root: &Rc<Term>) -> Vec<Rc<Term>> {
    fn visit(term: &Rc<Term>, acc: &mut IndexSet<Rc<Term>>) {
        if !acc.insert(term.clone()) {
            return;
        }

        match &**term {
            Term::Const(_) | Term::Var(_, _) | Term::Sort(_) => {}
            Term::App(fun, args) => {
                visit(fun, acc);
                for arg in args {
                    visit(arg, acc);
                }
            }
            Term::Op(_, args) => {
                for arg in args {
                    visit(arg, acc);
                }
            }
            Term::Binder(_, bindings, body) | Term::Let(bindings, body) => {
                for (_, value) in bindings {
                    visit(value, acc);
                }
                visit(body, acc);
            }
            Term::Match(term, patterns) => {
                visit(term, acc);
                for (bindings, pattern, result) in patterns {
                    for (_, sort) in bindings {
                        visit(sort, acc);
                    }
                    visit(pattern, acc);
                    visit(result, acc);
                }
            }
            Term::ParamOp { op_args, args, .. } => {
                for arg in op_args.iter().chain(args.iter()) {
                    visit(arg, acc);
                }
            }
        }
    }

    let mut terms = IndexSet::new();
    visit(root, &mut terms);
    terms.into_iter().collect()
}

// Notice this unify patterns in both directions, so be aware if you are using against some pattern in side-unique direction
pub fn unify_pattern_bidirectional(
    pat: &Rc<Term>,
    val: &Rc<Term>,
) -> Option<(HashMap<Rc<Term>, Rc<Term>>, HashMap<Rc<Term>, Rc<Term>>)> {
    fn occurs(v: &Rc<Term>, t: &Rc<Term>) -> bool {
        if v == t {
            return true;
        }
        match &**t {
            Term::Const(_) => false,
            Term::Var(_, _) => v == t,
            Term::Sort(s) => match s {
                Sort::Function(ts) => ts.iter().any(|x| occurs(v, x)),
                Sort::Atom(_, ts) => ts.iter().any(|x| occurs(v, x)),
                Sort::Array(i, e) => occurs(v, i) || occurs(v, e),
                Sort::Datatype(_, ts) => ts.iter().any(|x| occurs(v, x)),
                Sort::ParamSort(ps, inner) => ps.iter().any(|x| occurs(v, x)) || occurs(v, inner),
                Sort::RareList(inner) => occurs(v, inner),
                Sort::BitVec(_)
                | Sort::Bool
                | Sort::Int
                | Sort::Real
                | Sort::String
                | Sort::RegLan
                | Sort::Type
                | Sort::Var(_) => false,
            },
            Term::App(f, args) => occurs(v, f) || args.iter().any(|a| occurs(v, a)),
            Term::Op(_, args) => args.iter().any(|a| occurs(v, a)),
            Term::Binder(_, bl, body) => bl.iter().any(|(_, t)| occurs(v, t)) || occurs(v, body),
            Term::Let(bl, body) => bl.iter().any(|(_, t)| occurs(v, t)) || occurs(v, body),
            Term::Match(term, patterns) => {
                occurs(v, term)
                    || patterns.iter().any(|(bindings, pattern, result)| {
                        bindings.iter().any(|(_, sort)| occurs(v, sort))
                            || occurs(v, pattern)
                            || occurs(v, result)
                    })
            }
            Term::ParamOp { op_args, args, .. } => {
                op_args.iter().any(|x| occurs(v, x)) || args.iter().any(|x| occurs(v, x))
            }
        }
    }

    fn unify_term(
        a: &Rc<Term>,
        b: &Rc<Term>,
        lhs_env: &mut HashMap<Rc<Term>, Rc<Term>>,
        rhs_env: &mut HashMap<Rc<Term>, Rc<Term>>,
    ) -> bool {
        if a == b {
            return true;
        }

        match (&**a, &**b) {
            // -------- term variables (no sort checking; trust structure) --------
            (Term::Var(_, _), _) => {
                if let Some(bound) = lhs_env.get(a).cloned() {
                    return unify_term(&bound, b, lhs_env, rhs_env);
                }
                if matches!(&**b, Term::Var(_, _)) {
                    if let Some(rbound) = rhs_env.get(b).cloned() {
                        return unify_term(a, &rbound, lhs_env, rhs_env);
                    }
                }
                if occurs(a, b) {
                    return false;
                }
                lhs_env.insert(a.clone(), b.clone());
                true
            }
            (_, Term::Var(_, _)) => {
                if let Some(bound) = rhs_env.get(b).cloned() {
                    return unify_term(a, &bound, lhs_env, rhs_env);
                }
                if matches!(&**a, Term::Var(_, _)) {
                    if let Some(lbound) = lhs_env.get(a).cloned() {
                        return unify_term(&lbound, b, lhs_env, rhs_env);
                    }
                }
                if occurs(b, a) {
                    return false;
                }
                rhs_env.insert(b.clone(), a.clone());
                true
            }

            // -------- constants --------
            (Term::Const(c1), Term::Const(c2)) => c1 == c2,

            // -------- operators --------
            (Term::Op(op1, a1), Term::Op(op2, a2)) if op1 == op2 && a1.len() == a2.len() => a1
                .iter()
                .zip(a2.iter())
                .all(|(x, y)| unify_term(x, y, lhs_env, rhs_env)),

            // -------- applications --------
            (Term::App(f1, a1), Term::App(f2, a2)) if a1.len() == a2.len() => {
                unify_term(f1, f2, lhs_env, rhs_env)
                    && a1
                        .iter()
                        .zip(a2.iter())
                        .all(|(x, y)| unify_term(x, y, lhs_env, rhs_env))
            }

            // -------- sorts as first-class terms --------
            (Term::Sort(s1), Term::Sort(s2)) => {
                match (s1, s2) {
                    // sort variable on the left → bind in lhs_env (keyed by the *whole* Term::Sort node)
                    (Sort::Var(_), _) => {
                        if let Some(bound) = lhs_env.get(a).cloned() {
                            return unify_term(&bound, b, lhs_env, rhs_env);
                        }
                        if let Term::Sort(Sort::Var(_)) = &**b {
                            if let Some(rbound) = rhs_env.get(b).cloned() {
                                return unify_term(a, &rbound, lhs_env, rhs_env);
                            }
                        }
                        if occurs(a, b) {
                            return false;
                        }
                        lhs_env.insert(a.clone(), b.clone());
                        true
                    }
                    // sort variable on the right → bind in rhs_env
                    (_, Sort::Var(_)) => {
                        if let Some(bound) = rhs_env.get(b).cloned() {
                            return unify_term(a, &bound, lhs_env, rhs_env);
                        }
                        if let Term::Sort(Sort::Var(_)) = &**a {
                            if let Some(lbound) = lhs_env.get(a).cloned() {
                                return unify_term(&lbound, b, lhs_env, rhs_env);
                            }
                        }
                        if occurs(b, a) {
                            return false;
                        }
                        rhs_env.insert(b.clone(), a.clone());
                        true
                    }

                    // ParamSort: same shape, unify params and inner structurally
                    (Sort::ParamSort(ps1, inner1), Sort::ParamSort(ps2, inner2)) => {
                        ps1.len() == ps2.len()
                            && ps1
                                .iter()
                                .zip(ps2.iter())
                                .all(|(x, y)| unify_term(x, y, lhs_env, rhs_env))
                            && unify_term(inner1, inner2, lhs_env, rhs_env)
                    }

                    // Function sorts
                    (Sort::Function(ts1), Sort::Function(ts2)) => {
                        ts1.len() == ts2.len()
                            && ts1
                                .iter()
                                .zip(ts2.iter())
                                .all(|(x, y)| unify_term(x, y, lhs_env, rhs_env))
                    }

                    // Array sorts
                    (Sort::Array(i1, e1), Sort::Array(i2, e2)) => {
                        unify_term(i1, i2, lhs_env, rhs_env) && unify_term(e1, e2, lhs_env, rhs_env)
                    }

                    // Atomic sorts with arguments
                    (Sort::Atom(n1, as1), Sort::Atom(n2, as2)) => {
                        n1 == n2
                            && as1.len() == as2.len()
                            && as1
                                .iter()
                                .zip(as2.iter())
                                .all(|(x, y)| unify_term(x, y, lhs_env, rhs_env))
                    }

                    (Sort::Datatype(n1, as1), Sort::Datatype(n2, as2)) => {
                        n1 == n2
                            && as1.len() == as2.len()
                            && as1
                                .iter()
                                .zip(as2.iter())
                                .all(|(x, y)| unify_term(x, y, lhs_env, rhs_env))
                    }

                    // BitVec width must match
                    (Sort::BitVec(w1), Sort::BitVec(w2)) => w1 == w2,

                    // Primitive sorts
                    (Sort::Bool, Sort::Bool)
                    | (Sort::Int, Sort::Int)
                    | (Sort::Real, Sort::Real)
                    | (Sort::String, Sort::String)
                    | (Sort::RegLan, Sort::RegLan)
                    | (Sort::Type, Sort::Type) => true,
                    (Sort::RareList(a), Sort::RareList(b)) => unify_term(a, b, lhs_env, rhs_env),

                    _ => false,
                }
            }

            // -------- binders --------
            (Term::Binder(b1, bl1, body1), Term::Binder(b2, bl2, body2))
                if b1 == b2 && bl1.len() == bl2.len() =>
            {
                let binds_ok = bl1
                    .iter()
                    .zip(bl2.iter())
                    .all(|((_, t1), (_, t2))| unify_term(t1, t2, lhs_env, rhs_env));
                binds_ok && unify_term(body1, body2, lhs_env, rhs_env)
            }

            // -------- let --------
            (Term::Let(b1, body1), Term::Let(b2, body2)) if b1.len() == b2.len() => {
                let binds_ok = b1
                    .iter()
                    .zip(b2.iter())
                    .all(|((_, t1), (_, t2))| unify_term(t1, t2, lhs_env, rhs_env));
                binds_ok && unify_term(body1, body2, lhs_env, rhs_env)
            }

            (Term::Match(t1, ps1), Term::Match(t2, ps2)) if ps1.len() == ps2.len() => {
                unify_term(t1, t2, lhs_env, rhs_env)
                    && ps1.iter().zip(ps2).all(
                        |((bindings1, pattern1, result1), (bindings2, pattern2, result2))| {
                            bindings1.len() == bindings2.len()
                                && bindings1.iter().zip(bindings2).all(
                                    |((_, sort1), (_, sort2))| {
                                        unify_term(sort1, sort2, lhs_env, rhs_env)
                                    },
                                )
                                && unify_term(pattern1, pattern2, lhs_env, rhs_env)
                                && unify_term(result1, result2, lhs_env, rhs_env)
                        },
                    )
            }

            (
                Term::ParamOp { op: op1, op_args: oa1, args: a1 },
                Term::ParamOp { op: op2, op_args: oa2, args: a2 },
            ) if op1 == op2 && oa1.len() == oa2.len() && a1.len() == a2.len() => {
                let ok_oa = oa1
                    .iter()
                    .zip(oa2.iter())
                    .all(|(x, y)| unify_term(x, y, lhs_env, rhs_env));
                let ok_a = a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(x, y)| unify_term(x, y, lhs_env, rhs_env));
                ok_oa && ok_a
            }

            _ => false,
        }
    }

    let mut lhs_env = HashMap::<Rc<Term>, Rc<Term>>::new(); // LHS vars (incl. sort vars-as-terms)
    let mut rhs_env = HashMap::<Rc<Term>, Rc<Term>>::new(); // RHS vars (incl. sort vars-as-terms)

    if unify_term(pat, val, &mut lhs_env, &mut rhs_env) {
        Some((lhs_env, rhs_env))
    } else {
        None
    }
}

pub fn unify_pattern(pat: &Rc<Term>, val: &Rc<Term>) -> bool {
    unify_pattern_bidirectional(pat, val).is_some()
}

pub fn hash_var_name(map: &mut HashMap<String, u64>, name: &str) -> u64 {
    let scoped_name = format!("var:{name}");
    if let Some(h) = map.get(&scoped_name) {
        return *h;
    }

    let h = str_to_u64(&scoped_name);
    map.insert(scoped_name, h);
    h
}

/// Collect all equality subterms from a term (including nested equalities)
pub fn collect_equality_subterms(term: &Rc<Term>) -> Vec<Rc<Term>> {
    let mut result = Vec::new();
    collect_equality_subterms_helper(term, &mut result);
    result
}

fn collect_equality_subterms_helper(term: &Rc<Term>, result: &mut Vec<Rc<Term>>) {
    match term.as_ref() {
        Term::Op(Operator::Equals, args) if args.len() == 2 => {
            // This is an equality - add it and recurse into arguments
            result.push(term.clone());
            collect_equality_subterms_helper(&args[0], result);
            collect_equality_subterms_helper(&args[1], result);
        }
        Term::Op(_, args) => {
            // Other operators - recurse into arguments
            for arg in args {
                collect_equality_subterms_helper(arg, result);
            }
        }
        Term::App(func, args) => {
            collect_equality_subterms_helper(func, result);
            for arg in args {
                collect_equality_subterms_helper(arg, result);
            }
        }
        Term::Binder(_, _, inner) => {
            collect_equality_subterms_helper(inner, result);
        }
        _ => {}
    }
}
