use super::{Datatype, DatatypeConstructor, Pool};
use crate::ast::{Rc, Sort, Term};
use crate::parser::tests::parse_terms;
use indexmap::IndexMap;
use std::sync::Arc;

const DEFINITIONS: &str = "
    (declare-sort U 0)
    (declare-fun f (Int) U)
    (declare-fun a () U)
    (declare-fun p () Bool)
    (declare-fun x () Int)
    (declare-fun r () Real)
    (declare-fun b () (_ BitVec 4))
    (declare-fun arr () (Array Int U))
";

#[test]
fn test_hash_consing() {
    let mut pool = Pool::new();
    let x1 = pool.add(Term::new_int(1));
    let x2 = pool.add(Term::new_int(1));
    let y = pool.add(Term::new_int(2));
    assert!(x1 == x2);
    assert!(x1 != y);

    let s1 = pool.add_sort(Sort::Int);
    let s2 = pool.add_sort(Sort::Int);
    let s3 = pool.add_sort(Sort::Real);
    assert!(s1 == s2);
    assert!(s1 != s3);

    assert!(pool.bool_true() == pool.bool_constant(true));
    assert!(pool.bool_false() == pool.bool_constant(false));
    assert!(pool.bool_true() != pool.bool_false());
}

#[test]
fn test_compute_sort() {
    let cases = [
        ("1", "Int"),
        ("1.5", "Real"),
        ("\"s\"", "String"),
        ("#b0101", "(_ BitVec 4)"),
        ("a", "U"),
        ("(f x)", "U"),
        ("(not p)", "Bool"),
        ("(= a a)", "Bool"),
        ("(+ x 1)", "Int"),
        ("(+ r 1.0)", "Real"),
        ("(bvadd b b)", "(_ BitVec 4)"),
        ("(concat b b)", "(_ BitVec 8)"),
        ("((_ extract 2 1) b)", "(_ BitVec 2)"),
        ("(ite p x 2)", "Int"),
        ("(select arr x)", "U"),
        ("(store arr x a)", "(Array Int U)"),
        ("(forall ((y Int)) (> y x))", "Bool"),
        ("(lambda ((y Int)) (f y))", "(-> Int U)"),
        ("(choice ((y Int)) (> y x))", "Int"),
        ("(let ((y x)) (+ y 1))", "Int"),
    ];
    for (term, expected) in cases {
        let mut pool = Pool::new();
        let [term] = parse_terms(&mut pool, DEFINITIONS, [term]);
        assert_eq!(pool.sort(&term).to_string(), expected);
    }
}

#[test]
fn test_free_vars_and_choice_subterms() {
    let mut pool = Pool::new();
    let [term, choice] = parse_terms(
        &mut pool,
        DEFINITIONS,
        [
            "(and p (forall ((y Int)) (> y x)) (= (choice ((z Int)) (> z x)) 1))",
            "(choice ((z Int)) (> z x))",
        ],
    );
    let free: Vec<_> = pool
        .free_vars(&term)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(free, ["p", "x"]);

    // The result is cached, so asking again gives the same set
    let again: Vec<_> = pool
        .free_vars(&term)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(again, free);

    let choices: Vec<_> = pool.choice_subterms(&term).iter().cloned().collect();
    assert!(choices == [choice]);
}

#[test]
fn test_datatypes() {
    let mut pool = Pool::new();
    let datatype = Datatype {
        params: Vec::new(),
        constructors: IndexMap::from([(
            "nil".to_owned(),
            DatatypeConstructor { selectors: Vec::new() },
        )]),
    };
    pool.add_datatype("List".to_owned(), datatype);
    assert!(pool.get_datatype("List").constructors.contains_key("nil"));
}

#[test]
fn test_child_pool() {
    let mut parent = Pool::new();
    let [p, not_p] = parse_terms(&mut parent, DEFINITIONS, ["p", "(not p)"]);
    let int_sort = parent.add_sort(Sort::Int);
    let datatype = Datatype {
        params: Vec::new(),
        constructors: IndexMap::new(),
    };
    parent.add_datatype("D".to_owned(), datatype);
    let parent = Arc::new(parent);

    let mut child = Pool::with_parent(parent.clone());

    // Terms and sorts that exist in the parent are reused, not reallocated
    assert!(child.add(Term::Op(crate::ast::Operator::Not, vec![p.clone()])) == not_p);
    assert!(child.add_sort(Sort::Int) == int_sort);

    // Metadata cached in the parent is visible from the child
    assert!(child.sort(&not_p) == parent.sort(&not_p));
    assert!(child.free_vars(&not_p).contains(&p));
    assert!(child.get_datatype("D").constructors.is_empty());

    // New terms are added to the child only
    let and = child.add(Term::Op(
        crate::ast::Operator::And,
        vec![p.clone(), not_p.clone()],
    ));
    assert!(parent.terms.get(&*and).is_none());
    assert_eq!(child.sort(&and).as_ref(), &Sort::Bool);
}

#[test]
fn test_child_pool_sorts_are_shared() {
    // A sort computed in the child pool must be the same allocation as the equal sort in the
    // parent, since `Rc`s are compared by pointer
    let mut parent = Pool::new();
    let [p] = parse_terms(&mut parent, DEFINITIONS, ["p"]);
    let parent = Arc::new(parent);
    let mut child = Pool::with_parent(parent.clone());

    let not_p = child.add(Term::Op(crate::ast::Operator::Not, vec![p.clone()]));
    let bool_in_parent: Rc<Sort> = parent.sort(&p);
    assert!(child.sort(&not_p) == bool_in_parent);
}
