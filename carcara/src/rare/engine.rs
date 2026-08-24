use std::{
    cell::OnceCell,
    collections::{HashMap, HashSet},
    iter::once,
    panic::{catch_unwind, AssertUnwindSafe},
    sync::Arc,
    time::{Duration, Instant},
};

use crate::{
    ast::{
        rare_rules::{AttributeParameters, RuleDefinition, Rules},
        Binder, Constant, Operator, ProofNode, Rc, Sort, Term, TermPool,
    },
    rare::{
        computational::{
            aci_norm::singleton_operators,
            arith_poly_norm, arith_poly_norm_rel,
            core::{declare_database_eliminations, declare_goal_eliminations},
            distinct_elim::declare_logic_operators,
            evaluation,
        },
        language::*,
        meta::lower_egg_language,
        util::{
            clauses_to_or, collect_subterms, collect_vars, get_equational_terms, hash_var_name,
        },
    },
};
use egg::Symbol;
use egglog::{
    self,
    ast::{Command, Span},
    constraint::{SimpleTypeConstraint, TypeConstraint},
    sort::{BoolSort, EqSort},
    ArcSort, EGraph, PrimitiveLike, Value,
};
use indexmap::{IndexMap, IndexSet};

#[derive(Clone, Debug, Default)]
pub struct EggFunctions {
    pub names: IndexMap<String, (bool, usize, Option<Sort>)>,
    pub shapes: IndexMap<String, IndexSet<Rc<Term>>>,
    pub assoc_calls: IndexMap<String, IndexSet<EggExpr>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RunEgglogOptions {
    pub max_goal_schedule_rounds: usize,
    pub continuous_saturation: bool,
    /// Cooperative wall-clock budget for one proof step, checked between egglog rule iterations.
    /// `None` means no timeout.
    pub timeout: Option<Duration>,
    /// If `true`, print the egglog program generated for each proof step.
    pub print_egglog: bool,
}

impl Default for RunEgglogOptions {
    fn default() -> Self {
        Self {
            max_goal_schedule_rounds: 3,
            continuous_saturation: false,
            timeout: None,
            print_egglog: false,
        }
    }
}

impl RunEgglogOptions {
    fn normalized_max_goal_schedule_rounds(self) -> usize {
        self.max_goal_schedule_rounds.max(1)
    }
}

pub struct RareCheckContext<'a> {
    database: &'a Rules,
    baseline: OnceCell<Result<RareDatabaseBaseline, String>>,
}

impl<'a> RareCheckContext<'a> {
    pub fn new(database: &'a Rules) -> Self {
        Self { database, baseline: OnceCell::new() }
    }

    fn baseline(&self) -> Result<&RareDatabaseBaseline, String> {
        self.baseline
            .get_or_init(|| prepare_database_safely(self.database))
            .as_ref()
            .map_err(Clone::clone)
    }

    #[cfg(test)]
    fn is_prepared(&self) -> bool {
        self.baseline.get().is_some()
    }
}

#[derive(Clone)]
struct RareDatabaseBaseline {
    egraph: EGraph,
    functions: EggFunctions,
    var_map: HashMap<String, u64>,
    code: String,
    has_distinct: bool,
    commands: HashSet<String>,
}

fn application_result_sort(head: &Rc<Term>) -> Option<Sort> {
    let Term::Var(_, sort_term) = head.as_ref() else {
        return None;
    };
    let Sort::Function(parts) = sort_term.as_sort()? else {
        return None;
    };
    parts.last()?.as_sort().cloned()
}

fn register_function_call(
    functions: &mut EggFunctions,
    name: &str,
    is_op: bool,
    arity: usize,
    result_sort: Option<Sort>,
) {
    functions
        .names
        .entry(name.to_owned())
        .and_modify(|info| {
            info.0 = is_op;
            info.1 = arity;
            if info.2.is_none() {
                info.2 = result_sort.clone();
            }
        })
        .or_insert((is_op, arity, result_sort));
}

fn bigrat_expr(numer: &rug::Integer, denom: &rug::Integer) -> EggExpr {
    EggExpr::Call(
        "bigrat".to_owned(),
        vec![
            EggExpr::Call(
                "from-string".to_owned(),
                vec![EggExpr::RawString(numer.to_string())],
            ),
            EggExpr::Call(
                "from-string".to_owned(),
                vec![EggExpr::RawString(denom.to_string())],
            ),
        ],
    )
}

struct CustomPrimitive {
    name: Symbol,
    input: Vec<ArcSort>,
    output: ArcSort,
    f: fn(&[Value]) -> Option<Value>,
}

impl PrimitiveLike for CustomPrimitive {
    fn name(&self) -> Symbol {
        self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        let sorts: Vec<_> = self
            .input
            .iter()
            .chain(once(&self.output as &ArcSort))
            .cloned()
            .collect();
        SimpleTypeConstraint::new(self.name(), sorts, span.clone()).into_box()
    }
    fn apply(
        &self,
        values: &[Value],
        _sorts: (&[ArcSort], &ArcSort),
        _egraph: Option<&mut EGraph>,
    ) -> Option<Value> {
        (self.f)(values)
    }
}

pub fn create_headers() -> EggLanguage {
    let stmts = vec![
        EggStatement::Ruleset("list-ruleset".to_owned()),
        EggStatement::DataType(
            "Term".to_owned(),
            vec![
                Constructor {
                    constr: (
                        "App".to_owned(),
                        vec![
                            ConstType::ConstrType("Term".to_owned()),
                            ConstType::ConstrType("Term".to_owned()),
                        ],
                    ),
                },
                Constructor {
                    constr: ("Const".to_owned(), vec![ConstType::Operator]),
                },
                Constructor {
                    constr: (
                        "Var".to_owned(),
                        vec![ConstType::Var, ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: ("Bool".to_owned(), vec![ConstType::Bool]),
                },
                Constructor {
                    constr: ("Num".to_owned(), vec![ConstType::Integer]),
                },
                Constructor {
                    constr: (
                        "Real".to_owned(),
                        vec![ConstType::Integer, ConstType::Integer],
                    ),
                },
                Constructor {
                    constr: (
                        "BitVec".to_owned(),
                        vec![ConstType::Operator, ConstType::Operator],
                    ),
                },
                Constructor {
                    constr: ("Op".to_owned(), vec![ConstType::Operator]),
                },
                Constructor {
                    constr: ("@String".to_owned(), vec![ConstType::Operator]),
                },
                Constructor {
                    constr: (
                        "Forall".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: (
                        "Exists".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: (
                        "Lambda".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: (
                        "Choice".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: (
                        "Sort".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
                Constructor {
                    constr: ("Empty".to_owned(), vec![]),
                },
                Constructor {
                    constr: (
                        "Args".to_owned(),
                        vec![
                            ConstType::ConstrType("Term".to_owned()),
                            ConstType::ConstrType("Term".to_owned()),
                        ],
                    ),
                },
                Constructor {
                    constr: (
                        "Mk".to_owned(),
                        vec![ConstType::ConstrType("Term".to_owned())],
                    ),
                },
            ],
        ),
        EggStatement::Constructor(
            "RatConst".to_owned(),
            vec![ConstType::ConstrType("BigRat".to_owned())],
            ConstType::ConstrType("Term".to_owned()),
        ),
        EggStatement::Sort(
            "AssocArgs".to_owned(),
            "Set".to_owned(),
            Box::new(EggExpr::Literal("Term".to_owned())),
        ),
        EggStatement::Constructor(
            "Assoc".to_owned(),
            vec![ConstType::ConstrType("AssocArgs".to_owned())],
            ConstType::ConstrType("Term".to_owned()),
        ),
        EggStatement::Relation(
            "Avaliable".to_owned(),
            vec![ConstType::ConstrType("Term".to_owned())],
        ),
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Mk(Box::new(EggExpr::Literal("t".to_owned())))],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("t".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Args(
                    Box::new(EggExpr::Literal("head".to_owned())),
                    Box::new(EggExpr::Literal("tail".to_owned())),
                )],
            )],
            head: vec![
                EggExpr::Call(
                    "Avaliable".to_owned(),
                    vec![EggExpr::Literal("head".to_owned())],
                ),
                EggExpr::Call(
                    "Avaliable".to_owned(),
                    vec![EggExpr::Literal("tail".to_owned())],
                ),
            ],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "App".to_owned(),
                    vec![
                        EggExpr::Literal("fn_term".to_owned()),
                        EggExpr::Literal("arg_term".to_owned()),
                    ],
                )],
            )],
            head: vec![
                EggExpr::Call(
                    "Avaliable".to_owned(),
                    vec![EggExpr::Literal("fn_term".to_owned())],
                ),
                EggExpr::Call(
                    "Avaliable".to_owned(),
                    vec![EggExpr::Literal("arg_term".to_owned())],
                ),
            ],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Var".to_owned(),
                    vec![
                        EggExpr::Literal("var_id".to_owned()),
                        EggExpr::Literal("sort_term".to_owned()),
                    ],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("sort_term".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Forall".to_owned(),
                    vec![EggExpr::Literal("body".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("body".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Exists".to_owned(),
                    vec![EggExpr::Literal("body".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("body".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Lambda".to_owned(),
                    vec![EggExpr::Literal("body".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("body".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Choice".to_owned(),
                    vec![EggExpr::Literal("body".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("body".to_owned())],
            )],
        },
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    "Sort".to_owned(),
                    vec![EggExpr::Literal("sort_term".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("sort_term".to_owned())],
            )],
        },
        EggStatement::Rewrite(
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t1".to_owned())),
                    Box::new(EggExpr::Literal("t2".to_owned())),
                )),
                Box::new(EggExpr::Literal("t3".to_owned())),
            )),
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Literal("t1".to_owned())),
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t2".to_owned())),
                    Box::new(EggExpr::Literal("t3".to_owned())),
                )),
            )),
            vec![],
        ),
        EggStatement::Rewrite(
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Literal("t1".to_owned())),
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t2".to_owned())),
                    Box::new(EggExpr::Literal("t3".to_owned())),
                )),
            )),
            Box::new(EggExpr::Args(
                Box::new(EggExpr::Args(
                    Box::new(EggExpr::Literal("t1".to_owned())),
                    Box::new(EggExpr::Literal("t2".to_owned())),
                )),
                Box::new(EggExpr::Literal("t3".to_owned())),
            )),
            vec![],
        ),
        EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Equal(
                Box::new(EggExpr::Mk(Box::new(EggExpr::Literal("x".to_owned())))),
                Box::new(EggExpr::Mk(Box::new(EggExpr::Literal("y".to_owned())))),
            )],
            head: vec![EggExpr::Union(
                Box::new(EggExpr::Literal("x".to_owned())),
                Box::new(EggExpr::Literal("y".to_owned())),
            )],
        },
    ];

    stmts
}

// This function is primarily used to insert premises to egraph
// But we use the relation Avaliable so we can know each one we added by using our translation
fn create_avaliable_premise(
    term: &Rc<Term>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
    recognize_vars: bool,
    context: &str,
) -> Result<Option<EggStatement>, String> {
    if term.is_var() {
        return Ok(None);
    }

    let mut premises = Vec::new();
    let mut sorted_vars = IndexMap::new();
    let vars = if recognize_vars {
        collect_vars(term, false)
    } else {
        IndexMap::default()
    };

    for (name, _sort) in &vars {
        let egg_expr = EggExpr::Literal(name.clone());
        sorted_vars.insert(name, (egg_expr.clone(), AttributeParameters::List));
        premises.push(EggExpr::Call("Avaliable".to_owned(), vec![egg_expr]));
    }

    let head = translate_term(term, &sorted_vars, func_cache, var_map, false, context)?;
    Ok(Some(EggStatement::Rule {
        ruleset: None,
        body: premises,
        head: vec![head],
    }))
}

pub fn to_egg_expr(
    term_rc: &Rc<Term>,
    subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
    collect_functions_shape: bool,
) -> Option<EggExpr> {
    fn build_args_list<I: IntoIterator<Item = Option<EggExpr>>>(it: I) -> Option<EggExpr> {
        let v: Vec<EggExpr> = it.into_iter().collect::<Option<Vec<EggExpr>>>()?;
        if v.is_empty() {
            return Some(EggExpr::Empty());
        }
        let mut it = v.into_iter().rev();
        let first = it.next()?;
        let mut acc = EggExpr::Args(Box::new(first), Box::new(EggExpr::Empty()));
        for e in it {
            acc = EggExpr::Args(Box::new(e), Box::new(acc));
        }
        Some(acc)
    }

    pub fn encapluse(egg_term: EggExpr) -> EggExpr {
        EggExpr::Mk(Box::new(egg_term))
    }

    pub fn to_raw_egg(
        term_rc: &Rc<Term>,
        subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
        func_cache: &mut EggFunctions,
        var_map: &mut HashMap<String, u64>,
        collect_functions_shape: bool,
    ) -> Option<EggExpr> {
        match &**term_rc {
            Term::Const(c) => match c {
                Constant::Integer(i) => Some(EggExpr::Num(i.clone())),
                Constant::String(s) => Some(EggExpr::String(s.clone())),
                Constant::BitVec(i, j) => Some(EggExpr::BitVec(i.clone(), (*j).into())),
                Constant::Real(d) => {
                    let (numer, denom) = d.clone().into_numer_denom();
                    if numer.to_i64().is_some() && denom.to_i64().is_some() {
                        Some(EggExpr::Real((numer, denom)))
                    } else {
                        Some(EggExpr::Call(
                            "RatConst".to_owned(),
                            vec![bigrat_expr(&numer, &denom)],
                        ))
                    }
                }
            },
            Term::Var(name, sort) => {
                if let Some(argument) = subs.get(name) {
                    Some(argument.0.clone())
                } else {
                    let sort =
                        to_raw_egg(sort, subs, func_cache, var_map, collect_functions_shape)?;
                    Some(EggExpr::Var(hash_var_name(var_map, name), Box::new(sort)))
                }
            }
            Term::App(head, args) => {
                let func_name = head.to_string();
                register_function_call(
                    func_cache,
                    &func_name,
                    false,
                    args.len(),
                    application_result_sort(head),
                );
                if collect_functions_shape {
                    func_cache
                        .shapes
                        .entry(func_name.clone())
                        .and_modify(|v| {
                            v.insert(term_rc.clone());
                        })
                        .or_insert({
                            let mut v = IndexSet::new();
                            v.insert(term_rc.clone());
                            v
                        });
                }

                if args.is_empty() {
                    return to_egg_expr(head, subs, func_cache, var_map, collect_functions_shape);
                }
                let args =
                    build_args_list(args.clone().iter().map(|x| {
                        to_egg_expr(x, subs, func_cache, var_map, collect_functions_shape)
                    }))?;

                Some(EggExpr::Call(format!("@{}", func_name), vec![args]))
            }
            Term::Op(Operator::RareList, args) => {
                let args =
                    build_args_list(args.clone().iter().map(|x| {
                        to_egg_expr(x, subs, func_cache, var_map, collect_functions_shape)
                    }))?;

                Some(args)
            }
            Term::Op(head, args) => {
                if args.is_empty() {
                    if head == &Operator::True || head == &Operator::False {
                        return Some(EggExpr::Bool(head == &Operator::True));
                    }
                    return Some(EggExpr::Op(head.to_string()));
                }

                register_function_call(func_cache, &head.to_string(), true, args.len(), None);
                let arg_exprs = args
                    .iter()
                    .map(|x| to_egg_expr(x, subs, func_cache, var_map, collect_functions_shape))
                    .collect::<Option<Vec<_>>>()?;
                let args_list = build_args_list(arg_exprs.iter().cloned().map(Some))?;

                let op_with_at = format!("@{}", head);
                if singleton_operators(*head).is_some() {
                    func_cache
                        .assoc_calls
                        .entry(op_with_at.clone())
                        .or_default()
                        .insert(args_list.clone());
                    Some(EggExpr::Call(op_with_at, vec![args_list]))
                } else {
                    Some(EggExpr::Call(format!("@{0}", head), vec![args_list]))
                }
            }
            Term::Binder(binder, bindings, body) => {
                // map binder enum -> ctor name (now arity = 1)
                let ctor = match binder {
                    Binder::Forall => "Forall",
                    Binder::Exists => "Exists",
                    Binder::Lambda => "Lambda",
                    Binder::Choice => "Choice",
                }
                .to_owned();

                // encode the bound variable list
                let vars_list = build_args_list(bindings.0.iter().map(|(name, sort)| {
                    let sort =
                        to_egg_expr(sort, subs, func_cache, var_map, collect_functions_shape)?;
                    Some(EggExpr::Var(hash_var_name(var_map, name), Box::new(sort)))
                }))?;

                // encode the body
                let body_e = to_egg_expr(body, subs, func_cache, var_map, collect_functions_shape)?;

                // single Term parameter: Args(vars_list, body_e)
                let packed = EggExpr::Args(Box::new(vars_list), Box::new(body_e));

                Some(EggExpr::Call(ctor, vec![packed]))
            }
            Term::Sort(sort) => {
                // Encode a Sort as a Term value (to be wrapped by the "Sort" ctor).
                fn sort_to_egg(
                    s: &Sort,
                    subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
                    func_cache: &mut EggFunctions,
                    var_map: &mut HashMap<String, u64>,
                    collect_shapes: bool,
                ) -> Option<EggExpr> {
                    match s {
                        Sort::Var(name) => Some(EggExpr::Var(
                            hash_var_name(var_map, name),
                            Box::new(EggExpr::Const("Type".to_owned())),
                        )),
                        Sort::Bool => Some(EggExpr::Const("Bool".to_owned())),
                        Sort::Int => Some(EggExpr::Const("Int".to_owned())),
                        Sort::Real => Some(EggExpr::Const("Real".to_owned())),
                        Sort::String => Some(EggExpr::Const("String".to_owned())),
                        Sort::RegLan => Some(EggExpr::Const("RegLan".to_owned())),
                        Sort::RareList(inner) => {
                            let tag = EggExpr::Const("RareList".to_owned());
                            let inner =
                                to_egg_expr(inner, subs, func_cache, var_map, collect_shapes)?;
                            build_args_list(vec![Some(tag), Some(inner)])
                        }
                        Sort::Type => Some(EggExpr::Const("Type".to_owned())),

                        Sort::BitVec(w) => {
                            let tag = EggExpr::Const("BitVec".to_owned());
                            let width = EggExpr::Num((*w).into());
                            build_args_list(vec![Some(tag), Some(width)])
                        }

                        Sort::Array(x, y) => {
                            let tag = EggExpr::Const("Array".to_owned());
                            let xs = to_egg_expr(x, subs, func_cache, var_map, collect_shapes)?;
                            let ys = to_egg_expr(y, subs, func_cache, var_map, collect_shapes)?;
                            build_args_list(vec![Some(tag), Some(xs), Some(ys)])
                        }

                        Sort::Function(parts) => {
                            let mut v = Vec::with_capacity(1 + parts.len());
                            v.push(Some(EggExpr::Const("Function".to_owned())));
                            for p in parts {
                                v.push(to_egg_expr(p, subs, func_cache, var_map, collect_shapes));
                            }
                            build_args_list(v)
                        }

                        Sort::Atom(name, args) => {
                            let mut v = Vec::with_capacity(1 + args.len());
                            v.push(Some(EggExpr::Const(name.to_string())));
                            for a in args {
                                v.push(to_egg_expr(a, subs, func_cache, var_map, collect_shapes));
                            }
                            Some(build_args_list(v)?)
                        }

                        Sort::Datatype(name, args) => {
                            let mut v = Vec::with_capacity(1 + args.len());
                            v.push(Some(EggExpr::Const(name.clone())));
                            for a in args {
                                v.push(to_egg_expr(a, subs, func_cache, var_map, collect_shapes));
                            }
                            Some(build_args_list(v)?)
                        }

                        Sort::ParamSort(vars, inner) => {
                            // list of vars
                            let mut vs = Vec::with_capacity(vars.len());
                            for v in vars {
                                vs.push(to_egg_expr(v, subs, func_cache, var_map, collect_shapes));
                            }
                            let vars_list = build_args_list(vs)?;

                            // body sort
                            let body =
                                to_egg_expr(inner, subs, func_cache, var_map, collect_shapes)?;

                            let tag = EggExpr::Const("ParamSort".to_owned());
                            build_args_list(vec![Some(tag), Some(vars_list), Some(body)])
                        }
                    }
                }

                let encoded =
                    sort_to_egg(sort, subs, func_cache, var_map, collect_functions_shape)?;
                // Wrap the encoded sort with the "Sort" constructor (as declared in create_headers)
                Some(EggExpr::Call("Sort".to_owned(), vec![encoded]))
            }
            Term::Let(bindings, body) => {
                // Build list of variable *names* (ignore bound values here)
                let vars_list = build_args_list(bindings.0.iter().map(|(name, sort)| {
                    let sort =
                        to_egg_expr(sort, subs, func_cache, var_map, collect_functions_shape)?;
                    Some(EggExpr::Var(hash_var_name(var_map, name), Box::new(sort)))
                }))?;

                // Translate the let-body
                let body_e = to_egg_expr(body, subs, func_cache, var_map, collect_functions_shape)?;

                // Make a single-argument constructor call for the Lambda binder:
                //   Lambda( Args(vars_list, body_e) )
                let lambda_e = EggExpr::Call(
                    "Lambda".to_owned(),
                    vec![EggExpr::Args(Box::new(vars_list), Box::new(body_e))],
                );

                // Now apply the lambda to each bound value using nested `App`:
                //   App(App(... App(lambda_e, v1), v2), ... vn)
                let mut applied = lambda_e;
                for (_name, val_term) in &bindings.0 {
                    let val_e =
                        to_egg_expr(val_term, subs, func_cache, var_map, collect_functions_shape)?;
                    applied = EggExpr::Call("App".to_owned(), vec![applied, val_e]);
                }

                Some(applied)
            }

            Term::ParamOp { op, op_args, args } => {
                // Register the symbol; we treat param-ops as operators.
                // Arity here is "parameters + arguments" because we flatten them below.
                register_function_call(
                    func_cache,
                    &op.to_string(),
                    true,
                    op_args.len() + args.len(),
                    None,
                );

                // Encode parameters (indexed or qualified) *first*,
                // then the regular arguments, all in a single Args list.
                let mut flat = Vec::with_capacity(op_args.len() + args.len());

                for p in op_args {
                    flat.push(to_egg_expr(
                        p,
                        subs,
                        func_cache,
                        var_map,
                        collect_functions_shape,
                    ));
                }
                for a in args {
                    flat.push(to_egg_expr(
                        a,
                        subs,
                        func_cache,
                        var_map,
                        collect_functions_shape,
                    ));
                }

                let packed = build_args_list(flat);

                // Call as @<param-op> with the single packed argument,
                // consistent with how Op/App are encoded elsewhere.
                Some(EggExpr::Call(format!("@{}", op), vec![packed?]))
            }
            // The RARE encoding does not currently model SMT-LIB datatype match expressions.
            // Reject them conservatively so the enclosing proof step remains a hole.
            Term::Match(_, _) => None,
        }
    }

    to_raw_egg(term_rc, subs, func_cache, var_map, collect_functions_shape).map(|x| {
        if let EggExpr::Literal(name) = &x {
            if let Some(argument) = subs.get(&name) {
                if argument.1 != AttributeParameters::List {
                    return encapluse(x);
                } else {
                    return x;
                }
            }
        };

        encapluse(x)
    })
}

fn translate_term(
    term: &Rc<Term>,
    subs: &IndexMap<&String, (EggExpr, AttributeParameters)>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
    collect_functions_shape: bool,
    context: &str,
) -> Result<EggExpr, String> {
    to_egg_expr(term, subs, func_cache, var_map, collect_functions_shape)
        .ok_or_else(|| format!("cannot translate term '{term}' while {context}"))
}

fn construct_premises(
    pool: &mut dyn TermPool,
    premise_clauses: &[&[Rc<Term>]],
    var_map: &mut HashMap<String, u64>,
    func_cache: &mut EggFunctions,
) -> Result<EggLanguage, String> {
    let mut grounds_terms = IndexSet::new();

    for premise_clause in premise_clauses {
        let clause: Option<Rc<Term>> = clauses_to_or(pool, premise_clause);
        if let Some(clause) = clause {
            let expr = get_equational_terms(&clause);
            if let Some((Operator::Equals, lhs, rhs)) = expr {
                grounds_terms.insert(EggStatement::Union(
                    Box::new(translate_term(
                        lhs,
                        &IndexMap::new(),
                        func_cache,
                        var_map,
                        false,
                        "translating a proof premise",
                    )?),
                    Box::new(translate_term(
                        rhs,
                        &IndexMap::new(),
                        func_cache,
                        var_map,
                        false,
                        "translating a proof premise",
                    )?),
                ));
            }

            if let Some(ground) = create_avaliable_premise(
                &clause,
                func_cache,
                var_map,
                false,
                "translating a proof premise",
            )? {
                grounds_terms.insert(ground);
            }
        }
    }

    Ok(grounds_terms.into_iter().collect())
}

fn construct_rules(
    database: &[RuleDefinition],
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
) -> Result<IndexSet<EggStatement>, String> {
    let mut rules = IndexSet::new();
    for definition in database {
        let mut premises = vec![];

        let subs = definition
            .arguments
            .iter()
            .map(|arg| {
                (
                    arg,
                    (
                        EggExpr::Literal(arg.clone()),
                        definition
                            .parameters
                            .get(arg)
                            .map_or(AttributeParameters::None, |x| x.attribute),
                    ),
                )
            })
            .collect::<IndexMap<_, _>>();

        let mut premise_available_args = IndexSet::new();

        let Some((Operator::Equals, conclusion_lhs, conclusion_rhs)) =
            get_equational_terms(&definition.conclusion)
        else {
            return Err(format!(
                "RARE rule '{}' must have a binary equality as its conclusion",
                definition.name
            ));
        };
        premise_available_args.extend(collect_vars(conclusion_lhs, false).into_keys());

        let context = format!("translating RARE rule '{}'", definition.name);

        for premise in &definition.premises {
            let Some((op @ (Operator::Equals | Operator::Distinct), lhs, rhs)) =
                get_equational_terms(premise)
            else {
                return Err(format!(
                    "RARE rule '{}' has a premise that is not a binary equality or disequality: {}",
                    definition.name, premise
                ));
            };
            match op {
                Operator::Equals => {
                    if let Some(lhs) =
                        create_avaliable_premise(lhs, func_cache, var_map, true, &context)?
                    {
                        rules.insert(lhs);
                    }

                    let lhs = Box::new(translate_term(
                        lhs,
                        &subs,
                        func_cache,
                        var_map,
                        definition.is_elaborated,
                        &context,
                    )?);

                    if let Some(rhs) =
                        create_avaliable_premise(rhs, func_cache, var_map, true, &context)?
                    {
                        rules.insert(rhs);
                    }
                    let rhs = Box::new(translate_term(
                        rhs,
                        &subs,
                        func_cache,
                        var_map,
                        definition.is_elaborated,
                        &context,
                    )?);

                    premises.push(EggExpr::Equal(lhs, rhs));
                }

                Operator::Distinct => {
                    if let Some(lhs) =
                        create_avaliable_premise(lhs, func_cache, var_map, true, &context)?
                    {
                        rules.insert(lhs);
                    }

                    let lhs = Box::new(translate_term(
                        lhs,
                        &subs,
                        func_cache,
                        var_map,
                        definition.is_elaborated,
                        &context,
                    )?);

                    if let Some(rhs) =
                        create_avaliable_premise(rhs, func_cache, var_map, true, &context)?
                    {
                        rules.insert(rhs);
                    }

                    let rhs = Box::new(translate_term(
                        rhs,
                        &subs,
                        func_cache,
                        var_map,
                        definition.is_elaborated,
                        &context,
                    )?);

                    premises.push(EggExpr::Distinct(lhs, rhs));
                }
                _ => {
                    return Err(format!(
                        "RARE rule '{}' has an unsupported premise operator: {}",
                        definition.name, premise
                    ))
                }
            }
        }

        let egg_equations: (Box<EggExpr>, Box<EggExpr>) = (
            Box::new(translate_term(
                conclusion_lhs,
                &subs,
                func_cache,
                var_map,
                definition.is_elaborated,
                &context,
            )?),
            Box::new(translate_term(
                conclusion_rhs,
                &subs,
                func_cache,
                var_map,
                definition.is_elaborated,
                &context,
            )?),
        );

        rules.insert(EggStatement::Rewrite(
            egg_equations.0.clone(),
            egg_equations.1.clone(),
            premises.clone(),
        ));
        if !premises.is_empty() {
            let lhs_available =
                EggExpr::Call("Avaliable".to_owned(), vec![(*egg_equations.0).clone()]);
            let mut availability_premises = premises.clone();
            availability_premises.push(lhs_available.clone());
            rules.insert(EggStatement::Rule {
                ruleset: None,
                body: availability_premises,
                head: vec![EggExpr::Call(
                    "Avaliable".to_owned(),
                    vec![(*egg_equations.1).clone()],
                )],
            });

            let mut seen_body = vec![lhs_available];
            let mut available_args = premise_available_args;
            for premise in &definition.premises {
                let Some((premise_op, premise_lhs, premise_rhs)) = get_equational_terms(premise)
                else {
                    return Err(format!(
                        "RARE rule '{}' has a malformed premise: {}",
                        definition.name, premise
                    ));
                };
                seen_body.push(match premise_op {
                    Operator::Equals => EggExpr::Equal(
                        Box::new(translate_term(
                            premise_lhs,
                            &subs,
                            func_cache,
                            var_map,
                            definition.is_elaborated,
                            &context,
                        )?),
                        Box::new(translate_term(
                            premise_rhs,
                            &subs,
                            func_cache,
                            var_map,
                            definition.is_elaborated,
                            &context,
                        )?),
                    ),
                    Operator::Distinct => EggExpr::Distinct(
                        Box::new(translate_term(
                            premise_lhs,
                            &subs,
                            func_cache,
                            var_map,
                            definition.is_elaborated,
                            &context,
                        )?),
                        Box::new(translate_term(
                            premise_rhs,
                            &subs,
                            func_cache,
                            var_map,
                            definition.is_elaborated,
                            &context,
                        )?),
                    ),
                    _ => {
                        return Err(format!(
                        "RARE rule '{}' has a premise that is not an equality or disequality: {}",
                        definition.name, premise
                    ))
                    }
                });

                let premise_args = collect_vars(premise_lhs, false)
                    .into_keys()
                    .chain(collect_vars(premise_rhs, false).into_keys())
                    .collect::<IndexSet<_>>();

                for arg in premise_args {
                    if available_args.insert(arg.clone()) {
                        rules.insert(EggStatement::Rule {
                            ruleset: None,
                            body: seen_body.clone(),
                            head: vec![EggExpr::Call(
                                "Avaliable".to_owned(),
                                vec![EggExpr::Literal(arg)],
                            )],
                        });
                    }
                }
            }
        }
    }
    Ok(rules)
}

const GOAL_LHS_NAME: &str = "goal_lhs";
const GOAL_RHS_NAME: &str = "goal_rhs";

fn set_goal(lhs_expr: EggExpr, rhs_expr: EggExpr) -> Vec<EggStatement> {
    vec![
        EggStatement::Let(GOAL_LHS_NAME.to_owned(), Box::new(lhs_expr)),
        EggStatement::Let(GOAL_RHS_NAME.to_owned(), Box::new(rhs_expr)),
        EggStatement::Premise(
            "Avaliable".to_owned(),
            Box::new(EggExpr::Literal(GOAL_LHS_NAME.to_owned())),
        ),
        EggStatement::Premise(
            "Avaliable".to_owned(),
            Box::new(EggExpr::Literal(GOAL_RHS_NAME.to_owned())),
        ),
    ]
}

fn available_subterm_premises(
    term: &Rc<Term>,
    func_cache: &mut EggFunctions,
    var_map: &mut HashMap<String, u64>,
) -> Result<Vec<EggStatement>, String> {
    let subs = IndexMap::new();
    let mut premises = Vec::new();
    for subterm in collect_subterms(term)
        .into_iter()
        .filter(|subterm| subterm != term && !subterm.is_var())
    {
        let expr = translate_term(
            &subterm,
            &subs,
            func_cache,
            var_map,
            false,
            "translating a goal subterm",
        )?;
        premises.push(EggStatement::Premise(
            "Avaliable".to_owned(),
            Box::new(expr),
        ));
    }
    Ok(premises)
}

fn goal_run_schedule(iterations: i16) -> Vec<EggStatement> {
    let mut schedule = vec![
        EggStatement::Run {
            ruleset: Some("list-ruleset".to_owned()),
            iterations,
        },
        EggStatement::Run {
            ruleset: Some("evaluation".to_owned()),
            iterations,
        },
    ];
    schedule.push(EggStatement::Run { ruleset: None, iterations });
    schedule
}

fn should_deduplicate_statement(statement: &EggStatement) -> bool {
    matches!(
        statement,
        EggStatement::Sort(..)
            | EggStatement::DataType(..)
            | EggStatement::Relation(..)
            | EggStatement::Function { .. }
            | EggStatement::Ruleset(..)
            | EggStatement::Constructor(..)
    )
}

fn should_deduplicate_command(command: &Command) -> bool {
    !matches!(command, Command::RunSchedule(..) | Command::Check(..))
}

fn compile_program(ast: Vec<EggStatement>) -> (Vec<Command>, String) {
    let mut seen = std::collections::HashSet::new();
    let ast: Vec<_> = ast
        .into_iter()
        .filter(|statement| {
            !should_deduplicate_statement(statement) || seen.insert(statement.clone())
        })
        .collect();

    let mut seen = std::collections::HashSet::new();
    let program: Vec<_> = lower_egg_language(ast)
        .into_iter()
        .filter(|command| !should_deduplicate_command(command) || seen.insert(command.to_string()))
        .collect();

    let code = render_program(&program);

    (program, code)
}

fn render_program(program: &[Command]) -> String {
    program
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n")
}

fn run_statements(egraph: &mut EGraph, ast: Vec<EggStatement>) -> (Result<(), String>, String) {
    let (program, code) = compile_program(ast);
    (run_program(egraph, program), code)
}

fn run_program(egraph: &mut EGraph, program: Vec<Command>) -> Result<(), String> {
    catch_unwind(AssertUnwindSafe(|| egraph.run_program(program)))
        .map_err(|panic| format!("egglog panic: {}", panic_message(panic)))
        .and_then(|result| result.map_err(|e| e.to_string()))
        .map(|_| ())
}

fn panic_message(panic: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = panic.downcast_ref::<&str>() {
        (*message).to_owned()
    } else if let Some(message) = panic.downcast_ref::<String>() {
        message.clone()
    } else {
        "unknown panic payload".to_owned()
    }
}

fn equal_terms() -> (EggExpr, EggExpr) {
    (
        EggExpr::Literal(GOAL_LHS_NAME.to_owned()),
        EggExpr::Literal(GOAL_RHS_NAME.to_owned()),
    )
}

fn check(
    egraph: &mut EGraph,
    lhs_expr: EggExpr,
    rhs_expr: EggExpr,
) -> (Result<(), String>, String) {
    run_statements(
        egraph,
        vec![EggStatement::Check(Box::new(EggExpr::Equal(
            Box::new(lhs_expr),
            Box::new(rhs_expr),
        )))],
    )
}

fn append_generated_code(code_str: &mut String, new_code: &str) {
    if new_code.is_empty() {
        return;
    }
    if !code_str.is_empty() {
        code_str.push('\n');
    }
    code_str.push_str(new_code);
}

fn run_and_record_statements(
    egraph: &mut EGraph,
    code_str: &mut String,
    ast: Vec<EggStatement>,
) -> Result<(), String> {
    let (result, code) = run_statements(egraph, ast);
    append_generated_code(code_str, &code);
    result
}

fn run_and_record_check(
    egraph: &mut EGraph,
    code_str: &mut String,
    lhs_expr: EggExpr,
    rhs_expr: EggExpr,
) -> Result<(), String> {
    let (result, code) = check(egraph, lhs_expr, rhs_expr);
    append_generated_code(code_str, &code);
    result
}

fn run_goal_schedule_round(
    egraph: &mut EGraph,
    code_str: &mut String,
    iterations: i16,
    deadline: Option<Instant>,
    goal_label: &str,
) -> Result<(), String> {
    for statement in goal_run_schedule(1) {
        for _ in 0..iterations {
            check_timeout(deadline, goal_label)?;
            run_and_record_statements(egraph, code_str, vec![statement.clone()])?;
            check_timeout(deadline, goal_label)?;
        }
    }
    Ok(())
}

#[derive(Clone)]
struct GoalFallbackPlan {
    label: &'static str,
    guard_setup: Vec<EggStatement>,
    guard: EggExpr,
    setup: Vec<EggStatement>,
    lhs: EggExpr,
    rhs: EggExpr,
}

impl GoalFallbackPlan {
    fn new(
        label: &'static str,
        guard_setup: Vec<EggStatement>,
        guard: EggExpr,
        (setup, lhs, rhs): (Vec<EggStatement>, EggExpr, EggExpr),
    ) -> Self {
        Self {
            label,
            guard_setup,
            guard,
            setup,
            lhs,
            rhs,
        }
    }
}

fn run_goal_fallback_attempt(
    egraph: &mut EGraph,
    code_str: &mut String,
    fallback: &GoalFallbackPlan,
    deadline: Option<Instant>,
    goal_label: &str,
) -> Result<(), String> {
    for statement in &fallback.guard_setup {
        check_timeout(deadline, goal_label)?;
        run_and_record_statements(egraph, code_str, vec![statement.clone()])?;
    }
    check_timeout(deadline, goal_label)?;
    run_and_record_check(
        egraph,
        code_str,
        fallback.guard.clone(),
        EggExpr::NativeBool(true),
    )?;
    for statement in &fallback.setup {
        check_timeout(deadline, goal_label)?;
        run_and_record_statements(egraph, code_str, vec![statement.clone()])?;
    }
    check_timeout(deadline, goal_label)?;
    let result = run_and_record_check(egraph, code_str, fallback.lhs.clone(), fallback.rhs.clone());
    check_timeout(deadline, goal_label)?;
    result
}

fn run_goal_fallback_attempts(
    egraph: &mut EGraph,
    code_str: &mut String,
    fallback_plans: &[GoalFallbackPlan],
    deadline: Option<Instant>,
    goal_label: &str,
) -> Result<(), String> {
    let mut errors = Vec::with_capacity(fallback_plans.len());

    for fallback in fallback_plans {
        match run_goal_fallback_attempt(egraph, code_str, fallback, deadline, goal_label) {
            Ok(()) => return Ok(()),
            Err(error) => errors.push(format!("{} fallback failed:\n{}", fallback.label, error)),
        }
    }

    Err(errors.join("\n"))
}

fn check_goal_against_current_state(
    egraph: &mut EGraph,
    code_str: &mut String,
    lhs_expr: &EggExpr,
    rhs_expr: &EggExpr,
    fallback_plans: &[GoalFallbackPlan],
    deadline: Option<Instant>,
    goal_label: &str,
) -> Result<(), String> {
    check_timeout(deadline, goal_label)?;
    match run_and_record_check(egraph, code_str, lhs_expr.clone(), rhs_expr.clone()) {
        Ok(()) => Ok(()),
        Err(raw_error) => {
            if fallback_plans.is_empty() {
                return Err(raw_error);
            }

            run_goal_fallback_attempts(egraph, code_str, fallback_plans, deadline, goal_label)
                .map_err(|fallback_error| format!("{raw_error}\n{fallback_error}"))
        }
    }
}

#[derive(Clone)]
struct GoalCheckTarget {
    goal_label: String,
    lhs_expr: EggExpr,
    rhs_expr: EggExpr,
    fallback_plans: Vec<GoalFallbackPlan>,
}

fn check_goal_with_retry_rounds(
    egraph: &mut EGraph,
    code_str: &mut String,
    goal: &GoalCheckTarget,
    options: RunEgglogOptions,
    deadline: Option<Instant>,
) -> Result<(), String> {
    let mut last_error = None;

    let mut round = 0;
    loop {
        check_timeout(deadline, &goal.goal_label)?;
        if !options.continuous_saturation && round >= options.normalized_max_goal_schedule_rounds()
        {
            break;
        }

        round += 1;
        let iterations = if options.continuous_saturation {
            1
        } else {
            round as i16
        };
        run_goal_schedule_round(egraph, code_str, iterations, deadline, &goal.goal_label)?;
        check_timeout(deadline, &goal.goal_label)?;

        let check_result = check_goal_against_current_state(
            egraph,
            code_str,
            &goal.lhs_expr,
            &goal.rhs_expr,
            &goal.fallback_plans,
            deadline,
            &goal.goal_label,
        );
        check_timeout(deadline, &goal.goal_label)?;

        match check_result {
            Ok(()) => {
                return Ok(());
            }
            Err(error) => last_error = Some(error),
        }
    }

    Err(format!(
        "egglog check for {} failed:\n{}",
        goal.goal_label,
        last_error.unwrap_or_else(|| "goal equality check failed".to_owned())
    ))
}

fn check_timeout(deadline: Option<Instant>, goal_label: &str) -> Result<(), String> {
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        Err(format!("egglog check for {goal_label} timed out"))
    } else {
        Ok(())
    }
}

fn declare_functions(functions: &EggFunctions) -> Vec<EggStatement> {
    let mut decls = Vec::new();

    for func in functions.names.keys() {
        decls.push(EggStatement::Constructor(
            format!("@{}", func),
            vec![ConstType::ConstrType("Term".to_owned())],
            ConstType::ConstrType("Term".to_owned()),
        ));
        decls.push(EggStatement::Rule {
            ruleset: None,
            body: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Call(
                    format!("@{}", func),
                    vec![EggExpr::Literal("args".to_owned())],
                )],
            )],
            head: vec![EggExpr::Call(
                "Avaliable".to_owned(),
                vec![EggExpr::Literal("args".to_owned())],
            )],
        });
    }

    // Note: @+ computation rule is now in arith_poly_norm.egglog

    decls
}

fn get_fallback_plans(enable_arith_poly: bool) -> Vec<GoalFallbackPlan> {
    if !enable_arith_poly {
        return Vec::new();
    }

    let (goal_lhs, goal_rhs) = equal_terms();
    vec![
        GoalFallbackPlan::new(
            "arithPolyNfOf",
            vec![
                EggStatement::Call(Box::new(EggExpr::Call(
                    "arithGoalPolyNfOf-demand".to_owned(),
                    vec![goal_lhs.clone()],
                ))),
                EggStatement::Run {
                    ruleset: Some("arith_poly_guard".to_owned()),
                    iterations: 1,
                },
            ],
            arith_poly_norm::poly_goal_guard_term(goal_lhs.clone()),
            arith_poly_norm::poly_goal_check_terms(goal_lhs.clone(), goal_rhs.clone()),
        ),
        GoalFallbackPlan::new(
            "arithRelBoolKeyOf",
            vec![
                EggStatement::Call(Box::new(EggExpr::Call(
                    "arithRelBoolKeyOf-demand".to_owned(),
                    vec![goal_lhs.clone()],
                ))),
                EggStatement::Run {
                    ruleset: Some("arith_poly_guard".to_owned()),
                    iterations: 1,
                },
            ],
            arith_poly_norm_rel::relation_bool_goal_guard_term(goal_lhs.clone()),
            arith_poly_norm_rel::relation_bool_goal_check_terms(goal_lhs, goal_rhs),
        ),
    ]
}

fn goal_log_label(node: &Rc<ProofNode>, conclusion: &Rc<Term>) -> String {
    format!("{}: {:?}", node.id(), conclusion)
}

fn register_ineq_primitive(egraph: &mut EGraph) {
    egraph.add_primitive(CustomPrimitive {
        name: Symbol::from("ineq"),
        input: vec![
            Arc::new(EqSort { name: Symbol::from("Term") }),
            Arc::new(EqSort { name: Symbol::from("Term") }),
        ],
        output: Arc::new(BoolSort),
        f: |x| Some(Value::from(x[0] != x[1])),
    });
}

fn prepare_database(database: &Rules) -> Result<RareDatabaseBaseline, String> {
    let mut functions = EggFunctions::default();
    let mut var_map = HashMap::new();
    let definitions: Vec<_> = database.rules.values().cloned().collect();
    let rules = construct_rules(&definitions, &mut functions, &mut var_map)?;
    let has_distinct = functions.names.contains_key("distinct");

    // Logic operators and all database-derived rules belong to the immutable
    // baseline. Every proof step starts by cloning this fully initialized EGraph.
    declare_logic_operators(&mut functions);
    let mut declarations = declare_functions(&functions);
    declare_database_eliminations(&mut declarations, &functions);

    let mut ast = create_headers();
    ast.extend(declarations);
    ast.extend(rules);
    let (program, code) = compile_program(ast);
    let baseline_commands = program
        .iter()
        .filter(|command| should_deduplicate_command(command))
        .map(ToString::to_string)
        .collect();

    let mut egraph = EGraph::default();
    evaluation::register_evaluation_primitives(&mut egraph);
    register_ineq_primitive(&mut egraph);
    run_program(&mut egraph, program)?;

    Ok(RareDatabaseBaseline {
        egraph,
        functions,
        var_map,
        code,
        has_distinct,
        commands: baseline_commands,
    })
}

fn prepare_database_safely(database: &Rules) -> Result<RareDatabaseBaseline, String> {
    catch_unwind(AssertUnwindSafe(|| prepare_database(database))).map_err(|panic| {
        format!(
            "preparing the RARE database panicked: {}",
            panic_message(panic)
        )
    })?
}

fn run_egglog_with_premises_inner(
    pool: &mut dyn TermPool,
    conclusion: Rc<Term>,
    premise_clauses: &[&[Rc<Term>]],
    goal_label: String,
    context: &RareCheckContext<'_>,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
    let deadline = match options.timeout {
        Some(timeout) => match Instant::now().checked_add(timeout) {
            Some(deadline) => Some(deadline),
            None => {
                return (
                    Err(format!(
                        "egglog check for {goal_label} has an invalid timeout"
                    )),
                    String::new(),
                )
            }
        },
        None => None,
    };
    if let Err(error) = check_timeout(deadline, &goal_label) {
        return (Err(error), String::new());
    }

    let baseline = match context.baseline() {
        Ok(baseline) => baseline,
        Err(error) => return (Err(error), String::new()),
    };
    let mut code_str = baseline.code.clone();
    if let Err(error) = check_timeout(deadline, &goal_label) {
        return (Err(error), code_str);
    }

    let mut egraph = baseline.egraph.clone();
    let mut var_map = baseline.var_map.clone();

    // Functions coming from the premises and the goal are collected separately
    // from the ones coming from the RARE rule database, so that the arith poly
    // norm machinery is only enabled when the proof step itself involves
    // arithmetic, and not just because some rule in the database does.
    let mut goal_functions = EggFunctions::default();
    let premises =
        match construct_premises(pool, premise_clauses, &mut var_map, &mut goal_functions) {
            Ok(premises) => premises,
            Err(error) => return (Err(error), code_str),
        };

    let Some((Operator::Equals, lhs, rhs)) = get_equational_terms(&conclusion) else {
        return (
            Err(format!(
                "egglog check for {goal_label} requires a binary equality goal"
            )),
            code_str,
        );
    };

    let goal_lhs_expr = match translate_term(
        lhs,
        &IndexMap::new(),
        &mut goal_functions,
        &mut var_map,
        false,
        "translating the goal's left-hand side",
    ) {
        Ok(expr) => expr,
        Err(error) => return (Err(error), code_str),
    };
    let goal_rhs_expr = match translate_term(
        rhs,
        &IndexMap::new(),
        &mut goal_functions,
        &mut var_map,
        false,
        "translating the goal's right-hand side",
    ) {
        Ok(expr) => expr,
        Err(error) => return (Err(error), code_str),
    };

    let mut goals_ast = set_goal(goal_lhs_expr, goal_rhs_expr);
    let lhs_subterms = match available_subterm_premises(lhs, &mut goal_functions, &mut var_map) {
        Ok(premises) => premises,
        Err(error) => return (Err(error), code_str),
    };
    goals_ast.extend(lhs_subterms);
    let rhs_subterms = match available_subterm_premises(rhs, &mut goal_functions, &mut var_map) {
        Ok(premises) => premises,
        Err(error) => return (Err(error), code_str),
    };
    goals_ast.extend(rhs_subterms);

    let (raw_lhs, raw_rhs) = equal_terms();
    let mut goal = GoalCheckTarget {
        goal_label,
        lhs_expr: raw_lhs,
        rhs_expr: raw_rhs,
        fallback_plans: Vec::new(),
    };

    let enable_arith_poly = arith_poly_norm::uses_arith_machinery(&goal_functions);
    goal.fallback_plans = get_fallback_plans(enable_arith_poly);

    // Only constructors absent from the baseline need declaring in the clone.
    // Goal-specific rules still receive the complete local function/call set.
    let mut new_functions = goal_functions.clone();
    new_functions
        .names
        .retain(|name, _| !baseline.functions.names.contains_key(name));
    let mut declarations = declare_functions(&new_functions);
    declare_goal_eliminations(
        &mut declarations,
        &goal_functions,
        enable_arith_poly,
        baseline.has_distinct,
    );
    if enable_arith_poly {
        declarations.extend(arith_poly_norm::declare_opaque_arith_poly_rules(
            &goal_functions,
        ));
    }

    let mut ast = declarations;
    ast.extend(premises);
    ast.extend(goals_ast);

    let (mut egglog, _) = compile_program(ast);
    egglog.retain(|command| {
        !should_deduplicate_command(command) || !baseline.commands.contains(&command.to_string())
    });
    let local_code = render_program(&egglog);
    append_generated_code(&mut code_str, &local_code);
    if enable_arith_poly {
        arith_poly_norm::register_arith_poly_primitives(&mut egraph);
    }

    let result = check_timeout(deadline, &goal.goal_label)
        .and_then(|_| run_program(&mut egraph, egglog))
        .and_then(|_| check_timeout(deadline, &goal.goal_label))
        .and_then(|_| {
            check_goal_with_retry_rounds(&mut egraph, &mut code_str, &goal, options, deadline)
        });

    (result.map(|_| egraph), code_str)
}

fn run_egglog_with_premises(
    pool: &mut dyn TermPool,
    conclusion: Rc<Term>,
    premise_clauses: &[&[Rc<Term>]],
    goal_label: String,
    context: &RareCheckContext<'_>,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
    match catch_unwind(AssertUnwindSafe(|| {
        run_egglog_with_premises_inner(
            pool,
            conclusion,
            premise_clauses,
            goal_label,
            context,
            options,
        )
    })) {
        Ok(result) => result,
        Err(panic) => (
            Err(format!(
                "RARE/egglog checking panicked: {}",
                panic_message(panic)
            )),
            String::new(),
        ),
    }
}

pub fn check_hole_rewrite_with_context(
    pool: &mut dyn TermPool,
    step_id: &str,
    conclusion: Rc<Term>,
    premise_clauses: &[&[Rc<Term>]],
    context: &RareCheckContext<'_>,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
    let goal_label = format!("{}: {:?}", step_id, conclusion);
    run_egglog_with_premises(
        pool,
        conclusion,
        premise_clauses,
        goal_label,
        context,
        options,
    )
}

pub fn check_hole_rewrite(
    pool: &mut dyn TermPool,
    step_id: &str,
    conclusion: Rc<Term>,
    premise_clauses: &[&[Rc<Term>]],
    database: &Rules,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
    let context = RareCheckContext::new(database);
    check_hole_rewrite_with_context(
        pool,
        step_id,
        conclusion,
        premise_clauses,
        &context,
        options,
    )
}

pub fn run_egglog(
    pool: &mut dyn TermPool,
    node: (Rc<Term>, &Rc<ProofNode>),
    database: &Rules,
    options: RunEgglogOptions,
) -> (Result<EGraph, String>, String) {
    let (conclusion, proof_node) = node;
    let assumptions = proof_node.get_assumptions();
    let premise_clauses = assumptions
        .iter()
        .map(|premise| premise.clause())
        .collect::<Vec<_>>();
    let goal_label = goal_log_label(proof_node, &conclusion);
    let context = RareCheckContext::new(database);
    run_egglog_with_premises(
        pool,
        conclusion,
        &premise_clauses,
        goal_label,
        &context,
        options,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{rare_rules::RareStatements, PrimitivePool};

    fn evaluation_goal(pool: &mut PrimitivePool) -> Rc<Term> {
        let truth = pool.add(Term::Op(Operator::True, vec![]));
        let falsity = pool.add(Term::Op(Operator::False, vec![]));
        let not_truth = pool.add(Term::Op(Operator::Not, vec![truth]));
        pool.add(Term::Op(Operator::Equals, vec![not_truth, falsity]))
    }

    #[test]
    fn rare_database_baseline_is_initialized_once_and_reused() {
        let mut pool = PrimitivePool::new();
        let goal = evaluation_goal(&mut pool);
        let database = RareStatements::default();
        let context = RareCheckContext::new(&database);
        assert!(!context.is_prepared());

        let (first, _) = check_hole_rewrite_with_context(
            &mut pool,
            "first",
            goal.clone(),
            &[],
            &context,
            RunEgglogOptions::default(),
        );
        assert!(first.is_ok(), "first check failed: {:?}", first.err());
        assert!(context.is_prepared());

        let baseline = context
            .baseline
            .get()
            .expect("baseline should have been initialized") as *const _;
        let (second, _) = check_hole_rewrite_with_context(
            &mut pool,
            "second",
            goal,
            &[],
            &context,
            RunEgglogOptions::default(),
        );
        assert!(second.is_ok(), "second check failed: {:?}", second.err());
        assert_eq!(
            baseline,
            context
                .baseline
                .get()
                .expect("baseline should remain initialized") as *const _
        );
    }

    #[test]
    fn malformed_programmatic_rare_rule_returns_an_error() {
        let mut pool = PrimitivePool::new();
        let truth = pool.add(Term::Op(Operator::True, vec![]));
        let goal = pool.add(Term::Op(
            Operator::Equals,
            vec![truth.clone(), truth.clone()],
        ));
        let malformed = RuleDefinition {
            name: "malformed".to_owned(),
            parameters: IndexMap::new(),
            arguments: vec![],
            premises: vec![],
            conclusion: truth,
            is_elaborated: false,
        };
        let database = RareStatements {
            rules: [(malformed.name.clone(), malformed)].into_iter().collect(),
        };
        let context = RareCheckContext::new(&database);

        let (result, _) = check_hole_rewrite_with_context(
            &mut pool,
            "malformed",
            goal,
            &[],
            &context,
            RunEgglogOptions::default(),
        );
        let error = match result {
            Ok(_) => panic!("malformed database must not be accepted"),
            Err(error) => error,
        };
        assert!(
            error.contains("binary equality"),
            "unexpected error: {error}"
        );
    }
}
