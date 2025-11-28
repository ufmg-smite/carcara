/// Lambdapi tactics DSL embedded within Rust macros.

macro_rules! make_term {
    ( ($( $args:tt ) +) ) => { make_term![  $( $args) + ] };
    (_) => { Term::Underscore };
    (or $i:ident) => { Term::Alethe(LTerm::NOr($i)) };
    (and $i:ident) => { Term::Alethe(LTerm::NAnd($i)) };
    ($l:tt => $r:tt) => { Term::Alethe(LTerm::Implies(Box::new(make_term![$l]) ,  Box::new(make_term![$r]))) };
    ( $f:tt ( $( $args:tt ) + ) ) => { Term::Terms(vec![  make_term![$f], $( make_term![$args] ) , + ]) };
    ( @$( $exp:tt )+ ) => { $( $exp )+  };
    ($f:tt) => { Term::from($f) };
}

pub(crate) use make_term;

macro_rules! inline_lambdapi {
    ($($tokens:tt)+) => {
        {
            lambdapi_wrapper!(
                begin
                    $($tokens)+
                end;
            ).pop().unwrap()
        }
    }
}

pub(crate) use inline_lambdapi;

macro_rules! tactic {
    ($steps:ident, simplify; $($body:tt)*) => { $steps.push(ProofStep::Simplify(vec![])) ; tactic![ $steps, $( $body )* ] };
    ($steps:ident, why3; $($body:tt)*) => { $steps.push(ProofStep::Why3) ; tactic![ $steps, $( $body )* ] };
    ($steps:ident, symmetry; $($body:tt)*) => { $steps.push(ProofStep::Symmetry) ; tactic![ $steps, $( $body )* ] };
    ($steps:ident, reflexivity; $($body:tt)*) => { $steps.push(ProofStep::Reflexivity) ; tactic![ $steps, $( $body )* ] };
    ($steps:ident, eval $i:tt; $($body:tt)+) => {
        $steps.push(ProofStep::Eval(Term::from($i)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, eval @$e:expr; $($body:tt)+) => {
        $steps.push(ProofStep::Eval(make_term![$e]));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, refine $i:tt; $($body:tt)+) => {
        $steps.push(ProofStep::Refine(Term::from($i), SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, refine @$e:expr; $($body:tt)+) => {
        $steps.push(ProofStep::Refine(make_term![$e], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, apply $i:tt; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(Term::from($i), SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, apply @$e:expr; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(make_term![$e], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, apply $i:tt $arg:tt; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(terms![Term::from($i), ..vec![ make_term![$arg] ]], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, apply $i:tt  $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Apply(Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, apply $i:tt  $( ( $($args:tt) + ) ) * $( { $($subproof:tt) * } ) + ; $($body:tt)+) => {
        let mut sub_proofs: Vec<Proof> = Vec::new();

        $(
            {
                let sub_proof = lambdapi_wrapper!{ begin $( $subproof )* end; };
                sub_proofs.push(Proof(sub_proof));
            }
        )*;

        $steps.push(ProofStep::Apply(Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(Some(sub_proofs))));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, have $i:tt : ( $($goal:tt) + ) {  $( $body_have:tt )+  }  ; $($body:tt)*) => {
        let have_body: Vec<ProofStep> = lambdapi!{ $( $body_have )+ };
        $steps.push(ProofStep::Have(stringify!($i).to_string(), make_term![  $( $goal )+ ] ,have_body))  ; tactic![ $steps, $( $body )* ]
    };
    ($steps:ident, assume [$($id:tt)+] ; $($body:tt)*) => {
        let mut ids: Vec<String> = Vec::new();

        $(
            ids.push(stringify!($id).to_string());
        )+

        $steps.push(ProofStep::Assume(ids));
        tactic![ $steps, $(  $body )* ]
    };
    ($steps:ident, try [ $($id:tt)+ ] ; $($body:tt)*) => {
        let step = inline_lambdapi![ $( $id )+ ];

        $steps.push(ProofStep::Try(Box::new(step)));
        tactic![ $steps, $(  $body )* ]
    };
    ($steps:ident, rewrite [$($i:tt)+] $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Rewrite(None, $($i)+, vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, rewrite .$pattern:tt $i:tt  $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Rewrite(false, Some($pattern.to_string()), Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, rewrite $i:tt  $( ( $($args:tt) + ) ) * ; $($body:tt)+) => {
        $steps.push(ProofStep::Rewrite(false, None, Term::from($i), vec![ $( make_term![  $( $args )+ ] , )* ], SubProofs(None)));
        tactic![ $steps, $( $body )+ ]
    };
    ($steps:ident, $code:block ; $($body:tt)*) => {  $steps.append(&mut $code) ; tactic![ $steps, $(  $body )* ]  };
    ($steps:ident, inject($code:expr) ; $($body:tt)*) => {  $steps.append(&mut $code) ; tactic![ $steps, $(  $body )* ]  };
    ($steps:ident, admit; $($body:tt)*) => { $steps.push(ProofStep::Admit)  ; tactic![ $steps, $(  $body )* ]  };
    ($steps:ident, end;) => { };
}

pub(crate) use tactic;

macro_rules! lambdapi_wrapper {
    (begin $($body:tt)+) => { { let mut steps: Vec<ProofStep> = vec![];  tactic![ steps, $( $body )+ ] ; steps } };
}

pub(crate) use lambdapi_wrapper;

macro_rules! lambdapi {
    ($($body:tt)+) => { { lambdapi_wrapper!{ begin $($body)+ end; } } };
}

pub(crate) use lambdapi;