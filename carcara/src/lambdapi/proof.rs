use super::*;

const WHITE_SPACE: &'static str = " ";

#[derive(Debug, Clone, PartialEq)]
pub struct Proof(pub Vec<ProofStep>);

#[macro_export]
macro_rules! proof {
    ($($sp:expr),+ $(,)? ) => {
        Proof(vec![ $( $sp),+ ])
    };
}

pub(crate) use proof;

impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Proof(steps) => {
                steps.iter().for_each(|s| write!(f, "{}", s).unwrap());
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ProofStep {
    Assume(Vec<String>),
    Apply(Term, Vec<Term>, SubProofs),
    Refine(Term, Vec<Term>, SubProofs),
    Have(String, Term, Vec<ProofStep>), //TODO: change Vec<ProofStep> for Proof
    Admit,
    Reflexivity,
    Try(Box<ProofStep>),
    Rewrite(Option<String>, Term, Vec<Term>),
    Symmetry,
}

macro_rules! apply {
    ($id:ident) => {
        ProofStep::Apply(Term::TermId(stringify!($id).into()), vec![], SubProofs(None))
    };
    ($t:expr) => {
        ProofStep::Apply($t, vec![], SubProofs(None))
    };
    ($id:expr, [ $($sp:expr),+ $(,)?  ]) => {
        ProofStep::Apply(Term::TermId(stringify!($id).into()), vec![], SubProofs(Some(
            vec![
                $( proof!($sp)),+
            ]
        )))
    };
}

pub(crate) use apply;

macro_rules! refine {
    ($id:ident) => {
        ProofStep::Refine(Term::TermId(stringify!($id).into()), vec![], SubProofs(None))
    };
    ($t:expr) => {
        ProofStep::Apply($t, vec![], SubProofs(None))
    };
    ($id:expr, [ $($sp:expr),+ $(,)?  ]) => {
        ProofStep::Refine(Term::TermId(stringify!($id).into()), vec![], SubProofs(Some(
            vec![
                $( proof!($sp)),+
            ]
        )))
    };
}

pub(crate) use refine;

macro_rules! r#try {
    ($t:expr) => {
        ProofStep::Try(Box::new($t))
    };
}

pub(crate) use r#try;

#[derive(Debug, Clone, PartialEq)]
pub struct SubProofs(pub Option<Vec<Proof>>);

impl fmt::Display for SubProofs {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let SubProofs(Some(ps)) = self {
            for p in ps.iter() {
                write!(f, "{{ {} }}", p)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for ProofStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ProofStep::Assume(ids) => {
                write!(
                    f,
                    "assume {};",
                    ids.iter()
                        .map(|e| format!("{}", e))
                        .collect::<Vec<_>>()
                        .join(WHITE_SPACE)
                )
            }
            ProofStep::Have(id, term, proof) => {
                let proof_steps_fmt: String = proof.iter().map(|p| format!("{}", p)).collect();
                let have_fmt = format!("have {} : {} {{ {} }};\n", id, term, proof_steps_fmt);
                write!(f, "{}", have_fmt)
            }
            ProofStep::Apply(t, args, subproofs) => {
                write!(f, "apply {}", t)?;

                if args.len() > 0 {
                    write!(
                        f,
                        " {}",
                        args.iter()
                            .map(|i| format!("{}", i))
                            .collect::<Vec<_>>()
                            .join(WHITE_SPACE)
                    )?;
                }

                if let SubProofs(Some(sp)) = subproofs {
                    write!(f, " {}", SubProofs(Some(sp.to_vec())))?;
                }

                write!(f, ";")
            }
            ProofStep::Refine(t, args, subproofs) => {
                write!(
                    f,
                    "refine {} {} {};",
                    t,
                    args.iter()
                        .map(|i| format!("{}", i))
                        .collect::<Vec<_>>()
                        .join(WHITE_SPACE),
                    subproofs
                )
            }
            ProofStep::Admit => write!(f, "admit;"),
            ProofStep::Reflexivity => write!(f, "simplify; reflexivity;"),
            ProofStep::Try(t) => write!(f, "try {}", t),
            ProofStep::Rewrite(pattern, hyp, args) => {
                let pattern = pattern.as_ref().map_or("", |p| p.as_str());
                let args = args
                    .iter()
                    .map(|i| format!("{}", i))
                    .collect::<Vec<_>>()
                    .join(WHITE_SPACE);
                write!(f, "rewrite {} ({} {});", pattern, hyp, args)
            }
            ProofStep::Symmetry => write!(f, "symmetry;"),
        }
    }
}

#[inline]
pub fn admit() -> Vec<ProofStep> {
    vec![ProofStep::Admit]
}
