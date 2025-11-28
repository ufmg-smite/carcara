use super::*;

const WHITE_SPACE: &str = " ";

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
    Apply(Term, SubProofs),
    Change(Term),
    Refine(Term, SubProofs),
    Have(String, Term, Vec<ProofStep>), //TODO: change Vec<ProofStep> for Proof
    Admit,
    Reflexivity,
    Try(Box<ProofStep>),
    Rewrite(bool, Option<String>, Term, Vec<Term>, SubProofs),
    Symmetry,
    Simplify(Vec<String>),
    Set(String, Term),
    Varmap(String, Vec<Term>),
    Why3,
    Eval(Term),
}

macro_rules! apply {
    ($id:ident) => {
        ProofStep::Apply(Term::TermId(stringify!($id).into()), SubProofs(None))
    };
    ($t:expr) => {
        ProofStep::Apply($t, SubProofs(None))
    };
    ($t:expr, { $($arg:expr),+ $(,)?  }) => {
        ProofStep::Apply(terms![$t, ..vec![$($arg),+]], SubProofs(None))
    };
    ($id:expr, { $($arg:expr),* $(,)?  }, [ $($sp:expr),* $(,)?  ]) => {
        ProofStep::Apply(terms![Term::TermId(stringify!($id).into()), ..vec![$($arg),*]], SubProofs(Some(
            vec![
                $( proof!($sp) ),*
            ]
        )))
    };
}

pub(crate) use apply;

#[derive(Debug, Clone, PartialEq)]
pub struct SubProofs(pub Option<Vec<Proof>>);

impl fmt::Display for SubProofs {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let SubProofs(Some(ps)) = self {
            for p in ps {
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
                    ids.clone()
                        .join(WHITE_SPACE)
                )
            }
            ProofStep::Have(id, term, proof) => {
                let proof_steps_fmt: String = proof.iter().map(|p| format!("{}", p)).collect();
                let have_fmt = format!("have {} : {} {{ {} }};\n", id, term, proof_steps_fmt);
                write!(f, "{}", have_fmt)
            }
            ProofStep::Apply(t, subproofs) => {
                write!(f, "apply {}", t)?;

                if let SubProofs(Some(sp)) = subproofs {
                    write!(f, " {}", SubProofs(Some(sp.clone())))?;
                }

                write!(f, ";")
            }
            ProofStep::Change(t) => write!(f, "change {}", t),
            ProofStep::Refine(t, subproofs) => {
                write!(
                    f,
                    "refine {} {};",
                    t,
                    subproofs
                )
            }
            ProofStep::Admit => write!(f, "admit;"),
            ProofStep::Reflexivity => write!(f, "simplify; reflexivity;"),
            ProofStep::Try(t) => write!(f, "try {}", t),
            ProofStep::Rewrite(_flag, pattern, hyp, args, subproofs) => {
                let pattern = pattern.as_ref().map_or("", |p| p.as_str());
                let args = args
                    .iter()
                    .map(|i| format!("{}", i))
                    .collect::<Vec<_>>()
                    .join(WHITE_SPACE);

                write!(f, "rewrite {} ({} {})", pattern, hyp, args)?;
                if let SubProofs(Some(sp)) = subproofs {
                    write!(f, " {}", SubProofs(Some(sp.clone())))?;
                };
                write!(f, ";")
            }
            ProofStep::Symmetry => write!(f, "symmetry;"),
            ProofStep::Simplify(s) => {
                for term in s {
                    write!(f, "simplify {};", term)?;
                }
                Ok(())
            }
            ProofStep::Set(name, def) => write!(f, "set {} ≔ {};", name, def),
            ProofStep::Varmap(name, _list) => write!(f, "set {} ≔;", name),
            ProofStep::Why3 => write!(f, "why3;"),
            ProofStep::Eval(t) => write!(f, "eval {};", t),
        }
    }
}

#[inline]
pub fn admit() -> Vec<ProofStep> {
    vec![ProofStep::Admit]
}
