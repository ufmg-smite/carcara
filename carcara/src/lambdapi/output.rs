use itertools::Itertools;

use super::Command;
use std::collections::{HashMap};
use std::fmt;
use std::io;

use super::normalize_name;
use crate::lambdapi::printer::PrettyPrint;
use crate::lambdapi::printer::PrettyPrintAx;

use crate::ast::{ProofNode, Rc, StepNode};

impl<'a> fmt::Display for ProofFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.render_fmt(f)
    }
}

pub trait Render {
    fn render<W: io::Write>(&self, f: &mut io::BufWriter<W>) -> io::Result<()>;
}

/// Lambdapi files are formed of a list of commands.
pub struct ProofFile {
    pub requires: Vec<Command>,
    pub definitions: Vec<Command>,
    pub content: Vec<Command>,
    pub dependencies: DependenciesStepMap,
}

impl Render for ProofFile {
    fn render<W: io::Write>(&self, f: &mut io::BufWriter<W>) -> io::Result<()> {
        PrettyPrint::render(self, f)
    }
}

impl<'a> Default for ProofFile {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> ProofFile {
    pub fn new() -> ProofFile {
        Self {
            requires: Vec::new(),
            definitions: Vec::new(),
            content: Vec::new(),
            dependencies: DependenciesStepMap::new(),
        }
    }
}

pub struct AxiomsFile {
    pub requires: Vec<Command>,
    pub content: Vec<Command>,
}

impl<'a> Default for AxiomsFile {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> AxiomsFile {
    pub fn new() -> AxiomsFile {
        Self {
            requires: Vec::new(),
            content: Vec::new(),
        }
    }
}

impl Render for AxiomsFile {
    fn render<W: io::Write>(&self, f: &mut io::BufWriter<W>) -> io::Result<()> {
        self.render_ax(f)
    }
}

type StepId = String;

type DependenciesStepMap = HashMap<StepId, (usize, Vec<StepId>)>;

/// Compute separetly the dependencies betweem proof steps by iterating on the graph proof.
/// This method is intended to be used for the spliting of the proof.
/// The `:discharge` references in subproof are considered as a dependencies.
pub fn get_dependencies_map<'a>(node: Rc<ProofNode>) -> DependenciesStepMap {
    let mut deps_map = HashMap::new();
    let mut index_in_proof: usize = 0;

    node.traverse(|node| {
        match node.as_ref() {
            ProofNode::Assume { id, .. } => {
                deps_map.insert(normalize_name(id.as_str()), (index_in_proof, vec![]));
            }
            ProofNode::Step(StepNode { id, premises, .. }) => {
                deps_map.insert(
                    normalize_name(id.as_str()),
                    (
                        index_in_proof,
                        premises
                            .iter()
                            .map(|n| normalize_name(n.id()))
                            .collect_vec(),
                    ),
                );
            }
            ProofNode::Subproof(sp) => {
                if let ProofNode::Step(StepNode { id, discharge, .. }) = sp.last_step.as_ref() {
                    deps_map
                        .entry(normalize_name(id))
                        .and_modify(|(_, dependencies)| {
                            let mut discharge_conv = discharge
                                .iter()
                                .map(|n| normalize_name(n.id()))
                                .collect_vec();
                            dependencies.append(&mut discharge_conv);
                        });
                }
            }
        };
        index_in_proof += 1;
    });

    deps_map
}
