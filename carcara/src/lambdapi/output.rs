//use super::*;
use super::Command;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::io;

use crate::lambdapi::printer::PrettyPrint;
use crate::lambdapi::printer::PrettyPrintAx;


impl <'a> fmt::Display for ProofFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.render_fmt(f)
    }
}

pub trait Render {
    fn render<W: io::Write>(&self, f: &mut io::BufWriter<W>) -> io::Result<()>;
}

/// Lambdapi files are formed of a list of commands.
pub struct ProofFile{
    pub requires: Vec<Command>,
    pub definitions: Vec<Command>,
    pub content: Vec<Command>,
    pub dependencies: HashMap<String, (usize, HashSet<usize>)>,
}

impl Render for ProofFile {
    fn render<W: io::Write>(&self, f: &mut io::BufWriter<W>) -> io::Result<()> {
        PrettyPrint::render(self, f)
    }
}

impl<'a> ProofFile {
    pub fn new() -> ProofFile {
        Self{
            requires: Vec::new(),
            definitions: Vec::new(),
            content: Vec::new(),
            dependencies: HashMap::new()
        }
    }
}

pub struct AxiomsFile {
    pub requires: Vec<Command>,
    pub content: Vec<Command>,
}


impl<'a> AxiomsFile {
    pub fn new() -> AxiomsFile {
        Self{
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