extern crate num_rational;

mod checker;
mod parser;

use error::*;
use parser::*;
use std::fs::File;
use std::io::{self, BufReader};

fn main() -> ParserResult<()> {
    let problem = if let Some(file_path) = std::env::args().nth(1) {
        let file = File::open(file_path)?;
        BufReader::new(file)
    } else {
        panic!("missing argument")
    };

    let proof = match std::env::args().nth(2) {
        Some(file_path) => {
            let file = File::open(file_path)?;
            parse_problem_proof(problem, BufReader::new(file))
        }
        None => {
            let stdin = io::stdin();
            parse_problem_proof(problem, stdin.lock())
        }
    }?;

    println!("{:#?}", proof);
    println!("{}", checker::ProofChecker::new(proof).check());
    Ok(())
}
