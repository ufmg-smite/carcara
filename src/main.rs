extern crate num_rational;

mod checker;
mod parser;

use error::*;
use parser::*;
use std::fs::File;
use std::io::{self, BufRead, BufReader};

fn parse_proof(reader: impl BufRead) -> ParserResult<ast::Proof> {
    let mut parser = Parser::new(reader)?;
    parser.parse_proof()
}

fn main() -> ParserResult<()> {
    let proof = match std::env::args().nth(1) {
        Some(file_path) => {
            let file = File::open(file_path)?;
            parse_proof(BufReader::new(file))
        }
        None => {
            let stdin = io::stdin();
            parse_proof(stdin.lock())
        }
    }?;
    println!("{:#?}", proof);
    println!("{}", checker::ProofChecker::new(proof).check());
    Ok(())
}
