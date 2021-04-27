use verit_proof_checker::*;

use checker::*;
use error::*;
use parser::*;

use std::fs::File;
use std::io::{self, BufReader};

fn print_used_rules(file_path: &str) -> ParserResult<()> {
    use parser::lexer::{Lexer, Token};
    let file = File::open(file_path).map_err(|err| (err, (0, 0)))?;
    let mut lex = Lexer::new(BufReader::new(file)).map_err(|err| (err, (0, 0)))?;
    loop {
        let tk = lex.next_token()?;
        match tk {
            Token::Eof => break,
            Token::Keyword(s) if &s == "rule" => {
                if let Token::Symbol(s) = lex.next_token()? {
                    println!("{}", s)
                }
            }
            _ => (),
        }
    }
    Ok(())
}

fn main() -> ParserResult<()> {
    const MISSING_ARG: &str = "missing argument";
    let mut args = std::env::args();
    args.next();

    match args.next().expect(MISSING_ARG).as_str() {
        "--print-used-rules" => print_used_rules(&args.next().expect(MISSING_ARG))?,
        "--is-rule-implemented" => {
            let rule = &args.next().expect(MISSING_ARG);
            println!("{}", ProofChecker::get_rule(rule).is_some());
        }
        file_path => {
            let problem = BufReader::new(File::open(file_path).map_err(|err| (err, (0, 0)))?);
            let proof = if let Some(file_path) = args.next() {
                let file = File::open(file_path).map_err(|err| (err, (0, 0)))?;
                parse_problem_proof(problem, BufReader::new(file))?
            } else {
                let stdin = io::stdin();
                parse_problem_proof(problem, stdin.lock())?
            };
            println!("{:#?}", proof);
            match ProofChecker::new(proof).check() {
                Ok(()) => println!("true"),
                Err(CheckerError::UnknownRule(s)) => println!("unknown rule: {}", s),
                Err(CheckerError::FailedOnRule(s)) => println!("false ({})", s),
            }
        }
    }

    Ok(())
}
