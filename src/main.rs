extern crate clap;

use verit_proof_checker::*;

use checker::*;
use error::*;
use parser::*;

use std::fs::File;
use std::io::BufReader;

use clap::{App, AppSettings, Arg, SubCommand};

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
    let matches = App::new("veriT proof checker")
        .version("0.1.0")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommands(vec![
            SubCommand::with_name("check")
                .about("Checks a proof file")
                .setting(AppSettings::DisableVersion)
                .arg(Arg::with_name("PROBLEM_FILE").required(true))
                .arg(Arg::with_name("PROOF_FILE").required(true))
                .arg(
                    Arg::with_name("print-ast")
                        .long("print-ast")
                        .help("Prints the parsed proof AST"),
                )
                .arg(
                    Arg::with_name("skip-unknown-rules")
                        .long("skip-unknown-rules")
                        .help("Skips rules that are not yet implemented"),
                ),
            SubCommand::with_name("print-used-rules")
                .setting(AppSettings::DisableVersion)
                .about("Prints all rules that were used in a proof file")
                .arg(Arg::with_name("PROOF_FILE").required(true)),
            SubCommand::with_name("is-rule-implemented")
                .setting(AppSettings::DisableVersion)
                .about("Prints \"true\" if the given rule is implemented, and \"false\" otherwise")
                .arg(Arg::with_name("RULE").required(true)),
        ])
        .get_matches();

    if let Some(matches) = matches.subcommand_matches("check") {
        let problem_file = BufReader::new(
            File::open(matches.value_of("PROBLEM_FILE").unwrap()).map_err(|err| (err, (0, 0)))?,
        );
        let proof_file = BufReader::new(
            File::open(matches.value_of("PROOF_FILE").unwrap()).map_err(|err| (err, (0, 0)))?,
        );
        let proof = parse_problem_proof(problem_file, proof_file)?;
        if matches.is_present("print-ast") {
            println!("{:#?}", proof);
        }
        match ProofChecker::new(proof, matches.is_present("skip-unknown-rules")).check() {
            Ok(()) => println!("true"),
            Err(CheckerError::UnknownRule(s)) => println!("unknown rule: {}", s),
            Err(CheckerError::FailedOnRule(s)) => println!("false ({})", s),
        }
    } else if let Some(matches) = matches.subcommand_matches("print-used-rules") {
        print_used_rules(matches.value_of("PROOF_FILE").unwrap())?
    } else if let Some(matches) = matches.subcommand_matches("is-rule-implemented") {
        println!(
            "{}",
            ProofChecker::get_rule(matches.value_of("RULE").unwrap()).is_some()
        )
    }
    Ok(())
}
