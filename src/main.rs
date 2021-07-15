extern crate clap;

use verit_proof_checker::*;

use checker::*;
use error::*;
use parser::*;

use std::{
    collections::HashSet,
    fs::File,
    io::{BufReader, Write},
};

use clap::{App, AppSettings, Arg, ArgGroup, SubCommand};

fn main() -> ParserResult<()> {
    let matches = App::new("veriT proof checker")
        .version("0.1.0")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommands(vec![
            SubCommand::with_name("check")
                .about("Checks a proof file")
                .setting(AppSettings::DisableVersion)
                .arg(Arg::with_name("PROBLEM_FILE").required(true))
                .arg(Arg::with_name("PROOF_FILE").required(false))
                .arg(
                    Arg::with_name("skip-unknown-rules")
                        .short("s")
                        .long("skip-unknown-rules")
                        .help("Skips rules that are not yet implemented"),
                ),
            SubCommand::with_name("parse")
                .about("Parses a proof file and prints the AST")
                .setting(AppSettings::DisableVersion)
                .arg(Arg::with_name("PROBLEM_FILE").required(true))
                .arg(Arg::with_name("PROOF_FILE").required(false)),
            SubCommand::with_name("progress-report")
                .setting(AppSettings::DisableVersion)
                .setting(AppSettings::DeriveDisplayOrder)
                .about("Prints a progress report on which rules are implemented")
                .arg(
                    Arg::with_name("by-files")
                        .short("f")
                        .long("by-files")
                        .help("Reports which files have all rules implemented"),
                )
                .arg(
                    Arg::with_name("by-rules")
                        .short("r")
                        .long("by-rules")
                        .help("Reports which rules in the given files are implemented"),
                )
                .arg(
                    Arg::with_name("by-files-and-rules")
                        .short("a")
                        .long("by-files-and-rules")
                        .help("For every file given, reports which rules are implemented"),
                )
                .group(
                    ArgGroup::with_name("mode")
                        .args(&["by-files", "by-rules", "by-files-and-rules"])
                        .required(true),
                )
                .arg(
                    Arg::with_name("quiet")
                        .short("-q")
                        .long("--quiet")
                        .help("Print only one character per file/rule"),
                )
                .arg(Arg::with_name("files").multiple(true)),
        ])
        .get_matches();

    if let Some(matches) = matches.subcommand_matches("check") {
        let problem = matches.value_of("PROBLEM_FILE").unwrap();
        let proof = matches
            .value_of("PROOF_FILE")
            .map(str::to_string)
            .unwrap_or(problem.to_string() + ".proof");
        let skip = matches.is_present("skip-unknown-rules");
        match check(problem, &proof, skip, false) {
            Ok(()) => println!("true"),
            Err(Error::Parser(e)) => return Err(e),
            Err(Error::Checker(CheckerError::UnknownRule(r))) => println!("unknown rule: {}", r),
            Err(Error::Checker(CheckerError::FailedOnRule(s))) => println!("false ({})", s),
        }
    } else if let Some(matches) = matches.subcommand_matches("parse") {
        let problem = matches.value_of("PROBLEM_FILE").unwrap();
        let proof = matches
            .value_of("PROOF_FILE")
            .map(str::to_string)
            .unwrap_or(problem.to_string() + ".proof");
        let (problem, proof) = (
            BufReader::new(File::open(problem)?),
            BufReader::new(File::open(proof)?),
        );
        let (proof, _) = parse_problem_proof(problem, proof)?;
        println!("{:#?}", proof);
    } else if let Some(matches) = matches.subcommand_matches("progress-report") {
        let files = matches
            .values_of("files")
            .map(Iterator::collect::<Vec<_>>)
            .unwrap_or_default();
        let quiet = matches.is_present("quiet");
        if matches.is_present("by-files") {
            report_by_files(&files, quiet)?;
        } else if matches.is_present("by-rules") {
            report_by_rules(&files, quiet)?;
        } else if matches.is_present("by-files-and-rules") {
            for file in files {
                println!("\x1b[0;0m{}:", file);
                report_by_rules(&[file], quiet)?;
                println!();
            }
        }
    }
    Ok(())
}

fn get_used_rules(file_path: &str) -> ParserResult<Vec<String>> {
    use parser::lexer::{Lexer, Token};

    let file = File::open(file_path)?;
    let mut lex = Lexer::new(BufReader::new(file))?;
    let mut result = Vec::new();
    loop {
        let tk = lex.next_token()?;
        match tk {
            Token::Eof => break,
            Token::Keyword(s) if &s == "rule" => {
                let rule_name = match lex.next_token()? {
                    Token::Symbol(s) => s,
                    Token::ReservedWord(r) => format!("{:?}", r),
                    _ => continue,
                };
                result.push(rule_name)
            }
            _ => (),
        }
    }
    Ok(result)
}

fn print_report_entry(s: &str, success: bool, quiet: bool) {
    print!("{}", if success { "\x1b[1;32m" } else { "\x1b[0;31m" });
    if quiet {
        print!(".");
        std::io::stdout().flush().unwrap();
    } else {
        println!("{}", s);
    }
}

fn report_by_files(files: &[&str], quiet: bool) -> ParserResult<()> {
    let mut implemented = 0;
    for file in files {
        let all_implemented = get_used_rules(file)?
            .iter()
            .all(|rule| ProofChecker::get_rule(rule, false).is_some());
        print_report_entry(file, all_implemented, quiet);
        implemented += all_implemented as i32;
    }
    if quiet {
        println!();
    }
    println!(
        "\x1b[0;0m{} / {} files with all rules implemented",
        implemented,
        files.len()
    );
    Ok(())
}

fn report_by_rules(files: &[&str], quiet: bool) -> ParserResult<()> {
    let rules = files.iter().flat_map(|file| match get_used_rules(file) {
        Ok(rules) => rules.into_iter().map(Ok).collect(),
        Err(e) => vec![Err(e)],
    });

    let mut seen = HashSet::new();
    let mut implemented = 0;
    for r in rules {
        let r = r?;
        if seen.insert(r.clone()) {
            let success = ProofChecker::get_rule(&r, false).is_some();
            print_report_entry(&r, success, quiet);
            implemented += success as i32;
        }
    }
    if quiet {
        println!();
    }
    println!(
        "\x1b[0;0m{} / {} rules implemented",
        implemented,
        seen.len()
    );
    Ok(())
}
