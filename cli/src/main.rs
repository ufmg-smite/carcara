extern crate clap;

mod path_args;

use ahash::AHashSet;
use alethe_proof_checker::{
    benchmarking, check,
    checker::{Correctness, ProofChecker},
    parser::{error::ParserResult, lexer, parse_problem_proof},
    Error,
};
use clap::{App, AppSettings, Arg, ArgGroup, ArgMatches, SubCommand};
use path_args::{get_instances_from_paths, infer_problem_path};
use std::{
    fs::File,
    io::{BufReader, Write},
    path::PathBuf,
};

fn app() -> App<'static, 'static> {
    let subcommands = vec![
        SubCommand::with_name("check")
            .about("Checks a proof file")
            .setting(AppSettings::DisableVersion)
            .arg(Arg::with_name("proof-file").required(true))
            .arg(Arg::with_name("problem-file"))
            .arg(
                Arg::with_name("skip-unknown-rules")
                    .short("s")
                    .long("skip-unknown-rules")
                    .help("Skips rules that are not yet implemented"),
            ),
        SubCommand::with_name("parse")
            .about("Parses a proof file and prints the AST")
            .setting(AppSettings::DisableVersion)
            .arg(Arg::with_name("proof-file").required(true))
            .arg(Arg::with_name("problem-file")),
        SubCommand::with_name("bench")
            .about("Checks a series of proof files and records performance statistics")
            .setting(AppSettings::DisableVersion)
            .arg(
                Arg::with_name("num-runs")
                    .short("n")
                    .long("num-runs")
                    .default_value("10")
                    .help("Number of times to run the benchmark for each file"),
            )
            .arg(Arg::with_name("files").multiple(true).required(true).help(
                "The proof files to be checked. The problem files will be inferred from the \
                proof files",
            )),
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
    ];
    App::new("Alethe proof checker")
        .version("0.1.0")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommands(subcommands)
}

fn main() -> Result<(), Error> {
    let matches = app().get_matches();

    if let Some(matches) = matches.subcommand_matches("check") {
        check_subcommand(matches)
    } else if let Some(matches) = matches.subcommand_matches("parse") {
        parse_subcommand(matches)
    } else if let Some(matches) = matches.subcommand_matches("bench") {
        bench_subcommand(matches)
    } else if let Some(matches) = matches.subcommand_matches("progress-report") {
        progress_report_subcommand(matches)
    } else {
        unreachable!()
    }
}

fn check_subcommand(matches: &ArgMatches) -> Result<(), Error> {
    let proof_file = matches.value_of("proof-file").unwrap();
    let problem_file = matches
        .value_of("problem-file")
        .map(PathBuf::from)
        .or_else(|| infer_problem_path(proof_file))
        .expect("Couldn't infer original problem file");
    let skip = matches.is_present("skip-unknown-rules");
    match check(problem_file, PathBuf::from(proof_file), skip, false)? {
        Correctness::True => println!("true"),
        Correctness::False(s, r) => println!("false ({}, {})", s, r),
    }
    Ok(())
}

fn parse_subcommand(matches: &ArgMatches) -> Result<(), Error> {
    let proof_file = matches.value_of("proof-file").unwrap();
    let problem_file = matches
        .value_of("problem-file")
        .map(PathBuf::from)
        .or_else(|| infer_problem_path(proof_file))
        .expect("Couldn't infer original problem file");
    let (problem, proof) = (
        BufReader::new(File::open(problem_file)?),
        BufReader::new(File::open(proof_file)?),
    );
    let (proof, _) = parse_problem_proof(problem, proof)?;
    println!("{:#?}", proof);
    Ok(())
}

fn bench_subcommand(matches: &ArgMatches) -> Result<(), Error> {
    // TODO: Add better error handling
    let num_runs = matches.value_of("num-runs").unwrap().parse().unwrap();
    let instances = get_instances_from_paths(matches.values_of("files").unwrap())?;

    if instances.is_empty() {
        println!("No files left, exiting");
        return Ok(());
    }

    println!(
        "running benchmark on {} files, doing {} runs each",
        instances.len(),
        num_runs
    );
    let results = benchmarking::run_benchmark(&instances, num_runs)?;

    println!("parsing:            {}", results.parsing());
    println!("checking:           {}", results.checking());
    println!("parsing + checking: {}", results.parsing_checking());
    println!("total:              {}", results.total());

    let data_by_rule = results.step_time_by_rule();
    let mut data_by_rule: Vec<_> = data_by_rule.iter().collect();
    data_by_rule.sort_by_key(|(_, m)| m.mean);
    println!("by rule:");
    for (rule, data) in data_by_rule {
        println!("    {: <18}{}", rule, data);
    }

    println!("worst cases:");
    let worst_step = results.step_time().max();
    println!("    step:            {} ({:?})", worst_step.0, worst_step.1);

    let worst_file_parsing = results.parsing().max();
    println!(
        "    file (parsing):  {} ({:?})",
        worst_file_parsing.0 .0, worst_file_parsing.1
    );

    let worst_file_checking = results.checking().max();
    println!(
        "    file (checking): {} ({:?})",
        worst_file_checking.0 .0, worst_file_checking.1
    );

    let worst_file_total = results.total().max();
    println!(
        "    file overall:    {} ({:?})",
        worst_file_total.0 .0, worst_file_total.1
    );
    Ok(())
}

fn progress_report_subcommand(matches: &ArgMatches) -> Result<(), Error> {
    let instances = get_instances_from_paths(matches.values_of("files").unwrap()).unwrap();
    let files: Vec<_> = instances
        .iter()
        .map(|(_problem, proof)| proof.to_str().unwrap())
        .collect();

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
    Ok(())
}

fn get_used_rules(file_path: &str) -> ParserResult<Vec<String>> {
    use lexer::{Lexer, Token};

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

    let mut seen = AHashSet::new();
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
