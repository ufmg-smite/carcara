mod benchmarking;
mod error;
mod logger;
mod path_args;

use carcara::{
    ast::print_proof,
    benchmarking::{Metrics, OnlineBenchmarkResults},
    check, check_and_elaborate, generate_lia_smt_instances, parser, CarcaraOptions,
};
use clap::{AppSettings, ArgEnum, Args, Parser, Subcommand};
use const_format::{formatcp, str_index};
use error::{CliError, CliResult};
use git_version::git_version;
use path_args::{get_instances_from_paths, infer_problem_path};
use std::{
    fs::File,
    io::{self, BufRead},
    path::Path,
};

// `git describe --all` will try to find any ref (including tags) that describes the current commit.
// This will include tags like `carcara-0.1.0`, that we create for github releases. To account for
// that, we pass the arguments `--exclude 'carcara-*'`, ignoring these tags.
const GIT_BRANCH_NAME: &str = git_version!(
    args = ["--all", "--exclude", "carcara-*"],
    fallback = "heads/none",
);
const GIT_COMMIT_HASH: &str = git_version!(fallback = "unknown");
const APP_VERSION: &str = env!("CARGO_PKG_VERSION");

const VERSION_STRING: &str = formatcp!(
    "{} [git {} {}]",
    APP_VERSION,
    // By default, `git describe` returns something like "heads/main". We ignore the "heads/" part
    // to get only the branch name
    str_index!(GIT_BRANCH_NAME, 6..),
    GIT_COMMIT_HASH,
);

#[derive(Parser)]
#[clap(
    name = "carcara",
    version = VERSION_STRING,
    setting = AppSettings::DeriveDisplayOrder
)]
struct Cli {
    #[clap(subcommand)]
    command: Command,

    /// Sets the maximum logging level.
    #[clap(arg_enum, global = true, long = "log", default_value_t = LogLevel::Warn)]
    log_level: LogLevel,

    /// Disables output coloring.
    #[clap(global = true, long)]
    no_color: bool,
}

#[derive(Subcommand)]
enum Command {
    /// Parses a proof file and prints it back.
    Parse(ParseCommandOptions),

    /// Checks a proof file.
    Check(CheckCommandOptions),

    /// Checks and elaborates a proof file.
    Elaborate(ElaborateCommandOptions),

    /// Checks a series of proof files and records performance statistics.
    Bench(BenchCommandOptions),

    /// Generates the equivalent SMT instance for every `lia_generic` step in a proof.
    GenerateLiaProblems(ParseCommandOptions),
}

#[derive(Args)]
struct Input {
    /// The proof file to be checked
    proof_file: String,

    /// The original problem file. If this argument is not present, it will be inferred from the
    /// proof file.
    problem_file: Option<String>,
}

#[derive(Args, Clone, Copy)]
struct ParsingOptions {
    /// Expand function definitions introduced by `define-fun`s in the SMT problem. If this flag is
    /// not present, they are instead interpreted as a function declaration and an `assert` that
    /// defines the function name to be equal to its body. Function definitions in the proof itself
    /// are always expanded.
    #[clap(long)]
    apply_function_defs: bool,

    /// Eliminates `let` bindings from terms when parsing.
    #[clap(long)]
    expand_let_bindings: bool,

    /// Enables `Int`/`Real` subtyping in the parser. This allows terms of sort `Int` to be passed
    /// to arithmetic operators that are expecting a term of sort `Real`.
    #[clap(long)]
    allow_int_real_subtyping: bool,
}

#[derive(Args, Clone, Copy)]
struct CheckingOptions {
    /// Enables the strict checking of certain rules.
    #[clap(short, long)]
    strict: bool,

    /// Skips rules that are not known by the checker.
    #[clap(long)]
    skip_unknown_rules: bool,

    /// Check `lia_generic` steps by calling into cvc5.
    #[clap(long)]
    lia_via_cvc5: bool,

    /// Defines the number of cores for proof checking.
    #[clap(short = 'u', long, required = false, default_value = "1", validator = |s: &str| -> Result<(), String> {
        if s == "0" { Err(String::from("The number of cores can't be 0.")) } else { Ok(()) }
    })]
    num_cores: usize,
}

#[derive(Args)]
struct PrintingOptions {
    /// Use sharing when printing proof terms.
    #[clap(long = "print-with-sharing")]
    use_sharing: bool,
}

fn build_carcara_options(
    ParsingOptions {
        apply_function_defs,
        expand_let_bindings,
        allow_int_real_subtyping,
    }: ParsingOptions,
    CheckingOptions {
        strict,
        skip_unknown_rules,
        lia_via_cvc5,
        num_cores,
    }: CheckingOptions,
) -> CarcaraOptions {
    CarcaraOptions {
        apply_function_defs,
        expand_lets: expand_let_bindings,
        allow_int_real_subtyping,
        check_lia_using_cvc5: lia_via_cvc5,
        strict,
        skip_unknown_rules,
        num_cores: num_cores,
    }
}

#[derive(Args)]
struct ParseCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    printing: PrintingOptions,
}

#[derive(Args)]
struct CheckCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    checking: CheckingOptions,
}

#[derive(Args)]
struct ElaborateCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    checking: CheckingOptions,

    #[clap(flatten)]
    printing: PrintingOptions,
}

#[derive(Args)]
struct BenchCommandOptions {
    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    checking: CheckingOptions,

    /// Also elaborate each proof in addition to parsing and checking.
    #[clap(long)]
    elaborate: bool,

    /// Number of times to run the benchmark for each file.
    #[clap(short, long, default_value_t = 1)]
    num_runs: usize,

    /// Number of threads to use when running the benchmark.
    #[clap(short = 'j', long, default_value_t = 1)]
    num_threads: usize,

    /// Show benchmark results sorted by total time taken, instead of by average time taken.
    #[clap(short = 't', long)]
    sort_by_total: bool,

    /// Dump results to csv files instead of printing to screen.
    #[clap(long = "dump-to-csv")]
    dump_to_csv: bool,

    /// The proof files on which the benchmark will be run. If a directory is passed, the checker
    /// will recursively find all '.proof' files in the directory. The problem files will be
    /// inferred from the proof files.
    files: Vec<String>,
}

#[derive(ArgEnum, Clone)]
enum LogLevel {
    Off,
    Error,
    Warn,
    Info,
}

impl From<LogLevel> for log::LevelFilter {
    fn from(l: LogLevel) -> Self {
        match l {
            LogLevel::Off => Self::Off,
            LogLevel::Error => Self::Error,
            LogLevel::Warn => Self::Warn,
            LogLevel::Info => Self::Info,
        }
    }
}

fn main() {
    let cli = Cli::parse();
    let colors_enabled = !cli.no_color && atty::is(atty::Stream::Stderr);
    logger::init(cli.log_level.into(), colors_enabled);
    if !matches!(cli.command, Command::Check(_)) && cfg!(feature = "thread-safety") {
        log::error!(
            "No avaiable implementation for {} command in thread safety mode. Please disable thread safety mode.",
            match cli.command {
                Command::Parse(_) => "parse",
                Command::Elaborate(_) => "elaborate",
                Command::Bench(_) => "bench",
                Command::GenerateLiaProblems(_) => "generate lia problems",
                _ => unreachable!(),
            }
        );
        std::process::exit(1);
    }

    let result = match cli.command {
        Command::Parse(options) => parse_command(options),
        Command::Check(options) => {
            match check_command(options) {
                Ok(false) => println!("valid"),
                Ok(true) => println!("holey"),
                Err(e) => {
                    log::error!("{}", e);
                    println!("invalid");
                    std::process::exit(1);
                }
            }
            return;
        }
        Command::Elaborate(options) => elaborate_command(options),
        Command::Bench(options) => bench_command(options),
        Command::GenerateLiaProblems(options) => generate_lia_problems_command(options),
    };
    if let Err(e) = result {
        log::error!("{}", e);
        std::process::exit(1);
    }
}

fn get_instance(options: &Input) -> CliResult<(Box<dyn BufRead>, Box<dyn BufRead>)> {
    fn reader_from_path<P: AsRef<Path>>(path: P) -> CliResult<Box<dyn BufRead>> {
        Ok(Box::new(io::BufReader::new(File::open(path)?)))
    }

    match (options.problem_file.as_deref(), options.proof_file.as_str()) {
        (Some("-"), "-") | (None, "-") => Err(CliError::BothFilesStdin),
        (Some(problem), "-") => Ok((reader_from_path(problem)?, Box::new(io::stdin().lock()))),
        (Some("-"), proof) => Ok((Box::new(io::stdin().lock()), reader_from_path(proof)?)),
        (Some(problem), proof) => Ok((reader_from_path(problem)?, reader_from_path(proof)?)),
        (None, proof) => Ok((
            reader_from_path(infer_problem_path(proof)?)?,
            reader_from_path(proof)?,
        )),
    }
}

fn parse_command(options: ParseCommandOptions) -> CliResult<()> {
    let (problem, proof) = get_instance(&options.input)?;
    let (_, proof, _) = parser::parse_instance(
        problem,
        proof,
        options.parsing.apply_function_defs,
        options.parsing.expand_let_bindings,
        options.parsing.allow_int_real_subtyping,
    )
    .map_err(carcara::Error::from)?;
    print_proof(&proof.commands, options.printing.use_sharing)?;
    Ok(())
}

fn check_command(options: CheckCommandOptions) -> CliResult<bool> {
    let (problem, proof) = get_instance(&options.input)?;
    check(
        problem,
        proof,
        build_carcara_options(options.parsing, options.checking),
    )
    .map_err(Into::into)
}

fn elaborate_command(options: ElaborateCommandOptions) -> CliResult<()> {
    let (problem, proof) = get_instance(&options.input)?;

    let elaborated = check_and_elaborate(
        problem,
        proof,
        build_carcara_options(options.parsing, options.checking),
    )?;
    print_proof(&elaborated, options.printing.use_sharing)?;
    Ok(())
}

fn bench_command(options: BenchCommandOptions) -> CliResult<()> {
    let instances = get_instances_from_paths(options.files.iter().map(|s| s.as_str()))?;
    if instances.is_empty() {
        log::warn!("no files passed");
        return Ok(());
    }

    println!(
        "running benchmark on {} files, doing {} runs each",
        instances.len(),
        options.num_runs
    );

    if options.dump_to_csv {
        benchmarking::run_csv_benchmark(
            &instances,
            options.num_runs,
            options.num_threads,
            &build_carcara_options(options.parsing, options.checking),
            options.elaborate,
            &mut File::create("runs.csv")?,
            &mut File::create("by-rule.csv")?,
        )?;
        return Ok(());
    }

    let results: OnlineBenchmarkResults = benchmarking::run_benchmark(
        &instances,
        options.num_runs,
        options.num_threads,
        &build_carcara_options(options.parsing, options.checking),
        options.elaborate,
    );
    if results.is_empty() {
        println!("no benchmark data collected");
        return Ok(());
    }

    print_benchmark_results(results, options.sort_by_total)
}

fn print_benchmark_results(results: OnlineBenchmarkResults, sort_by_total: bool) -> CliResult<()> {
    let [parsing, checking, elaborating, accounted_for, total] = [
        results.parsing(),
        results.checking(),
        results.elaborating(),
        results.total_accounted_for(),
        results.total(),
    ]
    .map(|m| {
        if sort_by_total {
            format!("{:#}", m)
        } else {
            format!("{}", m)
        }
    });

    println!("parsing:             {}", parsing);
    println!("checking:            {}", checking);
    if !elaborating.is_empty() {
        println!("elaborating:      {}", elaborating);
    }
    println!(
        "on assume:           {} ({:.02}% of checking time)",
        results.assume_time,
        100.0 * results.assume_time.mean().as_secs_f64() / results.checking().mean().as_secs_f64(),
    );
    println!("on assume (core):    {}", results.assume_core_time);
    println!("assume ratio:        {}", results.assume_time_ratio);
    println!(
        "on deep equality:    {} ({:.02}% of checking time)",
        results.deep_eq_time,
        100.0 * results.deep_eq_time.mean().as_secs_f64() / results.checking().mean().as_secs_f64(),
    );
    println!("deep equality ratio: {}", results.deep_eq_time_ratio);
    println!("total accounted for: {}", accounted_for);
    println!("total:               {}", total);

    let data_by_rule = results.step_time_by_rule();
    let mut data_by_rule: Vec<_> = data_by_rule.iter().collect();
    data_by_rule.sort_by_key(|(_, m)| if sort_by_total { m.total() } else { m.mean() });

    println!("by rule:");
    for (rule, data) in data_by_rule {
        print!("    {: <18}", rule);
        if sort_by_total {
            println!("{:#}", data)
        } else {
            println!("{}", data)
        }
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

    let worst_file_assume = results.assume_time_ratio.max();
    println!(
        "    file (assume):   {} ({:.04}%)",
        worst_file_assume.0 .0,
        worst_file_assume.1 * 100.0
    );

    let worst_file_deep_eq = results.deep_eq_time_ratio.max();
    println!(
        "    file (deep_eq):  {} ({:.04}%)",
        worst_file_deep_eq.0 .0,
        worst_file_deep_eq.1 * 100.0
    );

    let worst_file_total = results.total().max();
    println!(
        "    file overall:    {} ({:?})",
        worst_file_total.0 .0, worst_file_total.1
    );

    let num_hard_assumes = results.num_assumes - results.num_easy_assumes;
    let percent_easy = (results.num_easy_assumes as f64) * 100.0 / (results.num_assumes as f64);
    let percent_hard = (num_hard_assumes as f64) * 100.0 / (results.num_assumes as f64);
    println!("          number of assumes: {}", results.num_assumes);
    println!(
        "                     (easy): {} ({:.02}%)",
        results.num_easy_assumes, percent_easy
    );
    println!(
        "                     (hard): {} ({:.02}%)",
        num_hard_assumes, percent_hard
    );

    let depths = results.deep_eq_depths;
    if !depths.is_empty() {
        println!("    max deep equality depth: {}", depths.max().1);
        println!("  total deep equality depth: {}", depths.total());
        println!("  number of deep equalities: {}", depths.count());
        println!("                 mean depth: {:.4}", depths.mean());
        println!(
            "standard deviation of depth: {:.4}",
            depths.standard_deviation()
        );
    }
    Ok(())
}

fn generate_lia_problems_command(options: ParseCommandOptions) -> CliResult<()> {
    use std::io::Write;

    let root_file_name = options.input.proof_file.clone();
    let (problem, proof) = get_instance(&options.input)?;

    let instances = generate_lia_smt_instances(
        problem,
        proof,
        options.parsing.apply_function_defs,
        options.parsing.expand_let_bindings,
        options.parsing.allow_int_real_subtyping,
        options.printing.use_sharing,
    )?;
    for (id, content) in instances {
        let file_name = format!("{}.{}.lia_smt2", root_file_name, id);
        let mut f = File::create(file_name)?;
        write!(f, "{}", content)?;
    }

    Ok(())
}
