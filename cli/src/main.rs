mod benchmarking;
mod error;
mod logger;
mod path_args;

use carcara::{
    ast::print_proof,
    benchmarking::{Metrics, OnlineBenchmarkResults},
    check, check_and_elaborate, generate_lia_smt_instances, parser,
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

const GIT_COMMIT_HASH: &str = git_version!(fallback = "unknown");
const GIT_BRANCH_NAME: &str = git_version!(args = ["--all"]);
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
    Parse(ParseOptions),

    /// Checks a proof file.
    Check(CheckOptions),

    /// Checks and elaborates a proof file.
    Elaborate(ElaborateOptions),

    /// Checks a series of proof files and records performance statistics.
    Bench(BenchmarkOptions),

    /// Generates the equivalent SMT instance for every `lia_generic` step in a proof.
    GenerateLiaProblems(InputOptions),
}

#[derive(Args)]
struct InputOptions {
    /// The proof file to be checked
    proof_file: String,

    /// The original problem file. If this argument is not present, it will be inferred from the
    /// proof file.
    problem_file: Option<String>,

    /// Don't apply function definitions introduced by `define-fun`s and `:named` attributes.
    /// Instead, interpret them as a function declaration and an `assert` that defines the function
    /// to be equal to its body.
    #[clap(long)]
    dont_apply_function_defs: bool,

    /// Enables `Int`/`Real` subtyping in the parser. This allows terms of sort `Int` to be passed
    /// to arithmetic operators that are expecting a term of sort `Real`.
    #[clap(long)]
    allow_int_real_subtyping: bool,
}

#[derive(Args)]
struct PrintingOptions {
    /// Use sharing when printing proof terms.
    #[clap(long = "print-with-sharing")]
    use_sharing: bool,
}

#[derive(Args)]
struct ParseOptions {
    #[clap(flatten)]
    input: InputOptions,

    #[clap(flatten)]
    printing: PrintingOptions,
}

#[derive(Args)]
struct CheckOptions {
    #[clap(flatten)]
    input: InputOptions,

    /// Enables the strict checking of certain rules.
    #[clap(short, long)]
    strict: bool,

    /// Skips rules that are not known by the checker.
    #[clap(long)]
    skip_unknown_rules: bool,
}

#[derive(Args)]
struct ElaborateOptions {
    #[clap(flatten)]
    checking: CheckOptions,

    #[clap(flatten)]
    printing: PrintingOptions,
}

#[derive(Args)]
struct BenchmarkOptions {
    /// Number of times to run the benchmark for each file.
    #[clap(short, long, default_value_t = 10)]
    num_runs: usize,

    /// Number of threads to use when running the benchmark.
    #[clap(short = 'j', long, default_value_t = 1)]
    num_threads: usize,

    /// Use strict checking in benchmarks
    #[clap(short, long)]
    strict: bool,

    /// Also elaborate each proof in addition to parsing and checking.
    #[clap(long)]
    elaborate: bool,

    /// Enables `Int`/`Real` subtyping in the parser.
    #[clap(long)]
    allow_int_real_subtyping: bool,

    /// Show benchmark results sorted by total time taken, instead of by average time taken.
    #[clap(short = 't', long)]
    sort_by_total: bool,

    /// Dump results to csv files instead of printing to screen.
    #[clap(long = "dump-to-csv")]
    dump_to_csv: bool,

    /// The proof files on which the benchkmark will be run. If a directory is passed, the checker
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

fn get_instance(options: &InputOptions) -> CliResult<(Box<dyn BufRead>, Box<dyn BufRead>)> {
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

fn parse_command(options: ParseOptions) -> CliResult<()> {
    let (problem, proof) = get_instance(&options.input)?;
    let (_, proof, _) = parser::parse_instance(
        problem,
        proof,
        !options.input.dont_apply_function_defs,
        options.input.allow_int_real_subtyping,
    )
    .map_err(carcara::Error::from)?;
    print_proof(&proof.commands, options.printing.use_sharing)?;
    Ok(())
}

fn check_command(options: CheckOptions) -> CliResult<bool> {
    let (problem, proof) = get_instance(&options.input)?;

    check(
        problem,
        proof,
        !options.input.dont_apply_function_defs,
        options.input.allow_int_real_subtyping,
        options.strict,
        options.skip_unknown_rules,
    )
    .map_err(Into::into)
}

fn elaborate_command(options: ElaborateOptions) -> CliResult<()> {
    let (problem, proof) = get_instance(&options.checking.input)?;

    let elaborated = check_and_elaborate(
        problem,
        proof,
        !options.checking.input.dont_apply_function_defs,
        options.checking.input.allow_int_real_subtyping,
        options.checking.strict,
        options.checking.skip_unknown_rules,
    )?;
    print_proof(&elaborated, options.printing.use_sharing)?;
    Ok(())
}

fn bench_command(options: BenchmarkOptions) -> CliResult<()> {
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
            options.strict,
            options.elaborate,
            options.allow_int_real_subtyping,
            &mut File::create("runs.csv")?,
            &mut File::create("by-rule.csv")?,
        )?;
        return Ok(());
    }

    let results: OnlineBenchmarkResults = benchmarking::run_benchmark(
        &instances,
        options.num_runs,
        options.num_threads,
        options.strict,
        options.elaborate,
        options.allow_int_real_subtyping,
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

fn generate_lia_problems_command(options: InputOptions) -> CliResult<()> {
    use std::io::Write;

    let root_file_name = options.proof_file.clone();
    let apply_function_defs = !options.dont_apply_function_defs;
    let (problem, proof) = get_instance(&options)?;

    let instances = generate_lia_smt_instances(problem, proof, apply_function_defs)?;
    for (id, content) in instances {
        let file_name = format!("{}.{}.lia_smt2", root_file_name, id);
        let mut f = File::create(file_name)?;
        write!(f, "{}", content)?;
    }

    Ok(())
}
