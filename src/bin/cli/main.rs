mod app;
mod benchmarking;
mod diff;
mod error;
mod logger;
mod path_args;

use app::*;
use carcara::{
    ast::{self, Proof, printer, rare_rules::Rules},
    benchmarking::{CollectStats, CsvStats, SummaryStats},
    check, check_and_elaborate, check_parallel, generate_lia_smt_instances,
    parser::{self, Source},
    slice,
    translation::{self, Translator},
};
use error::{CliError, CliResult};
use path_args::{get_instances_from_paths, infer_problem_path};
use std::{
    fs::File,
    io::{IsTerminal, Write},
    path::{Path, PathBuf},
    sync::atomic,
};

use clap::Parser;

fn main() {
    let cli = Cli::parse();
    let stderr_colors = !cli.no_color && std::io::stderr().is_terminal();
    let stdout_colors = !cli.no_color && std::io::stdout().is_terminal();

    ast::printer::USE_SHARING_IN_TERM_DISPLAY
        .store(!cli.no_print_with_sharing, atomic::Ordering::Relaxed);

    logger::init(cli.log_level.into(), stderr_colors);

    let display_options = printer::DisplayOptions::new().use_sharing(!cli.no_print_with_sharing);
    let result = match cli.command {
        Command::Parse(options) => {
            parse_command(options).map(|(_, pf, _, _)| println!("{}", pf.display(display_options)))
        }
        Command::Check(options) => {
            match check_command(options) {
                Ok(s) => println!("{}", s),
                Err(e) => {
                    log::error!("{}", e);
                    if cli.print_diffs
                        && let Some(diff) = diff_from_error(&e)
                    {
                        eprint!("{}", diff.display(stderr_colors))
                    }
                    println!("invalid");
                    std::process::exit(1);
                }
            }
            return;
        }
        Command::Elaborate(options) => elaborate_command(options).map(|(res, _, pf, _)| {
            println!("{}", res);
            println!("{}", pf.display(display_options))
        }),
        Command::Bench(options) => bench_command(options).map(|success| {
            if !success {
                std::process::exit(1);
            }
        }),
        Command::Slice(options) => slice_command(options, cli.no_print_with_sharing)
            .map(|(_, pf, _)| println!("{}", pf.display(display_options))),
        Command::GenerateLiaProblems(options) => {
            generate_lia_problems_command(options, !cli.no_print_with_sharing)
        }
        Command::Translate(options) => translate_command(options, !cli.no_print_with_sharing),
        Command::Diff(options) => {
            diff_command(options).map(|d| print!("{}", d.display(stdout_colors)))
        }
    };
    if let Err(e) = result {
        log::error!("{}", e);
        if cli.print_diffs
            && let Some(diff) = diff_from_error(&e)
        {
            eprint!("{}", diff.display(stderr_colors))
        }
        std::process::exit(1);
    }
}

/// Reads the problem, proof and (optional) Rare rules sources given in the command-line input.
fn get_input(options: &Input) -> CliResult<carcara::Input<'static>> {
    let problem_file = match &options.problem_file {
        Some(f) => f.clone(),
        None => infer_problem_path(&options.proof_file)?,
    };
    let problem = Source::file(problem_file)?;
    let proof = Source::file_or_stdin(&options.proof_file)?;
    let rare_rules = options.rare_file.as_ref().map(Source::file).transpose()?;
    Ok(carcara::Input { problem, proof, rare_rules })
}

fn parse_command(
    options: ParseCommandOptions,
) -> CliResult<(ast::Problem, ast::Proof, Rules, ast::pool::Pool)> {
    let result = parser::parse(get_input(&options.input)?, options.parsing.into_config())?;
    Ok(result)
}

fn check_command(options: CheckCommandOptions) -> CliResult<carcara::Status> {
    if options.stats.stats {
        let mut results = SummaryStats::new();
        let status = check_command_impl(options, &mut results)?;
        results.print(false);
        Ok(status)
    } else {
        check_command_impl(options, &mut ())
    }
}

fn check_command_impl<S: CollectStats + Send + Default>(
    options: CheckCommandOptions,
    stats: &mut S,
) -> CliResult<carcara::Status> {
    let input = get_input(&options.input)?;
    let parser_config = options.parsing.into_config();
    let checker_config = (options.checking, options.tools).into_config();

    let status = if options.num_threads.get() == 1 {
        check(input, parser_config, checker_config, stats)
    } else {
        check_parallel(
            input,
            parser_config,
            checker_config,
            options.num_threads,
            options.stack.stack_size,
            stats,
        )
    }?;
    Ok(status)
}

fn elaborate_command(
    options: ElaborateCommandOptions,
) -> CliResult<(carcara::Status, ast::Problem, ast::Proof, ast::pool::Pool)> {
    if options.stats.stats {
        let mut results = SummaryStats::new();
        let result = elaborate_command_impl(options, &mut results)?;
        results.print(false);
        Ok(result)
    } else {
        elaborate_command_impl(options, &mut ())
    }
}

fn elaborate_command_impl<S: CollectStats>(
    options: ElaborateCommandOptions,
    stats: &mut S,
) -> CliResult<(carcara::Status, ast::Problem, ast::Proof, ast::pool::Pool)> {
    let input = get_input(&options.input)?;

    let checker_config = (options.checking, options.tools.clone()).into_config();
    let (elab_config, pipeline) = (options.elaboration, options.tools).into_config();

    Ok(check_and_elaborate(
        input,
        options.parsing.into_config(),
        checker_config,
        elab_config,
        pipeline,
        stats,
    )?)
}

/// Runs the benchmark and prints its results. Returns `false` if any run failed.
fn bench_command(options: BenchCommandOptions) -> CliResult<bool> {
    let instances = get_instances_from_paths(&options.files)?;
    if instances.is_empty() {
        log::warn!("no files passed");
        return Ok(true);
    }

    log::info!(
        "running benchmark on {} files, doing {} runs each",
        instances.len(),
        options.num_runs
    );

    let checker_config = (options.checking, options.tools.clone()).into_config();
    let (elab_config, pipeline) = (options.elaboration, options.tools).into_config();

    if options.dump_to_csv {
        let result = benchmarking::run_benchmark::<CsvStats>(
            &instances,
            options.num_runs,
            options.num_jobs,
            options.parsing.into_config(),
            checker_config,
            options.elaborate.then_some((elab_config, pipeline)),
        );
        result.print_status();
        result.stats.write_csv("runs.csv", "steps.csv")?;
        Ok(result.num_errors == 0)
    } else {
        let result = benchmarking::run_benchmark::<SummaryStats>(
            &instances,
            options.num_runs,
            options.num_jobs,
            options.parsing.into_config(),
            checker_config,
            options.elaborate.then_some((elab_config, pipeline)),
        );
        result.print_status();
        if result.stats.is_empty() {
            println!("no benchmark data collected");
        } else {
            result.stats.print(options.sort_by_total);
        }
        Ok(result.num_errors == 0)
    }
}

fn slice_command(
    options: SliceCommandOptions,
    no_print_with_sharing: bool,
) -> CliResult<(ast::Problem, ast::Proof, ast::pool::Pool)> {
    let (problem, proof, _, mut pool) =
        parser::parse(get_input(&options.input)?, options.parsing.into_config())?;

    let sliced = {
        let (sliced_proof, sliced_asserts) = slice::slice(
            &proof,
            &options.from,
            &mut pool,
            options.max_distance.unwrap_or(0),
        )
        .ok_or(CliError::InvalidSliceId(options.from.clone()))?;

        // Write sliced problem and proof to output paths, if provided
        if let Some(files) = options.sliced_output {
            let (proof_filename, problem_filename) = (&files[0], &files[1]);
            File::create(problem_filename)
                .and_then(|mut f| {
                    f.write_all(format!("{}", problem.prelude).as_bytes())?;

                    let options = printer::DisplayOptions::new()
                        .use_sharing(false)
                        .sharing_prefix("p_".into())
                        .smt_lib_strict(true);
                    write!(f, "{}", printer::display_asserts(&sliced_asserts, options))?;
                    f.write_all(b"(check-sat)\n")?;
                    f.write_all(b"(exit)\n")
                })
                .map_err(|inner| carcara::Error::Io {
                    inner,
                    file: problem_filename.as_str().into(),
                })?;

            File::create(proof_filename)
                .and_then(|mut f| {
                    let options =
                        printer::DisplayOptions::new().use_sharing(!no_print_with_sharing);
                    write!(f, "{}", sliced_proof.display(options))?;
                    f.write_all(b"\n")
                })
                .map_err(|inner| carcara::Error::Io {
                    inner,
                    file: proof_filename.as_str().into(),
                })?;
        }

        sliced_proof
    };

    Ok((problem, sliced, pool))
}

fn generate_lia_problems_command(options: ParseCommandOptions, use_sharing: bool) -> CliResult<()> {
    use std::io::Write;

    let root_file_name = options.input.proof_file.clone();
    let instances = generate_lia_smt_instances(
        get_input(&options.input)?,
        options.parsing.into_config(),
        use_sharing,
    )?;
    for (id, content) in instances {
        let mut file_name = root_file_name.clone().into_os_string();
        file_name.push(format!("-{}.lia_smt2", id));
        let file_name = PathBuf::from(file_name);
        File::create(&file_name)
            .and_then(|mut f| write!(f, "{}", content))
            .map_err(|inner| carcara::Error::Io { inner, file: file_name })?;
    }

    Ok(())
}

// Translation-related commands.
fn translate_command(options: TranslateCommandOptions, use_sharing: bool) -> CliResult<()> {
    let (alethe_problem, mut alethe_proof, _, _) =
        parser::parse(get_input(&options.input)?, options.parsing.into_config())?;

    // NOTE: currently supporting only translation into Eunoia.
    match &options.target {
        TranslationTarget::Eunoia => translate_2_eunoia_command(
            &alethe_problem,
            &mut alethe_proof,
            &options.eunoia_mech,
            use_sharing,
        ),
    }
}

fn translate_2_eunoia_command(
    alethe_problem: &ast::Problem,
    proof: &mut Proof,
    eunoia_mech: &Path,
    use_sharing: bool,
) -> CliResult<()> {
    use translation::eunoia::DisplayEunoiaProof;

    let mut translator = translation::eunoia::alethe_2_eunoia::EunoiaTranslator::new(eunoia_mech);
    let eunoia_prelude = translator.translate_problem(alethe_problem);
    let eunoia_proof = translator.translate(proof);
    println!("{}", DisplayEunoiaProof(&eunoia_prelude, use_sharing));
    println!("{}", DisplayEunoiaProof(eunoia_proof, use_sharing));

    Ok(())
}

fn diff_from_error(error: &CliError) -> Option<diff::TermDiff> {
    use carcara::{
        checker::error::{CheckerError, EqualityError},
        elaborator::error::ElaborationError,
    };

    let error = match error {
        CliError::CarcaraError(carcara::Error::Checker { inner, .. }) => inner,
        CliError::CarcaraError(carcara::Error::Elaborator { inner, .. }) => match inner.as_ref() {
            ElaborationError::Checker(inner) => inner,
            _ => return None,
        },
        _ => return None,
    };

    match error {
        CheckerError::ReflexivityFailed(l, r)
        | CheckerError::SimplificationFailed { result: r, target: l, .. }
        | CheckerError::TermEquality(EqualityError::ExpectedEqual(l, r))
        | CheckerError::TermEquality(EqualityError::ExpectedToBe { expected: l, got: r })
        | CheckerError::RarePremiseAreNotEqual(l, r)
        | CheckerError::RareConclusionAreNotEqual(l, r) => Some(diff::diff(l, r)),
        _ => None,
    }
}

fn diff_command(options: DiffCommandOptions) -> CliResult<diff::TermDiff> {
    let problem = Source::file(&options.problem_file)?;
    let terms = Source::file_or_stdin(&options.terms_file)?;

    let mut pool = ast::pool::Pool::new();
    let mut parser = parser::Parser::new(&mut pool, options.parsing.into_config(), problem)?;
    let _ = parser.parse_problem()?; // We only parse the problem to get the definitions
    parser.reset(terms)?;
    let left = parser.parse_term()?;
    let right = parser.parse_term()?;
    Ok(diff::diff(&left, &right))
}
