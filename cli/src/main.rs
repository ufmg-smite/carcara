mod app;
mod benchmarking;
mod error;
mod logger;
mod path_args;

use app::*;
use carcara::{
    ast::{self, rare_rules::Rules},
    benchmarking::OnlineBenchmarkResults,
    check, check_and_elaborate, check_parallel, generate_lia_smt_instances, parser, slice,
};
use error::{CliError, CliResult};
use path_args::{get_instances_from_paths, infer_problem_path};
use std::{
    fs::File,
    io::{self, IsTerminal, Read, Write},
    sync::atomic,
};

use clap::Parser;

fn main() {
    let cli = Cli::parse();
    let colors_enabled = !cli.no_color && std::io::stderr().is_terminal();

    ast::USE_SHARING_IN_TERM_DISPLAY.store(!cli.no_print_with_sharing, atomic::Ordering::Relaxed);

    logger::init(cli.log_level.into(), colors_enabled);

    let result = match cli.command {
        Command::Parse(options) => parse_command(options).and_then(|(pb, pf, _rules, mut pool)| {
            ast::print_proof(&mut pool, &pb.prelude, &pf, !cli.no_print_with_sharing)?;
            Ok(())
        }),
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
        Command::Elaborate(options) => {
            elaborate_command(options).and_then(|(res, pb, pf, mut pool)| {
                if res {
                    println!("holey");
                } else {
                    println!("valid");
                }
                ast::print_proof(&mut pool, &pb.prelude, &pf, !cli.no_print_with_sharing)?;
                Ok(())
            })
        }
        Command::Bench(options) => bench_command(options),
        Command::Slice(options) => {
            slice_command(options, cli.no_print_with_sharing).and_then(|(pb, pf, mut pool)| {
                ast::print_proof(&mut pool, &pb.prelude, &pf, !cli.no_print_with_sharing)?;
                Ok(())
            })
        }
        Command::GenerateLiaProblems(options) => {
            generate_lia_problems_command(options, !cli.no_print_with_sharing)
        }
    };
    if let Err(e) = result {
        log::error!("{}", e);
        std::process::exit(1);
    }
}

fn get_instance(options: &Input) -> CliResult<(String, String, Option<String>)> {
    use std::fs::read_to_string;

    let read_rare_file = || match &options.rare_file {
        Some(file) => read_to_string(file).map(Some),
        None => Ok(None),
    };

    let read_stdin = || -> Result<_, io::Error> {
        let mut buf = String::new();
        io::stdin().read_to_string(&mut buf)?;
        Ok(buf)
    };

    match (options.problem_file.as_deref(), options.proof_file.as_str()) {
        (Some("-"), "-") | (None, "-") => Err(CliError::BothFilesStdin),
        (Some(problem), "-") => {
            let rare_file = read_rare_file()?;
            Ok((read_to_string(problem)?, read_stdin()?, rare_file))
        }
        (Some("-"), proof) => {
            let rare_file = read_rare_file()?;
            Ok((read_stdin()?, read_to_string(proof)?, rare_file))
        }
        (Some(problem), proof) => {
            let rare_file = read_rare_file()?;
            Ok((read_to_string(problem)?, read_to_string(proof)?, rare_file))
        }
        (None, proof) => {
            let rare_file = read_rare_file()?;
            Ok((
                read_to_string(infer_problem_path(proof)?)?,
                read_to_string(proof)?,
                rare_file,
            ))
        }
    }
}

fn parse_command(
    options: ParseCommandOptions,
) -> CliResult<(ast::Problem, ast::Proof, Rules, ast::PrimitivePool)> {
    let (problem, proof, rules) = get_instance(&options.input)?;
    let result = parser::parse_instance(
        &problem,
        &proof,
        rules.as_deref(),
        options.parsing.into_config(),
    )?;
    Ok(result)
}

fn check_command(options: CheckCommandOptions) -> CliResult<bool> {
    let (problem, proof, rules) = get_instance(&options.input)?;
    let parser_config = options.parsing.into_config();
    let checker_config = (options.checking, options.tools).into_config();

    let collect_stats = options.stats.stats;
    if options.num_threads == 1 {
        check(
            &problem,
            &proof,
            rules.as_deref(),
            parser_config,
            checker_config,
            collect_stats,
        )
    } else {
        check_parallel(
            &problem,
            &proof,
            rules.as_deref(),
            parser_config,
            checker_config,
            collect_stats,
            options.num_threads,
            options.stack.stack_size,
        )
    }
    .map_err(Into::into)
}

fn elaborate_command(
    options: ElaborateCommandOptions,
) -> CliResult<(bool, ast::Problem, ast::Proof, ast::PrimitivePool)> {
    let (problem, proof, rules) = get_instance(&options.input)?;

    let checker_config = (options.checking, options.tools.clone()).into_config();
    let (elab_config, pipeline) = (options.elaboration, options.tools).into_config();

    check_and_elaborate(
        &problem,
        &proof,
        rules.as_deref(),
        options.parsing.into_config(),
        checker_config,
        elab_config,
        pipeline,
        options.stats.stats,
    )
    .map_err(CliError::CarcaraError)
}

fn bench_command(options: BenchCommandOptions) -> CliResult<()> {
    let instances = get_instances_from_paths(options.files.iter().map(|s| s.as_str()))?;
    if instances.is_empty() {
        log::warn!("no files passed");
        return Ok(());
    }

    log::info!(
        "running benchmark on {} files, doing {} runs each",
        instances.len(),
        options.num_runs
    );

    let checker_config = (options.checking, options.tools.clone()).into_config();
    let (elab_config, pipeline) = (options.elaboration, options.tools).into_config();

    if options.dump_to_csv {
        benchmarking::run_csv_benchmark(
            &instances,
            options.num_runs,
            options.num_jobs,
            options.parsing.into_config(),
            checker_config,
            options.elaborate.then_some((elab_config, pipeline)),
            &mut File::create("runs.csv")?,
            &mut File::create("steps.csv")?,
        )?;
        return Ok(());
    }

    let results: OnlineBenchmarkResults = benchmarking::run_benchmark(
        &instances,
        options.num_runs,
        options.num_jobs,
        options.parsing.into_config(),
        checker_config,
        options.elaborate.then_some((elab_config, pipeline)),
    );
    if results.is_empty() {
        println!("no benchmark data collected");
        return Ok(());
    }

    if results.had_error {
        println!("invalid");
    } else if results.is_holey {
        println!("holey");
    } else {
        println!("valid");
    }
    results.print(options.sort_by_total);
    Ok(())
}

fn slice_command(
    options: SliceCommandOptions,
    no_print_with_sharing: bool,
) -> CliResult<(ast::Problem, ast::Proof, ast::PrimitivePool)> {
    use std::fs;
    let (problem, proof, rules) = get_instance(&options.input)?;
    let (problem, proof, _, mut pool) = parser::parse_instance(
        &problem,
        &proof,
        rules.as_deref(),
        options.parsing.into_config(),
    )?;

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
            let (sliced_proof_file_name, sliced_problem_file_name) = (&files[0], &files[1]);
            let mut sliced_problem_file = fs::File::create(sliced_problem_file_name)?;
            sliced_problem_file
                .write_all(format!("{}", problem.prelude).as_bytes())
                .unwrap();
            ast::write_asserts(
                &mut pool,
                &problem.prelude,
                &mut sliced_problem_file,
                &sliced_asserts,
                false,
            )?;
            sliced_problem_file.write_all(b"(check-sat)\n")?;
            sliced_problem_file.write_all(b"(exit)\n")?;

            let mut sliced_proof_file = fs::File::create(sliced_proof_file_name)?;
            ast::write_proof_to_dest(
                &mut pool,
                &problem.prelude,
                &sliced_proof,
                &mut sliced_proof_file,
                !no_print_with_sharing,
            )?;
            sliced_proof_file.write_all(b"\n")?;
        }

        sliced_proof
    };

    Ok((problem, sliced, pool))
}

fn generate_lia_problems_command(options: ParseCommandOptions, use_sharing: bool) -> CliResult<()> {
    use std::io::Write;

    let root_file_name = options.input.proof_file.clone();
    let (problem, proof, rules) = get_instance(&options.input)?;

    let instances = generate_lia_smt_instances(
        &problem,
        &proof,
        rules.as_deref(),
        options.parsing.into_config(),
        use_sharing,
    )?;
    for (id, content) in instances {
        let file_name = format!("{}-{}.lia_smt2", root_file_name, id);
        let mut f = File::create(file_name)?;
        write!(f, "{}", content)?;
    }

    Ok(())
}
