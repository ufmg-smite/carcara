use crate::{checker, parser::parse_problem_proof};
use std::{
    fs::File,
    io::BufReader,
    time::{Duration, Instant},
};

#[derive(Debug)]
pub struct Metrics<K> {
    pub total: Duration,
    pub count: usize,
    pub mean: Duration,
    pub standard_deviation: Duration,
    pub max: (K, Duration),
    pub min: (K, Duration),
}

impl<K: Clone> Metrics<K> {
    pub fn new(data: &[(K, Duration)]) -> Option<Self> {
        if data.is_empty() {
            return None;
        }

        let count = data.len();
        let total = data.iter().map(|(_, x)| x).sum();
        let mean: Duration = total / count as u32;

        // To calculate the standard deviation, we need to convert the `Duration`s into `f64`s and
        // back, which might result in some loss of precision
        let mean_f64 = mean.as_secs_f64();
        let variance: f64 = data
            .iter()
            .map(|&(_, x)| {
                let diff = x.as_secs_f64() - mean_f64;
                diff * diff
            })
            .sum();
        let standard_deviation = Duration::from_secs_f64(variance.sqrt());

        let max = data.iter().max_by_key(|(_, x)| x).unwrap().clone();
        let min = data.iter().min_by_key(|(_, x)| x).unwrap().clone();

        Some(Self {
            total,
            count,
            mean,
            standard_deviation,
            max,
            min,
        })
    }
}

// TODO: Store run index in run measurement
#[derive(Debug)]
pub struct CheckerRunMeasurement {
    proof_file_name: String,
    parsing_time: Duration,
    step_measurements: Vec<StepMeasurement>,
}

#[derive(Debug)]
pub struct StepMeasurement {
    pub(crate) step_index: String,
    pub(crate) rule: String,
    pub(crate) time: Duration,
}

pub fn run_benchmark(
    instances: &[(&str, &str)],
    num_runs: usize,
) -> Result<Vec<CheckerRunMeasurement>, crate::Error> {
    let mut runs = Vec::new();
    for &(problem_file, proof_file) in instances {
        for _ in 0..num_runs {
            let parsing_time = Instant::now();
            let (proof, pool) = parse_problem_proof(
                BufReader::new(File::open(problem_file)?),
                BufReader::new(File::open(proof_file)?),
            )?;
            let parsing_time = parsing_time.elapsed();

            let mut step_measurements = Vec::new();
            let config = checker::Config {
                skip_unknown_rules: false,
                allow_test_rule: false,
                statistics: Some(&mut step_measurements),
            };
            let _ = checker::ProofChecker::new(pool, config).check(&proof)?;
            runs.push(CheckerRunMeasurement {
                proof_file_name: proof_file.to_string(),
                parsing_time,
                step_measurements,
            })
        }
    }
    Ok(runs)
}

pub mod compile_measurements {
    use super::*;

    pub fn total_parsing_time(runs: &[CheckerRunMeasurement]) -> Metrics<String> {
        Metrics::new(
            runs.iter()
                .map(|m| (m.proof_file_name.clone(), m.parsing_time))
                .collect::<Vec<_>>()
                .as_slice(),
        )
        .unwrap()
    }

    pub fn total_checking_time(runs: &[CheckerRunMeasurement]) -> Metrics<String> {
        Metrics::new(
            runs.iter()
                .map(|m| {
                    let checking_time = m.step_measurements.iter().map(|s| s.time).sum();
                    (m.proof_file_name.clone(), checking_time)
                })
                .collect::<Vec<_>>()
                .as_slice(),
        )
        .unwrap()
    }

    pub fn total_time(runs: &[CheckerRunMeasurement]) -> Metrics<String> {
        Metrics::new(
            runs.iter()
                .map(|m| {
                    let total_time =
                        m.parsing_time + m.step_measurements.iter().map(|s| s.time).sum();
                    (m.proof_file_name.clone(), total_time)
                })
                .collect::<Vec<_>>()
                .as_slice(),
        )
        .unwrap()
    }
}
