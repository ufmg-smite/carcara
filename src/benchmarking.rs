use crate::{checker, parser::parse_problem_proof};
use std::{
    fmt,
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
        let variance = variance / std::cmp::max(1, count - 1) as f64;
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

impl<K> fmt::Display for Metrics<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} ± {:?}", self.mean, self.standard_deviation)
    }
}

#[derive(Debug)]
pub struct CheckerRunMeasurement {
    proof_file_name: String,
    run_index: usize,
    parsing_time: Duration,
    step_measurements: Vec<StepMeasurement>,
    total_time: Duration,
}

#[derive(Debug)]
pub struct StepMeasurement {
    pub(crate) step_index: String,
    pub(crate) rule: String,
    pub(crate) time: Duration,
}

pub fn run_benchmark(
    instances: &[(String, String)],
    num_runs: usize,
) -> Result<Vec<CheckerRunMeasurement>, crate::Error> {
    let mut runs = Vec::new();
    for (problem_file, proof_file) in instances {
        for i in 0..num_runs {
            let total_time = Instant::now();
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
            let total_time = total_time.elapsed();
            runs.push(CheckerRunMeasurement {
                proof_file_name: proof_file.to_string(),
                run_index: i,
                parsing_time,
                step_measurements,
                total_time,
            })
        }
    }
    Ok(runs)
}

pub mod compile_measurements {
    use super::*;
    use ahash::AHashMap;

    type Runs<'a> = &'a [CheckerRunMeasurement];

    /// For each rule, reports the time taken to check each step of each file that uses that rule.
    pub fn by_rule(runs: Runs) -> AHashMap<String, Metrics<(String, String)>> {
        let mut data_by_rule = AHashMap::new();
        for measurement in runs {
            for s in &measurement.step_measurements {
                let entry = data_by_rule.entry(s.rule.clone()).or_insert_with(Vec::new);
                entry.push((
                    (measurement.proof_file_name.clone(), s.step_index.clone()),
                    s.time,
                ));
            }
        }
        data_by_rule
            .into_iter()
            .filter_map(|(k, v)| Some((k, Metrics::new(&v)?)))
            .collect()
    }

    fn aggregate_by_run_index(
        runs: Runs,
        key: fn(&CheckerRunMeasurement) -> (usize, Duration),
    ) -> Metrics<usize> {
        Metrics::new(runs.iter().map(key).collect::<Vec<_>>().as_slice()).unwrap()
    }

    /// The time per run to completely parse the proof.
    pub fn parsing_time(runs: Runs) -> Metrics<usize> {
        aggregate_by_run_index(runs, |m| (m.run_index, m.parsing_time))
    }

    /// The time per run to check all the steps in the proof.
    pub fn checking_time(runs: Runs) -> Metrics<usize> {
        aggregate_by_run_index(runs, |m| {
            let checking_time = m.step_measurements.iter().map(|s| s.time).sum();
            (m.run_index, checking_time)
        })
    }

    /// The combined time per run to parse and check all the steps in the proof.
    pub fn parsing_checking_time(runs: Runs) -> Metrics<usize> {
        aggregate_by_run_index(runs, |m| {
            let parsing_checking_time =
                m.parsing_time + m.step_measurements.iter().map(|s| s.time).sum();
            (m.run_index, parsing_checking_time)
        })
    }

    /// The total time per run. Should be pretty similar to `total_parsing_checking_time`.
    pub fn total_time(runs: Runs) -> Metrics<usize> {
        aggregate_by_run_index(runs, |m| (m.run_index, m.total_time))
    }
}
