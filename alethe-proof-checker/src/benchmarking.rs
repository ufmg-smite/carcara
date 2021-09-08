use crate::{checker, parser::parse_problem_proof};
use ahash::AHashMap;
use std::{
    fmt,
    fs::File,
    io::BufReader,
    path::PathBuf,
    time::{Duration, Instant},
};

#[derive(Debug)]
pub struct Metrics<K> {
    pub total: Duration,
    pub count: usize,
    pub mean: Duration,
    pub standard_deviation: Duration,
    pub max_min: Option<((K, Duration), (K, Duration))>,

    /// This is equal to the sum of the square distances of every sample to the mean, that is,
    /// `variance * (n - 1)`. This is used to calculate the standard deviation.
    sum_of_squared_distances: f64,
}

impl<K> Default for Metrics<K> {
    // Ideally, I would like to just `#[derive(Default)]`, but because of a quirk in how `derive`
    // works, that would require the type parameter `K` to always be `Default` as well, even though
    // it is not necessary. Therefore, I have to implement `Default` manually. For more info, see:
    // https://github.com/rust-lang/rust/issues/26925

    fn default() -> Self {
        Self {
            total: Duration::ZERO,
            count: 0,
            mean: Duration::ZERO,
            standard_deviation: Duration::ZERO,
            max_min: None,
            sum_of_squared_distances: 0.0,
        }
    }
}

impl<K: Clone> Metrics<K> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn max(&self) -> &(K, Duration) {
        &self.max_min.as_ref().unwrap().0
    }

    pub fn min(&self) -> &(K, Duration) {
        &self.max_min.as_ref().unwrap().1
    }

    /// Adds a new sample to the metrics. This updates all the fields of the struct to equal the
    /// new mean, standard deviation, etc. For simplicity, these are calculated every time a new
    /// sample is added, which means you can stop adding samples at any time and the metrics will
    /// always be valid.
    pub fn add(&mut self, key: &K, value: Duration) {
        let old_mean_f64 = self.mean.as_secs_f64();

        // Since the total is a `Duration`, which is represented using integers, we don't have to
        // worry about the numerical stability of calculating the mean like this
        self.total += value;
        self.count += 1;
        self.mean = self.total / self.count as u32;

        let new_mean_f64 = self.mean.as_secs_f64();

        // We calculate the new variance using Welford's algorithm. See:
        // https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Welford's_online_algorithm
        let variance_delta =
            (value.as_secs_f64() - new_mean_f64) * (value.as_secs_f64() - old_mean_f64);
        self.sum_of_squared_distances += variance_delta;
        self.standard_deviation = Duration::from_secs_f64(self.sum_of_squared_distances.sqrt())
            / std::cmp::max(1, self.count as u32 - 1);

        match &mut self.max_min {
            Some((max, min)) => {
                // If there are ties for `min` or `max`, we take the first value.
                if value > max.1 {
                    *max = (key.clone(), value);
                }
                if value < min.1 {
                    *min = (key.clone(), value);
                }
            }
            None => self.max_min = Some(((key.clone(), value), (key.clone(), value))),
        }
    }
}

#[cfg(test)]
#[test]
fn test_metrics() {
    use rand::Rng;

    fn run_tests(n: usize, max_value: u64) {
        let mut rng = rand::thread_rng();
        let mut data = Vec::with_capacity(n);
        let mut metrics = Metrics::new();
        for _ in 0..n {
            let sample = Duration::from_nanos(rng.gen_range(0..max_value));
            data.push(sample);
            metrics.add(&(), sample)
        }

        let expected_total: Duration = data.iter().sum();
        assert_eq!(expected_total, metrics.total);

        let expected_mean = expected_total / n as u32;
        assert_eq!(expected_mean, metrics.mean);

        let mean_f64 = expected_mean.as_secs_f64();
        let expected_std = Duration::from_secs_f64(
            data.iter()
                .map(|x| {
                    let diff = x.as_secs_f64() - mean_f64;
                    diff * diff
                })
                .sum::<f64>()
                .sqrt()
                / n as f64,
        );
        let delta =
            (expected_std.as_nanos() as i128 - metrics.standard_deviation.as_nanos() as i128).abs();
        assert!(delta < 2);

        let expected_max = data.iter().max().unwrap();
        let expected_min = data.iter().min().unwrap();
        assert_eq!(*expected_max, metrics.max().1);
        assert_eq!(*expected_min, metrics.min().1);
    }

    run_tests(100, 1_000);
    run_tests(10_000, 1_000);
    run_tests(1_000_000, 10);
    run_tests(1_000_000, 100);
    run_tests(1_000_000, 100_000);
}

impl<K> fmt::Display for Metrics<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} ± {:?}", self.mean, self.standard_deviation)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StepId {
    pub(crate) file: Box<str>,
    pub(crate) step_index: Box<str>,
    pub(crate) rule: Box<str>,
}

impl fmt::Display for StepId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{} ({})", self.file, self.step_index, self.rule)
    }
}

type RunId = (String, usize);

#[derive(Debug, Default)]
pub struct BenchmarkResults {
    parsing: Metrics<RunId>,
    checking: Metrics<RunId>,
    parsing_checking: Metrics<RunId>,
    total: Metrics<RunId>,
    pub(crate) step_time: Metrics<StepId>,
    pub(crate) step_time_by_file: AHashMap<String, Metrics<StepId>>,
    pub(crate) step_time_by_rule: AHashMap<String, Metrics<StepId>>,
}

impl BenchmarkResults {
    pub fn new() -> Self {
        Default::default()
    }

    /// The time per run to completely parse the proof.
    pub fn parsing(&self) -> &Metrics<RunId> {
        &self.parsing
    }

    /// The time per run to check all the steps in the proof.
    pub fn checking(&self) -> &Metrics<RunId> {
        &self.checking
    }

    /// The combined time per run to parse and check all the steps in the proof.
    pub fn parsing_checking(&self) -> &Metrics<RunId> {
        &self.parsing_checking
    }

    /// The total time spent per run. Should be pretty similar to `total_parsing_checking_time`.
    pub fn total(&self) -> &Metrics<RunId> {
        &self.total
    }

    /// The time spent checking each step.
    pub fn step_time(&self) -> &Metrics<StepId> {
        &self.step_time
    }

    /// For each file, the time spent checking each step in the file.
    pub fn step_time_by_file(&self) -> &AHashMap<String, Metrics<StepId>> {
        &self.step_time_by_file
    }

    /// For each rule, the time spent checking each step that uses that rule.
    pub fn step_time_by_rule(&self) -> &AHashMap<String, Metrics<StepId>> {
        &self.step_time_by_rule
    }
}

pub fn run_benchmark(
    instances: &[(PathBuf, PathBuf)],
    num_runs: usize,
) -> Result<BenchmarkResults, crate::Error> {
    let mut result = BenchmarkResults::new();
    for (problem_file, proof_file) in instances {
        let proof_file_name = proof_file.to_str().unwrap();

        for i in 0..num_runs {
            let total_time = Instant::now();
            let parsing_time = Instant::now();
            let (proof, pool) = parse_problem_proof(
                BufReader::new(File::open(problem_file)?),
                BufReader::new(File::open(proof_file)?),
            )?;
            let parsing_time = parsing_time.elapsed();

            let mut checking_time = Duration::ZERO;
            let config = checker::Config {
                skip_unknown_rules: false,
                allow_test_rule: false,
                statistics: Some(checker::CheckerStatistics {
                    file_name: proof_file_name,
                    checking_time: &mut checking_time,
                    step_time: &mut result.step_time,
                    step_time_by_file: &mut result.step_time_by_file,
                    step_time_by_rule: &mut result.step_time_by_rule,
                }),
            };
            let _ = checker::ProofChecker::new(pool, config).check(&proof)?;
            let total_time = total_time.elapsed();

            let run_id = (proof_file_name.to_string(), i);
            result.parsing.add(&run_id, parsing_time);
            result.checking.add(&run_id, checking_time);
            result
                .parsing_checking
                .add(&run_id, parsing_time + checking_time);
            result.total.add(&run_id, total_time);
        }
    }
    Ok(result)
}
