use ahash::AHashMap;
use std::{
    cmp, fmt,
    iter::Sum,
    ops::{Add, AddAssign, Sub},
    time::Duration,
};

pub trait MetricsUnit:
    Copy + Default + PartialOrd + Add<Output = Self> + AddAssign + Sum + Sub<Output = Self>
{
    type MeanType: MetricsUnit;

    fn as_f64(&self) -> f64;
    fn from_f64(x: f64) -> Self::MeanType;
    fn div_u32(self, rhs: u32) -> Self::MeanType;
}

impl MetricsUnit for Duration {
    type MeanType = Self;

    fn as_f64(&self) -> f64 {
        self.as_secs_f64()
    }

    fn from_f64(x: f64) -> Self::MeanType {
        Self::from_secs_f64(x)
    }

    fn div_u32(self, rhs: u32) -> Self::MeanType {
        self / rhs
    }
}

impl MetricsUnit for f64 {
    type MeanType = Self;

    fn as_f64(&self) -> f64 {
        *self
    }

    fn from_f64(x: f64) -> Self::MeanType {
        x
    }

    fn div_u32(self, rhs: u32) -> Self::MeanType {
        self / (rhs as f64)
    }
}

impl MetricsUnit for usize {
    type MeanType = f64;

    fn as_f64(&self) -> f64 {
        *self as f64
    }

    fn from_f64(x: f64) -> Self::MeanType {
        x
    }

    fn div_u32(self, rhs: u32) -> Self::MeanType {
        (self / rhs as usize) as Self::MeanType
    }
}

pub trait Metrics<K, T: MetricsUnit> {
    fn add_sample(&mut self, key: &K, value: T);
    fn combine(self, other: Self) -> Self;
    fn is_empty(&self) -> bool;

    fn max(&self) -> &(K, T);
    fn min(&self) -> &(K, T);
    fn total(&self) -> T;
    fn count(&self) -> usize;
    fn mean(&self) -> T::MeanType;
    fn standard_deviation(&self) -> T::MeanType;
}

#[derive(Debug)]
pub struct OnlineMetrics<K, T: MetricsUnit = Duration> {
    total: T,
    count: usize,
    mean: T::MeanType,
    standard_deviation: T::MeanType,
    max_min: Option<((K, T), (K, T))>,

    /// This is equal to the sum of the square distances of every sample to the mean, that is,
    /// `variance * (n - 1)`. This is used to calculate the standard deviation.
    sum_of_squared_distances: f64,
}

impl<K, T: MetricsUnit> OnlineMetrics<K, T> {
    pub fn new() -> Self {
        Default::default()
    }
}

impl<K, T: MetricsUnit> Default for OnlineMetrics<K, T> {
    // Ideally, I would like to just `#[derive(Default)]`, but because of a quirk in how `derive`
    // works, that would require the type parameter `K` to always be `Default` as well, even though
    // it is not necessary. Therefore, I have to implement `Default` manually. For more info, see:
    // https://github.com/rust-lang/rust/issues/26925

    fn default() -> Self {
        Self {
            total: T::default(),
            count: 0,
            mean: T::MeanType::default(),
            standard_deviation: T::MeanType::default(),
            max_min: None,
            sum_of_squared_distances: 0.0,
        }
    }
}

impl<K: Clone, T: MetricsUnit> Metrics<K, T> for OnlineMetrics<K, T> {
    /// Adds a new sample to the metrics. This updates all the fields of the struct to equal the
    /// new mean, standard deviation, etc. For simplicity, these are calculated every time a new
    /// sample is added, which means you can stop adding samples at any time and the metrics will
    /// always be valid.
    fn add_sample(&mut self, key: &K, value: T) {
        let old_mean_f64 = self.mean.as_f64();

        self.total += value;
        self.count += 1;
        self.mean = self.total.div_u32(self.count as u32);

        let new_mean_f64 = self.mean.as_f64();

        // We calculate the new variance using Welford's algorithm. See:
        // https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Welford's_online_algorithm
        let variance_delta = (value.as_f64() - new_mean_f64) * (value.as_f64() - old_mean_f64);
        self.sum_of_squared_distances += variance_delta;
        let count = cmp::max(2, self.count) - 1;
        self.standard_deviation = T::from_f64(self.sum_of_squared_distances.sqrt() / count as f64);

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

    /// Combines two metrics into one. If one the metrics has only one data point, this is
    /// equivalent to `Metrics::add_sample`. This is generally numerically stable if the metrics
    /// have many data points, or exactly one. If one of the metrics is small, the error in the
    /// variance introduced by using this method (as opposed to using `Metrics::add_sample` on each
    /// data point) can be as high as 30%.
    fn combine(self, other: Self) -> Self {
        match (self.count, other.count) {
            (0, _) => return other,
            (_, 0) => return self,
            (1, _) => {
                let mut result = other;
                let only_entry = self.min();
                result.add_sample(&only_entry.0, only_entry.1);
                return result;
            }
            (_, 1) => return other.combine(self),
            _ => (),
        }
        let total = self.total + other.total;
        let count = self.count + other.count;
        let mean = total.div_u32(count as u32);

        // To combine the two variances, we use a generalization of Welford's algorithm. See:
        // https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Parallel_algorithm
        let delta = other.mean.as_f64() - self.mean.as_f64();
        let sum_of_squared_distances = self.sum_of_squared_distances
            + other.sum_of_squared_distances
            + delta * delta * (self.count * other.count / count) as f64;
        let standard_deviation =
            T::from_f64(sum_of_squared_distances.sqrt() / (cmp::max(2, count) - 1) as f64);

        let max_min = match (self.max_min, other.max_min) {
            (a, None) => a,
            (None, b) => b,
            (Some((a_max, a_min)), Some((b_max, b_min))) => {
                let max = if a_max.1 > b_max.1 { a_max } else { b_max };
                let min = if a_min.1 < b_min.1 { a_min } else { b_min };
                Some((max, min))
            }
        };

        Self {
            total,
            count,
            mean,
            standard_deviation,
            max_min,
            sum_of_squared_distances,
        }
    }

    fn is_empty(&self) -> bool {
        self.count == 0
    }

    fn max(&self) -> &(K, T) {
        &self.max_min.as_ref().unwrap().0
    }

    fn min(&self) -> &(K, T) {
        &self.max_min.as_ref().unwrap().1
    }

    fn total(&self) -> T {
        self.total
    }

    fn count(&self) -> usize {
        self.count
    }

    fn mean(&self) -> T::MeanType {
        self.mean
    }

    fn standard_deviation(&self) -> T::MeanType {
        self.standard_deviation
    }
}

impl<K> fmt::Display for OnlineMetrics<K, Duration> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:?} ({:?} * {})", self.total, self.mean, self.count)
        } else {
            write!(f, "{:?} ± {:?}", self.mean, self.standard_deviation)
        }
    }
}

impl<K> fmt::Display for OnlineMetrics<K, f64> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:.04} ({:.04} * {})", self.total, self.mean, self.count)
        } else {
            write!(f, "{:.04} ± {:.04}", self.mean, self.standard_deviation)
        }
    }
}

pub struct OfflineMetrics<K, T = Duration> {
    data: Vec<(K, T)>,
}

impl<K, T: MetricsUnit> OfflineMetrics<K, T> {
    pub fn new() -> Self {
        Default::default()
    }
}

impl<K, T: MetricsUnit> Default for OfflineMetrics<K, T> {
    fn default() -> Self {
        Self { data: Vec::new() }
    }
}

impl<K: Clone, T: MetricsUnit> Metrics<K, T> for OfflineMetrics<K, T> {
    fn add_sample(&mut self, key: &K, value: T) {
        self.data.push((key.clone(), value));
    }

    fn combine(mut self, mut other: Self) -> Self {
        self.data.append(&mut other.data);
        self
    }

    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    fn max(&self) -> &(K, T) {
        self.data
            .iter()
            .max_by(|a, b| PartialOrd::partial_cmp(&a.1, &b.1).unwrap_or(cmp::Ordering::Equal))
            .unwrap()
    }

    fn min(&self) -> &(K, T) {
        self.data
            .iter()
            .min_by(|a, b| PartialOrd::partial_cmp(&a.1, &b.1).unwrap_or(cmp::Ordering::Equal))
            .unwrap()
    }

    fn total(&self) -> T {
        self.data.iter().map(|(_, v)| *v).sum()
    }

    fn count(&self) -> usize {
        self.data.len()
    }

    fn mean(&self) -> T::MeanType {
        self.total().div_u32(self.count() as u32)
    }

    fn standard_deviation(&self) -> T::MeanType {
        let mean = self.mean();
        let sum_of_squared_distances: f64 = self
            .data
            .iter()
            .map(|&(_, v)| {
                let delta = v.as_f64() - mean.as_f64();
                delta * delta
            })
            .sum();
        let variance = sum_of_squared_distances / (cmp::max(2, self.count()) - 1) as f64;
        T::from_f64(variance.sqrt())
    }
}

#[derive(Debug, Default)]
pub struct NullMetrics;

fn null_metrics_panic() -> ! {
    panic!("trying to extract data from null metrics")
}

impl<K: Clone, T: MetricsUnit> Metrics<K, T> for NullMetrics {
    fn add_sample(&mut self, _: &K, _: T) {}

    fn combine(self, _: Self) -> Self {
        self
    }

    fn is_empty(&self) -> bool {
        true
    }

    fn max(&self) -> &(K, T) {
        null_metrics_panic()
    }

    fn min(&self) -> &(K, T) {
        null_metrics_panic()
    }

    fn total(&self) -> T {
        null_metrics_panic()
    }

    fn count(&self) -> usize {
        null_metrics_panic()
    }

    fn mean(&self) -> T::MeanType {
        null_metrics_panic()
    }

    fn standard_deviation(&self) -> T::MeanType {
        null_metrics_panic()
    }
}

fn combine_map<K, V, M>(mut a: AHashMap<String, M>, b: AHashMap<String, M>) -> AHashMap<String, M>
where
    V: MetricsUnit,
    M: Metrics<K, V> + Default,
{
    use std::collections::hash_map::Entry;
    for (k, v) in b {
        match a.entry(k) {
            Entry::Occupied(mut e) => {
                // To take the old value from the entry without moving it entirely, we have
                // to insert something in its place, so we insert an empty `M`
                let old = e.insert(M::default());
                e.insert(old.combine(v));
            }
            Entry::Vacant(e) => {
                e.insert(v);
            }
        }
    }
    a
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StepId {
    pub(crate) file: Box<str>,
    pub(crate) step_id: Box<str>,
    pub(crate) rule: Box<str>,
}

impl fmt::Display for StepId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{} ({})", self.file, self.step_id, self.rule)
    }
}

type RunId = (String, usize);

// Higher kinded types would be very useful here. Ideally, I would like `BenchmarkResults` to be
// generic on any kind that implements `Metrics`, like `OnlineMetrics` or `OfflineMetrics`.
#[derive(Debug, Default)]
pub struct BenchmarkResults<ByRun, ByStep, ByRunF64> {
    pub parsing: ByRun,
    pub checking: ByRun,
    pub reconstructing: ByRun,
    pub total_accounted_for: ByRun,
    pub total: ByRun,
    pub step_time: ByStep,
    pub step_time_by_file: AHashMap<String, ByStep>,
    pub step_time_by_rule: AHashMap<String, ByStep>,

    pub deep_eq_time: ByRun,
    pub deep_eq_time_ratio: ByRunF64,
    pub assume_time: ByRun,
    pub assume_time_ratio: ByRunF64,
    pub num_assumes: usize,
    pub num_easy_assumes: usize,
    pub deep_eq_depths: Vec<usize>,
}

pub type OnlineBenchmarkResults =
    BenchmarkResults<OnlineMetrics<RunId>, OnlineMetrics<StepId>, OnlineMetrics<RunId, f64>>;

pub type OfflineBenchmarkResults =
    BenchmarkResults<OfflineMetrics<RunId>, OfflineMetrics<StepId>, OfflineMetrics<RunId, f64>>;

impl<ByRun, ByStep, ByRunF64> BenchmarkResults<ByRun, ByStep, ByRunF64>
where
    ByRun: Metrics<RunId, Duration> + Default,
    ByStep: Metrics<StepId, Duration> + Default,
    ByRunF64: Metrics<RunId, f64> + Default,
{
    pub fn new() -> Self {
        Default::default()
    }

    /// Return `true` if the results have no entries.
    pub fn is_empty(&self) -> bool {
        self.total.is_empty()
    }

    /// The time per run to completely parse the proof.
    pub fn parsing(&self) -> &ByRun {
        &self.parsing
    }

    /// The time per run to check all the steps in the proof.
    pub fn checking(&self) -> &ByRun {
        &self.checking
    }

    /// The time per run to reconstruct the proof.
    pub fn reconstructing(&self) -> &ByRun {
        &self.reconstructing
    }

    /// The combined time per run to parse, check, and reconstruct all the steps in the proof.
    pub fn total_accounted_for(&self) -> &ByRun {
        &self.total_accounted_for
    }

    /// The total time spent per run. Should be pretty similar to `total_accounted_for`.
    pub fn total(&self) -> &ByRun {
        &self.total
    }

    /// The time spent checking each step.
    pub fn step_time(&self) -> &ByStep {
        &self.step_time
    }

    /// For each file, the time spent checking each step in the file.
    pub fn step_time_by_file(&self) -> &AHashMap<String, ByStep> {
        &self.step_time_by_file
    }

    /// For each rule, the time spent checking each step that uses that rule.
    pub fn step_time_by_rule(&self) -> &AHashMap<String, ByStep> {
        &self.step_time_by_rule
    }

    /// Combines two `BenchmarkResults` into one. This method is subject to some numerical
    /// stability issues, as is described in `Metrics::combine`.
    pub fn combine(a: Self, b: Self) -> Self {
        Self {
            parsing: a.parsing.combine(b.parsing),
            checking: a.checking.combine(b.checking),
            reconstructing: a.reconstructing.combine(b.reconstructing),
            total_accounted_for: a.total_accounted_for.combine(b.total_accounted_for),
            total: a.total.combine(b.total),
            step_time: a.step_time.combine(b.step_time),
            step_time_by_file: combine_map(a.step_time_by_file, b.step_time_by_file),
            step_time_by_rule: combine_map(a.step_time_by_rule, b.step_time_by_rule),

            deep_eq_time: a.deep_eq_time.combine(b.deep_eq_time),
            deep_eq_time_ratio: a.deep_eq_time_ratio.combine(b.deep_eq_time_ratio),
            assume_time: a.assume_time.combine(b.assume_time),
            assume_time_ratio: a.assume_time_ratio.combine(b.assume_time_ratio),
            num_assumes: a.num_assumes + b.num_assumes,
            num_easy_assumes: a.num_easy_assumes + b.num_easy_assumes,

            deep_eq_depths: {
                let mut result = a.deep_eq_depths;
                result.extend(b.deep_eq_depths);
                result
            },
        }
    }
}

pub trait CollectResults {
    fn add_step_measurement(&mut self, file: &str, step_id: &str, rule: &str, time: Duration);
    fn add_assume_measurement(&mut self, file: &str, id: &str, is_easy: bool, time: Duration);
    fn add_deep_eq_depth(&mut self, depth: usize);
}

impl<ByRun, ByStep, ByRunF64> CollectResults for BenchmarkResults<ByRun, ByStep, ByRunF64>
where
    ByRun: Metrics<RunId, Duration> + Default,
    ByStep: Metrics<StepId, Duration> + Default,
    ByRunF64: Metrics<RunId, f64> + Default,
{
    fn add_step_measurement(&mut self, file: &str, step_id: &str, rule: &str, time: Duration) {
        let file = file.to_owned();
        let rule = rule.to_owned();
        let id = StepId {
            file: file.clone().into_boxed_str(),
            step_id: step_id.into(),
            rule: rule.clone().into_boxed_str(),
        };
        self.step_time.add_sample(&id, time);
        self.step_time_by_file
            .entry(file)
            .or_default()
            .add_sample(&id, time);
        self.step_time_by_rule
            .entry(rule)
            .or_default()
            .add_sample(&id, time);
    }

    fn add_assume_measurement(&mut self, file: &str, id: &str, is_easy: bool, time: Duration) {
        self.num_assumes += 1;
        self.num_easy_assumes += is_easy as usize;
        self.add_step_measurement(file, id, "assume*", time);
    }

    fn add_deep_eq_depth(&mut self, depth: usize) {
        self.deep_eq_depths.push(depth);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn test_metrics_add() {
        fn run_tests(n: usize, max_value: u64) {
            let mut rng = rand::thread_rng();
            let mut data = Vec::with_capacity(n);
            let mut metrics = OnlineMetrics::new();
            for _ in 0..n {
                let sample = Duration::from_nanos(rng.gen_range(0..max_value));
                data.push(sample);
                metrics.add_sample(&(), sample);
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
            let delta = (expected_std.as_nanos() as i128
                - metrics.standard_deviation.as_nanos() as i128)
                .abs();
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

    #[test]
    fn test_metrics_combine() {
        fn run_tests(num_chunks: usize, chunk_size: usize, error_margin: f64) {
            let mut rng = rand::thread_rng();
            let mut overall_metrics = OnlineMetrics::new();
            let mut combined_metrics = OnlineMetrics::new();
            for _ in 0..num_chunks {
                let mut chunk_metrics = OnlineMetrics::new();
                for _ in 0..chunk_size {
                    let sample = Duration::from_nanos(rng.gen_range(0..10_000));
                    overall_metrics.add_sample(&(), sample);
                    chunk_metrics.add_sample(&(), sample);
                }
                combined_metrics = combined_metrics.combine(chunk_metrics);
            }

            assert_eq!(combined_metrics.total, overall_metrics.total);
            assert_eq!(combined_metrics.count, overall_metrics.count);
            assert_eq!(combined_metrics.mean, overall_metrics.mean);

            // Instead of comparing the standard deviations directly, we compare the
            // `sum_of_squared_distances`, since it is (in theory) more accurate
            let delta = combined_metrics.sum_of_squared_distances
                - overall_metrics.sum_of_squared_distances;
            let error = delta.abs() / overall_metrics.sum_of_squared_distances;
            assert!(error < error_margin, "{} ({})", error, num_chunks);

            assert_eq!(combined_metrics.max_min, overall_metrics.max_min);
        }

        // Depending on how big the chunks are, the numerical error may be bigger or smaller. For a
        // small number of very large chunks, the error margin is pretty low
        run_tests(100, 10_000, 1.0e-5);
        run_tests(100, 1_000, 1.0e-5);

        // As the chunks get smaller, the error increases rapidly
        run_tests(1_000, 100, 0.0001);
        run_tests(1_000, 50, 0.001);
        run_tests(10_000, 10, 0.02);
        run_tests(10_000, 5, 0.05);
        run_tests(10_000, 2, 0.3); // The worst case happens when the chunk size is 2

        // When the chunks are only one data entry in size, `Metrics::combine` simply calls
        // `Metrics::add` with that entry, which makes the numerical error small again
        run_tests(10_000, 1, 1.0e-6);
    }
}
