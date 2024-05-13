use super::{Duration, Metrics, MetricsUnit, OfflineMetrics, OnlineMetrics};
use rand::{prelude::ThreadRng, Rng};
use std::fmt;

trait IsClose {
    fn is_close(&self, other: Self) -> bool;
}

macro_rules! assert_is_close {
    ($a:expr, $b:expr $(,)?) => {
        assert!(($a).is_close($b), "{:?} != {:?}", $a, $b)
    };
}

impl IsClose for Duration {
    fn is_close(&self, other: Self) -> bool {
        self.absolute_diff(other).as_nanos() <= 2
    }
}

impl IsClose for f64 {
    fn is_close(&self, other: Self) -> bool {
        const EPSILON: f64 = 1.0e-6;
        (*self - other).abs() < EPSILON
    }
}

impl IsClose for usize {
    fn is_close(&self, other: Self) -> bool {
        *self == other
    }
}

fn usize_generator(max_value: usize) -> impl Fn(&mut ThreadRng) -> usize {
    move |rng| rng.gen_range(0..max_value)
}

fn duration_generator(max_value: u64) -> impl Fn(&mut ThreadRng) -> Duration {
    move |rng| Duration::from_nanos(rng.gen_range(0..max_value))
}

fn f64_generator(max_value: f64) -> impl Fn(&mut ThreadRng) -> f64 {
    move |rng| rng.gen_range(0.0..max_value)
}

#[test]
fn test_metrics_add() {
    fn run_tests<T, F>(n: usize, get_random: F)
    where
        T: MetricsUnit + fmt::Debug + PartialEq + IsClose,
        T::MeanType: fmt::Debug + IsClose,
        F: Fn(&mut ThreadRng) -> T,
    {
        let mut rng = rand::thread_rng();
        let mut offline = OfflineMetrics::new();
        let mut online = OnlineMetrics::new();

        for _ in 0..n {
            let sample = get_random(&mut rng);
            offline.add_sample(&(), sample);
            online.add_sample(&(), sample);
        }

        assert_is_close!(offline.total(), online.total());
        assert_is_close!(offline.mean(), online.mean());
        assert_is_close!(offline.standard_deviation(), online.standard_deviation());

        assert_is_close!(offline.min().1, online.min().1);
        assert_is_close!(offline.max().1, online.max().1);
    }

    run_tests(100, duration_generator(1_000));
    run_tests(10_000, duration_generator(1_000));
    run_tests(1_000_000, duration_generator(10));
    run_tests(1_000_000, duration_generator(100));
    run_tests(1_000_000, duration_generator(100_000));

    run_tests(100, f64_generator(1_000.0));
    run_tests(10_000, f64_generator(1_000.0));
    run_tests(1_000_000, f64_generator(10.0));
    run_tests(1_000_000, f64_generator(100.0));
    run_tests(1_000_000, f64_generator(100_000.0));

    run_tests(100, usize_generator(1_000));
    run_tests(10_000, usize_generator(1_000));
    run_tests(1_000_000, usize_generator(10));
    run_tests(1_000_000, usize_generator(100));
    run_tests(1_000_000, usize_generator(100_000));
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

        assert_eq!(combined_metrics.total(), overall_metrics.total());
        assert_eq!(combined_metrics.count(), overall_metrics.count());
        assert_eq!(combined_metrics.mean(), overall_metrics.mean());

        // Instead of comparing the standard deviations directly, we compare the
        // `sum_of_squared_distances`, since it is (in theory) more accurate
        let delta =
            combined_metrics.sum_of_squared_distances - overall_metrics.sum_of_squared_distances;
        let error = delta.abs() / overall_metrics.sum_of_squared_distances;
        assert!(error < error_margin, "{} ({})", error, num_chunks);

        assert_eq!(combined_metrics.max(), overall_metrics.max());
        assert_eq!(combined_metrics.min(), overall_metrics.min());
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
