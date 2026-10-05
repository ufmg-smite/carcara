use super::{Duration, Metrics, MetricsUnit};
use rand::{RngExt, prelude::ThreadRng};
use std::{cmp, fmt};

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
    move |rng| rng.random_range(0..max_value)
}

fn duration_generator(max_value: u64) -> impl Fn(&mut ThreadRng) -> Duration {
    move |rng| Duration::from_nanos(rng.random_range(0..max_value))
}

fn f64_generator(max_value: f64) -> impl Fn(&mut ThreadRng) -> f64 {
    move |rng| rng.random_range(0.0..max_value)
}

#[test]
fn test_metrics_add() {
    fn run_tests<T, F>(n: usize, get_random: F)
    where
        T: MetricsUnit + fmt::Debug + PartialEq + IsClose,
        T::MeanType: fmt::Debug + IsClose,
        F: Fn(&mut ThreadRng) -> T,
    {
        let mut rng = rand::rng();
        let mut metrics = Metrics::new();
        let mut samples = Vec::with_capacity(n);

        for _ in 0..n {
            let sample = get_random(&mut rng);
            metrics.add_sample(&(), sample);
            samples.push(sample);
        }

        // Compute the expected statistics directly from the stored samples.
        let expected_total: T = samples.iter().copied().sum();
        let expected_mean = expected_total.div_u32(samples.len() as u32);
        let expected_sum_of_squared_distances: f64 = samples
            .iter()
            .map(|&v| {
                let delta = v.mean_diff(expected_mean).as_f64();
                delta * delta
            })
            .sum();
        let expected_std = T::from_f64(
            (expected_sum_of_squared_distances / (cmp::max(2, samples.len()) - 1) as f64).sqrt(),
        );
        let expected_min = samples
            .iter()
            .copied()
            .reduce(|a, b| if b < a { b } else { a });
        let expected_max = samples
            .iter()
            .copied()
            .reduce(|a, b| if b > a { b } else { a });

        assert_is_close!(metrics.total(), expected_total);
        assert_is_close!(metrics.mean(), expected_mean);
        assert_is_close!(metrics.standard_deviation(), expected_std);

        assert_eq!(metrics.min().1, expected_min.unwrap());
        assert_eq!(metrics.max().1, expected_max.unwrap());
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
    fn run_tests(num_chunks: usize, chunk_size: usize) {
        let mut rng = rand::rng();
        let mut overall_metrics = Metrics::new();
        let mut combined_metrics = Metrics::new();
        for _ in 0..num_chunks {
            let mut chunk_metrics = Metrics::new();
            for _ in 0..chunk_size {
                let sample = Duration::from_nanos(rng.random_range(0..10_000));
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
        assert!(error < 1.0e-4, "{} ({})", error, num_chunks);

        assert_eq!(combined_metrics.max(), overall_metrics.max());
        assert_eq!(combined_metrics.min(), overall_metrics.min());
    }

    run_tests(100, 10_000);
    run_tests(100, 1_000);
    run_tests(1_000, 100);
    run_tests(1_000, 50);
    run_tests(10_000, 10);
    run_tests(10_000, 5);
    run_tests(10_000, 2);
    run_tests(10_000, 1);
}
