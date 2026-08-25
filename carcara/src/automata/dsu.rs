/// A Disjoint Set Union (DSU) / Union-Find data structure with union by size
/// and path compression optimizations.
pub struct DSU {
    repr: Vec<usize>,
    size: Vec<usize>,
}

impl DSU {
    /// Creates a new `DSU` with `n` elements, each initially in its own subset.
    pub fn new(n: usize) -> Self {
        DSU {
            repr: (0..n).collect(),
            size: vec![1; n],
        }
    }

    /// Finds the representative element of the set containing `x`, applying path compression.
    pub fn find(&mut self, x: usize) -> usize {
        if self.repr[x] != x {
            self.repr[x] = self.find(self.repr[x]);
        }
        self.repr[x]
    }

    /// Merges the set containing `x` with the set containing `y` using union by size.
    pub fn union(&mut self, x: usize, y: usize) {
        let mut x_repr = self.find(x);
        let mut y_repr = self.find(y);

        if x_repr == y_repr {
            return;
        }

        if self.size[x_repr] < self.size[y_repr] {
            std::mem::swap(&mut x_repr, &mut y_repr);
        }
        self.size[x_repr] += self.size[y_repr];
        self.repr[y_repr] = x_repr;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initial_state() {
        let mut dsu = DSU::new(5);
        assert!(dsu.repr == (0..5).collect::<Vec<usize>>());
        assert!(dsu.size.iter().all(|&x| x == 1));
        for i in 0..5 {
            assert_eq!(dsu.find(i), i);
        }
    }

    #[test]
    fn test_union_and_find() {
        let mut dsu = DSU::new(5);

        dsu.union(0, 1);
        assert_eq!(dsu.find(0), dsu.find(1));

        dsu.union(1, 2);
        assert_eq!(dsu.find(0), dsu.find(2));

        assert_ne!(dsu.find(0), dsu.find(3));
        assert_ne!(dsu.find(1), dsu.find(4));
    }

    #[test]
    fn test_multiple_unions() {
        let mut dsu = DSU::new(10);
        for i in 0..9 {
            dsu.union(i, i + 1);
        }

        for i in 0..10 {
            assert_eq!(dsu.find(0), dsu.find(i));
        }

        let repr = dsu.find(0);
        assert_eq!(dsu.size[repr], 10);
    }

    #[test]
    fn test_balancing() {
        let mut dsu = DSU::new(6);
        dsu.union(0, 1);
        dsu.union(2, 3);
        dsu.union(4, 5);
        dsu.union(0, 2);
        dsu.union(0, 4);

        let root = dsu.find(0);
        for i in 1..6 {
            assert_eq!(dsu.find(i), root);
        }
        assert_eq!(dsu.size[root], 6);
    }
}
