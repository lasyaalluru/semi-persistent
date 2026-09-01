//! Union-find with path compression and union by rank.

#[derive(Clone, Debug)]
pub struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl UnionFind {
    pub fn new() -> Self {
        Self {
            parent: Vec::new(),
            rank: Vec::new(),
        }
    }

    pub fn make(&mut self) -> usize {
        let id = self.parent.len();
        self.parent.push(id);
        self.rank.push(0);
        id
    }

    pub fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    pub fn union(&mut self, a: usize, b: usize) -> (usize, usize) {
        let mut ra = self.find(a);
        let mut rb = self.find(b);
        if ra == rb {
            return (ra, ra);
        }
        if self.rank[ra] < self.rank[rb] {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.parent[rb] = ra;
        if self.rank[ra] == self.rank[rb] {
            self.rank[ra] += 1;
        }
        (ra, rb)
    }

    pub fn same(&mut self, a: usize, b: usize) -> bool {
        self.find(a) == self.find(b)
    }
}

/// Specification: a partition as a vec of disjoint sets.
#[derive(Clone, Debug)]
pub struct NaivePartition {
    sets: Vec<Vec<usize>>,
}

impl NaivePartition {
    pub fn new() -> Self {
        Self { sets: Vec::new() }
    }

    pub fn make(&mut self) -> usize {
        let id = self.sets.iter().map(|s| s.len()).sum();
        self.sets.push(vec![id]);
        id
    }

    fn set_of(&self, x: usize) -> usize {
        self.sets
            .iter()
            .position(|s| s.contains(&x))
            .expect("unknown id")
    }

    pub fn same(&self, a: usize, b: usize) -> bool {
        self.set_of(a) == self.set_of(b)
    }

    pub fn union(&mut self, a: usize, b: usize) {
        let ia = self.set_of(a);
        let ib = self.set_of(b);
        if ia == ib {
            return;
        }
        let mut other = self.sets[ib].clone();
        self.sets[ia].append(&mut other);
        self.sets.swap_remove(ib);
    }
}
