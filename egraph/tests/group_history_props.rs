// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Grouped history at the e-graph level: `EGraph::mark`/`restore` fan out by
//! hand over eight members (classes, nodes, the sort/op/rule/axiom registries,
//! the literal store and the shared history). The verified group (`ForkHistory`)
//! proves lockstep for its own members; this property test checks the same
//! thing for the e-graph's hand-rolled group on random workloads: after every
//! restore, every observable of every member equals (a) the snapshot taken at
//! the mark and (b) a fresh replay of the effective operation history, ids
//! minted after the restore continue without gaps, and registrations made
//! after the mark are gone.
use num_bigint::BigInt;
use proptest::prelude::*;
use proptest::test_runner::{Config, TestRunner};
use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, true, false>;

#[derive(Clone, Debug)]
enum Op {
    Leaf,
    Unary(usize),
    Binary(usize, usize),
    Lit(i64),
    Merge(usize, usize),
    Rebuild,
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        20 => Just(Op::Leaf),
        15 => any::<usize>().prop_map(Op::Unary),
        15 => (any::<usize>(), any::<usize>()).prop_map(|(a, b)| Op::Binary(a, b)),
        8 => (-4i64..4).prop_map(Op::Lit),
        18 => (any::<usize>(), any::<usize>()).prop_map(|(a, b)| Op::Merge(a, b)),
        8 => Just(Op::Rebuild),
        10 => Just(Op::Mark),
        8 => any::<usize>().prop_map(Op::Restore),
    ]
}

/// One e-graph plus the bookkeeping the observables need.
struct Harness {
    eg: Eg,
    sort: SortId,
    f: OpId,
    g: OpId,
    lit: OpId,
    ids: Vec<ENodeId>,
    leaves: usize,
}

/// Everything a member exposes, in one comparable value.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Obs {
    classes: usize,
    nodes: usize,
    lits: usize,
    sorts: usize,
    ids: usize,
    leaves: usize,
    /// Partition of the tracked ids into classes, numbered by first occurrence.
    partition: Vec<usize>,
}

impl Harness {
    fn fresh() -> Self {
        let mut eg = Eg::new();
        let sort = eg.intern_sort("s");
        let f = eg.register_op1("f", sort, sort);
        let g = eg.register_op2("g", sort, sort, sort);
        let lit = eg.register_op0("lit", sort);
        Harness {
            eg,
            sort,
            f,
            g,
            lit,
            ids: Vec::new(),
            leaves: 0,
        }
    }

    /// Apply one effective (non-persistence) operation. Returns false when the
    /// operation has nothing to act on (kept out of the effective history).
    fn apply(&mut self, op: &Op) -> bool {
        let n = self.ids.len();
        match op {
            Op::Leaf => {
                let o = self
                    .eg
                    .register_op0(&format!("c{}", self.leaves), self.sort);
                self.leaves += 1;
                let id = self.eg.add(o, &[]);
                self.ids.push(id);
                true
            }
            Op::Unary(i) => {
                if n == 0 {
                    return false;
                }
                let a = self.ids[i % n];
                let id = self.eg.add(self.f, &[a]);
                self.ids.push(id);
                true
            }
            Op::Binary(i, j) => {
                if n == 0 {
                    return false;
                }
                let (a, b) = (self.ids[i % n], self.ids[j % n]);
                let id = self.eg.add(self.g, &[a, b]);
                self.ids.push(id);
                true
            }
            Op::Lit(v) => {
                let l = self.eg.intern_lit(NiraLitVal::Int(BigInt::from(*v)));
                let id = self.eg.add_lit(self.lit, l);
                self.ids.push(id);
                true
            }
            Op::Merge(i, j) => {
                if n == 0 {
                    return false;
                }
                let (a, b) = (self.ids[i % n], self.ids[j % n]);
                self.eg.merge(a, b);
                true
            }
            Op::Rebuild => {
                self.eg.rebuild();
                true
            }
            Op::Mark | Op::Restore(_) => unreachable!("persistence ops are not replayed"),
        }
    }

    fn observe(&mut self) -> Obs {
        let mut reps: Vec<ENodeId> = Vec::new();
        let mut partition = Vec::with_capacity(self.ids.len());
        for k in 0..self.ids.len() {
            let r = self.eg.find(self.ids[k]);
            let idx = match reps.iter().position(|&x| x == r) {
                Some(p) => p,
                None => {
                    reps.push(r);
                    reps.len() - 1
                }
            };
            partition.push(idx);
        }
        Obs {
            classes: self.eg.class_count(),
            nodes: self.eg.node_count(),
            lits: self.eg.lits().len(),
            sorts: self.eg.sorts().len(),
            ids: self.ids.len(),
            leaves: self.leaves,
            partition,
        }
    }

    /// The registries rolled back with everything else: leaf ops below the
    /// count exist, the next one does not.
    fn registries_match(&self) -> bool {
        (0..self.leaves).all(|k| self.eg.op(&format!("c{k}")).is_some())
            && self.eg.op(&format!("c{}", self.leaves)).is_none()
    }
}

fn replay(history: &[Op]) -> Harness {
    let mut h = Harness::fresh();
    for op in history {
        assert!(h.apply(op), "effective history only holds applicable ops");
    }
    h
}

#[test]
fn egraph_group_restores_every_member_to_the_marked_version() {
    let strat = proptest::collection::vec(op_strategy(), 1..64);
    let mut runner = TestRunner::new(Config {
        cases: 128,
        ..Config::default()
    });
    runner
        .run(&strat, |ops| {
            let mut h = Harness::fresh();
            let mut history: Vec<Op> = Vec::new();
            // Live marks: token, effective-history length, ids/leaves at the mark
            // and the observables snapshot.
            let mut live: Vec<(_, usize, usize, usize, Obs)> = Vec::new();
            for op in ops {
                match op {
                    Op::Mark => {
                        // `EGraph::mark` rebuilds before sealing the frame, so the
                        // effective history carries that rebuild too.
                        let t = h.eg.mark(ShrinkPolicy::Never);
                        history.push(Op::Rebuild);
                        let obs = h.observe();
                        live.push((t, history.len(), h.ids.len(), h.leaves, obs));
                    }
                    Op::Restore(k) => {
                        if live.is_empty() {
                            continue;
                        }
                        let k = k % live.len();
                        let (t, hist_len, ids_len, leaves, snap) = live[k].clone();
                        h.eg.restore(t);
                        h.ids.truncate(ids_len);
                        h.leaves = leaves;
                        history.truncate(hist_len);
                        // (a) every member is back at the mark's snapshot ...
                        let now = h.observe();
                        prop_assert_eq!(&now, &snap, "restore must land on the mark's snapshot");
                        prop_assert!(
                            h.registries_match(),
                            "registrations after the mark must be gone"
                        );
                        // (b) ... which is exactly what replaying the effective history gives.
                        let mut fresh = replay(&history);
                        let again = fresh.observe();
                        prop_assert_eq!(&now, &again, "restore must equal a fresh replay");
                        // Deeper marks are the abandoned future; the consumed one is gone.
                        live.truncate(k);
                    }
                    other => {
                        if h.apply(&other) {
                            history.push(other);
                        }
                    }
                }
            }
            // No gaps after the restores: the final state equals a fresh replay.
            let end = h.observe();
            let mut fresh = replay(&history);
            prop_assert_eq!(
                &end,
                &fresh.observe(),
                "final state must equal a fresh replay"
            );
            prop_assert!(h.registries_match());
            Ok(())
        })
        .unwrap();
}
