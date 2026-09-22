// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! H4a.4 measurement: wall-clock for `EGraph::mark` and `EGraph::restore`,
//! sequential vs parallel member fan-out, reported separately, on a synthetic
//! backtrack-heavy driver. Run with:
//!
//!     cargo test --release --test par_fanout_bench -- --ignored --nocapture
//!
//! The workload marks after every growth round and then unwinds the whole
//! frame stack, so mark and restore each run `ROUNDS` times per configuration
//! at frames whose size is set by `LEAVES`.

use std::time::{Duration, Instant};

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, true, false>;

const ROUNDS: usize = 24;

fn grow(eg: &mut Eg, round: usize, leaves: usize) -> Vec<ENodeId> {
    let sort = eg.intern_sort("E");
    let f = eg.register_op1(&format!("f{round}"), sort, sort);
    let ls: Vec<ENodeId> = (0..leaves)
        .map(|i| {
            let op = eg.register_op0(&format!("a{round}_{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    let parents: Vec<ENodeId> = ls.iter().map(|&l| eg.add(f, &[l])).collect();
    for k in (2..leaves).step_by(2) {
        eg.merge(ls[0], ls[k]);
    }
    eg.rebuild();
    parents
}

/// One full run: grow+mark ROUNDS times, then restore all the way down.
/// Returns (total mark wall, total restore wall).
fn run(par: bool, leaves: usize) -> (Duration, Duration) {
    let mut eg = Eg::new();
    let mut tokens = Vec::new();
    let mut mark_wall = Duration::ZERO;
    for round in 0..ROUNDS {
        grow(&mut eg, round, leaves);
        let t = Instant::now();
        tokens.push(eg.mark_with(ShrinkPolicy::Never, par));
        mark_wall += t.elapsed();
    }
    let mut restore_wall = Duration::ZERO;
    while let Some(tok) = tokens.pop() {
        let t = Instant::now();
        eg.restore_with(tok, par);
        restore_wall += t.elapsed();
    }
    (mark_wall, restore_wall)
}

#[test]
#[ignore = "measurement, run explicitly with --ignored --nocapture"]
fn par_fanout_wall_clock() {
    for &leaves in &[256usize, 4096, 32768] {
        // Warm both paths once (rayon pool startup, allocator).
        let _ = run(false, leaves.min(256));
        let _ = run(true, leaves.min(256));
        let (seq_mark, seq_restore) = run(false, leaves);
        let (par_mark, par_restore) = run(true, leaves);
        println!(
            "leaves/round={leaves} rounds={ROUNDS}: \
             mark seq {:.2}ms par {:.2}ms ({:.2}x) | \
             restore seq {:.2}ms par {:.2}ms ({:.2}x)",
            seq_mark.as_secs_f64() * 1e3,
            par_mark.as_secs_f64() * 1e3,
            seq_mark.as_secs_f64() / par_mark.as_secs_f64(),
            seq_restore.as_secs_f64() * 1e3,
            par_restore.as_secs_f64() * 1e3,
            seq_restore.as_secs_f64() / par_restore.as_secs_f64(),
        );
    }
}

/// H4b.3, the real e-graph: the ONE shared genealogy's measured bytes at
/// depth. The counterfactual per-member duplication is this times the
/// column census (46 semi-persistent columns across the members, counted
/// from the pre-H2 member token structure: 9 in EClasses, 29 in the node
/// store, 8 across registries and maps).
#[test]
fn shared_fork_history_bytes() {
    for &depth in &[64usize, 1024] {
        let mut eg = Eg::new();
        for round in 0..depth {
            grow(&mut eg, round, 4);
            let _ = eg.mark_with(ShrinkPolicy::Never, false);
        }
        let b = eg.fork_history_bytes();
        println!(
            "e-graph shared fork-history bytes at depth {depth}: {b}              (pre-H2 duplication: 46 columns x {b} = {} B)",
            46 * b
        );
    }
}
