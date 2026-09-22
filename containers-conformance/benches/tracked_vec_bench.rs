// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Tracked-vector benches shaped like the e-graph's saturation loop:
//! FREQUENT marks, FEW writes per mark, over VecI (InlineStore — union-find
//! parent/rank, caches, classes) and VecP, with a size sweep. This is the
//! workload distinguishes an O(len)-per-mark store from one that clears only
//! slots named by the previous frame's diffs. At fixed writes per mark, scaling
//! with `n` exposes an unintended whole-vector sweep.
//!
//! The `mark_churn` groups keep the historical sizes and 200 marks per timed
//! iteration. The `mark_churn_large` groups extend the sweep to 10M and 100M
//! elements with fewer marks per iteration (`marks_for`) so one iteration
//! stays in the sub-second range; compare per-cycle times (iteration time /
//! marks) across groups, not iteration times.

use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use verus::group::ForkHistory;

use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

const MARKS: usize = 200; // marks per timed iteration (historical sizes)
const WRITES_PER_MARK: usize = 8; // few writes between marks (e-graph shape)

/// Marks per timed iteration for the large sweep: 200 at 1M scales down
/// with `n` (20 at 10M, 2 at 100M).
fn marks_for(n: usize) -> usize {
    (MARKS * 1_000_000 / n).max(2)
}

fn veci_prod(b: &mut criterion::Bencher<'_>, n: usize, marks: usize) {
    b.iter_batched_ref(
        || {
            let mut v: prod::VecI<u32, u32, true> = prod::VecI::new();
            for i in 0..n {
                v.push((i as u32) & 0x7FFF_FFFF);
            }
            v
        },
        |v| {
            let mut x: u64 = 0x2545F491;
            for _ in 0..marks {
                let tok = v.mark(prod::ShrinkPolicy::Never);
                for _ in 0..WRITES_PER_MARK {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let idx = (x % n as u64) as u32;
                    v.set(idx, (x as u32) & 0x7FFF_FFFF);
                }
                v.restore(tok);
            }
            black_box(v.len());
        },
        BatchSize::LargeInput,
    )
}

fn veci_verus(b: &mut criterion::Bencher<'_>, n: usize, marks: usize) {
    type V = ForkHistory<verus::VecI<u32, u32, true>>;
    b.iter_batched_ref(
        || {
            let mut v: V = ForkHistory::new(verus::VecI::new());
            for i in 0..n {
                v.try_push((i as u32) & 0x7FFF_FFFF)
                    .expect("push: within index word");
            }
            v
        },
        |v| {
            let mut x: u64 = 0x2545F491;
            for _ in 0..marks {
                let tok = v
                    .mark(verus::ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness");
                for _ in 0..WRITES_PER_MARK {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let idx = (x % n as u64) as u32;
                    v.set_index(idx, (x as u32) & 0x7FFF_FFFF);
                }
                // Legacy restore == verified restore_and_pop (restore + pop_scope fused; design doc 08 §1).
                assert!(v.restore_and_pop(tok), "restore: own token");
            }
            black_box(v.len());
        },
        BatchSize::LargeInput,
    )
}

fn vecp_prod(b: &mut criterion::Bencher<'_>, n: usize, marks: usize) {
    b.iter_batched_ref(
        || {
            let mut v: prod::VecP<u64, u32, true> = prod::VecP::new();
            for i in 0..n {
                v.push(i as u64);
            }
            v
        },
        |v| {
            let mut x: u64 = 0x2545F492;
            for _ in 0..marks {
                let tok = v.mark(prod::ShrinkPolicy::Never);
                for _ in 0..WRITES_PER_MARK {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let idx = (x % n as u64) as u32;
                    v.set(idx, x);
                }
                v.restore(tok);
            }
            black_box(v.len());
        },
        BatchSize::LargeInput,
    )
}

fn vecp_verus(b: &mut criterion::Bencher<'_>, n: usize, marks: usize) {
    type V = ForkHistory<verus::VecP<u64, u32, true>>;
    b.iter_batched_ref(
        || {
            let mut v: V = ForkHistory::new(verus::VecP::new());
            for i in 0..n {
                v.try_push(i as u64).expect("push: within index word");
            }
            v
        },
        |v| {
            let mut x: u64 = 0x2545F492;
            for _ in 0..marks {
                let tok = v
                    .mark(verus::ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness");
                for _ in 0..WRITES_PER_MARK {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let idx = (x % n as u64) as u32;
                    v.set_index(idx, x);
                }
                assert!(v.restore_and_pop(tok), "restore: own token");
            }
            black_box(v.len());
        },
        BatchSize::LargeInput,
    )
}

fn bench_veci_mark_churn(c: &mut Criterion) {
    let mut g = c.benchmark_group("tracked_veci/mark_churn");
    for &n in &[1_000usize, 100_000, 1_000_000] {
        g.bench_with_input(BenchmarkId::new("prod", n), &n, |b, &n| {
            veci_prod(b, n, MARKS)
        });
        g.bench_with_input(BenchmarkId::new("verus", n), &n, |b, &n| {
            veci_verus(b, n, MARKS)
        });
    }
    g.finish();
}

fn bench_vecp_mark_churn(c: &mut Criterion) {
    let mut g = c.benchmark_group("tracked_vecp/mark_churn");
    for &n in &[1_000usize, 1_000_000] {
        g.bench_with_input(BenchmarkId::new("prod", n), &n, |b, &n| {
            vecp_prod(b, n, MARKS)
        });
        g.bench_with_input(BenchmarkId::new("verus", n), &n, |b, &n| {
            vecp_verus(b, n, MARKS)
        });
    }
    g.finish();
}

fn bench_veci_mark_churn_large(c: &mut Criterion) {
    let mut g = c.benchmark_group("tracked_veci/mark_churn_large");
    g.sample_size(10);
    for &n in &[10_000_000usize, 100_000_000] {
        let marks = marks_for(n);
        g.bench_with_input(BenchmarkId::new("prod", n), &n, |b, &n| {
            veci_prod(b, n, marks)
        });
        g.bench_with_input(BenchmarkId::new("verus", n), &n, |b, &n| {
            veci_verus(b, n, marks)
        });
    }
    g.finish();
}

fn bench_vecp_mark_churn_large(c: &mut Criterion) {
    let mut g = c.benchmark_group("tracked_vecp/mark_churn_large");
    g.sample_size(10);
    for &n in &[10_000_000usize, 100_000_000] {
        let marks = marks_for(n);
        g.bench_with_input(BenchmarkId::new("prod", n), &n, |b, &n| {
            vecp_prod(b, n, marks)
        });
        g.bench_with_input(BenchmarkId::new("verus", n), &n, |b, &n| {
            vecp_verus(b, n, marks)
        });
    }
    g.finish();
}

criterion_group!(
    benches,
    bench_veci_mark_churn,
    bench_vecp_mark_churn,
    bench_veci_mark_churn_large,
    bench_vecp_mark_churn_large
);
criterion_main!(benches);
