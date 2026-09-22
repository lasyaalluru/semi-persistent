// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The `aov/log` composite as a placement experiment.
//!
//! `retained_containers_bench`'s `aov/log` row does 100 000 pushes with a mark
//! in the middle, a slice scan, and a restore, and sat at 0.92–0.96× of the
//! legacy container for the whole branch. Its phases (now `aov/push`,
//! `aov/push_presized`, `aov/scan`, `aov/mark_restore` in the retained bench)
//! are each at parity or better; this file keeps the experiments that showed
//! where the composite's few per cent comes from: the same body in
//! `#[inline(never)]` functions in both orders, and a legacy body given one
//! small extra allocation mid-iteration. On unchanged source the composite's
//! speedup moved between 0.92× and 1.02× with LLVM's alignment flags alone.

use criterion::{Criterion, criterion_group, criterion_main};
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use semi_persistent_containers_verus::group::ForkHistory;
use std::hint::black_box;

const N: usize = 100_000;

type Legacy = prod::AppendOnlyVec<u64, usize, true>;
type Verified = ForkHistory<verus::AppendOnlyVec<u64, usize, true>>;

/// The whole `aov/log` body on each side, in a function the inliner cannot
/// merge into the harness, registered in both orders. If the two orders
/// disagree the composite row's difference is placement, not work.
#[inline(never)]
fn composite_legacy() -> (u64, usize) {
    let mut v = Legacy::new();
    for i in 0..N / 2 {
        v.push(i as u64);
    }
    let tok = v.mark(prod::ShrinkPolicy::Never);
    for i in 0..N / 2 {
        v.push(i as u64);
    }
    let mut acc = 0u64;
    for x in v.as_slice() {
        acc = acc.wrapping_add(*x);
    }
    v.restore(tok);
    (acc, v.len())
}

#[inline(never)]
fn composite_verified() -> (u64, usize) {
    let mut v: Verified = ForkHistory::new(verus::AppendOnlyVec::new());
    for i in 0..N / 2 {
        v.try_push(i as u64).expect("push: within index word");
    }
    let tok = v
        .mark(verus::ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    for i in 0..N / 2 {
        v.try_push(i as u64).expect("push: within index word");
    }
    let mut acc = 0u64;
    for x in v.as_slice() {
        acc = acc.wrapping_add(*x);
    }
    assert!(v.restore_and_pop(tok), "restore: own token");
    (acc, v.len())
}

/// The legacy body with one small extra allocation live from the mark to the
/// end, as the verified side's history has. If this alone moves the legacy
/// time to the verified time, the composite difference is where the data
/// buffer lands relative to that allocation, not the container's work.
#[inline(never)]
fn composite_legacy_perturbed() -> (u64, usize) {
    let mut v = Legacy::new();
    for i in 0..N / 2 {
        v.push(i as u64);
    }
    let tok = v.mark(prod::ShrinkPolicy::Never);
    let stamps: std::vec::Vec<u64> = std::vec::Vec::with_capacity(4);
    for i in 0..N / 2 {
        v.push(i as u64);
    }
    let mut acc = 0u64;
    for x in v.as_slice() {
        acc = acc.wrapping_add(*x);
    }
    v.restore(tok);
    black_box(&stamps);
    (acc, v.len())
}

fn bench_composite(c: &mut Criterion) {
    let mut g = c.benchmark_group("aov_phase/composite");
    g.bench_function("legacy", |b| b.iter(|| black_box(composite_legacy())));
    g.bench_function("verified", |b| b.iter(|| black_box(composite_verified())));
    g.bench_function("legacy_perturbed", |b| {
        b.iter(|| black_box(composite_legacy_perturbed()))
    });
    g.finish();
    let mut g = c.benchmark_group("aov_phase/composite_swapped");
    g.bench_function("verified", |b| b.iter(|| black_box(composite_verified())));
    g.bench_function("legacy", |b| b.iter(|| black_box(composite_legacy())));
    g.finish();
}

criterion_group!(aov_phases, bench_composite);
criterion_main!(aov_phases);
