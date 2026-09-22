// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Isolates the compression pass's normalize step: is the packed-key
//! decoration sort faster than sorting the (T, I) tuples directly, and at
//! what stratum size? Three candidates over unique and duplicate-heavy
//! (trail-shaped) strata:
//!   tuple_unstable - today's unique-discipline path (sort_unstable_by_key)
//!   tuple_stable   - today's trail path (stable sort + first-of-group fold)
//!   packed_keys    - proposed: build (idx << 32 | pos) u64 keys,
//!                    sort_unstable, walk groups reading payloads by pos
//! The verdict is ns/element at each size; the product only changes if a
//! candidate wins at sizes eviction actually sees.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

fn make_stratum(m: usize, dup_factor: usize, seed0: u64) -> Vec<(u64, u32)> {
    // dup_factor 1 = unique indices; k>1 = each index written ~k times
    // (trail shape), in scattered temporal order.
    let distinct = (m / dup_factor).max(1);
    let mut seed = seed0;
    (0..m)
        .map(|_| {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let idx = ((seed >> 33) as usize % distinct) as u32;
            (seed, idx)
        })
        .collect()
}

fn tuple_unstable(frame: &mut [(u64, u32)]) -> usize {
    frame.sort_unstable_by_key(|p| p.1);
    frame.len()
}

fn tuple_stable_fold(frame: &mut [(u64, u32)]) -> usize {
    frame.sort_by_key(|p| p.1);
    let n = frame.len();
    if n == 0 {
        return 0;
    }
    let mut w = 1usize;
    for r in 1..n {
        if frame[r].1 != frame[w - 1].1 {
            frame[w] = frame[r];
            w += 1;
        }
    }
    w
}

fn packed_keys(frame: &[(u64, u32)], keys: &mut Vec<u64>, out: &mut Vec<(u64, u32)>) -> usize {
    keys.clear();
    keys.extend(
        frame
            .iter()
            .enumerate()
            .map(|(j, p)| ((p.1 as u64) << 32) | j as u64),
    );
    keys.sort_unstable();
    out.clear();
    let mut last_idx = u64::MAX;
    for &k in keys.iter() {
        let idx = k >> 32;
        if idx != last_idx {
            last_idx = idx;
            let pos = (k & 0xFFFF_FFFF) as usize;
            out.push(frame[pos]);
        }
    }
    out.len()
}

fn bench_normalize(c: &mut Criterion) {
    for &dup in &[1usize, 4] {
        let mut g = c.benchmark_group(if dup == 1 {
            "normalize/unique"
        } else {
            "normalize/trail_dup4"
        });
        for &m in &[32usize, 256, 4096, 65536] {
            let base = make_stratum(m, dup, 0x5EED);
            g.bench_with_input(BenchmarkId::new("tuple_unstable", m), &m, |b, _| {
                let mut buf = base.clone();
                b.iter(|| {
                    buf.copy_from_slice(&base);
                    black_box(tuple_unstable(&mut buf))
                })
            });
            g.bench_with_input(BenchmarkId::new("tuple_stable_fold", m), &m, |b, _| {
                let mut buf = base.clone();
                b.iter(|| {
                    buf.copy_from_slice(&base);
                    black_box(tuple_stable_fold(&mut buf))
                })
            });
            g.bench_with_input(BenchmarkId::new("packed_keys", m), &m, |b, _| {
                let mut keys: Vec<u64> = Vec::with_capacity(m);
                let mut out: Vec<(u64, u32)> = Vec::with_capacity(m);
                b.iter(|| black_box(packed_keys(&base, &mut keys, &mut out)))
            });
        }
        g.finish();
    }
}

criterion_group!(benches, bench_normalize);
criterion_main!(benches);
