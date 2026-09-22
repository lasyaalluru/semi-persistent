// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! What the map's last-write-wins encoding costs a unique-key caller.
//!
//! Every `SpMap` in this workspace is an interning table: it looks a key up and
//! inserts only on a miss, so no key is ever overwritten. The general
//! (last-write-wins) map costs such a caller two things on the insert path — a
//! push to the previous-occurrence column (the column exists so a restore can
//! point the index back at a key's earlier occurrence, which never happens
//! here) and, written as a membership check followed by an insert, a second
//! hash of the key. `try_intern` removes the second hash; the unique-keys
//! discipline (`SpUniqueMap`) removes the column. Both are measured here against
//! the general map and against the hand-rolled reference.
//!
//! The reference side is a hand-rolled interning table with exactly the shape
//! the anti-unification memo used before it moved onto `SpMap`: an append-only
//! log of `(key, value)`, a plain index to log positions, one saved length per
//! frame, and a restore that walks the discarded suffix removing keys. It is the
//! lower bound the unique-key discipline should approach, not a proposal to go
//! back to hand-rolling.
//!
//! Key shapes are the ones that actually occur: a pair of `u64` (the memo, the
//! action cache), a `String` (the four registries), and a `Vec<u32>` (the
//! context store, where hashing and cloning a key touch the heap).
//!
//! Reading the numbers: on an Apple Silicon machine a benchmark process may land
//! on efficiency cores, where every row is about twice as slow and, worse, the
//! ORDER of two close variants can differ from the performance-core order (a
//! column push and a hash cost different fractions of an insert on each). The
//! `spmap/intern/u64pair/spmap_unique_intern` row is the canary: about 82 µs on
//! the performance cores of an M4 Pro, about 160 µs on its efficiency cores.
//! Discard a run whose canary is off, and never trust a single-run difference
//! under ten per cent from this file; the paired protocol in `bench_pair.sh` is
//! for those.
//!
//! Both sides use the crate's `IndexHasher`. That is not a detail: with std's
//! default `RandomState` on the reference side the comparison measures the
//! hasher and nothing else — the map came out between 1.4x and 5.7x faster on
//! every case, which says the verified map beats a hand-rolled table built on
//! SipHash, not what its own encoding costs. Holding the hasher fixed is what
//! isolates the previous-occurrence column and the double hash.

use std::collections::HashMap;
use std::hash::{Hash, RandomState};

use semi_persistent_containers_verus::hasher_spec::IndexHasher;

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use semi_persistent_containers_verus::append_only_vec::AppendOnlyVec;
use semi_persistent_containers_verus::group::Member;
use semi_persistent_containers_verus::{ShrinkPolicy, SpMap, SpUniqueMap};

const N: usize = 4096;

// ---------------------------------------------------------------------------
// The reference: a unique-key interning table, hand-rolled
// ---------------------------------------------------------------------------

struct Intern<K, V> {
    log: AppendOnlyVec<(K, V), usize>,
    index: HashMap<K, usize, IndexHasher>,
    frame_lens: Vec<usize>,
}

impl<K: Clone + Eq + Hash, V> Intern<K, V> {
    fn new() -> Self {
        Intern {
            log: AppendOnlyVec::new(),
            index: HashMap::with_hasher(IndexHasher::default()),
            frame_lens: Vec::new(),
        }
    }

    fn get(&self, key: &K) -> Option<&V> {
        let &pos = self.index.get(key)?;
        Some(&self.log.get(pos).1)
    }

    /// The interning insert: one hash for the check, one for the insert — the
    /// same double hash every `SpMap` caller pays today.
    fn intern(&mut self, key: K, val: V) {
        if self.index.contains_key(&key) {
            return;
        }
        let pos = self.log.len();
        self.log
            .try_push((key.clone(), val))
            .expect("bench table fits its index word");
        self.index.insert(key, pos);
    }

    fn push_frame(&mut self) {
        self.frame_lens.push(self.log.len());
        Member::push_frame(&mut self.log, ShrinkPolicy::Never);
    }

    /// Semantics B: reset to the frame and keep it open. The index repair is the
    /// deletion walk a unique-key discipline permits.
    fn reset_frame(&mut self, depth: usize) {
        let saved = self.frame_lens[depth];
        let live = self.log.len();
        for pos in saved..live {
            let key = &self.log.get(pos).0;
            self.index.remove(key);
        }
        Member::reset_frame(&mut self.log, depth);
        self.frame_lens.truncate(depth + 1);
    }
}

// ---------------------------------------------------------------------------
// Key shapes
// ---------------------------------------------------------------------------

fn pairs(n: usize) -> Vec<(u64, u64)> {
    (0..n as u64)
        .map(|i| (i, i.wrapping_mul(2_654_435_761)))
        .collect()
}

fn strings(n: usize) -> Vec<String> {
    (0..n).map(|i| format!("operator_{i:07}")).collect()
}

fn vecs(n: usize) -> Vec<Vec<u32>> {
    (0..n)
        .map(|i| (0..8u32).map(|j| (i as u32) * 8 + j).collect())
        .collect()
}

// ---------------------------------------------------------------------------
// Benchmarks
// ---------------------------------------------------------------------------

/// Fill both sides through the interning path: lookup, then insert on a miss.
fn bench_intern<K: Clone + Eq + Hash + 'static>(c: &mut Criterion, shape: &str, keys: Vec<K>) {
    let mut g = c.benchmark_group(format!("spmap/intern/{shape}"));
    if keys.len() > N {
        g.sample_size(30);
    }
    g.bench_function("spmap_precheck", |b| {
        b.iter_batched(
            || keys.clone(),
            |ks| {
                let mut m: SpMap<K, u32> = SpMap::new();
                for (i, k) in ks.into_iter().enumerate() {
                    if !m.contains_key(&k) {
                        m.try_insert(k, i as u32).expect("fits the index word");
                    }
                }
                m.len()
            },
            BatchSize::SmallInput,
        )
    });
    // The interning entry point: one hash, membership decided by the same probe.
    g.bench_function("spmap_intern", |b| {
        b.iter_batched(
            || keys.clone(),
            |ks| {
                let mut m: SpMap<K, u32> = SpMap::new();
                for (i, k) in ks.into_iter().enumerate() {
                    m.try_intern(k, i as u32).expect("fits the index word");
                }
                m.len()
            },
            BatchSize::SmallInput,
        )
    });
    // The unique-keys discipline: one hash, and no column push.
    g.bench_function("spmap_unique_intern", |b| {
        b.iter_batched(
            || keys.clone(),
            |ks| {
                let mut m: SpUniqueMap<K, u32> = SpUniqueMap::new();
                for (i, k) in ks.into_iter().enumerate() {
                    m.try_intern(k, i as u32).expect("fits the index word");
                }
                m.len()
            },
            BatchSize::SmallInput,
        )
    });
    // The same map on std's SipHash `RandomState`: what DoS resistance costs
    // when the keys come from an untrusted source.
    g.bench_function("spmap_unique_intern_randomstate", |b| {
        b.iter_batched(
            || keys.clone(),
            |ks| {
                let mut m: SpUniqueMap<K, u32, usize, true, RandomState> = SpUniqueMap::new();
                for (i, k) in ks.into_iter().enumerate() {
                    m.try_intern(k, i as u32).expect("fits the index word");
                }
                m.len()
            },
            BatchSize::SmallInput,
        )
    });
    g.bench_function("handrolled", |b| {
        b.iter_batched(
            || keys.clone(),
            |ks| {
                let mut t: Intern<K, u32> = Intern::new();
                for (i, k) in ks.into_iter().enumerate() {
                    t.intern(k, i as u32);
                }
                t.index.len()
            },
            BatchSize::SmallInput,
        )
    });
    g.finish();
}

/// Hit every key once on a filled table.
fn bench_lookup<K: Clone + Eq + Hash + 'static>(c: &mut Criterion, shape: &str, keys: Vec<K>) {
    let mut m: SpMap<K, u32> = SpMap::new();
    let mut u: SpUniqueMap<K, u32> = SpUniqueMap::new();
    let mut t: Intern<K, u32> = Intern::new();
    for (i, k) in keys.iter().enumerate() {
        m.try_insert(k.clone(), i as u32).expect("fits");
        u.try_insert(k.clone(), i as u32).expect("fits");
        t.intern(k.clone(), i as u32);
    }
    let mut g = c.benchmark_group(format!("spmap/lookup_hit/{shape}"));
    g.bench_function("spmap", |b| {
        b.iter(|| {
            let mut acc: u64 = 0;
            for k in &keys {
                acc += *m.get_by_key(k).expect("present") as u64;
            }
            acc
        })
    });
    g.bench_function("spmap_unique", |b| {
        b.iter(|| {
            let mut acc: u64 = 0;
            for k in &keys {
                acc += *u.get_by_key(k).expect("present") as u64;
            }
            acc
        })
    });
    g.bench_function("handrolled", |b| {
        b.iter(|| {
            let mut acc: u64 = 0;
            for k in &keys {
                acc += *t.get(k).expect("present") as u64;
            }
            acc
        })
    });
    g.finish();
}

/// Mark, insert a suffix, then reset to the mark. `share` is the fraction of the
/// table the suffix covers, which is what decides whether the map unwinds the
/// index entry by entry or rebuilds it from the survivors.
fn bench_restore<K: Clone + Eq + Hash + 'static>(
    c: &mut Criterion,
    shape: &str,
    keys: Vec<K>,
    share: usize,
    label: &str,
) {
    let split = keys.len() - keys.len() / share;
    let mut g = c.benchmark_group(format!("spmap/{label}/{shape}"));
    g.bench_function("spmap", |b| {
        b.iter_batched(
            || {
                let mut m: SpMap<K, u32> = SpMap::new();
                for (i, k) in keys[..split].iter().enumerate() {
                    m.try_insert(k.clone(), i as u32).expect("fits");
                }
                Member::push_frame(&mut m, ShrinkPolicy::Never);
                for (i, k) in keys[split..].iter().enumerate() {
                    m.try_insert(k.clone(), i as u32).expect("fits");
                }
                m
            },
            |mut m| {
                Member::reset_frame(&mut m, 0);
                m.len()
            },
            BatchSize::SmallInput,
        )
    });
    g.bench_function("spmap_unique", |b| {
        b.iter_batched(
            || {
                let mut m: SpUniqueMap<K, u32> = SpUniqueMap::new();
                for (i, k) in keys[..split].iter().enumerate() {
                    m.try_insert(k.clone(), i as u32).expect("fits");
                }
                Member::push_frame(&mut m, ShrinkPolicy::Never);
                for (i, k) in keys[split..].iter().enumerate() {
                    m.try_insert(k.clone(), i as u32).expect("fits");
                }
                m
            },
            |mut m| {
                Member::reset_frame(&mut m, 0);
                m.len()
            },
            BatchSize::SmallInput,
        )
    });
    g.bench_function("handrolled", |b| {
        b.iter_batched(
            || {
                let mut t: Intern<K, u32> = Intern::new();
                for (i, k) in keys[..split].iter().enumerate() {
                    t.intern(k.clone(), i as u32);
                }
                t.push_frame();
                for (i, k) in keys[split..].iter().enumerate() {
                    t.intern(k.clone(), i as u32);
                }
                t
            },
            |mut t| {
                t.reset_frame(0);
                t.index.len()
            },
            BatchSize::SmallInput,
        )
    });
    g.finish();
}

fn benches(c: &mut Criterion) {
    bench_intern(c, "u64pair", pairs(N));
    bench_intern(c, "string", strings(N));
    bench_intern(c, "vec32", vecs(N));
    // Sixteen times larger, so the column's growth (16 bytes per entry,
    // reallocated as the table grows) is a 1 MB allocation rather than 64 KB.
    // On performance cores the unique map is 2–3 per cent ahead of the general
    // map's `try_intern` here and level with the hand-rolled table.
    bench_intern(c, "string_64k", strings(16 * N));
    bench_intern(c, "vec32_64k", vecs(16 * N));

    bench_lookup(c, "u64pair", pairs(N));
    bench_lookup(c, "string", strings(N));
    bench_lookup(c, "vec32", vecs(N));

    // A shallow reset discards an eighth (the map unwinds); a deep one discards
    // seven eighths (the map rebuilds from the survivors).
    bench_restore(c, "u64pair", pairs(N), 8, "reset_shallow");
    bench_restore(c, "string", strings(N), 8, "reset_shallow");
    bench_restore(c, "u64pair", pairs(N), 8 * 7 / 8 + 1, "reset_deep");
}

criterion_group!(spmap_discipline, benches);
criterion_main!(spmap_discipline);
