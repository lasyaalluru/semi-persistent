// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Criterion comparison between the reference container implementation and the
//! verified implementation used by the engine.
//!
//! Workloads model the e-graph consumer:
//! - `vec/try_extend`: total batch insertion versus the reference push loop.
//! - `vec/mark_set_restore`: interleaved set-heavy work under a mark, then
//!   restore — the union-find / caches / classes rollback pattern.
//! - `vec/restore_replay`: restore in isolation, after capture setup.
//! - `vec/push_pop_untracked`: TRACK=false push/pop — the plain-store use.
//! - `list/append_iter`: build many small lists, iterate them — the use-list
//!   build + walk pattern.
//! - `list/splice`: repeated list concatenation — the merge pattern.
//! - `class_ring/*`: isolated untracked splice/traversal and tracked
//!   merge/restore for the ring protocol inside the class layer. Aggregate
//!   retained-vs-verified measurements live in `eclasses_bench`.
//! - `map/intern*`: the interner pattern (insert-or-hit) over the key shapes
//!   the consumers use; `map/restore_small_suffix*`: a large live map with a
//!   few inserts per frame and a restore — the SMT-style mark/backtrack use.
//!
//! Criterion supplies warm-up, adaptive iteration counts, outlier analysis,
//! and bootstrap confidence intervals. Results remain host- and revision-bound:
//! this suite reports evidence and does not fail CI on a fixed ratio. Run the
//! two registration orders separately when comparing implementations, because
//! allocation-heavy arms can retain order effects even when each estimate has
//! a narrow confidence interval.

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use verus::group::ForkHistory;

use containers_conformance::prod_class_ring::{self as pring, PNodeId};
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use verus::opt::DenseId as _;

// Typed ids for the ListArena pairs (same width both sides).
prod::define_id31! { pub struct PElem / StoredPElem, "e"; }
prod::define_id31! { pub struct PList / StoredPList, "l"; }
prod::define_id31! { pub struct PNode / StoredPNode, "n"; }
verus::define_id31! { pub struct VElem / StoredVElem, "e"; }
verus::define_id31! { pub struct VList / StoredVList, "l"; }
verus::define_id31! { pub struct VNode / StoredVNode, "n"; }
verus::define_id31! { pub struct VRingNode / StoredVRingNode, "r"; }
verus::define_id31! { pub struct VRingKey / StoredVRingKey, "rk"; }

const VEC_N: usize = 100_000;
const VEC_TOUCHES: usize = 50_000;
const LISTS: usize = 2_000;
const PER_LIST: usize = 30;
const RESTORE_BATCH: usize = 8;
const RING_N: usize = 20_000;
const RING_MERGES: usize = RING_N / 2;
const RING_WALK_PASSES: usize = 8;

type VerusTrackedVec =
    ForkHistory<verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, true>>;
type VerusRing<const TRACK: bool> = verus::CircularList<verus::Opt<VRingKey>, VRingNode, TRACK>;

// ---------------------------------------------------------------------------
// vec/try_extend
// ---------------------------------------------------------------------------

fn bench_vec_try_extend(c: &mut Criterion) {
    let mut g = c.benchmark_group("vec/try_extend");

    g.bench_function("legacy", |b| {
        b.iter_batched_ref(
            || (0..VEC_N as u64).collect::<Vec<_>>(),
            |src| {
                let mut v: prod::VecP<u64, u32, false> = prod::VecP::new();
                for &x in src.iter() {
                    v.push(x);
                }
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function("verified", |b| {
        b.iter_batched_ref(
            || (0..VEC_N as u64).collect::<Vec<_>>(),
            |src| {
                let mut v = verus::vec::Vec::<
                    u64,
                    u32,
                    verus::parallel_store::ParallelStore<u64, u32>,
                    false,
                >::new();
                v.try_extend(src).expect("100k fits a u32 index word");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// vec/mark_set_restore
// ---------------------------------------------------------------------------

fn bench_vec_mark_set_restore(c: &mut Criterion) {
    let mut g = c.benchmark_group("vec/mark_set_restore");

    g.bench_function("legacy", |b| {
        b.iter_batched_ref(
            || {
                let mut v: prod::VecP<u64, u32, true> = prod::VecP::new();
                for i in 0..VEC_N {
                    v.push(i as u64);
                }
                v
            },
            |v| {
                let tok = v.mark(prod::ShrinkPolicy::Never);
                let mut x: u64 = 0x9E3779B97F4A7C15;
                for _ in 0..VEC_TOUCHES {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let idx = (x % VEC_N as u64) as u32;
                    v.set(idx, x);
                }
                v.restore(tok);
                black_box(v.len());
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function("verified", |b| {
        type V = ForkHistory<
            verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, true>,
        >;
        b.iter_batched_ref(
            || {
                let mut v: V = ForkHistory::new(verus::vec::Vec::<
                    u64,
                    u32,
                    verus::parallel_store::ParallelStore<u64, u32>,
                    true,
                >::new());
                for i in 0..VEC_N {
                    v.try_push(i as u64).expect("push: within index word");
                }
                v
            },
            |v| {
                let tok = v
                    .mark(verus::vec::ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness");
                let mut x: u64 = 0x9E3779B97F4A7C15;
                for _ in 0..VEC_TOUCHES {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let idx = (x % VEC_N as u64) as u32;
                    v.set(idx, x);
                }
                // Legacy restore == verified restore_and_pop (restore + pop_scope fused; design doc 08 §1).
                assert!(v.restore_and_pop(tok), "restore: own token");
                black_box(v.len());
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// vec/restore_replay
// ---------------------------------------------------------------------------

fn prod_restore_fixture() -> (prod::VecP<u64, u32, true>, prod::VecToken) {
    let mut v: prod::VecP<u64, u32, true> = prod::VecP::new();
    for i in 0..VEC_N {
        v.push(i as u64);
    }
    let warm = v.mark(prod::ShrinkPolicy::Never);
    for i in 0..VEC_TOUCHES {
        v.set(i as u32, i as u64);
    }
    v.restore(warm);

    let token = v.mark(prod::ShrinkPolicy::Never);
    for i in 0..VEC_TOUCHES {
        v.set(i as u32, (i + 999) as u64);
    }
    (v, token)
}

fn verus_restore_fixture() -> (VerusTrackedVec, verus::vec::VecToken) {
    let mut v: VerusTrackedVec = ForkHistory::new(verus::vec::Vec::<
        u64,
        u32,
        verus::parallel_store::ParallelStore<u64, u32>,
        true,
    >::new());
    for i in 0..VEC_N {
        v.try_push(i as u64).expect("push: within index word");
    }
    let warm = v
        .mark(verus::vec::ShrinkPolicy::Never)
        .expect("mark: bounded depth");
    for i in 0..VEC_TOUCHES {
        v.set(i as u32, i as u64);
    }
    assert!(v.restore_and_pop(warm), "restore: own token");

    let token = v
        .mark(verus::vec::ShrinkPolicy::Never)
        .expect("mark: bounded depth");
    for i in 0..VEC_TOUCHES {
        v.set(i as u32, (i + 999) as u64);
    }
    (v, token)
}

fn bench_vec_restore_replay(c: &mut Criterion) {
    let mut g = c.benchmark_group("vec/restore_replay");

    g.bench_function("legacy", |b| {
        b.iter_batched_ref(
            || {
                (0..RESTORE_BATCH)
                    .map(|_| prod_restore_fixture())
                    .collect::<Vec<_>>()
            },
            |fixtures| {
                let mut total = 0usize;
                for (v, token) in fixtures.iter_mut() {
                    v.restore(*token);
                    total += v.len() as usize;
                }
                black_box(total)
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function("verified", |b| {
        b.iter_batched_ref(
            || {
                (0..RESTORE_BATCH)
                    .map(|_| verus_restore_fixture())
                    .collect::<Vec<_>>()
            },
            |fixtures| {
                let mut total = 0usize;
                for (v, token) in fixtures.iter_mut() {
                    assert!(v.restore_and_pop(*token), "restore: own token");
                    total += v.len() as usize;
                }
                black_box(total)
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// vec/push_pop_untracked
// ---------------------------------------------------------------------------

fn bench_vec_push_pop_untracked(c: &mut Criterion) {
    let mut g = c.benchmark_group("vec/push_pop_untracked");

    g.bench_function("legacy", |b| {
        b.iter(|| {
            let mut v: prod::VecP<u64, u32, false> = prod::VecP::new();
            for i in 0..VEC_N {
                v.push(i as u64);
            }
            let mut acc = 0u64;
            while let Some(x) = v.pop() {
                acc = acc.wrapping_add(x);
            }
            black_box(acc)
        })
    });

    g.bench_function("verified", |b| {
        type V = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, false>;
        b.iter(|| {
            let mut v: V = V::new();
            for i in 0..VEC_N {
                v.try_push(i as u64).expect("push: within index word");
            }
            let mut acc = 0u64;
            while let Some(x) = v.pop() {
                acc = acc.wrapping_add(x);
            }
            black_box(acc)
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// list/append_iter
// ---------------------------------------------------------------------------

fn bench_list_append_iter(c: &mut Criterion) {
    let mut g = c.benchmark_group("list/append_iter");

    g.bench_function("legacy", |b| {
        b.iter(|| {
            let mut a: prod::ListArena<PElem, PList, PNode, false> = prod::ListArena::new();
            let mut lists = Vec::with_capacity(LISTS);
            for _ in 0..LISTS {
                lists.push(a.new_list());
            }
            for (k, &l) in lists.iter().enumerate() {
                for j in 0..PER_LIST {
                    a.append(l, PElem::new((k * PER_LIST + j) as u32 & 0x7FFF_FFFF));
                }
            }
            let mut acc = 0u64;
            for &l in &lists {
                for e in a.iter(l) {
                    acc = acc.wrapping_add(e.raw() as u64);
                }
            }
            black_box(acc)
        })
    });

    g.bench_function("verified", |b| {
        b.iter(|| {
            let mut a: verus::ListArena<VElem, VList, VNode, false> = verus::ListArena::new();
            let mut lists = Vec::with_capacity(LISTS);
            for _ in 0..LISTS {
                lists.push(a.try_new_list().expect("within id space"));
            }
            for (k, &l) in lists.iter().enumerate() {
                for j in 0..PER_LIST {
                    a.try_append(l, VElem::new((k * PER_LIST + j) as u32 & 0x7FFF_FFFF))
                        .expect("within id space");
                }
            }
            let mut acc = 0u64;
            for &l in &lists {
                for e in a.iter(l) {
                    acc = acc.wrapping_add(e.raw() as u64);
                }
            }
            black_box(acc)
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// list/splice
// ---------------------------------------------------------------------------

fn bench_list_splice(c: &mut Criterion) {
    let mut g = c.benchmark_group("list/splice");

    g.bench_function("legacy", |b| {
        b.iter(|| {
            let mut a: prod::ListArena<PElem, PList, PNode, false> = prod::ListArena::new();
            let mut lists = Vec::with_capacity(LISTS);
            for k in 0..LISTS {
                let l = a.new_list();
                for j in 0..4 {
                    a.append(l, PElem::new((k * 4 + j) as u32 & 0x7FFF_FFFF));
                }
                lists.push(l);
            }
            // Tournament merge into lists[0].
            let dst = lists[0];
            for &src in &lists[1..] {
                a.splice(dst, src);
            }
            black_box(a.len(dst))
        })
    });

    g.bench_function("verified", |b| {
        b.iter(|| {
            let mut a: verus::ListArena<VElem, VList, VNode, false> = verus::ListArena::new();
            let mut lists = Vec::with_capacity(LISTS);
            for k in 0..LISTS {
                let l = a.try_new_list().expect("within id space");
                for j in 0..4 {
                    a.try_append(l, VElem::new((k * 4 + j) as u32 & 0x7FFF_FFFF))
                        .expect("within id space");
                }
                lists.push(l);
            }
            let dst = lists[0];
            for &src in &lists[1..] {
                a.splice(dst, src);
            }
            black_box(a.len(dst))
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// class_ring: retained pre-integration ring versus verified CircularList
// ---------------------------------------------------------------------------

fn prod_ring_ids(i: usize) -> (PNodeId, PNodeId) {
    (
        prod::DenseId::from_usize(2 * i),
        prod::DenseId::from_usize(2 * i + 1),
    )
}

fn verus_ring_ids(i: usize) -> (VRingNode, VRingNode) {
    (
        VRingNode::from_usize(2 * i),
        VRingNode::from_usize(2 * i + 1),
    )
}

fn prod_ring_build<const TRACK: bool>() -> pring::ProdRing<TRACK> {
    pring::build(RING_N)
}

fn verus_ring_build<const TRACK: bool>() -> VerusRing<TRACK> {
    let mut ring = VerusRing::new();
    for i in 0..RING_N {
        ring.try_add_singleton(verus::Opt::some(VRingKey::from_usize(i)))
            .expect("ring id space");
    }
    ring
}

fn verus_ring_splice<const TRACK: bool>(
    ring: &mut VerusRing<TRACK>,
    survivor: VRingNode,
    absorbed: VRingNode,
) {
    let mut payload = ring.payload_of(absorbed);
    payload.set_none();
    ring.splice_absorb(survivor, absorbed, payload);
}

fn prod_ring_merge_all<const TRACK: bool>(ring: &mut pring::ProdRing<TRACK>) {
    for i in 0..RING_MERGES {
        let (survivor, absorbed) = prod_ring_ids(i);
        pring::splice(ring, survivor, absorbed);
    }
}

fn verus_ring_merge_all<const TRACK: bool>(ring: &mut VerusRing<TRACK>) {
    for i in 0..RING_MERGES {
        let (survivor, absorbed) = verus_ring_ids(i);
        verus_ring_splice(ring, survivor, absorbed);
    }
}

fn bench_class_ring_splice(c: &mut Criterion) {
    let mut g = c.benchmark_group("class_ring/splice_untracked");

    // The merged structure must be OBSERVED, or the untracked pointer swaps
    // are dead stores into a buffer the batch drops right after and LLVM
    // elides them (measured: ~0.6 ns per splice on both sides, physically
    // impossible for two loads and two stores). One ring walk from a
    // black-boxed node keeps every swap alive on both sides at O(ring) cost.
    g.bench_function("legacy", |b| {
        b.iter_batched_ref(
            prod_ring_build::<false>,
            |ring| {
                prod_ring_merge_all(ring);
                let probe = prod_ring_ids(black_box(RING_MERGES / 2)).0;
                black_box((ring.len(), pring::walk(ring, probe)))
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function("verified", |b| {
        b.iter_batched_ref(
            verus_ring_build::<false>,
            |ring| {
                verus_ring_merge_all(ring);
                let probe = verus_ring_ids(black_box(RING_MERGES / 2)).0;
                black_box((ring.len(), ring.iter_class(probe).count()))
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

fn bench_class_ring_walk(c: &mut Criterion) {
    let mut g = c.benchmark_group("class_ring/walk");

    g.bench_function("legacy", |b| {
        b.iter_batched_ref(
            || {
                let mut ring = prod_ring_build::<false>();
                prod_ring_merge_all(&mut ring);
                ring
            },
            |ring| {
                let mut total = 0usize;
                for _ in 0..RING_WALK_PASSES {
                    for i in 0..RING_MERGES {
                        total += pring::walk(ring, prod_ring_ids(i).0);
                    }
                }
                black_box(total)
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function("verified", |b| {
        b.iter_batched_ref(
            || {
                let mut ring = verus_ring_build::<false>();
                verus_ring_merge_all(&mut ring);
                ring
            },
            |ring| {
                let mut total = 0usize;
                for _ in 0..RING_WALK_PASSES {
                    for i in 0..RING_MERGES {
                        total += ring.iter_class(verus_ring_ids(i).0).count();
                    }
                }
                black_box(total)
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

fn bench_class_ring_merge_restore(c: &mut Criterion) {
    let mut g = c.benchmark_group("class_ring/merge_restore");

    g.bench_function("legacy", |b| {
        b.iter_batched_ref(
            prod_ring_build::<true>,
            |ring| {
                let token = ring.mark(prod::ShrinkPolicy::Never);
                prod_ring_merge_all(ring);
                ring.restore(token);
                black_box(ring.len())
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function("verified", |b| {
        b.iter_batched_ref(
            || ForkHistory::new(verus_ring_build::<true>()),
            |ring| {
                let token = ring
                    .mark(verus::vec::ShrinkPolicy::Never)
                    .expect("mark: bounded depth");
                verus_ring_merge_all(ring);
                assert!(ring.restore_and_pop(token), "restore: own token");
                black_box(ring.len())
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// map/intern: SpMap as the interner it is in the e-graph (LitValStore
// pattern) — insert-or-hit with a mark/restore cycle. u64 keys (primitive
// key model on both sides).
// ---------------------------------------------------------------------------

fn bench_map_intern(c: &mut Criterion) {
    let mut g = c.benchmark_group("map/intern");
    const N: usize = 50_000;

    g.bench_function("legacy", |b| {
        b.iter(|| {
            let mut m: prod::Map<u64, (), usize, true> = prod::Map::new();
            let mut x: u64 = 0x243F_6A88_85A3_08D3;
            let tok = {
                for _ in 0..N / 2 {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    // 50% duplicate rate: intern hits and misses both measured
                    let key = x % (N as u64 / 2);
                    if m.id_of(&key).is_none() {
                        m.insert(key, ());
                    }
                }
                m.mark(prod::ShrinkPolicy::Never)
            };
            for _ in 0..N / 2 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let key = x % (N as u64);
                if m.id_of(&key).is_none() {
                    m.insert(key, ());
                }
            }
            m.restore(tok);
            black_box(m.len())
        })
    });

    g.bench_function("verified", |b| {
        b.iter(|| {
            let mut m: ForkHistory<verus::SpMap<u64, (), usize, true>> =
                ForkHistory::new(verus::SpMap::new());
            let mut x: u64 = 0x243F_6A88_85A3_08D3;
            let tok = {
                for _ in 0..N / 2 {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let key = x % (N as u64 / 2);
                    if m.id_of(&key).is_none() {
                        m.try_insert(key, ()).expect("insert: within index word");
                    }
                }
                m.mark(verus::ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness")
            };
            for _ in 0..N / 2 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let key = x % (N as u64);
                if m.id_of(&key).is_none() {
                    m.try_insert(key, ()).expect("insert: within index word");
                }
            }
            assert!(m.restore_and_pop(tok), "restore: own token");
            black_box(m.len())
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// sparse_set/churn: add/remove churn under a mark, then restore — the
// e-class registry pattern (stable ids, recycled slots).
// ---------------------------------------------------------------------------

fn bench_sparse_set_churn(c: &mut Criterion) {
    let mut g = c.benchmark_group("sparse_set/churn");
    const N: usize = 20_000;

    g.bench_function("legacy", |b| {
        b.iter(|| {
            let mut s: prod::SparseSet<u64, PElem, prod::ParallelStore<u64, PElem>, true> =
                prod::SparseSet::new();
            let mut ids = Vec::with_capacity(N);
            for i in 0..N {
                ids.push(s.add(i as u64));
            }
            let tok = s.mark(prod::ShrinkPolicy::Never);
            let mut x: u64 = 0xB5297A4D;
            for _ in 0..N / 2 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let k = (x % ids.len() as u64) as usize;
                let id = ids[k];
                if s.contains(id) {
                    s.remove(id);
                } else {
                    ids[k] = s.add(x);
                }
            }
            s.restore(tok);
            black_box(s.len().raw())
        })
    });

    g.bench_function("verified", |b| {
        b.iter(|| {
            let mut s: ForkHistory<
                verus::SparseSet<u64, VElem, verus::ParallelStore<u64, VElem>, true>,
            > = ForkHistory::new(verus::SparseSet::new());
            let mut ids = Vec::with_capacity(N);
            for i in 0..N {
                ids.push(s.try_add(i as u64).expect("add: within id space"));
            }
            let tok = s
                .mark(verus::ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness");
            let mut x: u64 = 0xB5297A4D;
            for _ in 0..N / 2 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let k = (x % ids.len() as u64) as usize;
                let id = ids[k];
                if s.contains(id) {
                    s.remove(id);
                } else {
                    ids[k] = s.try_add(x).expect("add: within id space");
                }
            }
            assert!(s.restore_and_pop(tok), "restore: own token");
            black_box(s.len().raw())
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// aov/log: AppendOnlyVec as the append log it is (node store pattern) —
// bulk push, slice scan, mark/restore.
//
// Read this row with its phase rows below. The composite is alignment-bound:
// on unchanged source its verified/legacy speedup moved between 0.92× and
// 1.02× with `-C llvm-args=-align-loops` / `-align-all-blocks` alone
// (2026-09-20), the two push loops are the same instructions, and every phase
// on its own is at parity or better. `aov/push`, `aov/push_presized`,
// `aov/scan` and `aov/mark_restore` are the rows that measure the container.
// ---------------------------------------------------------------------------

fn bench_aov_log(c: &mut Criterion) {
    let mut g = c.benchmark_group("aov/log");
    const N: usize = 100_000;

    g.bench_function("legacy", |b| {
        b.iter(|| {
            let mut v: prod::AppendOnlyVec<u64, usize, true> = prod::AppendOnlyVec::new();
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
            black_box((acc, v.len()))
        })
    });

    g.bench_function("verified", |b| {
        b.iter(|| {
            let mut v: ForkHistory<verus::AppendOnlyVec<u64, usize, true>> =
                ForkHistory::new(verus::AppendOnlyVec::new());
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
            black_box((acc, v.len()))
        })
    });

    g.finish();
}

fn aov_filled_legacy(n: usize) -> prod::AppendOnlyVec<u64, usize, true> {
    let mut v = prod::AppendOnlyVec::new();
    for i in 0..n {
        v.push(i as u64);
    }
    v
}

fn aov_filled_verified(n: usize) -> ForkHistory<verus::AppendOnlyVec<u64, usize, true>> {
    let mut v = ForkHistory::new(verus::AppendOnlyVec::new());
    for i in 0..n {
        v.try_push(i as u64).expect("push: within index word");
    }
    v
}

/// `aov/log` taken apart: the pushes from empty (growth included), the pushes
/// into a presized vec, the slice scan, and mark/push/restore, each on both
/// sides. These are the container's own costs; the composite above adds the
/// allocator's and the compiler's placement.
fn bench_aov_phases(c: &mut Criterion) {
    const N: usize = 100_000;

    let mut g = c.benchmark_group("aov/push");
    g.bench_function("legacy", |b| {
        b.iter(|| {
            let mut v: prod::AppendOnlyVec<u64, usize, true> = prod::AppendOnlyVec::new();
            for i in 0..N {
                v.push(i as u64);
            }
            black_box(v.len())
        })
    });
    g.bench_function("verified", |b| {
        b.iter(|| {
            let mut v: ForkHistory<verus::AppendOnlyVec<u64, usize, true>> =
                ForkHistory::new(verus::AppendOnlyVec::new());
            for i in 0..N {
                v.try_push(i as u64).expect("push: within index word");
            }
            black_box(v.len())
        })
    });
    g.finish();

    let mut g = c.benchmark_group("aov/push_presized");
    g.bench_function("legacy", |b| {
        b.iter_batched_ref(
            || {
                let mut v = aov_filled_legacy(N);
                let tok = v.mark(prod::ShrinkPolicy::Never);
                v.restore(tok);
                v
            },
            |v| {
                for i in 0..N {
                    v.push(i as u64);
                }
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.bench_function("verified", |b| {
        b.iter_batched_ref(
            || aov_filled_verified(N),
            |v| {
                for i in 0..N {
                    v.try_push(i as u64).expect("push: within index word");
                }
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.finish();

    let mut g = c.benchmark_group("aov/scan");
    let l = aov_filled_legacy(N);
    let v = aov_filled_verified(N);
    g.bench_function("legacy", |b| {
        b.iter(|| {
            let mut acc = 0u64;
            for x in l.as_slice() {
                acc = acc.wrapping_add(*x);
            }
            black_box(acc)
        })
    });
    g.bench_function("verified", |b| {
        b.iter(|| {
            let mut acc = 0u64;
            for x in v.as_slice() {
                acc = acc.wrapping_add(*x);
            }
            black_box(acc)
        })
    });
    g.finish();

    let mut g = c.benchmark_group("aov/mark_restore");
    g.bench_function("legacy", |b| {
        b.iter_batched_ref(
            || aov_filled_legacy(N / 2),
            |v| {
                let tok = v.mark(prod::ShrinkPolicy::Never);
                for i in 0..N / 2 {
                    v.push(i as u64);
                }
                v.restore(tok);
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.bench_function("verified", |b| {
        b.iter_batched_ref(
            || aov_filled_verified(N / 2),
            |v| {
                let tok = v
                    .mark(verus::ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness");
                for i in 0..N / 2 {
                    v.try_push(i as u64).expect("push: within index word");
                }
                assert!(v.restore_and_pop(tok), "restore: own token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.finish();
}

// ---------------------------------------------------------------------------
// map/intern_string + map/intern_composite: the CONSUMER key shapes (the
// e-graph's registries key by String; AU maps key by tuples of ids). SipHash's
// per-byte cost is where the std-vs-hashbrown gap widens beyond the u64
// numbers, so both representative key shapes are measured.
// ---------------------------------------------------------------------------

fn bench_map_intern_string(c: &mut Criterion) {
    let mut g = c.benchmark_group("map/intern_string");
    const N: usize = 20_000;

    fn keys() -> Vec<String> {
        (0..N)
            .map(|i| format!("op::namespace_{}::symbol_{:08}", i % 37, i))
            .collect()
    }

    g.bench_function("legacy", |b| {
        let ks = keys();
        b.iter(|| {
            let mut m: prod::Map<String, u32, usize, true> = prod::Map::new();
            for (i, k) in ks.iter().enumerate() {
                if m.id_of(k).is_none() {
                    m.insert(k.clone(), i as u32);
                }
            }
            let mut hits = 0usize;
            for k in &ks {
                if m.id_of(k).is_some() {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });

    g.bench_function("verified", |b| {
        let ks = keys();
        b.iter(|| {
            let mut m: verus::SpMap<String, u32, usize, true> = verus::SpMap::new();
            for (i, k) in ks.iter().enumerate() {
                if m.id_of(k).is_none() {
                    m.try_insert(k.clone(), i as u32)
                        .expect("insert: within index word");
                }
            }
            let mut hits = 0usize;
            for k in &ks {
                if m.id_of(k).is_some() {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });

    g.finish();
}

fn bench_map_intern_composite(c: &mut Criterion) {
    let mut g = c.benchmark_group("map/intern_composite");
    const N: usize = 20_000;
    // (u32, Vec<u32>) — the AU by_structure / space-index key shape.
    fn keys() -> Vec<(u32, Vec<u32>)> {
        (0..N as u32)
            .map(|i| {
                (
                    i % 97,
                    vec![i, i.wrapping_mul(7), i.wrapping_mul(31), i % 13],
                )
            })
            .collect()
    }

    g.bench_function("legacy", |b| {
        let ks = keys();
        b.iter(|| {
            let mut m: prod::Map<(u32, Vec<u32>), u32, usize, true> = prod::Map::new();
            for (i, k) in ks.iter().enumerate() {
                if m.id_of(k).is_none() {
                    m.insert(k.clone(), i as u32);
                }
            }
            let mut hits = 0usize;
            for k in &ks {
                if m.id_of(k).is_some() {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });

    g.bench_function("verified", |b| {
        let ks = keys();
        b.iter(|| {
            let mut m: verus::SpMap<(u32, Vec<u32>), u32, usize, true> = verus::SpMap::new();
            for (i, k) in ks.iter().enumerate() {
                if m.id_of(k).is_none() {
                    m.try_insert(k.clone(), i as u32)
                        .expect("insert: within index word");
                }
            }
            let mut hits = 0usize;
            for k in &ks {
                if m.id_of(k).is_some() {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// map/restore_small_suffix: the SMT-style map cycle — a large live map, then
// per frame a handful of inserts and a restore. Legacy rebuilds the whole
// index (one key clone per survivor) on every restore; the verified map
// unwinds only the discarded suffix. Measured with u64 keys (LitValStore
// pattern) and String keys (registry pattern, where the clone is a heap
// allocation). The map is built once per bench; each iteration returns it
// to the marked state, so the setup is outside the timed region.
// ---------------------------------------------------------------------------

fn bench_map_restore_small_suffix(c: &mut Criterion) {
    const LIVE: usize = 100_000;
    const PER_FRAME: u64 = 64;

    let mut g = c.benchmark_group("map/restore_small_suffix");
    g.bench_function("legacy", |b| {
        let mut m: prod::Map<u64, (), usize, true> = prod::Map::new();
        for k in 0..LIVE as u64 {
            m.insert(k, ());
        }
        b.iter(|| {
            let tok = m.mark(prod::ShrinkPolicy::Never);
            for k in 0..PER_FRAME {
                m.insert(LIVE as u64 + k, ());
            }
            m.restore(tok);
            black_box(m.len())
        })
    });
    g.bench_function("verified", |b| {
        let mut m: ForkHistory<verus::SpMap<u64, (), usize, true>> =
            ForkHistory::new(verus::SpMap::new());
        for k in 0..LIVE as u64 {
            m.try_insert(k, ()).expect("insert: within index word");
        }
        b.iter(|| {
            let tok = m
                .mark(verus::ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness");
            for k in 0..PER_FRAME {
                m.try_insert(LIVE as u64 + k, ())
                    .expect("insert: within index word");
            }
            assert!(m.restore_and_pop(tok), "restore: own token");
            black_box(m.len())
        })
    });
    g.finish();

    let mut g = c.benchmark_group("map/restore_small_suffix_string");
    const LIVE_STRING: usize = 20_000;
    fn key(i: u64) -> String {
        format!("op::namespace_{}::symbol_{:08}", i % 37, i)
    }
    g.bench_function("legacy", |b| {
        let mut m: prod::Map<String, u32, usize, true> = prod::Map::new();
        for i in 0..LIVE_STRING as u64 {
            m.insert(key(i), i as u32);
        }
        let fresh: Vec<String> = (0..PER_FRAME)
            .map(|k| key(LIVE_STRING as u64 + k))
            .collect();
        b.iter(|| {
            let tok = m.mark(prod::ShrinkPolicy::Never);
            for (k, s) in fresh.iter().enumerate() {
                m.insert(s.clone(), k as u32);
            }
            m.restore(tok);
            black_box(m.len())
        })
    });
    g.bench_function("verified", |b| {
        let mut m: ForkHistory<verus::SpMap<String, u32, usize, true>> =
            ForkHistory::new(verus::SpMap::new());
        for i in 0..LIVE_STRING as u64 {
            m.try_insert(key(i), i as u32)
                .expect("insert: within index word");
        }
        let fresh: Vec<String> = (0..PER_FRAME)
            .map(|k| key(LIVE_STRING as u64 + k))
            .collect();
        b.iter(|| {
            let tok = m
                .mark(verus::ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness");
            for (k, s) in fresh.iter().enumerate() {
                m.try_insert(s.clone(), k as u32)
                    .expect("insert: within index word");
            }
            assert!(m.restore_and_pop(tok), "restore: own token");
            black_box(m.len())
        })
    });
    g.finish();
}
criterion_group!(
    benches,
    bench_vec_try_extend,
    bench_vec_mark_set_restore,
    bench_vec_restore_replay,
    bench_vec_push_pop_untracked,
    bench_list_append_iter,
    bench_list_splice,
    bench_class_ring_splice,
    bench_class_ring_walk,
    bench_class_ring_merge_restore,
    bench_map_intern,
    bench_map_intern_string,
    bench_map_intern_composite,
    bench_map_restore_small_suffix,
    bench_sparse_set_churn,
    bench_aov_log,
    bench_aov_phases,
);
criterion_main!(benches);
