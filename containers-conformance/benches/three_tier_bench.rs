// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E5 measurements for the policy-driven three-tier tracked Vec runtime.
//!
//! Fixtures are deterministic and are rebuilt outside timed loops. Production
//! arms are workload controls only: production implements first-capture-wins
//! history, not the explicit trail/hot/cold policies measured here. Tier
//! occupancy and capacity-based byte diagnostics are emitted outside timing.

use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;
use verus::group::ForkHistory;
use verus::{
    MarkOptions, ReclaimPolicy, RolloverPolicy, ShrinkPolicy, StoreKind, TierLimit, TierPolicy,
};

type V = ForkHistory<verus::VecD<u64, u32, true>>;
type P = prod::VecP<u64, u32, true>;

const N: usize = 8_192;
const WRITES: usize = 512;
const FRAMES: usize = 8;
const TRACE_FRAMES: usize = 24;
const TRACE_WRITES: usize = 32;

struct CountingAllocator;

static ALLOCATOR_LIVE_BYTES: AtomicUsize = AtomicUsize::new(0);
static ALLOCATOR_PEAK_BYTES: AtomicUsize = AtomicUsize::new(0);

#[global_allocator]
static GLOBAL_ALLOCATOR: CountingAllocator = CountingAllocator;

fn record_allocation(bytes: usize) {
    let live = ALLOCATOR_LIVE_BYTES.fetch_add(bytes, Ordering::SeqCst) + bytes;
    ALLOCATOR_PEAK_BYTES.fetch_max(live, Ordering::SeqCst);
}

fn record_deallocation(bytes: usize) {
    ALLOCATOR_LIVE_BYTES.fetch_sub(bytes, Ordering::SeqCst);
}

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            record_allocation(layout.size());
        }
        ptr
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if !ptr.is_null() {
            record_allocation(layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) };
        record_deallocation(layout.size());
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let new_ptr = unsafe { System.realloc(ptr, layout, new_size) };
        if !new_ptr.is_null() {
            if new_size >= layout.size() {
                record_allocation(new_size - layout.size());
            } else {
                record_deallocation(layout.size() - new_size);
            }
        }
        new_ptr
    }
}

#[derive(Clone, Copy)]
struct AllocationWindow {
    before_bytes: usize,
    after_bytes: usize,
    peak_bytes: usize,
}

impl AllocationWindow {
    fn peak_growth_bytes(self) -> usize {
        self.peak_bytes.saturating_sub(self.before_bytes)
    }

    fn transient_peak_bytes(self) -> usize {
        self.peak_bytes
            .saturating_sub(self.before_bytes.max(self.after_bytes))
    }
}

fn allocation_window(operation: impl FnOnce()) -> AllocationWindow {
    let before_bytes = ALLOCATOR_LIVE_BYTES.load(Ordering::SeqCst);
    ALLOCATOR_PEAK_BYTES.store(before_bytes, Ordering::SeqCst);
    operation();
    let after_bytes = ALLOCATOR_LIVE_BYTES.load(Ordering::SeqCst);
    let peak_bytes = ALLOCATOR_PEAK_BYTES
        .load(Ordering::SeqCst)
        .max(before_bytes)
        .max(after_bytes);
    AllocationWindow {
        before_bytes,
        after_bytes,
        peak_bytes,
    }
}

fn report_allocation(label: &str, window: AllocationWindow) {
    eprintln!(
        "three_tier_allocator label={label} before_bytes={} after_bytes={} peak_bytes={} peak_growth_bytes={} transient_peak_bytes={}",
        window.before_bytes,
        window.after_bytes,
        window.peak_bytes,
        window.peak_growth_bytes(),
        window.transient_peak_bytes(),
    );
}

#[derive(Clone, Copy)]
struct Profile {
    name: &'static str,
    kind: StoreKind,
    policy: TierPolicy,
}

const PROFILES: [Profile; 4] = [
    Profile {
        name: "trail_smt",
        kind: StoreKind::Trail,
        policy: TierPolicy::smt(),
    },
    Profile {
        name: "trail_adaptive",
        kind: StoreKind::Trail,
        policy: TierPolicy::adaptive(),
    },
    Profile {
        name: "inline_restore_optimized",
        kind: StoreKind::Inline,
        policy: TierPolicy::restore_optimized(),
    },
    Profile {
        name: "parallel_buffered_unique",
        kind: StoreKind::Parallel,
        policy: TierPolicy::fully_buffered_unique(),
    },
];

fn finite_all_tiers_policy() -> TierPolicy {
    TierPolicy {
        trail: TierLimit::Frames(1),
        hot: TierLimit::Frames(1),
        cold_reclaim: ReclaimPolicy::RetainCapacity,
    }
}

fn build_verus(kind: StoreKind, policy: TierPolicy) -> V {
    let mut v = ForkHistory::new(verus::VecD::<u64, u32, true>::new_kind_with_policy(
        kind, policy,
    ));
    for i in 0..N {
        v.try_push(i as u64).expect("fixture fits u32 index");
    }
    v
}

fn build_prod() -> P {
    let mut v = P::new();
    for i in 0..N {
        v.push(i as u64);
    }
    v
}

#[inline]
fn index_for(write: usize, distinct: usize, frame: usize) -> u32 {
    ((write.wrapping_mul(2_053) + frame.wrapping_mul(97)) % distinct) as u32
}

fn write_verus(v: &mut V, writes: usize, distinct: usize, frame: usize) {
    for write in 0..writes {
        let index = index_for(write, distinct, frame);
        let value = ((frame as u64) << 40) ^ write as u64 ^ 0x9E37_79B9;
        v.set_index(index, value);
    }
}

fn write_prod(v: &mut P, writes: usize, distinct: usize, frame: usize) {
    for write in 0..writes {
        let index = index_for(write, distinct, frame);
        let value = ((frame as u64) << 40) ^ write as u64 ^ 0x9E37_79B9;
        v.set(index, value);
    }
}

fn mark_verus(v: &mut V) -> verus::vec::VecToken {
    v.mark(ShrinkPolicy::Never)
        .expect("fixture depth is bounded")
}

fn build_closed_trail(frames: usize, writes: usize, distinct: usize) -> V {
    let mut v = build_verus(StoreKind::Trail, TierPolicy::smt());
    mark_verus(&mut v);
    for frame in 0..frames {
        write_verus(&mut v, writes, distinct, frame);
        mark_verus(&mut v);
    }
    assert!(v.tier_stats().trail_frames > frames);
    v
}

fn build_closed_hot(frames: usize, writes: usize, distinct: usize) -> V {
    let mut v = build_verus(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    mark_verus(&mut v);
    for frame in 0..frames {
        write_verus(&mut v, writes, distinct, frame);
        mark_verus(&mut v);
    }
    assert!(v.tier_stats().hot_frames > frames);
    v
}

fn trail_restore_fixture() -> (V, verus::vec::VecToken) {
    let mut v = build_verus(StoreKind::Trail, TierPolicy::smt());
    let token = mark_verus(&mut v);
    write_verus(&mut v, WRITES, 32, 0);
    assert_eq!(v.tier_stats().trail_entries, WRITES);
    (v, token)
}

fn hot_restore_fixture() -> (V, verus::vec::VecToken) {
    let mut v = build_verus(StoreKind::Parallel, TierPolicy::fully_buffered_unique());
    let token = mark_verus(&mut v);
    write_verus(&mut v, WRITES, WRITES, 0);
    assert_eq!(v.tier_stats().hot_entries, WRITES);
    (v, token)
}

fn cold_restore_fixture() -> (V, verus::vec::VecToken) {
    let mut v = build_verus(StoreKind::Parallel, TierPolicy::restore_optimized());
    let token = mark_verus(&mut v);
    write_verus(&mut v, WRITES, WRITES, 0);
    mark_verus(&mut v);
    assert!(v.tier_stats().cold_frames > 0);
    (v, token)
}

fn all_tiers_restore_fixture() -> (V, verus::vec::VecToken) {
    let mut v = build_verus(StoreKind::Trail, finite_all_tiers_policy());
    let root = mark_verus(&mut v);
    for frame in 0..6 {
        write_verus(&mut v, WRITES, 64, frame);
        mark_verus(&mut v);
    }
    let stats = v.tier_stats();
    assert!(stats.trail_frames > 0 && stats.hot_frames > 0 && stats.cold_frames > 0);
    (v, root)
}

fn prod_restore_fixture() -> (P, prod::VecToken) {
    let mut v = build_prod();
    let token = v.mark(prod::ShrinkPolicy::Never);
    write_prod(&mut v, WRITES, WRITES, 0);
    (v, token)
}

fn promotion_fixture() -> (V, verus::vec::VecToken) {
    let mut v = build_verus(StoreKind::Parallel, TierPolicy::restore_optimized());
    let mut tokens = Vec::with_capacity(5);
    for frame in 0..5 {
        tokens.push(mark_verus(&mut v));
        write_verus(&mut v, WRITES, WRITES, frame);
    }
    mark_verus(&mut v);
    assert!(v.tier_stats().cold_frames >= 5);
    (v, tokens[2])
}

fn logical_tier_bytes(stats: verus::TierStats) -> (usize, usize, usize) {
    let pair = core::mem::size_of::<(u64, u32)>();
    let trail = stats.trail_entries * pair
        + stats.trail_frames * core::mem::size_of::<verus::frame::TrailFrame<u32>>();
    let hot = stats.hot_entries * pair
        + stats.hot_frames * core::mem::size_of::<verus::frame::HotFrame<u32>>();
    let cold = stats.cold_values * core::mem::size_of::<u64>()
        + stats.cold_runs * core::mem::size_of::<verus::frame::IndexRun<u32>>()
        + stats.cold_frames * core::mem::size_of::<verus::frame::ColdFrameHdr<u32>>();
    (trail, hot, cold)
}

fn report_one(label: &str, v: &V) {
    let stats = v.tier_stats();
    let (trail_bytes, hot_bytes, cold_bytes) = logical_tier_bytes(stats);
    eprintln!(
        "three_tier_stats label={label} stats={stats:?} logical_trail_bytes={trail_bytes} logical_hot_bytes={hot_bytes} logical_cold_bytes={cold_bytes} tracking_bytes={} total_bytes={}",
        v.tracking_bytes(),
        v.total_bytes()
    );
}

fn report_tier_diagnostics() {
    let (trail, _) = trail_restore_fixture();
    report_one("restore_trail", &trail);
    let (hot, _) = hot_restore_fixture();
    report_one("restore_hot", &hot);
    let (cold, _) = cold_restore_fixture();
    report_one("restore_cold", &cold);
    let (all, _) = all_tiers_restore_fixture();
    report_one("restore_all", &all);

    let mut converted = build_closed_trail(FRAMES, WRITES, 32);
    let before = converted.tracking_bytes();
    let before_stats = converted.tier_stats();
    let before_logical = logical_tier_bytes(before_stats);
    converted.flush_trail();
    let after_stats = converted.tier_stats();
    let after_logical = logical_tier_bytes(after_stats);
    eprintln!(
        "three_tier_conversion label=trail_to_hot before_bytes={before} after_bytes={} reclaimed_bytes={} before_logical={before_logical:?} after_logical={after_logical:?} stats={after_stats:?}",
        converted.tracking_bytes(),
        before.saturating_sub(converted.tracking_bytes()),
    );

    let mut compressed = build_closed_hot(FRAMES, WRITES, WRITES);
    let before = compressed.tracking_bytes();
    let before_stats = compressed.tier_stats();
    let before_logical = logical_tier_bytes(before_stats);
    compressed.compress_hot();
    let after_stats = compressed.tier_stats();
    let after_logical = logical_tier_bytes(after_stats);
    eprintln!(
        "three_tier_conversion label=hot_to_cold before_bytes={before} after_bytes={} reclaimed_bytes={} before_logical={before_logical:?} after_logical={after_logical:?} stats={after_stats:?}",
        compressed.tracking_bytes(),
        before.saturating_sub(compressed.tracking_bytes()),
    );

    let (mut promoted, token) = promotion_fixture();
    assert!(promoted.restore(token), "own ancestor token");
    report_one("promotion_after_restore", &promoted);
}

fn report_allocation_diagnostics() {
    let mut converted = build_closed_trail(FRAMES, WRITES, 32);
    let window = allocation_window(|| converted.flush_trail());
    report_allocation("trail_to_hot", window);

    let mut compressed = build_closed_hot(FRAMES, WRITES, WRITES);
    let window = allocation_window(|| compressed.compress_hot());
    report_allocation("hot_to_cold", window);

    let (mut all, root) = all_tiers_restore_fixture();
    let window = allocation_window(|| assert!(all.restore(root), "own root token"));
    report_allocation("restore_all", window);

    let (mut promoted, ancestor) = promotion_fixture();
    let window = allocation_window(|| {
        assert!(promoted.restore(ancestor), "own ancestor token");
        let inner = mark_verus(&mut promoted);
        write_verus(&mut promoted, WRITES, 64, 17);
        assert!(promoted.restore(inner), "new token after promotion");
    });
    report_allocation("promotion", window);
}

fn bench_write(c: &mut Criterion) {
    for &(density, distinct) in &[("low_duplicates", WRITES), ("high_duplicates", 32)] {
        let mut group = c.benchmark_group(format!("three_tier/write/{density}"));
        for profile in PROFILES {
            group.bench_function(profile.name, |b| {
                b.iter_batched_ref(
                    || {
                        let mut v = build_verus(profile.kind, profile.policy);
                        mark_verus(&mut v);
                        v
                    },
                    |v| {
                        write_verus(v, WRITES, distinct, 0);
                        black_box(v.diff_log_len())
                    },
                    BatchSize::LargeInput,
                )
            });
        }
        group.bench_function("production", |b| {
            b.iter_batched_ref(
                || {
                    let mut v = build_prod();
                    v.mark(prod::ShrinkPolicy::Never);
                    v
                },
                |v| {
                    write_prod(v, WRITES, distinct, 0);
                    black_box(v.len())
                },
                BatchSize::LargeInput,
            )
        });
        group.finish();
    }
}

fn bench_mark(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/mark");
    group.bench_function("no_rollover_smt", |b| {
        b.iter_batched_ref(
            || {
                let mut v = build_verus(StoreKind::Trail, TierPolicy::smt());
                mark_verus(&mut v);
                write_verus(&mut v, WRITES, WRITES, 0);
                v
            },
            |v| black_box(mark_verus(v)),
            BatchSize::LargeInput,
        )
    });
    group.bench_function("explicit_defer_smt", |b| {
        b.iter_batched_ref(
            || {
                let mut v = build_verus(StoreKind::Trail, TierPolicy::smt());
                mark_verus(&mut v);
                write_verus(&mut v, WRITES, WRITES, 0);
                v
            },
            |v| {
                v.member
                    .try_push_frame_with(MarkOptions::new(
                        ShrinkPolicy::Never,
                        RolloverPolicy::Defer,
                    ))
                    .expect("fixture remains within mark limits");
                black_box(v.mint_pushed().expect("the member is one frame ahead"))
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("no_rollover_production", |b| {
        b.iter_batched_ref(
            || {
                let mut v = build_prod();
                v.mark(prod::ShrinkPolicy::Never);
                write_prod(&mut v, WRITES, WRITES, 0);
                v
            },
            |v| black_box(v.mark(prod::ShrinkPolicy::Never)),
            BatchSize::LargeInput,
        )
    });
    group.bench_function("trail_to_hot", |b| {
        b.iter_batched_ref(
            || {
                let policy = TierPolicy {
                    trail: TierLimit::Frames(0),
                    hot: TierLimit::Unbounded,
                    cold_reclaim: ReclaimPolicy::RetainCapacity,
                };
                let mut v = build_verus(StoreKind::Trail, policy);
                mark_verus(&mut v);
                write_verus(&mut v, WRITES, 32, 0);
                v
            },
            |v| black_box(mark_verus(v)),
            BatchSize::LargeInput,
        )
    });
    group.bench_function("hot_to_cold", |b| {
        b.iter_batched_ref(
            || {
                let mut v = build_verus(StoreKind::Parallel, TierPolicy::restore_optimized());
                mark_verus(&mut v);
                write_verus(&mut v, WRITES, WRITES, 0);
                v
            },
            |v| black_box(mark_verus(v)),
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn bench_restore(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/restore");
    group.bench_function("trail_one_frame", |b| {
        b.iter_batched_ref(
            trail_restore_fixture,
            |(v, token)| {
                // Legacy restore == verified restore_and_pop (restore + pop_scope fused; design doc 08 §1).
                assert!(v.restore_and_pop(*token), "own token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("hot_one_frame", |b| {
        b.iter_batched_ref(
            hot_restore_fixture,
            |(v, token)| {
                assert!(v.restore_and_pop(*token), "own token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("cold_one_frame", |b| {
        b.iter_batched_ref(
            cold_restore_fixture,
            |(v, token)| {
                assert!(v.restore_and_pop(*token), "own token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("all_tiers_deep", |b| {
        b.iter_batched_ref(
            all_tiers_restore_fixture,
            |(v, token)| {
                assert!(v.restore_and_pop(*token), "own root token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    // Semantics B on its own (design doc 08 §1): the restore keeps the
    // checkpoint's frame open — the SAT core's backjump. No legacy pair.
    group.bench_function("hot_one_frame_keep_open", |b| {
        b.iter_batched_ref(
            hot_restore_fixture,
            |(v, token)| {
                assert!(v.restore(*token), "own token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("cold_one_frame_keep_open", |b| {
        b.iter_batched_ref(
            cold_restore_fixture,
            |(v, token)| {
                assert!(v.restore(*token), "own token");
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("production_one_frame", |b| {
        b.iter_batched_ref(
            prod_restore_fixture,
            |(v, token)| {
                v.restore(*token);
                black_box(v.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn bench_conversion(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/conversion");
    group.bench_function("trail_to_hot_dedupe", |b| {
        b.iter_batched_ref(
            || build_closed_trail(FRAMES, WRITES, 32),
            |v| {
                v.flush_trail();
                black_box(v.diff_log_len())
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("hot_to_cold_runs", |b| {
        b.iter_batched_ref(
            || build_closed_hot(FRAMES, WRITES, WRITES),
            |v| {
                v.compress_hot();
                black_box(v.diff_log_len())
            },
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn bench_promotion(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/promotion");
    group.bench_function("cold_survivor_write_restore", |b| {
        b.iter_batched_ref(
            promotion_fixture,
            |(v, ancestor)| {
                assert!(v.restore_and_pop(*ancestor), "own ancestor token");
                let inner = mark_verus(v);
                write_verus(v, WRITES, 64, 17);
                assert!(v.restore_and_pop(inner), "new token after promotion");
                black_box(v.diff_log_len())
            },
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn bench_adaptive(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/adaptive_decision");
    for &(name, distinct) in &[
        ("low_duplicates_no_convert", WRITES),
        ("high_duplicates_convert", 32),
    ] {
        group.bench_with_input(BenchmarkId::new(name, WRITES), &distinct, |b, &distinct| {
            b.iter_batched_ref(
                || {
                    let mut v = build_verus(StoreKind::Trail, TierPolicy::adaptive());
                    mark_verus(&mut v);
                    write_verus(&mut v, WRITES, distinct, 0);
                    v
                },
                |v| black_box(mark_verus(v)),
                BatchSize::LargeInput,
            )
        });
    }
    group.finish();
}

fn run_smt_backtrack() -> usize {
    let mut v = build_verus(StoreKind::Trail, TierPolicy::smt());
    for frame in 0..64 {
        let token = mark_verus(&mut v);
        write_verus(&mut v, TRACE_WRITES, 8, frame);
        assert!(v.restore_and_pop(token), "own token");
    }
    v.len() as usize
}

fn run_prod_backtrack() -> usize {
    let mut v = build_prod();
    for frame in 0..64 {
        let token = v.mark(prod::ShrinkPolicy::Never);
        write_prod(&mut v, TRACE_WRITES, 8, frame);
        v.restore(token);
    }
    v.len() as usize
}

fn run_nested(kind: StoreKind, policy: TierPolicy) -> usize {
    let mut v = build_verus(kind, policy);
    let root = mark_verus(&mut v);
    for frame in 0..TRACE_FRAMES {
        write_verus(&mut v, TRACE_WRITES, 16, frame);
        mark_verus(&mut v);
    }
    assert!(v.restore_and_pop(root), "own root token");
    v.len() as usize
}

fn run_prod_nested() -> usize {
    let mut v = build_prod();
    let root = v.mark(prod::ShrinkPolicy::Never);
    for frame in 0..TRACE_FRAMES {
        write_prod(&mut v, TRACE_WRITES, 16, frame);
        v.mark(prod::ShrinkPolicy::Never);
    }
    v.restore(root);
    v.len() as usize
}

fn bench_end_to_end(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier/end_to_end");
    group.bench_function("smt_backtrack", |b| {
        b.iter(|| black_box(run_smt_backtrack()))
    });
    group.bench_function("smt_backtrack_production", |b| {
        b.iter(|| black_box(run_prod_backtrack()))
    });
    group.bench_function("eqsat_retained", |b| {
        b.iter(|| black_box(run_nested(StoreKind::Trail, TierPolicy::adaptive())))
    });
    group.bench_function("eqsat_retained_production", |b| {
        b.iter(|| black_box(run_prod_nested()))
    });
    group.bench_function("restore_optimized", |b| {
        b.iter(|| {
            black_box(run_nested(
                StoreKind::Parallel,
                TierPolicy::restore_optimized(),
            ))
        })
    });
    group.bench_function("buffered_unique", |b| {
        b.iter(|| {
            black_box(run_nested(
                StoreKind::Parallel,
                TierPolicy::fully_buffered_unique(),
            ))
        })
    });
    group.finish();
}

// Versioned container-level matrix. Keep these IDs stable independently of the
// original E5 IDs above so future measurements can compare like for like.
const V1_DEEP_FRAMES: usize = 64;
const V1_LARGE_FRAMES: usize = 256;
const V1_TRACE_WRITES: usize = 64;

type VI = ForkHistory<verus::VecI<u64, u32, true>>;
type VP = ForkHistory<verus::VecP<u64, u32, true>>;
type VT = ForkHistory<verus::VecT<u64, u32, true>>;
type PI = prod::VecI<u64, u32, true>;

fn unbounded_policy() -> TierPolicy {
    TierPolicy {
        trail: TierLimit::Unbounded,
        hot: TierLimit::Unbounded,
        cold_reclaim: ReclaimPolicy::RetainCapacity,
    }
}

trait MatrixColumn: Sized {
    type Token: Copy;

    fn new(policy: TierPolicy) -> Self;
    fn push(&mut self, value: u64);
    fn set(&mut self, index: u32, value: u64);
    fn mark(&mut self) -> Self::Token;
    fn restore(&mut self, token: Self::Token);
    fn len(&self) -> usize;
}

trait MeasuredMatrixColumn: MatrixColumn {
    fn mark_with(&mut self, rollover: RolloverPolicy) -> Self::Token;
    fn apply_adaptive(&mut self, input: verus::AdaptiveInput) -> verus::AdaptiveReport;
    fn stats(&self) -> verus::TierStats;
    fn tracking_bytes(&self) -> usize;
    fn total_bytes(&self) -> usize;
}

// The write and push wrappers are `#[inline(always)]`, not `#[inline]`: a
// column type used by every group in this file has enough call sites that
// LLVM declines the hint, and the wrapper then becomes a standalone function
// whose prologue spills for the largest arm of the runtime-selected column on
// every call — a harness cost no consumer pays (a consumer writes to a column
// from one place). Measured: the same wrapper generated under a second name
// with one call site ran the dyn Trail write row at 861 ns against 1575 ns.
macro_rules! verified_matrix_column {
    ($wrapper:ident, $inner:ty, $constructor:expr) => {
        struct $wrapper($inner);

        impl MatrixColumn for $wrapper {
            type Token = verus::vec::VecToken;

            #[inline]
            fn new(policy: TierPolicy) -> Self {
                Self(($constructor)(policy))
            }

            #[inline(always)]
            fn push(&mut self, value: u64) {
                self.0
                    .try_push(value)
                    .expect("matrix fixture fits u32 index");
            }

            #[inline(always)]
            fn set(&mut self, index: u32, value: u64) {
                self.0.set_index(index, value);
            }

            #[inline]
            fn mark(&mut self) -> Self::Token {
                self.0
                    .mark(ShrinkPolicy::Never)
                    .expect("matrix fixture depth is bounded")
            }

            #[inline]
            fn restore(&mut self, token: Self::Token) {
                assert!(self.0.restore_and_pop(token), "own live matrix token");
            }

            #[inline]
            fn len(&self) -> usize {
                self.0.len() as usize
            }
        }

        impl MeasuredMatrixColumn for $wrapper {
            #[inline]
            fn mark_with(&mut self, rollover: RolloverPolicy) -> Self::Token {
                self.0
                    .member
                    .try_push_frame_with(MarkOptions::new(ShrinkPolicy::Never, rollover))
                    .expect("matrix fixture depth is bounded");
                self.0.mint_pushed().expect("the member is one frame ahead")
            }

            #[inline]
            fn apply_adaptive(&mut self, input: verus::AdaptiveInput) -> verus::AdaptiveReport {
                self.0.apply_adaptive(input)
            }

            #[inline]
            fn stats(&self) -> verus::TierStats {
                self.0.tier_stats()
            }

            #[inline]
            fn tracking_bytes(&self) -> usize {
                self.0.tracking_bytes()
            }

            #[inline]
            fn total_bytes(&self) -> usize {
                self.0.total_bytes()
            }
        }
    };
}

verified_matrix_column!(DynInline, V, |policy| ForkHistory::new(
    verus::VecD::<u64, u32, true>::new_kind_with_policy(StoreKind::Inline, policy)
));
verified_matrix_column!(DynParallel, V, |policy| ForkHistory::new(
    verus::VecD::<u64, u32, true>::new_kind_with_policy(StoreKind::Parallel, policy)
));
verified_matrix_column!(DynTrail, V, |policy| ForkHistory::new(verus::VecD::<
    u64,
    u32,
    true,
>::new_kind_with_policy(
    StoreKind::Trail,
    policy
)));
verified_matrix_column!(StaticVecI, VI, |policy| ForkHistory::new(verus::VecI::<
    u64,
    u32,
    true,
>::new_with_policy(
    policy
)));
verified_matrix_column!(StaticVecP, VP, |policy| ForkHistory::new(verus::VecP::<
    u64,
    u32,
    true,
>::new_with_policy(
    policy
)));
verified_matrix_column!(StaticVecT, VT, |policy| ForkHistory::new(verus::VecT::<
    u64,
    u32,
    true,
>::new_with_policy(
    policy
)));

macro_rules! production_matrix_column {
    ($wrapper:ident, $inner:ty) => {
        struct $wrapper($inner);

        impl MatrixColumn for $wrapper {
            type Token = prod::VecToken;

            #[inline]
            fn new(_policy: TierPolicy) -> Self {
                Self(<$inner>::new())
            }

            #[inline(always)]
            fn push(&mut self, value: u64) {
                self.0.push(value);
            }

            #[inline(always)]
            fn set(&mut self, index: u32, value: u64) {
                self.0.set(index, value);
            }

            #[inline]
            fn mark(&mut self) -> Self::Token {
                self.0.mark(prod::ShrinkPolicy::Never)
            }

            #[inline]
            fn restore(&mut self, token: Self::Token) {
                self.0.restore(token);
            }

            #[inline]
            fn len(&self) -> usize {
                self.0.len() as usize
            }
        }
    };
}

production_matrix_column!(ProductionVecI, PI);
production_matrix_column!(ProductionVecP, P);

fn build_matrix<C: MatrixColumn>(policy: TierPolicy) -> C {
    let mut v = C::new(policy);
    for i in 0..N {
        v.push(i as u64);
    }
    v
}

fn write_matrix<C: MatrixColumn>(v: &mut C, writes: usize, distinct: usize, frame: usize) {
    for write in 0..writes {
        let index = index_for(write, distinct, frame);
        let value = ((frame as u64) << 40) ^ write as u64 ^ 0x9E37_79B9;
        v.set(index, value);
    }
}

fn mark_deferred<C: MeasuredMatrixColumn>(v: &mut C) -> C::Token {
    v.mark_with(RolloverPolicy::Defer)
}

fn bench_matrix_write<C: MatrixColumn>(b: &mut criterion::Bencher<'_>, distinct: usize) {
    b.iter_batched_ref(
        || {
            let mut v = build_matrix::<C>(unbounded_policy());
            v.mark();
            v
        },
        |v| {
            write_matrix(v, WRITES, distinct, 0);
            black_box(v);
        },
        BatchSize::LargeInput,
    );
}

fn shallow_restore_matrix_fixture<C: MatrixColumn>() -> (C, C::Token) {
    let mut v = build_matrix::<C>(unbounded_policy());
    let root = v.mark();
    write_matrix(&mut v, WRITES, 32, 0);
    (v, root)
}

fn deep_restore_matrix_fixture<C: MatrixColumn>() -> (C, C::Token) {
    let mut v = build_matrix::<C>(unbounded_policy());
    let root = v.mark();
    for frame in 0..V1_DEEP_FRAMES {
        write_matrix(&mut v, V1_TRACE_WRITES, 16, frame);
        v.mark();
    }
    (v, root)
}

fn direct_cold_restore_matrix_fixture<C: MeasuredMatrixColumn>() -> (C, C::Token) {
    let mut v = build_matrix::<C>(unbounded_policy());
    let root = mark_deferred(&mut v);
    write_matrix(&mut v, WRITES, WRITES, 0);
    v.mark_with(RolloverPolicy::ForceClosed {
        trail_to_hot: true,
        hot_to_cold: true,
    });
    assert_eq!(v.stats().cold_frames, 1);
    assert_eq!(v.stats().cold_runs, 1);
    (v, root)
}

fn bench_matrix_shallow_restore<C: MatrixColumn>(b: &mut criterion::Bencher<'_>) {
    b.iter_batched_ref(
        shallow_restore_matrix_fixture::<C>,
        |(v, root)| {
            v.restore(*root);
            black_box(v.len())
        },
        BatchSize::LargeInput,
    );
}

fn bench_matrix_deep_restore<C: MatrixColumn>(b: &mut criterion::Bencher<'_>) {
    b.iter_batched_ref(
        deep_restore_matrix_fixture::<C>,
        |(v, root)| {
            v.restore(*root);
            black_box(v.len())
        },
        BatchSize::LargeInput,
    );
}

fn bench_matrix_direct_cold_restore<C: MeasuredMatrixColumn>(b: &mut criterion::Bencher<'_>) {
    b.iter_batched_ref(
        direct_cold_restore_matrix_fixture::<C>,
        |(v, root)| {
            v.restore(*root);
            black_box(v.len())
        },
        BatchSize::LargeInput,
    );
}

macro_rules! register_verified_matrix {
    ($group:ident, $runner:ident $(, $arg:expr)*) => {
        $group.bench_function("dyn_inline", |b| $runner::<DynInline>(b $(, $arg)*));
        $group.bench_function("dyn_parallel", |b| $runner::<DynParallel>(b $(, $arg)*));
        $group.bench_function("dyn_trail", |b| $runner::<DynTrail>(b $(, $arg)*));
        $group.bench_function("static_veci", |b| $runner::<StaticVecI>(b $(, $arg)*));
        $group.bench_function("static_vecp", |b| $runner::<StaticVecP>(b $(, $arg)*));
        $group.bench_function("static_vect", |b| $runner::<StaticVecT>(b $(, $arg)*));
    };
}

macro_rules! register_production_matrix {
    ($group:ident, $runner:ident $(, $arg:expr)*) => {
        $group.bench_function("production_veci", |b| {
            $runner::<ProductionVecI>(b $(, $arg)*)
        });
        $group.bench_function("production_vecp", |b| {
            $runner::<ProductionVecP>(b $(, $arg)*)
        });
    };
}

fn bench_v1_write(c: &mut Criterion) {
    for &(density, distinct) in &[("low_duplicates", WRITES), ("high_duplicates", 32)] {
        let mut group = c.benchmark_group(format!("three_tier_v1/write/{density}"));
        register_verified_matrix!(group, bench_matrix_write, distinct);
        register_production_matrix!(group, bench_matrix_write, distinct);
        group.finish();
    }
}

fn bench_v1_restore(c: &mut Criterion) {
    let mut shallow = c.benchmark_group("three_tier_v1/restore/shallow_high_duplicates");
    register_verified_matrix!(shallow, bench_matrix_shallow_restore);
    register_production_matrix!(shallow, bench_matrix_shallow_restore);
    shallow.finish();

    let mut deep = c.benchmark_group("three_tier_v1/restore/deep_64_frames");
    register_verified_matrix!(deep, bench_matrix_deep_restore);
    register_production_matrix!(deep, bench_matrix_deep_restore);
    deep.finish();

    let mut cold = c.benchmark_group("three_tier_v1/restore/direct_cold_contiguous");
    register_verified_matrix!(cold, bench_matrix_direct_cold_restore);
    cold.finish();
}

fn trail_rollover_fixture() -> V {
    let policy = TierPolicy {
        trail: TierLimit::Frames(0),
        hot: TierLimit::Unbounded,
        cold_reclaim: ReclaimPolicy::RetainCapacity,
    };
    let mut v = build_verus(StoreKind::Trail, policy);
    {
        v.member
            .try_push_frame_with(MarkOptions::new(ShrinkPolicy::Never, RolloverPolicy::Defer))
            .expect("fixture depth is bounded");
        v.mint_pushed().expect("the member is one frame ahead")
    };
    write_verus(&mut v, WRITES, 32, 0);
    v
}

fn hot_rollover_fixture() -> V {
    let policy = TierPolicy {
        trail: TierLimit::Unbounded,
        hot: TierLimit::Frames(0),
        cold_reclaim: ReclaimPolicy::RetainCapacity,
    };
    let mut v = build_verus(StoreKind::Parallel, policy);
    {
        v.member
            .try_push_frame_with(MarkOptions::new(ShrinkPolicy::Never, RolloverPolicy::Defer))
            .expect("fixture depth is bounded");
        v.mint_pushed().expect("the member is one frame ahead")
    };
    write_verus(&mut v, WRITES, WRITES, 0);
    v
}

fn hot_singleton_rollover_fixture() -> V {
    let policy = TierPolicy {
        trail: TierLimit::Unbounded,
        hot: TierLimit::Frames(0),
        cold_reclaim: ReclaimPolicy::RetainCapacity,
    };
    let mut v = build_verus(StoreKind::Parallel, policy);
    {
        v.member
            .try_push_frame_with(MarkOptions::new(ShrinkPolicy::Never, RolloverPolicy::Defer))
            .expect("fixture depth is bounded");
        v.mint_pushed().expect("the member is one frame ahead")
    };
    for write in 0..WRITES {
        let index = (write * 2) as u32;
        v.set_index(index, 0x51A6_1E70 ^ write as u64);
    }
    v
}

fn both_rollover_fixture() -> V {
    let policy = TierPolicy {
        trail: TierLimit::Frames(0),
        hot: TierLimit::Frames(0),
        cold_reclaim: ReclaimPolicy::RetainCapacity,
    };
    let mut v = build_verus(StoreKind::Trail, policy);
    {
        v.member
            .try_push_frame_with(MarkOptions::new(ShrinkPolicy::Never, RolloverPolicy::Defer))
            .expect("fixture depth is bounded");
        v.mint_pushed().expect("the member is one frame ahead")
    };
    write_verus(&mut v, WRITES, 32, 0);
    v
}

fn bench_rollover_action(
    b: &mut criterion::Bencher<'_>,
    fixture: fn() -> V,
    rollover: RolloverPolicy,
) {
    b.iter_batched_ref(
        fixture,
        |v| {
            black_box({
                v.member
                    .try_push_frame_with(MarkOptions::new(ShrinkPolicy::Never, rollover))
                    .expect("fixture depth is bounded");
                v.mint_pushed().expect("the member is one frame ahead")
            })
        },
        BatchSize::LargeInput,
    );
}

/// Per-mark rollover of small Trail frames: every mark migrates the 8-write
/// frame it closes, so the Trail-to-Hot dedupe runs once per mark. This is
/// the shape where the dedupe set's allocation is comparable to the dedupe
/// itself (the other rollover cases migrate one 512-write frame).
fn small_frames_fixture() -> V {
    let policy = TierPolicy {
        trail: TierLimit::Frames(0),
        hot: TierLimit::Unbounded,
        cold_reclaim: ReclaimPolicy::RetainCapacity,
    };
    let mut v = build_verus(StoreKind::Trail, policy);
    {
        v.member
            .try_push_frame_with(MarkOptions::new(ShrinkPolicy::Never, RolloverPolicy::Defer))
            .expect("fixture depth is bounded");
        v.mint_pushed().expect("the member is one frame ahead")
    };
    v
}

fn bench_rollover_small_frames(b: &mut criterion::Bencher<'_>) {
    b.iter_batched_ref(
        small_frames_fixture,
        |v| {
            for k in 0..64usize {
                write_verus(v, 8, 8, k);
                black_box({
                    v.member
                        .try_push_frame_with(MarkOptions::new(
                            ShrinkPolicy::Never,
                            RolloverPolicy::ApplyConfigured,
                        ))
                        .expect("fixture depth is bounded");
                    v.mint_pushed().expect("the member is one frame ahead")
                });
            }
        },
        BatchSize::LargeInput,
    );
}

fn bench_rollover_compatible(b: &mut criterion::Bencher<'_>, fixture: fn() -> V) {
    b.iter_batched_ref(
        fixture,
        |v| black_box(v.mark(ShrinkPolicy::Never).expect("fixture is bounded")),
        BatchSize::LargeInput,
    );
}

fn bench_v1_rollover(c: &mut Criterion) {
    let mut trail = c.benchmark_group("three_tier_v1/rollover/trail_to_hot_high_duplicates");
    trail.bench_function("defer", |b| {
        bench_rollover_action(b, trail_rollover_fixture, RolloverPolicy::Defer)
    });
    trail.bench_function("apply_configured", |b| {
        bench_rollover_action(b, trail_rollover_fixture, RolloverPolicy::ApplyConfigured)
    });
    trail.bench_function("force_closed", |b| {
        bench_rollover_action(
            b,
            trail_rollover_fixture,
            RolloverPolicy::ForceClosed {
                trail_to_hot: true,
                hot_to_cold: false,
            },
        )
    });
    trail.finish();

    let mut small = c.benchmark_group("three_tier_v1/rollover/trail_to_hot_small_frames_per_mark");
    small.bench_function("apply_configured_x64", bench_rollover_small_frames);
    small.finish();

    let mut hot = c.benchmark_group("three_tier_v1/rollover/hot_to_cold_contiguous");
    hot.bench_function("defer", |b| {
        bench_rollover_action(b, hot_rollover_fixture, RolloverPolicy::Defer)
    });
    hot.bench_function("apply_configured", |b| {
        bench_rollover_action(b, hot_rollover_fixture, RolloverPolicy::ApplyConfigured)
    });
    hot.bench_function("force_closed", |b| {
        bench_rollover_action(
            b,
            hot_rollover_fixture,
            RolloverPolicy::ForceClosed {
                trail_to_hot: false,
                hot_to_cold: true,
            },
        )
    });
    hot.finish();

    let mut singleton = c.benchmark_group("three_tier_v1/rollover/hot_to_cold_singleton_runs");
    singleton.bench_function("defer", |b| {
        bench_rollover_action(b, hot_singleton_rollover_fixture, RolloverPolicy::Defer)
    });
    singleton.bench_function("apply_configured", |b| {
        bench_rollover_action(
            b,
            hot_singleton_rollover_fixture,
            RolloverPolicy::ApplyConfigured,
        )
    });
    singleton.bench_function("force_closed", |b| {
        bench_rollover_action(
            b,
            hot_singleton_rollover_fixture,
            RolloverPolicy::ForceClosed {
                trail_to_hot: false,
                hot_to_cold: true,
            },
        )
    });
    singleton.finish();

    let mut both = c.benchmark_group("three_tier_v1/rollover/both_edges_high_duplicates");
    both.bench_function("source_compatible_try_mark", |b| {
        bench_rollover_compatible(b, both_rollover_fixture)
    });
    both.bench_function("explicit_apply_configured", |b| {
        bench_rollover_action(b, both_rollover_fixture, RolloverPolicy::ApplyConfigured)
    });
    both.bench_function("force_closed", |b| {
        bench_rollover_action(
            b,
            both_rollover_fixture,
            RolloverPolicy::ForceClosed {
                trail_to_hot: true,
                hot_to_cold: true,
            },
        )
    });
    both.finish();
}

fn promotion_matrix_fixture<C: MeasuredMatrixColumn>() -> (C, C::Token) {
    let mut v = build_matrix::<C>(unbounded_policy());
    let mut tokens = Vec::with_capacity(9);
    for frame in 0..8 {
        tokens.push(mark_deferred(&mut v));
        write_matrix(&mut v, WRITES, 64, frame);
    }
    v.mark_with(RolloverPolicy::ForceClosed {
        trail_to_hot: true,
        hot_to_cold: true,
    });
    assert!(v.stats().cold_frames >= 8);
    (v, tokens[3])
}

fn bench_matrix_promotion<C: MeasuredMatrixColumn>(b: &mut criterion::Bencher<'_>) {
    b.iter_batched_ref(
        promotion_matrix_fixture::<C>,
        |(v, ancestor)| {
            v.restore(*ancestor);
            let inner = mark_deferred(v);
            write_matrix(v, WRITES, 64, 17);
            v.restore(inner);
            black_box(v.len())
        },
        BatchSize::LargeInput,
    );
}

fn bench_v1_promotion(c: &mut Criterion) {
    let mut group = c.benchmark_group("three_tier_v1/promotion/cold_survivor_write_restore");
    register_verified_matrix!(group, bench_matrix_promotion);
    group.finish();
}

fn run_matrix_smt_backtrack<C: MatrixColumn>() -> usize {
    let mut v = build_matrix::<C>(unbounded_policy());
    for frame in 0..128 {
        let token = v.mark();
        write_matrix(&mut v, V1_TRACE_WRITES, 8, frame);
        v.restore(token);
    }
    v.len()
}

fn run_matrix_eqsat_retained<C: MatrixColumn>() -> usize {
    let mut v = build_matrix::<C>(unbounded_policy());
    let root = v.mark();
    for frame in 0..V1_DEEP_FRAMES {
        write_matrix(&mut v, V1_TRACE_WRITES, 16, frame);
        v.mark();
    }
    v.restore(root);
    v.len()
}

fn run_matrix_eclasses<C: MatrixColumn>() -> usize {
    let mut v = build_matrix::<C>(unbounded_policy());
    for round in 0..32 {
        let token = v.mark();
        for merge in 1..256 {
            let parent = ((merge * 17 + round * 13) % 256) as u32;
            v.set(parent, ((round as u64) << 32) | merge as u64);
            v.set(0, parent as u64);
        }
        v.restore(token);
    }
    v.len()
}

fn run_matrix_large_retained<C: MatrixColumn>() -> usize {
    let mut v = build_matrix::<C>(unbounded_policy());
    let root = v.mark();
    for frame in 0..V1_LARGE_FRAMES {
        write_matrix(&mut v, V1_TRACE_WRITES, 16, frame);
        v.mark();
    }
    v.restore(root);
    v.len()
}

fn bench_matrix_smt<C: MatrixColumn>(b: &mut criterion::Bencher<'_>) {
    b.iter(|| black_box(run_matrix_smt_backtrack::<C>()));
}

fn bench_matrix_eqsat<C: MatrixColumn>(b: &mut criterion::Bencher<'_>) {
    b.iter(|| black_box(run_matrix_eqsat_retained::<C>()));
}

fn bench_matrix_eclasses<C: MatrixColumn>(b: &mut criterion::Bencher<'_>) {
    b.iter(|| black_box(run_matrix_eclasses::<C>()));
}

fn bench_matrix_large<C: MatrixColumn>(b: &mut criterion::Bencher<'_>) {
    b.iter(|| black_box(run_matrix_large_retained::<C>()));
}

fn bench_v1_traces(c: &mut Criterion) {
    let mut smt = c.benchmark_group("three_tier_v1/trace/smt_backtracking_128");
    register_verified_matrix!(smt, bench_matrix_smt);
    register_production_matrix!(smt, bench_matrix_smt);
    smt.finish();

    let mut eqsat = c.benchmark_group("three_tier_v1/trace/eqsat_retained_64_frames");
    register_verified_matrix!(eqsat, bench_matrix_eqsat);
    register_production_matrix!(eqsat, bench_matrix_eqsat);
    eqsat.finish();

    let mut eclasses = c.benchmark_group("three_tier_v1/trace/eclasses_mark_merge_restore_32");
    register_verified_matrix!(eclasses, bench_matrix_eclasses);
    register_production_matrix!(eclasses, bench_matrix_eclasses);
    eclasses.finish();

    let mut large = c.benchmark_group("three_tier_v1/trace/large_retained_256_frames");
    register_verified_matrix!(large, bench_matrix_large);
    register_production_matrix!(large, bench_matrix_large);
    large.finish();
}

fn workload_shape(writes: usize, distinct: usize, frame: usize) -> (usize, usize, usize) {
    let mut indices = Vec::with_capacity(writes);
    for write in 0..writes {
        indices.push(index_for(write, distinct, frame) as usize);
    }
    indices.sort_unstable();
    indices.dedup();
    let runs = indices
        .iter()
        .enumerate()
        .filter(|(position, index)| *position == 0 || **index != indices[*position - 1] + 1)
        .count();
    (writes, indices.len(), runs)
}

fn report_matrix_column<C: MeasuredMatrixColumn>(
    label: &str,
    writes: usize,
    distinct: usize,
    frames: usize,
) {
    let mut v = build_matrix::<C>(unbounded_policy());
    mark_deferred(&mut v);
    for frame in 0..frames {
        write_matrix(&mut v, writes, distinct, frame);
        mark_deferred(&mut v);
    }
    let stats = v.stats();
    let (trail, hot, cold) = logical_tier_bytes(stats);
    let (w, u, r) = workload_shape(writes, distinct, 0);
    eprintln!(
        "three_tier_v1_stats label={label} frames={frames} W={w} U={u} R={r} stats={stats:?} logical_trail_bytes={trail} logical_hot_bytes={hot} logical_cold_bytes={cold} tracking_bytes={} total_bytes={}",
        v.tracking_bytes(),
        v.total_bytes(),
    );
}

fn report_rollover_window(label: &str, mut v: V, rollover: RolloverPolicy) {
    let before_stats = v.tier_stats();
    let before_logical = logical_tier_bytes(before_stats);
    let before_tracking = v.tracking_bytes();
    let before_total = v.total_bytes();
    let window = allocation_window(|| {
        {
            v.member
                .try_push_frame_with(MarkOptions::new(ShrinkPolicy::Never, rollover))
                .expect("diagnostic fixture depth is bounded");
            v.mint_pushed().expect("the member is one frame ahead")
        };
    });
    let after_stats = v.tier_stats();
    let after_logical = logical_tier_bytes(after_stats);
    eprintln!(
        "three_tier_v1_transition label={label} before_stats={before_stats:?} after_stats={after_stats:?} before_logical={before_logical:?} after_logical={after_logical:?} before_tracking_bytes={before_tracking} after_tracking_bytes={} before_total_bytes={before_total} after_total_bytes={} allocator_before_bytes={} allocator_after_bytes={} allocator_peak_bytes={} allocator_peak_growth_bytes={} allocator_transient_peak_bytes={}",
        v.tracking_bytes(),
        v.total_bytes(),
        window.before_bytes,
        window.after_bytes,
        window.peak_bytes,
        window.peak_growth_bytes(),
        window.transient_peak_bytes(),
    );
}

fn report_adaptive_inputs() {
    let pair = core::mem::size_of::<(u64, u32)>();
    let run = core::mem::size_of::<verus::frame::IndexRun<u32>>();
    for &(label, w, u, r, budget) in &[
        ("high_duplicates_contiguous", WRITES, 32, 1, 4_096usize),
        ("unique_contiguous", WRITES, WRITES, 1, 8_192usize),
        ("unique_singleton_runs", WRITES, WRITES, WRITES, 16_384usize),
    ] {
        let trail_bytes = w * pair;
        let hot_bytes = u * pair;
        let cold_bytes = u * core::mem::size_of::<u64>() + r * run;
        let candidate = if trail_bytes > budget && w >= u.saturating_mul(2) {
            if cold_bytes <= budget && u >= r.saturating_mul(2) {
                "trail_to_hot_to_cold"
            } else {
                "trail_to_hot"
            }
        } else if hot_bytes > budget && cold_bytes <= budget && u >= r.saturating_mul(2) {
            "hot_to_cold"
        } else {
            "defer"
        };
        eprintln!(
            "three_tier_v1_policy_input label={label} W={w} U={u} R={r} explicit_budget_bytes={budget} logical_entry_bytes_trail={trail_bytes} logical_entry_bytes_hot={hot_bytes} logical_entry_bytes_cold={cold_bytes} benchmark_only_candidate={candidate}"
        );
    }
}

fn report_v1_diagnostics() {
    report_adaptive_inputs();
    for &(density, distinct) in &[("low_duplicates", WRITES), ("high_duplicates", 32)] {
        report_matrix_column::<DynInline>(
            &format!("write_{density}_dyn_inline"),
            WRITES,
            distinct,
            1,
        );
        report_matrix_column::<DynParallel>(
            &format!("write_{density}_dyn_parallel"),
            WRITES,
            distinct,
            1,
        );
        report_matrix_column::<DynTrail>(
            &format!("write_{density}_dyn_trail"),
            WRITES,
            distinct,
            1,
        );
    }
    report_matrix_column::<DynInline>(
        "large_retained_dyn_inline",
        V1_TRACE_WRITES,
        16,
        V1_LARGE_FRAMES,
    );
    report_matrix_column::<DynParallel>(
        "large_retained_dyn_parallel",
        V1_TRACE_WRITES,
        16,
        V1_LARGE_FRAMES,
    );
    report_matrix_column::<DynTrail>(
        "large_retained_dyn_trail",
        V1_TRACE_WRITES,
        16,
        V1_LARGE_FRAMES,
    );

    report_rollover_window(
        "trail_to_hot_high_duplicates",
        trail_rollover_fixture(),
        RolloverPolicy::ForceClosed {
            trail_to_hot: true,
            hot_to_cold: false,
        },
    );
    report_rollover_window(
        "hot_to_cold_contiguous_W512_U512_R1",
        hot_rollover_fixture(),
        RolloverPolicy::ForceClosed {
            trail_to_hot: false,
            hot_to_cold: true,
        },
    );
    report_rollover_window(
        "hot_to_cold_singleton_W512_U512_R512",
        hot_singleton_rollover_fixture(),
        RolloverPolicy::ForceClosed {
            trail_to_hot: false,
            hot_to_cold: true,
        },
    );
    report_rollover_window(
        "both_edges_high_duplicates",
        both_rollover_fixture(),
        RolloverPolicy::ForceClosed {
            trail_to_hot: true,
            hot_to_cold: true,
        },
    );
}

fn adaptive_v2_input(budget: usize) -> verus::AdaptiveInput {
    verus::AdaptiveInput {
        max_closed_history_bytes: budget,
        min_writes_per_unique: verus::Ratio::new(2, 1).expect("nonzero ratio denominator"),
        min_uniques_per_run: verus::Ratio::new(2, 1).expect("nonzero ratio denominator"),
    }
}

fn adaptive_v2_policy(reclaim: ReclaimPolicy) -> TierPolicy {
    TierPolicy {
        cold_reclaim: reclaim,
        ..unbounded_policy()
    }
}

fn adaptive_v2_fixture<C: MeasuredMatrixColumn>(
    writes: usize,
    distinct: usize,
    frames: usize,
    singleton_runs: bool,
    reclaim: ReclaimPolicy,
) -> C {
    let mut v = build_matrix::<C>(adaptive_v2_policy(reclaim));
    mark_deferred(&mut v);
    for frame in 0..frames {
        if singleton_runs {
            for write in 0..writes {
                let index = (write * 2 + frame % 2) as u32;
                v.set(index, ((frame as u64) << 40) ^ write as u64 ^ 0x51A6_1E70);
            }
        } else {
            write_matrix(&mut v, writes, distinct, frame);
        }
        mark_deferred(&mut v);
    }
    v
}

fn bench_matrix_adaptive_v2<C: MeasuredMatrixColumn>(
    b: &mut criterion::Bencher<'_>,
    writes: usize,
    distinct: usize,
    frames: usize,
    singleton_runs: bool,
    budget: usize,
    reclaim: ReclaimPolicy,
) {
    let input = adaptive_v2_input(budget);
    b.iter_batched_ref(
        || adaptive_v2_fixture::<C>(writes, distinct, frames, singleton_runs, reclaim),
        |v| black_box(v.apply_adaptive(input)),
        BatchSize::LargeInput,
    );
}

macro_rules! register_dyn_adaptive_v2 {
    ($group:ident, $writes:expr, $distinct:expr, $frames:expr, $singletons:expr, $budget:expr) => {
        $group.bench_function("dyn_inline", |b| {
            bench_matrix_adaptive_v2::<DynInline>(
                b,
                $writes,
                $distinct,
                $frames,
                $singletons,
                $budget,
                ReclaimPolicy::RetainCapacity,
            )
        });
        $group.bench_function("dyn_parallel", |b| {
            bench_matrix_adaptive_v2::<DynParallel>(
                b,
                $writes,
                $distinct,
                $frames,
                $singletons,
                $budget,
                ReclaimPolicy::RetainCapacity,
            )
        });
        $group.bench_function("dyn_trail", |b| {
            bench_matrix_adaptive_v2::<DynTrail>(
                b,
                $writes,
                $distinct,
                $frames,
                $singletons,
                $budget,
                ReclaimPolicy::RetainCapacity,
            )
        });
    };
}

macro_rules! register_dyn_adaptive_v2_shrink {
    ($group:ident, $writes:expr, $distinct:expr, $frames:expr, $singletons:expr, $budget:expr) => {
        $group.bench_function("dyn_inline_shrink", |b| {
            bench_matrix_adaptive_v2::<DynInline>(
                b,
                $writes,
                $distinct,
                $frames,
                $singletons,
                $budget,
                ReclaimPolicy::ShrinkToFit,
            )
        });
        $group.bench_function("dyn_parallel_shrink", |b| {
            bench_matrix_adaptive_v2::<DynParallel>(
                b,
                $writes,
                $distinct,
                $frames,
                $singletons,
                $budget,
                ReclaimPolicy::ShrinkToFit,
            )
        });
        $group.bench_function("dyn_trail_shrink", |b| {
            bench_matrix_adaptive_v2::<DynTrail>(
                b,
                $writes,
                $distinct,
                $frames,
                $singletons,
                $budget,
                ReclaimPolicy::ShrinkToFit,
            )
        });
    };
}

fn bench_v2_adaptive(c: &mut Criterion) {
    let mut stop_hot =
        c.benchmark_group("three_tier_v2/adaptive/high_duplicates_W512_U32_R1/budget_4096");
    register_dyn_adaptive_v2!(stop_hot, WRITES, 32, 1, false, 4_096);
    stop_hot.finish();

    let mut cascade =
        c.benchmark_group("three_tier_v2/adaptive/high_duplicates_W512_U32_R1/budget_256");
    register_dyn_adaptive_v2!(cascade, WRITES, 32, 1, false, 256);
    cascade.finish();

    let mut contiguous =
        c.benchmark_group("three_tier_v2/adaptive/unique_W512_U512_R1/budget_4096");
    register_dyn_adaptive_v2!(contiguous, WRITES, WRITES, 1, false, 4_096);
    contiguous.finish();

    let mut singleton =
        c.benchmark_group("three_tier_v2/adaptive/singleton_W512_U512_R512/budget_4096");
    register_dyn_adaptive_v2!(singleton, WRITES, WRITES, 1, true, 4_096);
    singleton.finish();

    for budget in [usize::MAX, 65_536, 32_768] {
        let budget_name = if budget == usize::MAX {
            "unbounded".to_owned()
        } else {
            budget.to_string()
        };
        let mut large = c.benchmark_group(format!(
            "three_tier_v2/large/W64_U16_R1_frames256/budget_{budget_name}"
        ));
        register_dyn_adaptive_v2!(large, V1_TRACE_WRITES, 16, V1_LARGE_FRAMES, false, budget);
        if budget != usize::MAX {
            register_dyn_adaptive_v2_shrink!(
                large,
                V1_TRACE_WRITES,
                16,
                V1_LARGE_FRAMES,
                false,
                budget
            );
        }
        large.finish();
    }
}

fn report_adaptive_v2_window<C: MeasuredMatrixColumn>(
    label: &str,
    writes: usize,
    distinct: usize,
    frames: usize,
    singleton_runs: bool,
    budget: usize,
    reclaim: ReclaimPolicy,
) {
    let mut v = adaptive_v2_fixture::<C>(writes, distinct, frames, singleton_runs, reclaim);
    let before_tracking = v.tracking_bytes();
    let before_total = v.total_bytes();
    let mut report = verus::AdaptiveReport::default();
    let window = allocation_window(|| report = v.apply_adaptive(adaptive_v2_input(budget)));
    eprintln!(
        "three_tier_v2_adaptive label={label} budget={budget} reclaim={reclaim:?} report={report:?} stats={:?} before_tracking_bytes={before_tracking} after_tracking_bytes={} before_total_bytes={before_total} after_total_bytes={} allocator_before_bytes={} allocator_after_bytes={} allocator_peak_bytes={} allocator_transient_peak_bytes={}",
        v.stats(),
        v.tracking_bytes(),
        v.total_bytes(),
        window.before_bytes,
        window.after_bytes,
        window.peak_bytes,
        window.transient_peak_bytes(),
    );
}

fn report_v2_diagnostics() {
    for &(label, writes, distinct, frames, singleton_runs, budget) in &[
        ("high_duplicates_budget_4096", WRITES, 32, 1, false, 4_096),
        ("high_duplicates_budget_256", WRITES, 32, 1, false, 256),
        (
            "unique_contiguous_budget_4096",
            WRITES,
            WRITES,
            1,
            false,
            4_096,
        ),
        ("singleton_budget_4096", WRITES, WRITES, 1, true, 4_096),
    ] {
        report_adaptive_v2_window::<DynInline>(
            &format!("{label}_dyn_inline"),
            writes,
            distinct,
            frames,
            singleton_runs,
            budget,
            ReclaimPolicy::RetainCapacity,
        );
        report_adaptive_v2_window::<DynParallel>(
            &format!("{label}_dyn_parallel"),
            writes,
            distinct,
            frames,
            singleton_runs,
            budget,
            ReclaimPolicy::RetainCapacity,
        );
        report_adaptive_v2_window::<DynTrail>(
            &format!("{label}_dyn_trail"),
            writes,
            distinct,
            frames,
            singleton_runs,
            budget,
            ReclaimPolicy::RetainCapacity,
        );
    }

    for budget in [65_536, 32_768] {
        for (reclaim_name, reclaim) in [
            ("retain", ReclaimPolicy::RetainCapacity),
            ("shrink", ReclaimPolicy::ShrinkToFit),
        ] {
            let label = format!("large_budget_{budget}_{reclaim_name}");
            report_adaptive_v2_window::<DynInline>(
                &format!("{label}_dyn_inline"),
                V1_TRACE_WRITES,
                16,
                V1_LARGE_FRAMES,
                false,
                budget,
                reclaim,
            );
            report_adaptive_v2_window::<DynParallel>(
                &format!("{label}_dyn_parallel"),
                V1_TRACE_WRITES,
                16,
                V1_LARGE_FRAMES,
                false,
                budget,
                reclaim,
            );
            report_adaptive_v2_window::<DynTrail>(
                &format!("{label}_dyn_trail"),
                V1_TRACE_WRITES,
                16,
                V1_LARGE_FRAMES,
                false,
                budget,
                reclaim,
            );
        }
    }
}

fn bench_diagnostics(c: &mut Criterion) {
    report_tier_diagnostics();
    report_allocation_diagnostics();
    report_v1_diagnostics();
    report_v2_diagnostics();
    let mut group = c.benchmark_group("three_tier/diagnostics");
    group.bench_function("reporting_excluded_from_timing", |b| {
        b.iter(|| black_box(0usize))
    });
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(10)
        .warm_up_time(Duration::from_millis(250))
        .measurement_time(Duration::from_millis(500));
    targets =
        bench_diagnostics,
        bench_write,
        bench_mark,
        bench_restore,
        bench_conversion,
        bench_promotion,
        bench_adaptive,
        bench_end_to_end,
        bench_v1_write,
        bench_v1_restore,
        bench_v1_rollover,
        bench_v1_promotion,
        bench_v1_traces,
        bench_v2_adaptive
}
criterion_main!(benches);
