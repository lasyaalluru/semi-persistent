// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Trail-column compression at eviction (design doc §7, deliverable 5).
//!
//! A trail column appends EVERY write, duplicates included, so before the
//! dedupe-first eviction converter it never compressed at all. This test
//! drives a `VecT` past the HOT_BUFFER with heavily duplicated per-frame
//! writes and checks two things: the diff log SHRANK below the append count
//! (dedupe-first dropped the later duplicates at eviction), and every
//! restore still reproduces its snapshot exactly (the chronologically first
//! capture per cell is the one reconstruction needs; later duplicates are
//! inert under overlay's first-entry-wins order).

use semi_persistent_containers_verus as verus;
use semi_persistent_containers_verus::group::ForkHistory;
use verus::VecT;
use verus::vec::ShrinkPolicy;

const LEN: usize = 64;
const FRAMES: usize = 14; // HOT_BUFFER is 8; evictions fire from mark 10 on.
const REPS: usize = 4; // duplicate factor per index per frame

#[test]
fn trail_column_compresses_at_eviction_and_restores() {
    let mut v: ForkHistory<VecT<u64, u32>> = ForkHistory::new(VecT::new());
    for i in 0..LEN {
        v.try_push(i as u64).expect("push");
    }

    let mut tokens = Vec::new();
    let mut models: Vec<Vec<u64>> = Vec::new();
    let mut model: Vec<u64> = (0..LEN as u64).collect();
    let mut total_writes: usize = 0;

    let mut seed: u64 = 0x9E3779B97F4A7C15;
    for _frame in 0..FRAMES {
        models.push(model.clone());
        tokens.push(v.mark(ShrinkPolicy::Never).expect("mark"));
        // Duplicated writes: 32 writes over 4 cells per frame, values
        // changing every write. The trail appends all of them; only the
        // FIRST capture per cell per frame matters for restore, and the
        // eviction converter must drop the other 28. (An earlier draft drew
        // indices from an LCG's low 6 bits - a full-period generator, so
        // every frame was accidentally duplicate-FREE and nothing could
        // compress; deterministic duplicates keep the test honest.)
        for _rep in 0..REPS {
            for j in 0..8u32 {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                let idx = j % 4;
                let val = seed ^ (j as u64);
                v.set_index(idx, val);
                model[idx as usize] = val;
                total_writes += 1;
            }
        }
    }

    // Compression: every write was appended, and eviction's dedupe-first
    // dropped the within-frame duplicates, so the log is strictly shorter
    // than the append count. (Each evicted frame wrote 32 entries over at
    // most 32 distinct cells with random collisions, so drops are certain
    // across 14 frames.)
    assert!(
        v.diff_log_len() < total_writes,
        "trail log did not compress: len {} vs {} writes appended",
        v.diff_log_len(),
        total_writes
    );

    // Correctness: unwind every frame, newest first, and compare all cells
    // with the model snapshot taken at its mark.
    while let Some(tok) = tokens.pop() {
        let want = models.pop().expect("model");
        assert!(v.restore(tok), "restore");
        for (i, w) in want.iter().enumerate() {
            assert_eq!(v.get_index(i as u32), *w, "cell {i} diverged after restore");
        }
    }
}

/// The no-check property, observed: every write appends, duplicates
/// included, so before any compression fires the log length equals the
/// write count exactly. A capture check anywhere on the path would drop
/// duplicates and break the equality.
#[test]
fn trail_appends_every_write_before_compression() {
    let mut v: ForkHistory<VecT<u64, u32>> = ForkHistory::new(VecT::new());
    for i in 0..16u64 {
        v.try_push(i).expect("push");
    }
    let mut writes = 0usize;
    // Stay at or below the buffer so compression never fires.
    for _frame in 0..4 {
        v.mark(ShrinkPolicy::Never).expect("mark");
        for rep in 0..5u64 {
            for j in 0..4u32 {
                v.set_index(j, rep * 100 + j as u64);
                writes += 1;
            }
        }
        assert_eq!(
            v.diff_log_len(),
            writes,
            "a write did not append: the trail hot path is supposed to be check-free"
        );
    }
}

/// First-entry-wins through the HOT path: restore a frame whose open
/// stratum still carries duplicates (no compression, no dedup has run) and
/// check the chronologically first capture is what comes back.
#[test]
fn trail_hot_restore_is_first_entry_wins() {
    let mut v: ForkHistory<VecT<u64, u32>> = ForkHistory::new(VecT::new());
    for i in 0..8u64 {
        v.try_push(i * 10).expect("push");
    }
    let t = v.mark(ShrinkPolicy::Never).expect("mark");
    // Cell 3 rewritten four times in one frame; the pre-frame value is 30.
    for rep in 0..4u64 {
        v.set_index(3u32, 1000 + rep);
    }
    assert!(v.restore(t), "restore");
    assert_eq!(
        v.get_index(3u32),
        30,
        "hot replay must restore the pre-frame value"
    );
}

/// Pop/churn below the buffer: marks and restores interleave, nothing ever
/// compresses, and every restore tracks the model. This is the SMT-profile
/// shape the trail store exists for (zero mark-time and write-time cost).
#[test]
fn trail_churn_below_buffer_tracks_model() {
    const LEN: usize = 32;
    let mut v: ForkHistory<VecT<u64, u32>> = ForkHistory::new(VecT::new());
    for i in 0..LEN {
        v.try_push(i as u64).expect("push");
    }
    let mut model: Vec<u64> = (0..LEN as u64).collect();
    let mut seed: u64 = 12345;
    for _round in 0..50 {
        let snap = model.clone();
        let t = v.mark(ShrinkPolicy::Never).expect("mark");
        for _w in 0..12 {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let idx = ((seed >> 33) as usize % LEN) as u32;
            let val = seed;
            v.set_index(idx, val);
            model[idx as usize] = val;
        }
        // Half the rounds roll back immediately (churn), half keep going
        // one more frame deep before rolling back both.
        if seed.is_multiple_of(2) {
            assert!(v.restore(t), "restore");
            model = snap.clone();
        } else {
            let snap2 = model.clone();
            let t2 = v.mark(ShrinkPolicy::Never).expect("mark2");
            for _w in 0..6 {
                seed = seed
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                let idx = ((seed >> 33) as usize % LEN) as u32;
                v.set_index(idx, seed);
                model[idx as usize] = seed;
            }
            assert!(v.restore(t2), "restore2");
            // Intermediate check: restore2 lands the state at t2 exactly.
            for (i, &expected) in snap2.iter().enumerate().take(LEN) {
                assert_eq!(
                    v.get_index(i as u32),
                    expected,
                    "cell {i} diverged after restore2"
                );
            }
            assert!(v.restore(t), "restore1");
            model = snap;
        }
        for (i, &expected) in model.iter().enumerate().take(LEN) {
            assert_eq!(v.get_index(i as u32), expected, "cell {i} diverged");
        }
    }
}
