// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Per-frame statistics and the exact-size scheme decision, plus a calibration
//! accumulator (`doc/design/09-diff-stack-compression.md`).
//!
//! A frame's scheme is decided by exact-size costing from two counts computed in
//! a single O(N) pass — `R`, the number of contiguous index runs (the scatter
//! signal), and `D`, the distinct value count (the value-repetition signal) —
//! without sorting; the sort happens only inside the winning encoder. Accumulated
//! across frames, the same per-scheme byte totals say which scheme wins *on
//! average* for a column, which is what lets a workload calibrate a static default
//! and re-check it periodically instead of paying the adaptive decision every
//! frame.

use crate::diff_compress::CompressionMode;
use crate::index_like::{IndexFromNat, IndexLike};
use vstd::prelude::*;

verus! {

/// One frame's shape: entry count, contiguous-run count, distinct-value count.
#[derive(Clone, Copy)]
pub struct FrameStats {
    pub n: usize,
    pub runs: usize,
    pub distinct: usize,
}

impl FrameStats {
    /// Bytes this frame would occupy under each scheme, given the element widths
    /// (`t`/`i`) and the code width (`c`, `usize` today). Saturating, so a huge
    /// frame never wraps the comparison. Verified via the crate's `sat_mul`/
    /// `sat_add` (discharged 2026-09; formerly `external_body` for
    /// `saturating_*`, which Verus does not model).
    pub fn plain_bytes(self, t: usize, i: usize) -> usize {
        sat_mul(self.n, sat_add(t, i))
    }
    /// Index-major (sort-first): run `starts` are `usize`, values are `T`. `runs`
    /// is the sorted run count (contiguous-run starts), which is what
    /// `compress_runs_sorted` achieves — the honest, not optimistic, count.
    pub fn runs_bytes(self, t: usize) -> usize {
        sat_add(sat_mul(self.runs, 8), sat_mul(self.n, t))
    }
    /// The code width in BITS the shipped value encoder narrows to
    /// (`Codes::from_usize`): 1/2/4 bit-packed for `D <= 2/4/16`, then byte-granular
    /// 8/16/32 for larger `D`. This is what makes the honest packed cost sub-byte.
    pub fn code_bits(self) -> usize {
        if self.distinct <= 2 { 1 }
        else if self.distinct <= 4 { 2 }
        else if self.distinct <= 16 { 4 }
        else if self.distinct <= 256 { 8 }
        else if self.distinct <= 65536 { 16 }
        else { 32 }
    }
    /// Value-major: dict (`D` values of `T`) + codes (`N` at the narrow bit width,
    /// rounded up to whole bytes) + indices (`N` of `I`, still stored — value-major
    /// does not drop them).
    pub fn dict_bytes(self, t: usize, i: usize) -> usize {
        let code_bytes = sat_add(sat_mul(self.n, self.code_bits()), 7) / 8;
        sat_add(sat_add(sat_mul(self.distinct, t), code_bytes), sat_mul(self.n, i))
    }

    /// The cheapest scheme for this frame, never worse than plain — costed at the
    /// achievable sizes of the shipped encoders, with a restore term.
    pub fn best_mode(self, t: usize, i: usize) -> CompressionMode {
        let plain = self.plain_bytes(t, i);
        let runs = self.runs_bytes(t);
        let dict = self.dict_bytes(t, i);
        // Restore term (design doc §5): a run-encoded frame restores with
        // one block copy per run, so a frame of mostly length-1 runs pays
        // the per-run setup once per element - strictly worse than plain's
        // single sequential pass, even when the encoding is smaller. Require
        // real coalescing (average run length >= 2) before the size
        // comparison may pick the run encoding.
        let runs_coalesce = sat_mul(self.runs, 2) <= self.n;
        if runs_coalesce && runs <= dict && runs < plain {
            // `runs_bytes` costs the sorted (index-set) run count, which is what
            // `compress_runs_sorted` achieves — so the honest winner is the sorted
            // encoder, not write-order `IndexRuns` (which fragments into more runs
            // and would exceed this cost). `compress_frame` falls back to
            // write-order if a frame's indices are not unique.
            CompressionMode::IndexRunsSorted
        } else if dict < plain {
            CompressionMode::ValueDict
        } else {
            CompressionMode::None
        }
    }
}

/// Running per-scheme byte totals over a window of frames. Feeds two decisions:
/// which static default to promote for a column (`recommend`), and whether an
/// active default is still optimal (compare `recommend` to it after a
/// re-calibration window). Pure accumulation, so it is verified exec.
#[derive(Clone, Copy)]
pub struct CalibrationStats {
    pub frames: usize,
    pub plain_total: usize,
    pub runs_total: usize,
    pub dict_total: usize,
}

impl CalibrationStats {
    pub fn new() -> CalibrationStats {
        CalibrationStats { frames: 0, plain_total: 0, runs_total: 0, dict_total: 0 }
    }

    /// The scheme with the smallest total over the observed frames — the default
    /// to promote for this column on this class of workload.
    pub fn recommend(&self) -> CompressionMode {
        if self.runs_total <= self.dict_total && self.runs_total < self.plain_total {
            // Same honesty point as `best_mode`: the runs totals are sorted-run
            // counts, so promote the sorted encoder.
            CompressionMode::IndexRunsSorted
        } else if self.dict_total < self.plain_total {
            CompressionMode::ValueDict
        } else {
            CompressionMode::None
        }
    }
}

/// Calibrated-adaptive scheme selection: run the exact-size selector (`Auto`) for
/// a calibration window, promote the average winner to a static default, run the
/// default for a period, then re-calibrate — so the per-frame adaptive cost is
/// paid only during the (short) calibration windows, not every frame. This is the
/// policy the e-graph columns use: the first frames of a workload establish each
/// column's default; periodic windows check the default is still optimal.
#[derive(Clone, Copy)]
pub struct CalibrationPolicy {
    /// Frames spent calibrating (running `Auto` + observing) before promoting.
    pub window: usize,
    /// Frames spent on the promoted default before re-calibrating.
    pub period: usize,
    /// True while calibrating; false while running the default.
    pub calibrating: bool,
    /// Frames elapsed in the current phase.
    pub counter: usize,
    /// The promoted default (meaningful once a calibration window has completed).
    pub default: CompressionMode,
    /// Byte totals accumulated during the current calibration window.
    pub stats: CalibrationStats,
}

impl CalibrationPolicy {
    pub fn new(window: usize, period: usize) -> CalibrationPolicy {
        CalibrationPolicy {
            window,
            period,
            calibrating: true,
            counter: 0,
            default: CompressionMode::None,
            stats: CalibrationStats::new(),
        }
    }

    /// The mode for the next flush: `Auto` (per-frame exact) while calibrating,
    /// the promoted default in steady state. Verified: a pure phase read.
    pub fn flush_mode(&self) -> CompressionMode {
        if self.calibrating {
            CompressionMode::Auto
        } else {
            self.default
        }
    }

}


// ===========================================================================
// F4: the shadow-encode harness. When SEMPER_SHADOW=1, every seal ALSO encodes
// the frame in every mode its value type supports and emits one machine-readable
// line per (column-instance, frame): entry count, run counts, distinct count
// where computable, and the REAL encoded byte size of every candidate (actual
// encoders, never projections), plus the mode the live selector chose. Off by
// default and gated by one cached boolean, so the seal path pays a single
// branch when disabled. Diagnostic only, and outside the verified perimeter
// (below the `verus!` block): no spec content to carry.
// ===========================================================================

/// Saturating byte arithmetic for the diagnostic counters. Verified (vstd
/// models `checked_mul`/`checked_add`), so a byte count can never trap and
/// Frame statistics: entry count, the contiguous-run count over the frame's
/// index SET, and the distinct-value count. Two linear passes with hash sets,
/// whose key model vstd supplies for `usize`.
///
/// Verified, with a deliberately trivial contract: only sizes depend on these
/// counts, never correctness — whichever mode they lead `best_mode` to pick,
/// `compress_frame`'s bijection still holds. So the proof carries termination
/// and overflow-freedom; the counts' exactness is pinned by the ported
/// production proptests, as it was when this function was trusted.
pub fn frame_stats<T: IndexLike, I: IndexLike>(diffs: &Vec<(T, I)>) -> FrameStats {
    broadcast use vstd::std_specs::hash::group_hash_axioms;

    let n = diffs.len();
    let mut idx_set: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut val_set: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == diffs@.len(),
        decreases n - k,
    {
        let d = diffs[k];
        idx_set.insert(d.1.as_usize());
        val_set.insert(d.0.as_usize());
        k = k + 1;
    }

    // A run starts at an index whose predecessor is absent from the set; each
    // distinct index is counted once, which is what `counted` enforces.
    let mut counted: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut runs: usize = 0;
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            n == diffs@.len(),
            runs <= j,
        decreases n - j,
    {
        let ix = diffs[j].1.as_usize();
        // A run starts at a not-yet-counted index whose predecessor is absent.
        if counted.insert(ix) && (ix == 0 || !idx_set.contains(&(ix - 1))) {
            runs = runs + 1;
        }
        j = j + 1;
    }

    FrameStats { n, runs, distinct: val_set.len() }
}

/// never needs a trust marker. Introduced 2026-09 when the counters were
/// discharged from the trust ledger.
pub fn sat_mul(a: usize, b: usize) -> usize {
    match a.checked_mul(b) {
        Some(v) => v,
        None => usize::MAX,
    }
}

pub fn sat_add(a: usize, b: usize) -> usize {
    match a.checked_add(b) {
        Some(v) => v,
        None => usize::MAX,
    }
}

} // verus!

// ---------------------------------------------------------------------------
// Read-only diagnostics — OUTSIDE the verified perimeter (stratified, as the
// byte reporters are; see `diagnostics.rs`). Nothing verified calls these: they
// observe frames and emit measurements, so they are neither proved nor trusted
// rather than `external_body` items the trust ledger has to carry.
// ---------------------------------------------------------------------------

impl CalibrationStats {
    /// Fold one frame's would-be sizes into the totals, at the shipped encoders'
    /// achievable widths (sorted run count, narrow code width).
    pub fn observe(&mut self, stats: FrameStats, t: usize, i: usize) {
        self.frames = self.frames.saturating_add(1);
        self.plain_total = self.plain_total.saturating_add(stats.plain_bytes(t, i));
        self.runs_total = self.runs_total.saturating_add(stats.runs_bytes(t));
        self.dict_total = self.dict_total.saturating_add(stats.dict_bytes(t, i));
    }
}

impl CalibrationPolicy {
    /// Advance the state machine by one observed frame. During calibration, fold
    /// the frame's would-be sizes in and, at the end of the window, promote the
    /// winner and switch to the default. During the default phase, count down to
    /// the next re-calibration. Outside the perimeter: heuristic bookkeeping
    /// (counters and size folds), no correctness surface.
    pub fn observe_frame(&mut self, stats: FrameStats, t: usize, i: usize) {
        if self.calibrating {
            self.stats.observe(stats, t, i);
            self.counter = self.counter.saturating_add(1);
            if self.counter >= self.window {
                self.default = self.stats.recommend();
                self.calibrating = false;
                self.counter = 0;
                self.stats = CalibrationStats::new();
            }
        } else {
            self.counter = self.counter.saturating_add(1);
            if self.counter >= self.period {
                self.calibrating = true;
                self.counter = 0;
                self.stats = CalibrationStats::new();
            }
        }
    }
}

pub fn shadow_enabled() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("SEMPER_SHADOW")
            .map(|v| !v.is_empty())
            .unwrap_or(false)
    })
}

/// Emit one shadow line. `SEMPER_SHADOW=1` writes stderr; any other non-empty
/// value is a file path appended to (survives harnesses that swallow a child's
/// stderr, and merges lines from many solver subprocesses).
fn shadow_emit(line: String) {
    use std::io::Write;
    static SINK: std::sync::OnceLock<Option<std::sync::Mutex<std::fs::File>>> =
        std::sync::OnceLock::new();
    let sink = SINK.get_or_init(|| match std::env::var("SEMPER_SHADOW") {
        Ok(v) if v != "1" && !v.is_empty() => std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(v)
            .ok()
            .map(std::sync::Mutex::new),
        _ => None,
    });
    match sink {
        Some(f) => {
            let mut g = f.lock().unwrap();
            let _ = writeln!(g, "{}", line);
        }
        None => eprintln!("{}", line),
    }
}

/// Shadow-encode with the value-opaque candidates (any `T: Copy` column):
/// plain, write-order runs, sorted runs. `instance` is an opaque column-instance
/// key (the diff log's address), `frame` the sealed frame's ordinal.
pub fn shadow_log_copy<T: Copy, I: IndexLike, VC: crate::value_compressor::ValueCompressor<T>>(
    pairs: &Vec<(T, I)>,
    instance: usize,
    frame: usize,
    chosen: &str,
) {
    if !shadow_enabled() {
        return;
    }
    let n = pairs.len();
    let plain = n * (core::mem::size_of::<T>() + core::mem::size_of::<I>());
    let wo = crate::diff_compress::RunCol::compress(pairs).byte_len();
    let so = crate::diff_compress::RunCol::compress_sorted(pairs).byte_len();
    // Value-layer candidates (F2.4): the column's own codec composed with the
    // sorted-runs and plain index layers, real encoders.
    let (vso, vpl) = if VC::enabled() {
        (
            format!(
                "{}",
                crate::layered::LayeredFrame::<T, I, VC>::compress_runs_sorted(pairs).byte_len()
            ),
            format!(
                "{}",
                crate::layered::LayeredFrame::<T, I, VC>::compress_plain(pairs).byte_len()
            ),
        )
    } else {
        ("-".to_string(), "-".to_string())
    };
    shadow_emit(format!(
        "SHADOW,{},{:?},{},{},{},{},{},{},{},{},{},{},{}",
        core::any::type_name::<T>(),
        instance,
        frame,
        n,
        run_count_writeorder(pairs),
        run_count_sorted(pairs),
        plain,
        wo,
        so,
        core::any::type_name::<VC>(),
        vso,
        vpl,
        chosen,
    ));
}

/// Shadow-encode with the full candidate set (`T: IndexLike` columns): the
/// value-opaque set plus dictionary and delta, and the distinct-value count.
pub fn shadow_log_full<
    T: IndexLike,
    I: IndexLike,
    VC: crate::value_compressor::ValueCompressor<T>,
>(
    pairs: &Vec<(T, I)>,
    instance: usize,
    frame: usize,
    chosen: &str,
) {
    if !shadow_enabled() {
        return;
    }
    let n = pairs.len();
    let plain = n * (core::mem::size_of::<T>() + core::mem::size_of::<I>());
    let wo = crate::diff_compress::RunCol::compress(pairs).byte_len();
    let so = crate::diff_compress::RunCol::compress_sorted(pairs).byte_len();
    let dict = {
        let d = crate::diff_compress::compress(pairs);
        d.dict.len() * core::mem::size_of::<T>()
            + d.codes.byte_len()
            + d.idxs.len() * core::mem::size_of::<I>()
    };
    let delta = crate::diff_compress::DeltaFrame::compress(pairs).byte_len();
    let distinct: std::collections::HashSet<usize> = pairs.iter().map(|p| p.0.as_usize()).collect();
    let (vso, vpl) = if VC::enabled() {
        (
            format!(
                "{}",
                crate::layered::LayeredFrame::<T, I, VC>::compress_runs_sorted(pairs).byte_len()
            ),
            format!(
                "{}",
                crate::layered::LayeredFrame::<T, I, VC>::compress_plain(pairs).byte_len()
            ),
        )
    } else {
        ("-".to_string(), "-".to_string())
    };
    shadow_emit(format!(
        "SHADOWF,{},{:?},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
        core::any::type_name::<T>(),
        instance,
        frame,
        n,
        distinct.len(),
        run_count_writeorder(pairs),
        run_count_sorted(pairs),
        plain,
        wo,
        so,
        dict,
        delta,
        core::any::type_name::<VC>(),
        vso,
        vpl,
        chosen,
    ));
}

fn run_count_writeorder<T: Copy, I: IndexLike>(pairs: &Vec<(T, I)>) -> usize {
    let mut runs = 0usize;
    let mut prev: Option<usize> = None;
    for p in pairs.iter() {
        let u = p.1.as_usize();
        match prev {
            Some(q) if u == q + 1 => {}
            _ => runs += 1,
        }
        prev = Some(u);
    }
    runs
}

fn run_count_sorted<T: Copy, I: IndexLike>(pairs: &Vec<(T, I)>) -> usize {
    let mut idx: Vec<usize> = pairs.iter().map(|p| p.1.as_usize()).collect();
    idx.sort_unstable();
    let mut runs = 0usize;
    let mut prev: Option<usize> = None;
    for &u in idx.iter() {
        match prev {
            Some(q) if u == q + 1 => {}
            _ => runs += 1,
        }
        prev = Some(u);
    }
    runs
}

/// Mode name for the shadow log's `chosen` column.
pub fn mode_name(mode: crate::diff_compress::CompressionMode) -> &'static str {
    match mode {
        crate::diff_compress::CompressionMode::None => "None",
        crate::diff_compress::CompressionMode::ValueDict => "ValueDict",
        crate::diff_compress::CompressionMode::IndexRuns => "IndexRuns",
        crate::diff_compress::CompressionMode::IndexRunsSorted => "IndexRunsSorted",
        crate::diff_compress::CompressionMode::Auto => "Auto",
    }
}
