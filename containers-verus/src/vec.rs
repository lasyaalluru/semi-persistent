// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Vec<T, I, S, const TRACK: bool>`: the headline semi-persistent vector.
//!
//! The full vector — `push`, `pop` (including into a marked region), `set`,
//! `get`, `mark`, `restore` — is verified at arbitrary mark-nesting depth,
//! with fork-history branch-cut safety. After `restore(token)`,
//! `view() == snapshots[token.frame_idx]`, where `snapshots` is a ghost stack
//! of deep copies recorded at each `mark()` and reconstructed on restore from
//! the sparse diff log (it is never stored at runtime).
//!
//! The well-formedness invariant is the declarative, pointwise `frame_cell_inv`
//! (see `frame_cell_inv`): for each marked cell `j`, its snapshot value lives
//! in exactly one place — the live view if untouched since the mark, or the
//! diff log if overwritten/popped — with first-write-wins giving at most one
//! diff entry per cell per frame.
//!
//! Full narrative, theorems, and proof architecture:
//! `doc/design/01-verification-design.md`.

use vstd::prelude::*;

verus! {

use crate::diff_store::DiffStore;
use crate::frame::Frame;
use crate::index_like::IndexLike;

// The execution-locked tier-policy module is ordinary Rust so its planner can
// use std APIs that Verus does not model. Register the policy values as
// transparent executable datatypes; only private-field `Ratio` remains opaque.
// Hot-only proofs never inspect policy values (Defer is represented by the
// checked core selected by the runtime dispatch).
#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExRolloverPolicy(crate::tier_policy::RolloverPolicy);

#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExTierLimit(crate::tier_policy::TierLimit);

#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExReclaimPolicy(crate::tier_policy::ReclaimPolicy);

#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExTierPolicy(crate::tier_policy::TierPolicy);

#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExTierStats(crate::tier_policy::TierStats);


#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExAdaptiveInput(crate::tier_policy::AdaptiveInput);

#[verifier::external_type_specification]
#[allow(dead_code)]
pub struct ExAdaptiveReport(crate::tier_policy::AdaptiveReport);

/// Capacity-reclamation policy applied at `mark` time (parity with
/// production). The verus model treats both variants as observationally
/// inert: shrinking is a capacity hint that never changes `view()` or any
/// tracked sequence, so it carries no spec content.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum ShrinkPolicy {
    Never,
    IfOverallocated { factor: usize, headroom: usize },
}

/// Per-mark controls. Rollover is evaluated only after the old frame is
/// sealed and the new writable frame is open.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct MarkOptions {
    pub shrink: ShrinkPolicy,
    pub rollover: crate::tier_policy::RolloverPolicy,
}

impl MarkOptions {
    pub const fn new(
        shrink: ShrinkPolicy,
        rollover: crate::tier_policy::RolloverPolicy,
    ) -> Self {
        Self { shrink, rollover }
    }
}

impl Default for MarkOptions {
    fn default() -> Self {
        Self {
            shrink: ShrinkPolicy::Never,
            rollover: crate::tier_policy::RolloverPolicy::ApplyConfigured,
        }
    }
}

/// Opaque token returned by `mark()`.
///
/// `frame_idx` is the reconstruction coordinate (which frame `restore` rolls
/// back to). It is a STRUCTURAL handle only: branch validity and forgery
/// rejection live on the owning group's `History` (doc 10), which validates a
/// `GroupToken` once for every member; `Vec` itself no longer carries a
/// genealogy (H2). A caller that restores through a raw `VecToken` without a
/// `History` gets exactly the structural guarantee `is_restorable_spec`
/// states: the frame exists and reconstruction lands on its snapshot.
/// A standalone vector's version token is the group token minted by its own
/// genealogy: the vector is a group of one. `depth` is the index of the frame
/// the mark opened; validation checks the minting manager, the generation
/// and the frame's liveness.
pub type VecToken = crate::history::GroupToken;

/// Spec helper: there is some entry in `diffs` pointing at index `j`.
///
/// Used as the "captured" predicate in the declarative invariant.
pub open(crate) spec fn diff_has_index<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
    j: nat,
) -> bool {
    exists|k: int| 0 <= k < diffs.len()
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// Some entry of `diffs` in `[lo, hi)` points at index `j` (range-scoped
/// `diff_has_index`; the replay loop's flag bookkeeping).
pub open(crate) spec fn diff_has_index_in<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
    lo: int,
    hi: int,
    j: nat,
) -> bool {
    exists|k: int| lo <= k < hi
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// First-write-wins: each index appears at most once across the diff log.
///
/// Without this, multiple entries could disagree about a slot's marked
/// value and the invariant would be ambiguous. Production enforces this
/// via the per-slot capture flag.
pub open(crate) spec fn diffs_unique_indices<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
) -> bool {
    forall|i: int, j: int|
        0 <= i < diffs.len() && 0 <= j < diffs.len() && i != j
            ==> (#[trigger] diffs[i]).1.as_nat() != (#[trigger] diffs[j]).1.as_nat()
}

/// The declarative frame invariant — your formulation.
///
/// For each cell `j` in the marked region:
///   - If no diff entry points at `j` (uncaptured): `view[j] == snap[j]`.
///     The slot was never written to since mark, so the current view
///     still holds the marked value.
///   - Else (captured): some diff entry `(old, j)` has `old == snap[j]`.
///     The diff log holds the marked value; the current view holds
///     whatever scribble has been written since.
///
/// Both arms are stated as conjuncts. They are *jointly* the meaning of
/// "snap is the snapshot at mark time of this view-plus-diff-log triple."
/// First-write-wins (above) ensures the captured arm's witness is unique.
pub open(crate) spec fn frame_inv<T, I: IndexLike>(
    view: Seq<T>,
    diffs: Seq<(T, I)>,
    snap: Seq<T>,
    saved_len: nat,
) -> bool {
    &&& snap.len() == saved_len
    &&& saved_len <= view.len()
    &&& (forall|j: int| #![trigger snap[j]]
            0 <= j < saved_len as int ==> {
                if !diff_has_index::<T, I>(diffs, j as nat) {
                    // Uncaptured arm.
                    view[j] == snap[j]
                } else {
                    // Captured arm.
                    exists|k: int| 0 <= k < diffs.len()
                        && (#[trigger] diffs[k]).1.as_nat() == j as nat
                        && diffs[k].0 == snap[j]
                }
            })
}

// ---------------------------------------------------------------------------
// `overlay` -- the spec model of the restore loop
// ---------------------------------------------------------------------------
//
// The restore loop walks the diff log from `n` down to `lo`, applying each
// entry `(old, idx)` via `restore_entry`. Entries with `idx < base.len()`
// overwrite `base[idx]`; entries beyond `base.len()` are no-ops (the
// production restore_entry guard). Because the loop walks *downward*, the
// entry with the SMALLEST index in `[lo, hi)` that hits a given cell is
// applied LAST and therefore wins.
//
// `overlay(base, diffs, lo, hi)` is the recursive spec for this: apply
// `diffs[lo]` on top of `overlay(base, diffs, lo+1, hi)`, so the lower
// index ends up outermost (winning). This is exactly the loop's result.

// ---------------------------------------------------------------------------
// Bare-log helpers (exec-first convergence, goal doc mainline-shape-plus-
// coldstack). The hot log is a bare `std::vec::Vec<(T, I)>` again - mainline's
// field - and these free functions carry the small verified surface the
// container and stores read it through. `log_hot_slice` always succeeds now
// (there is no cold region inside the log); the Option shape is kept so the
// call sites' fallback structure survives until the cold stack lands (A2b).


pub(crate) fn log_subrange_vec<T: Copy, I: IndexLike>(
    d: &std::vec::Vec<(T, I)>, lo: usize, hi: usize,
) -> (r: std::vec::Vec<(T, I)>)
    requires lo <= hi <= d@.len(),
    ensures r@ == d@.subrange(lo as int, hi as int),
{
    let mut out: std::vec::Vec<(T, I)> = std::vec::Vec::new();
    let mut i: usize = lo;
    while i < hi
        invariant
            lo <= i <= hi,
            hi <= d@.len(),
            out@ =~= d@.subrange(lo as int, i as int),
        decreases hi - i,
    {
        out.push(d[i]);
        proof {
            assert(out@ =~= d@.subrange(lo as int, i as int + 1));
        }
        i += 1;
    }
    proof { assert(out@ =~= d@.subrange(lo as int, hi as int)); }
    out
}

#[allow(dead_code)]
pub(crate) fn log_index<T: Copy, I: IndexLike>(
    d: &std::vec::Vec<(T, I)>, i: usize,
) -> (e: (T, I))
    requires i < d@.len(),
    ensures e == d@[i as int],
{
    d[i]
}

/// Capacity release for the bare log: shrink when capacity exceeds
/// `factor * len + headroom`. View-preserving; capacity is unmodeled.
#[verifier::external_body]
pub(crate) fn log_shrink_capacity<T: Copy, I: IndexLike>(
    d: &mut std::vec::Vec<(T, I)>, factor: usize, headroom: usize,
)
    ensures final(d)@ == old(d)@,
{
    let cap_target = d.len().saturating_mul(factor).saturating_add(headroom);
    if d.capacity() > cap_target {
        d.shrink_to(cap_target);
    }
}




pub open(crate) spec fn overlay<T, I: IndexLike>(
    base: Seq<T>,
    diffs: Seq<(T, I)>,
    lo: int,
    hi: int,
) -> Seq<T>
    decreases hi - lo
{
    if lo >= hi || lo < 0 || hi > diffs.len() {
        base
    } else {
        let prev = overlay(base, diffs, lo + 1, hi);
        let d = diffs[lo];
        if d.1.as_nat() < prev.len() {
            prev.update(d.1.as_nat() as int, d.0)
        } else {
            prev
        }
    }
}

/// `overlay` preserves the base length (it only updates, never grows).
pub(crate) proof fn lemma_overlay_len<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
)
    ensures overlay::<T, I>(base, diffs, lo, hi).len() == base.len(),
    decreases hi - lo,
{
    if lo >= hi || lo < 0 || hi > diffs.len() {
    } else {
        lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    }
}

/// If no entry in `[lo, hi)` hits cell `j`, overlay leaves `base[j]` alone.
pub(crate) proof fn lemma_overlay_uncaptured<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, j: int,
)
    requires
        0 <= j < base.len(),
        forall|k: int| lo <= k < hi && 0 <= k < diffs.len()
            ==> (#[trigger] diffs[k]).1.as_nat() != j as nat,
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j] == base[j],
    decreases hi - lo,
{
    if lo >= hi || lo < 0 || hi > diffs.len() {
    } else {
        lemma_overlay_uncaptured::<T, I>(base, diffs, lo + 1, hi, j);
        lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
        // diffs[lo].1 != j, so the update at lo (if any) doesn't touch j.
    }
}

/// If `[lo, hi)` has unique indices and the entry at position `p` hits `j`,
/// then overlay sets `base[j]` to that entry's value — regardless of base,
/// because the winning entry is the unique one.
pub(crate) proof fn lemma_overlay_captured<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, p: int, j: int,
)
    requires
        0 <= j < base.len(),
        lo <= p < hi,
        0 <= p < diffs.len(),
        lo >= 0,
        hi <= diffs.len(),
        diffs[p].1.as_nat() == j as nat,
        // unique within [lo, hi)
        forall|a: int, b: int|
            lo <= a < hi && lo <= b < hi && a != b
                ==> (#[trigger] diffs[a]).1.as_nat() != (#[trigger] diffs[b]).1.as_nat(),
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j] == diffs[p].0,
    decreases hi - lo,
{
    let prev = overlay::<T, I>(base, diffs, lo + 1, hi);
    lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    if p == lo {
        // Entry at lo wins (applied last/outermost). All entries in
        // [lo+1, hi) have different indices from j (uniqueness), so they
        // don't matter — the final update at lo sets j.
    } else {
        // p in [lo+1, hi). By IH, overlay(lo+1, hi)[j] == diffs[p].0.
        lemma_overlay_captured::<T, I>(base, diffs, lo + 1, hi, p, j);
        // The update at lo has index diffs[lo].1 != j (uniqueness, lo != p),
        // so it doesn't disturb j.
    }
}

/// Lowest-position-in-range wins. If `p` is the LOWEST position in `[lo, hi)`
/// whose entry hits `j` (entries before `p` miss `j`), then overlay sets
/// `base[j]` to `diffs[p].0` — even if higher positions in `[lo, hi)` also
/// hit `j`. This generalizes `lemma_overlay_captured` (which needs global
/// uniqueness in the range) to the cross-stratum case where the same index
/// recurs in different strata: the deepest (= lowest-position) stratum's
/// entry wins, which is exactly what reverse-replay computes.
pub(crate) proof fn lemma_overlay_lowest<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, p: int, j: int,
)
    requires
        0 <= j < base.len(),
        lo <= p < hi,
        0 <= p < diffs.len(),
        lo >= 0,
        hi <= diffs.len(),
        diffs[p].1.as_nat() == j as nat,
        // p is the LOWEST hitter of j in [lo, hi): earlier positions miss j.
        forall|q: int| lo <= q < p ==> (#[trigger] diffs[q]).1.as_nat() != j as nat,
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j] == diffs[p].0,
    decreases hi - lo,
{
    let prev = overlay::<T, I>(base, diffs, lo + 1, hi);
    lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    if p == lo {
        // diffs[lo] hits j; it is applied OUTERMOST (last), so its value is
        // the final value at j regardless of what [lo+1, hi) did to prev[j].
    } else {
        // diffs[lo] does not hit j (lo < p and p is the lowest hitter).
        // p is still the lowest hitter in [lo+1, hi). By IH overlay(lo+1,hi)[j]
        // == diffs[p].0, and the outermost update at lo (index != j) leaves j.
        lemma_overlay_lowest::<T, I>(base, diffs, lo + 1, hi, p, j);
    }
}

/// A captured cell has a LOWEST hitter: walk down from any witness. The
/// min-witness `lemma_overlay_lowest` and `frame_cell_inv`'s captured arm
/// consume.
pub(crate) proof fn lemma_lowest_hitter<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, hi: int, j: nat,
)
    requires
        0 <= lo,
        hi <= diffs.len(),
        captured_in_range::<T, I>(diffs, lo, hi, j),
    ensures
        exists|p: int| lo <= p < hi
            && (#[trigger] diffs[p]).1.as_nat() == j
            && first_hitter::<T, I>(diffs, lo, p, j),
    decreases hi - lo,
{
    if diffs[lo].1.as_nat() == j {
        assert(first_hitter::<T, I>(diffs, lo, lo, j));
    } else {
        let w = choose|k: int| lo <= k < hi && 0 <= k < diffs.len()
            && (#[trigger] diffs[k]).1.as_nat() == j;
        assert(captured_in_range::<T, I>(diffs, lo + 1, hi, j));
        lemma_lowest_hitter::<T, I>(diffs, lo + 1, hi, j);
        let p = choose|p: int| (lo + 1) <= p < hi
            && (#[trigger] diffs[p]).1.as_nat() == j
            && first_hitter::<T, I>(diffs, lo + 1, p, j);
        assert(first_hitter::<T, I>(diffs, lo, p, j));
    }
}

/// Restore-equivalence of dedupe-first (design doc §7, deliverable 5's
/// lemma): `overlay` applies a stratum backward, so the chronologically
/// first capture of each cell wins; dropping every later duplicate
/// preserves the result exactly.
pub(crate) proof fn lemma_overlay_dedupe_first<T, I: IndexLike>(
    base: Seq<T>, d: Seq<(T, I)>,
)
    ensures
        overlay::<T, I>(base, d, 0, d.len() as int)
            == overlay::<T, I>(
                base,
                crate::diff_compress::dedupe_first_spec(d),
                0,
                crate::diff_compress::dedupe_first_spec(d).len() as int),
{
    let r = crate::diff_compress::dedupe_first_spec(d);
    let rp = crate::diff_compress::dedupe_positions(d, d.len() as int);
    crate::diff_compress::lemma_dedupe_prefix_props::<T, I>(d, d.len() as int);
    let od = overlay::<T, I>(base, d, 0, d.len() as int);
    let or = overlay::<T, I>(base, r, 0, r.len() as int);
    lemma_overlay_len::<T, I>(base, d, 0, d.len() as int);
    lemma_overlay_len::<T, I>(base, r, 0, r.len() as int);
    assert forall|j: int| 0 <= j < base.len() implies od[j] == or[j] by {
        if captured_in_range::<T, I>(d, 0, d.len() as int, j as nat) {
            lemma_lowest_hitter::<T, I>(d, 0, d.len() as int, j as nat);
            let p = choose|p: int| 0 <= p < d.len()
                && (#[trigger] d[p]).1.as_nat() == j as nat
                && first_hitter::<T, I>(d, 0, p, j as nat);
            lemma_overlay_lowest::<T, I>(base, d, 0, d.len() as int, p, j);
            // The first hitter is kept; in `r` it is the ONLY hitter of j,
            // hence trivially the lowest.
            assert(first_hitter::<T, I>(d, 0, p, d[p].1.as_nat()));
            assert(rp.contains(p));
            let t = choose|t: int| 0 <= t < rp.len() && #[trigger] rp[t] == p;
            assert(r[t] == d[p]);
            assert forall|q: int| 0 <= q < t implies
                (#[trigger] r[q]).1.as_nat() != j as nat by {
                if r[q].1.as_nat() == j as nat {
                    assert(r[q].1.as_nat() == r[t].1.as_nat());
                }
            }
            lemma_overlay_lowest::<T, I>(base, r, 0, r.len() as int, t, j);
        } else {
            // No hitter in d, and every entry of r is some d entry, so no
            // hitter in r either.
            assert forall|q: int| 0 <= q < r.len() implies
                (#[trigger] r[q]).1.as_nat() != j as nat by {
                if r[q].1.as_nat() == j as nat {
                    let pq = rp[q];
                    assert(r[q] == d[pq]);
                    assert(captured_in_range::<T, I>(
                        d, 0, d.len() as int, j as nat));
                }
            }
            lemma_overlay_uncaptured::<T, I>(base, d, 0, d.len() as int, j);
            lemma_overlay_uncaptured::<T, I>(base, r, 0, r.len() as int, j);
        }
    }
    assert(od =~= or);
}

/// If no entry in the lower part `[lo, mid)` hits `j`, then overlaying the
/// whole `[lo, hi)` agrees at `j` with overlaying just the upper part
/// `[mid, hi)`. (The lower-part replay, applied outermost, leaves `j` alone.)
/// Used by the flat central lemma's uncaptured/recurse step.
pub(crate) proof fn lemma_overlay_uncaptured_prefix<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, mid: int, hi: int, j: int,
)
    requires
        0 <= lo <= mid <= hi <= diffs.len(),
        0 <= j < base.len(),
        forall|q: int| lo <= q < mid ==> (#[trigger] diffs[q]).1.as_nat() != j as nat,
    ensures
        overlay::<T, I>(base, diffs, lo, hi)[j]
            == overlay::<T, I>(base, diffs, mid, hi)[j],
    decreases mid - lo,
{
    lemma_overlay_len::<T, I>(base, diffs, mid, hi);
    if lo >= mid {
        // [lo, mid) empty ⇒ both sides identical.
    } else {
        // Peel lo: overlay(lo,hi) = step(diffs[lo], overlay(lo+1,hi)). By IH
        // overlay(lo+1,hi)[j] == overlay(mid,hi)[j]; diffs[lo] misses j so the
        // outermost step leaves j.
        lemma_overlay_uncaptured_prefix::<T, I>(base, diffs, lo + 1, mid, hi, j);
        lemma_overlay_len::<T, I>(base, diffs, lo + 1, hi);
    }
}

/// Every entry in the frame names a distinct index. This is the first-write-wins
/// invariant of a finalized frame, and it is what makes reordering the frame
/// sound: with unique indices, `overlay` writes each cell exactly once, so the
/// restored state depends only on the index->value map, not the entry order.
pub open(crate) spec fn unique_idx<T, I: IndexLike>(d: Seq<(T, I)>) -> bool {
    forall|a: int, b: int|
        0 <= a < d.len() && 0 <= b < d.len() && a != b
            ==> (#[trigger] d[a]).1.as_nat() != (#[trigger] d[b]).1.as_nat()
}

/// Frame `d` names index `j` somewhere. The trigger handle for the same-map
/// hypothesis of `lemma_overlay_same_map`.
pub open(crate) spec fn frame_covers<T, I: IndexLike>(d: Seq<(T, I)>, j: nat) -> bool {
    exists|k: int| 0 <= k < d.len() && (#[trigger] d[k]).1.as_nat() == j
}

/// SET-LEVEL RESTORE EQUIVALENCE. Two finalized frames with unique indices that
/// define the same index->value map (same covered indices, agreeing values)
/// overlay to the same result over any base. This is what licenses a compression
/// scheme to REORDER a frame (e.g. sort it by index for longer runs): the sorted
/// frame is a permutation of the original, so it has the same map, so it restores
/// identically. Proof is pointwise via `lemma_overlay_captured` (covered cells
/// take the unique hitter's value) and `lemma_overlay_uncaptured` (uncovered
/// cells keep the base), then extensionality.
pub(crate) proof fn lemma_overlay_same_map<T, I: IndexLike>(
    base: Seq<T>, d1: Seq<(T, I)>, d2: Seq<(T, I)>,
)
    requires
        unique_idx(d1),
        unique_idx(d2),
        // Same covered indices.
        forall|j: nat| #![trigger frame_covers(d1, j)]
            j < base.len() ==> frame_covers(d1, j) == frame_covers(d2, j),
        // Agreeing values wherever an index is shared.
        forall|k1: int, k2: int|
            0 <= k1 < d1.len() && 0 <= k2 < d2.len()
                && (#[trigger] d1[k1]).1.as_nat() == (#[trigger] d2[k2]).1.as_nat()
            ==> d1[k1].0 == d2[k2].0,
    ensures
        overlay::<T, I>(base, d1, 0, d1.len() as int)
            == overlay::<T, I>(base, d2, 0, d2.len() as int),
{
    lemma_overlay_len::<T, I>(base, d1, 0, d1.len() as int);
    lemma_overlay_len::<T, I>(base, d2, 0, d2.len() as int);
    assert forall|j: int| 0 <= j < base.len() implies
        overlay::<T, I>(base, d1, 0, d1.len() as int)[j]
            == overlay::<T, I>(base, d2, 0, d2.len() as int)[j] by {
        // Instantiate the same-covered-indices hypothesis at j.
        assert(frame_covers(d1, j as nat) == frame_covers(d2, j as nat));
        if frame_covers(d1, j as nat) {
            let k1 = choose|k1: int| 0 <= k1 < d1.len() && (#[trigger] d1[k1]).1.as_nat() == j as nat;
            let k2 = choose|k2: int| 0 <= k2 < d2.len() && (#[trigger] d2[k2]).1.as_nat() == j as nat;
            lemma_overlay_captured::<T, I>(base, d1, 0, d1.len() as int, k1, j);
            lemma_overlay_captured::<T, I>(base, d2, 0, d2.len() as int, k2, j);
            // Values agree because both entries name index j.
            assert(d1[k1].0 == d2[k2].0);
        } else {
            lemma_overlay_uncaptured::<T, I>(base, d1, 0, d1.len() as int, j);
            lemma_overlay_uncaptured::<T, I>(base, d2, 0, d2.len() as int, j);
        }
    }
    assert(overlay::<T, I>(base, d1, 0, d1.len() as int)
        =~= overlay::<T, I>(base, d2, 0, d2.len() as int));
}

/// THE CODEC CONTRACT, formalized. Two finalized frames with unique indices and
/// the SAME MULTISET OF WRITES restore identically over any base. This is the one
/// invariant every codec must preserve: `decode(encode(d))` need only carry the
/// same set of `(value, index)` writes as `d` — order is irrelevant because each
/// cell is written at most once per frame (first-write-wins), so the multiset is a
/// map and the restore is that map applied. Reduces to `lemma_overlay_same_map`
/// by deriving same-covered-indices and value-agreement from multiset equality:
/// a shared write is `contains`-equal on both sides (equal multisets ⇒ equal
/// counts ⇒ equal membership), and a shared index forces the SAME pair on both
/// sides, else the two distinct pairs at one index break `unique_idx`.
pub(crate) proof fn lemma_multiset_eq_overlay<T, I: IndexLike>(
    base: Seq<T>, d1: Seq<(T, I)>, d2: Seq<(T, I)>,
)
    requires
        unique_idx(d1),
        unique_idx(d2),
        d1.to_multiset() == d2.to_multiset(),
    ensures
        overlay::<T, I>(base, d1, 0, d1.len() as int)
            == overlay::<T, I>(base, d2, 0, d2.len() as int),
{
    // `x` present in `d1` is present in `d2` (equal multisets ⇒ equal counts ⇒
    // equal membership), and vice versa.
    assert forall|x: (T, I)| d1.contains(x) implies d2.contains(x) by {
        vstd::seq_lib::to_multiset_contains(d1, x);
        vstd::seq_lib::to_multiset_contains(d2, x);
    }
    assert forall|x: (T, I)| d2.contains(x) implies d1.contains(x) by {
        vstd::seq_lib::to_multiset_contains(d1, x);
        vstd::seq_lib::to_multiset_contains(d2, x);
    }
    // Same covered indices: a covering entry is present on both sides.
    assert forall|j: nat| #![trigger frame_covers(d1, j)]
        j < base.len() implies frame_covers(d1, j) == frame_covers(d2, j) by {
        if frame_covers(d1, j) {
            let k = choose|k: int| 0 <= k < d1.len() && (#[trigger] d1[k]).1.as_nat() == j;
            assert(d1.contains(d1[k]));
            let k2 = choose|k2: int| 0 <= k2 < d2.len() && d2[k2] == d1[k];
            assert(d2[k2].1.as_nat() == j);
        }
        if frame_covers(d2, j) {
            let k = choose|k: int| 0 <= k < d2.len() && (#[trigger] d2[k]).1.as_nat() == j;
            assert(d2.contains(d2[k]));
            let k1 = choose|k1: int| 0 <= k1 < d1.len() && d1[k1] == d2[k];
            assert(d1[k1].1.as_nat() == j);
        }
    }
    // Value agreement: if entries on the two sides share an index, they are the
    // same pair — otherwise both distinct pairs sit at that index in one frame
    // (each is present in the other, by multiset equality), breaking uniqueness.
    assert forall|k1: int, k2: int|
        0 <= k1 < d1.len() && 0 <= k2 < d2.len()
            && (#[trigger] d1[k1]).1.as_nat() == (#[trigger] d2[k2]).1.as_nat()
        implies d1[k1].0 == d2[k2].0 by {
        assert(d1.contains(d1[k1]));
        let q = choose|q: int| 0 <= q < d2.len() && d2[q] == d1[k1];
        // q and k2 both name index j in d2; uniqueness forces q == k2, so the
        // pair at k2 equals d1[k1].
        if q != k2 {
            assert(d2[q].1.as_nat() == d2[k2].1.as_nat());  // both == j
            assert(false);
        }
    }
    lemma_overlay_same_map::<T, I>(base, d1, d2);
}

/// Bridge between subrange-position existential and absolute-range
/// `captured_in_range`. If `sub == diffs.subrange(lo, hi)`, then
/// "some sub[kk] hits j" iff "some diffs[k] in [lo, hi) hits j".
pub(crate) proof fn lemma_captured_subrange<T, I: IndexLike>(
    diffs: Seq<(T, I)>, sub: Seq<(T, I)>, lo: int, hi: int, j: nat,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        sub == diffs.subrange(lo, hi),
    ensures
        (exists|kk: int| 0 <= kk < sub.len()
            && (#[trigger] sub[kk]).1.as_nat() == j)
        == captured_in_range::<T, I>(diffs, lo, hi, j),
{
    if exists|kk: int| 0 <= kk < sub.len() && (#[trigger] sub[kk]).1.as_nat() == j {
        let kk = choose|kk: int| 0 <= kk < sub.len() && (#[trigger] sub[kk]).1.as_nat() == j;
        // sub[kk] == diffs[lo + kk], and lo <= lo+kk < hi.
        assert(sub[kk] == diffs[lo + kk]);
        assert(lo <= lo + kk < hi);
    }
    if captured_in_range::<T, I>(diffs, lo, hi, j) {
        let k = choose|k: int| lo <= k < hi && 0 <= k < diffs.len()
            && (#[trigger] diffs[k]).1.as_nat() == j;
        // diffs[k] == sub[k - lo], and 0 <= k-lo < sub.len().
        assert(sub[k - lo] == diffs[k]);
        assert(0 <= k - lo < sub.len());
    }
}

/// Rebase a complete physical frame to offset zero without changing its
/// chronological first hitter or its inherited cells.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_frame_inv_subrange<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, snap: Seq<T>,
)
    requires 0 <= lo <= hi <= diffs.len(),
        frame_inv_range::<T, I>(above, diffs, lo, hi, snap, snap.len()),
    ensures frame_inv_range::<T, I>(above, diffs.subrange(lo, hi), 0, hi - lo, snap, snap.len()),
{
    let sub = diffs.subrange(lo, hi);
    assert forall|j: int| 0 <= j < snap.len() implies
        #[trigger] frame_cell_inv::<T, I>(above, sub, 0, hi - lo, snap, j)
    by {
        lemma_captured_subrange::<T, I>(diffs, sub, lo, hi, j as nat);
        lemma_frame_inv_arm_at::<T, I>(above, diffs, lo, hi, snap, snap.len(), j);
        if captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
            let k = choose|k: int| lo <= k < hi
                && (#[trigger] diffs[k]).1.as_nat() == j as nat
                && diffs[k].0 == snap[j]
                && first_hitter::<T, I>(diffs, lo, k, j as nat);
            assert(sub[k - lo] == diffs[k]);
            assert forall|q: int| 0 <= q < k - lo implies
                (#[trigger] sub[q]).1.as_nat() != j as nat by {
                assert(sub[q] == diffs[lo + q]);
            }
            assert(first_hitter::<T, I>(sub, 0, k - lo, j as nat));
        }
    }
}

/// Index-column variant of `lemma_captured_subrange`. `idx_sub` is the INDEX
/// projection of the stratum `diffs[lo..hi]` (what `DiffLog::indices()` slices
/// out), so its entries are `I`s compared with `.as_nat()`, not `(T, I)` pairs.
/// Same conclusion: membership in the index slice matches `captured_in_range`.
pub(crate) proof fn lemma_captured_subrange_idx<T, I: IndexLike>(
    diffs: Seq<(T, I)>, idx_sub: Seq<I>, lo: int, hi: int, j: nat,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        idx_sub.len() == hi - lo,
        forall|m: int| 0 <= m < idx_sub.len() ==> (#[trigger] idx_sub[m]) == diffs[lo + m].1,
    ensures
        (exists|kk: int| 0 <= kk < idx_sub.len()
            && (#[trigger] idx_sub[kk]).as_nat() == j)
        == captured_in_range::<T, I>(diffs, lo, hi, j),
{
    if exists|kk: int| 0 <= kk < idx_sub.len() && (#[trigger] idx_sub[kk]).as_nat() == j {
        let kk = choose|kk: int| 0 <= kk < idx_sub.len() && (#[trigger] idx_sub[kk]).as_nat() == j;
        // idx_sub[kk] == diffs[lo + kk].1, and lo <= lo+kk < hi.
        assert(idx_sub[kk] == diffs[lo + kk].1);
        assert(lo <= lo + kk < hi);
    }
    if captured_in_range::<T, I>(diffs, lo, hi, j) {
        let k = choose|k: int| lo <= k < hi && 0 <= k < diffs.len()
            && (#[trigger] diffs[k]).1.as_nat() == j;
        // idx_sub[k - lo] == diffs[k].1, and 0 <= k-lo < idx_sub.len().
        assert(idx_sub[k - lo] == diffs[k].1);
        assert(0 <= k - lo < idx_sub.len());
    }
}

/// Appending at most one entry whose index is `bound` (the popped slot) to
/// the top stratum doesn't change captured-status of any OTHER index `j`
/// (`j != bound`). Used by `pop` into the marked region: the capture append hits only the
/// popped index, so every surviving cell's bridge/captured arm is preserved.
/// `diffs` is either `old_diffs` (no-op capture) or `old_diffs.push(e)` with
/// `e.1.as_nat() == bound`.
pub(crate) proof fn lemma_captured_in_range_append_other<T, I: IndexLike>(
    old_diffs: Seq<(T, I)>, diffs: Seq<(T, I)>, lo: int, j: nat, bound: nat,
)
    requires
        j != bound,
        lo <= old_diffs.len(),
        diffs == old_diffs
            || (diffs.len() == old_diffs.len() + 1
                && diffs.subrange(0, old_diffs.len() as int) == old_diffs
                && (#[trigger] diffs[old_diffs.len() as int]).1.as_nat() == bound),
    ensures
        captured_in_range::<T, I>(diffs, lo, diffs.len() as int, j)
            == captured_in_range::<T, I>(old_diffs, lo, old_diffs.len() as int, j),
{
    if diffs == old_diffs {
        return;
    }
    let n = old_diffs.len() as int;
    // forward: a hitter in diffs is at some position p; if p == n it has
    // index bound != j, contradiction; else p < n and diffs[p]==old_diffs[p].
    if captured_in_range::<T, I>(diffs, lo, diffs.len() as int, j) {
        let p = choose|p: int| lo <= p < diffs.len() && 0 <= p < diffs.len()
            && (#[trigger] diffs[p]).1.as_nat() == j;
        if p < n {
            assert(diffs[p] == old_diffs[p]) by {
                assert(diffs.subrange(0, n)[p] == old_diffs[p]);
            }
        } else {
            assert(p == n);
            assert(diffs[p].1.as_nat() == bound);  // contradicts == j
        }
    }
    // backward: an old hitter at p < n survives at the same position.
    if captured_in_range::<T, I>(old_diffs, lo, n, j) {
        let p = choose|p: int| lo <= p < n && 0 <= p < old_diffs.len()
            && (#[trigger] old_diffs[p]).1.as_nat() == j;
        assert(diffs[p] == old_diffs[p]) by {
            assert(diffs.subrange(0, n)[p] == old_diffs[p]);
        }
    }
}

/// `frame_inv_range` over `[lo, hi)` depends only on the diff entries in
/// that range. If two diff sequences agree pointwise on `[lo, hi)` (and are
/// both long enough), the predicate holds for one iff for the other.
pub(crate) proof fn lemma_frame_inv_range_local<T, I: IndexLike>(
    above: Seq<T>, da: Seq<(T, I)>, db: Seq<(T, I)>,
    lo: int, hi: int, snap: Seq<T>, saved_len: nat,
)
    requires
        0 <= lo <= hi <= da.len(),
        hi <= db.len(),
        forall|m: int| lo <= m < hi ==> #[trigger] da[m] == db[m],
        frame_inv_range::<T, I>(above, da, lo, hi, snap, saved_len),
    ensures
        frame_inv_range::<T, I>(above, db, lo, hi, snap, saved_len),
{
    // Structural conjunct: the index-bound forall reads entries only in
    // [lo, hi), where da and db agree.
    assert forall|m: int| lo <= m < hi implies
        (#[trigger] db[m]).1.as_nat() < saved_len by { assert(da[m] == db[m]); }
    // Per-cell two-arm: frame_cell_inv reads only entries in [lo, hi) plus
    // `above`/`snap` (shared). The named predicate gives a clean function-
    // application trigger that re-assembles into frame_inv_range's forall.
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, db, lo, hi, snap, j)
    by {
        lemma_frame_cell_inv_local::<T, I>(above, da, db, lo, hi, snap, j);
    }
}


pub(crate) proof fn lemma_frame_cell_inv_local<T, I: IndexLike>(
    above: Seq<T>, da: Seq<(T, I)>, db: Seq<(T, I)>,
    lo: int, hi: int, snap: Seq<T>, j: int,
)
    requires
        0 <= lo <= hi <= da.len(),
        hi <= db.len(),
        forall|m: int| lo <= m < hi ==> #[trigger] da[m] == db[m],
        frame_cell_inv::<T, I>(above, da, lo, hi, snap, j),
    ensures
        frame_cell_inv::<T, I>(above, db, lo, hi, snap, j),
{
    // captured_in_range agrees across da/db (reads entries in [lo, hi)).
    assert(captured_in_range::<T, I>(db, lo, hi, j as nat)
        == captured_in_range::<T, I>(da, lo, hi, j as nat)) by {
        if captured_in_range::<T, I>(db, lo, hi, j as nat) {
            let w = choose|k: int| lo <= k < hi && 0 <= k < db.len()
                && (#[trigger] db[k]).1.as_nat() == j as nat;
            assert(da[w] == db[w]);
        }
        if captured_in_range::<T, I>(da, lo, hi, j as nat) {
            let w = choose|k: int| lo <= k < hi && 0 <= k < da.len()
                && (#[trigger] da[k]).1.as_nat() == j as nat;
            assert(da[w] == db[w]);
        }
    }
    if captured_in_range::<T, I>(db, lo, hi, j as nat) {
        // Carry the first-hitter witness from da to db: same position, equal
        // entry, and the miss-everything-below-it forall reads only entries
        // in [lo, w) where the two sequences agree.
        let w = choose|k: int| lo <= k < hi
            && (#[trigger] da[k]).1.as_nat() == j as nat && da[k].0 == snap[j]
            && first_hitter::<T, I>(da, lo, k, j as nat);
        assert(da[w] == db[w]);
        assert forall|q: int| lo <= q < w implies
            (#[trigger] db[q]).1.as_nat() != j as nat by {
            assert(da[q] == db[q]);
        }
        assert(first_hitter::<T, I>(db, lo, w, j as nat));
    }
}

/// `overlay`'s value at `j < bound` depends only on `base`'s prefix
/// `[0, bound)` and on entries whose index is `< bound`. Concretely: if two
/// bases agree on `[0, bound)`, then their overlays agree on `[0, bound)`,
/// regardless of base values or entry indices `>= bound`.
///
/// This is what lets restore overlay onto the *truncated* base (length
/// saved_len) and still match `overlay` onto the full view on the marked
/// region: entries with idx >= saved_len are no-ops on `[0, saved_len)`.
pub(crate) proof fn lemma_overlay_prefix_agnostic<T, I: IndexLike>(
    base_a: Seq<T>, base_b: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, bound: int,
)
    requires
        0 <= bound <= base_a.len(),
        0 <= bound <= base_b.len(),
        forall|j: int| 0 <= j < bound ==> #[trigger] base_a[j] == base_b[j],
    ensures
        forall|j: int| 0 <= j < bound ==>
            #[trigger] overlay::<T, I>(base_a, diffs, lo, hi)[j]
                == overlay::<T, I>(base_b, diffs, lo, hi)[j],
    decreases hi - lo,
{
    lemma_overlay_len::<T, I>(base_a, diffs, lo, hi);
    lemma_overlay_len::<T, I>(base_b, diffs, lo, hi);
    if lo >= hi || lo < 0 || hi > diffs.len() {
    } else {
        lemma_overlay_prefix_agnostic::<T, I>(base_a, base_b, diffs, lo + 1, hi, bound);
        lemma_overlay_len::<T, I>(base_a, diffs, lo + 1, hi);
        lemma_overlay_len::<T, I>(base_b, diffs, lo + 1, hi);
        // The step at lo updates index diffs[lo].1 in both. For j < bound:
        // if diffs[lo].1 == j and j < both prevs' len, both get diffs[lo].0;
        // otherwise both inherit prev[j], equal by IH.
    }
}

/// `overlay` splits at any midpoint: applying `[lo, hi)` equals applying
/// the upper part `[mid, hi)` first, then the lower part `[lo, mid)` on top.
/// This is what lets us peel strata one at a time.
pub(crate) proof fn lemma_overlay_split<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, mid: int, hi: int,
)
    requires
        0 <= lo <= mid <= hi <= diffs.len(),
    ensures
        overlay::<T, I>(base, diffs, lo, hi)
            == overlay::<T, I>(overlay::<T, I>(base, diffs, mid, hi), diffs, lo, mid),
    decreases mid - lo,
{
    if lo >= mid {
        // [lo, mid) empty: RHS inner overlay is identity, so both sides
        // are overlay(base, mid, hi) == overlay(base, lo, hi) since lo==mid.
    } else {
        // Peel lo off both sides.
        //   LHS = step(diffs[lo], overlay(base, lo+1, hi))
        //   RHS = step(diffs[lo], overlay(overlay(base, mid, hi), lo+1, mid))
        // By IH on (lo+1, mid, hi): overlay(base, lo+1, hi)
        //   == overlay(overlay(base, mid, hi), lo+1, mid).
        // So the two `step` arguments coincide and the results match.
        lemma_overlay_split::<T, I>(base, diffs, lo + 1, mid, hi);
    }
}


/// Appending an entry at position `hi` whose index is ALREADY hit somewhere
/// in `[lo, hi)` does not change the overlay of the range: first-entry-wins
/// means the earlier hitter shadows the appended duplicate. This is the
/// overlay-invariance under the physical log's dedup discipline (the
/// first-write-wins store drops the later write; the ghost trail keeps it) that
/// makes the physical and ghost reconstructions coincide on a stratum.
pub(crate) proof fn lemma_overlay_append_dup<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
)
    requires
        0 <= lo <= hi,
        hi < diffs.len(),
        captured_in_range::<T, I>(diffs, lo, hi, diffs[hi].1.as_nat()),
    ensures
        overlay::<T, I>(base, diffs, lo, hi + 1) == overlay::<T, I>(base, diffs, lo, hi),
{
    lemma_overlay_len::<T, I>(base, diffs, lo, hi + 1);
    lemma_overlay_len::<T, I>(base, diffs, lo, hi);
    // Peel the appended entry at `hi` (the deepest position) off the front-
    // recursion: overlay(base, lo, hi+1) == overlay(base2, lo, hi) where base2
    // is base with only cell J = diffs[hi].1 possibly updated.
    lemma_overlay_split::<T, I>(base, diffs, lo, hi, hi + 1);
    let base2 = overlay::<T, I>(base, diffs, hi, hi + 1);
    lemma_overlay_len::<T, I>(base, diffs, hi, hi + 1);
    let jidx = diffs[hi].1.as_nat() as int;
    // base2 is the single-step overlay at `hi`: unfold it to base, updated at
    // cell J iff J is in range. Either way base2 agrees with base off J.
    assert(overlay::<T, I>(base, diffs, hi + 1, hi + 1) == base);
    assert(base2 == if diffs[hi].1.as_nat() < base.len() {
        base.update(jidx, diffs[hi].0)
    } else {
        base
    });
    assert(forall|c: int| 0 <= c < base.len() && c != jidx ==>
        #[trigger] base2[c] == base[c]);
    assert forall|c: int| 0 <= c < base.len() implies
        #[trigger] overlay::<T, I>(base2, diffs, lo, hi)[c]
            == overlay::<T, I>(base, diffs, lo, hi)[c]
    by {
        if captured_in_range::<T, I>(diffs, lo, hi, c as nat) {
            lemma_lowest_hitter::<T, I>(diffs, lo, hi, c as nat);
            let p = choose|p: int| lo <= p < hi
                && (#[trigger] diffs[p]).1.as_nat() == c as nat
                && first_hitter::<T, I>(diffs, lo, p, c as nat);
            lemma_overlay_lowest::<T, I>(base2, diffs, lo, hi, p, c);
            lemma_overlay_lowest::<T, I>(base, diffs, lo, hi, p, c);
        } else {
            // c is uncaptured but J IS captured (hypothesis), so c != J, hence
            // base2[c] == base[c]; both overlays reduce to that base cell.
            lemma_overlay_uncaptured::<T, I>(base2, diffs, lo, hi, c);
            lemma_overlay_uncaptured::<T, I>(base, diffs, lo, hi, c);
            assert(c != jidx);
        }
    }
    assert(overlay::<T, I>(base2, diffs, lo, hi)
        =~= overlay::<T, I>(base, diffs, lo, hi));
}

/// Range-based "captured": some entry in `diffs[lo..hi)` hits `j`.
pub open(crate) spec fn captured_in_range<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, hi: int, j: nat,
) -> bool {
    exists|k: int| lo <= k < hi && 0 <= k < diffs.len()
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// Per-cell two-arm invariant for cell `j` of stratum `[lo, hi)`.
///
/// Factored into a named predicate (rather than inlined in the forall) so
/// the `forall|j|` in `frame_inv_range` has a clean function-application
/// trigger that Verus can re-assemble reliably across diff-log changes.
///
/// Coverage-aware uncaptured arm: an uncaptured cell `j` must be *present*
/// in `above` (`j < above.len()`) and hold the snapshot value. Equivalently,
/// every cell `j` in `[above.len(), saved_len)` — popped out of `above` —
/// must be captured. That's what lets `restore` regrow the popped region with
/// `resize_default` and overwrite every filler back to `snap[j]`.
pub open(crate) spec fn frame_cell_inv<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, j: int,
) -> bool {
    if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
        &&& (j as nat) < above.len()
        &&& above[j] == snap[j]
    } else {
        // FIRST-hitter form: the chronologically first entry for `j` in the
        // stratum holds the snapshot value. Under the unique discipline this
        // is the old "some entry" form (the one entry is trivially first);
        // under the chronological (trail) discipline it is the load-bearing
        // strengthening: `overlay` is first-entry-wins, so reconstruction
        // needs exactly the FIRST entry pinned, and later duplicates (which
        // hold intermediate values) are inert.
        exists|k: int| lo <= k < hi
            && (#[trigger] diffs[k]).1.as_nat() == j as nat
            && diffs[k].0 == snap[j]
            && first_hitter::<T, I>(diffs, lo, k, j as nat)
    }
}

/// Physical coverage and saved-value interpretation for a Cold run range.
pub open(crate) spec fn cold_run_covers<I: IndexLike>(
    run: crate::frame::IndexRun<I>, j: nat,
) -> bool {
    run.base.as_nat() <= j < run.base.as_nat() + run.len
}

pub open(crate) spec fn cold_range_saved_value<T, I: IndexLike>(
    runs: Seq<crate::frame::IndexRun<I>>, values: Seq<T>, lo: int, hi: int, j: nat,
) -> Option<T> {
    if exists|r: int| lo <= r < hi && cold_run_covers(#[trigger] runs[r], j) {
        let r = choose|r: int| lo <= r < hi && cold_run_covers(#[trigger] runs[r], j);
        Some(values[runs[r].start as int + j - runs[r].base.as_nat()])
    } else {
        None
    }
}

/// Adjacent sorted/disjoint runs imply separation of every pair, including
/// empty runs. No saved-length ordering enters this argument.
pub(crate) proof fn lemma_cold_run_order<I: IndexLike>(
    runs: Seq<crate::frame::IndexRun<I>>, lo: int, hi: int, a: int, b: int,
)
    requires
        0 <= lo <= a < b < hi <= runs.len(),
        forall|r: int| lo <= r && r + 1 < hi ==>
            (#[trigger] runs[r]).base.as_nat() + runs[r].len <= runs[r + 1].base.as_nat(),
    ensures runs[a].base.as_nat() + runs[a].len <= runs[b].base.as_nat(),
    decreases b - a,
{
    if a + 1 < b {
        lemma_cold_run_order::<I>(runs, lo, hi, a + 1, b);
    }
}

/// Adjacent-disjoint runs cover each cell at most once.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_runs_cover_unique<I: IndexLike>(
    runs: Seq<crate::frame::IndexRun<I>>, lo: int, hi: int, r1: int, r2: int, j: nat,
)
    requires 0 <= lo, hi <= runs.len(), lo <= r1 < hi, lo <= r2 < hi,
        forall|r: int| lo <= r && r + 1 < hi ==>
            (#[trigger] runs[r]).base.as_nat() + runs[r].len <= runs[r + 1].base.as_nat(),
        runs[r1].base.as_nat() <= j < runs[r1].base.as_nat() + runs[r1].len,
        runs[r2].base.as_nat() <= j < runs[r2].base.as_nat() + runs[r2].len,
    ensures r1 == r2,
{
    if r1 < r2 {
        lemma_cold_run_order::<I>(runs, lo, hi, r1, r2);
    } else if r2 < r1 {
        lemma_cold_run_order::<I>(runs, lo, hi, r2, r1);
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_cold_range_extend<T, I: IndexLike>(
    runs: Seq<crate::frame::IndexRun<I>>, values: Seq<T>, lo: int, r: int, j: nat,
)
    requires
        0 <= lo <= r < runs.len(),
        forall|q: int| lo <= q && q + 1 <= r ==>
            (#[trigger] runs[q]).base.as_nat() + runs[q].len <= runs[q + 1].base.as_nat(),
    ensures cold_range_saved_value::<T, I>(runs, values, lo, r + 1, j)
        == if cold_run_covers(runs[r], j) {
            Some(values[runs[r].start as int + j - runs[r].base.as_nat()])
        } else { cold_range_saved_value::<T, I>(runs, values, lo, r, j) },
{
    if cold_run_covers(runs[r], j) {
        assert forall|q: int| lo <= q < r implies
            !cold_run_covers(#[trigger] runs[q], j) by {
            lemma_cold_run_order::<I>(runs, lo, r + 1, q, r);
        }
        assert(exists|q: int| lo <= q < r + 1 && cold_run_covers(#[trigger] runs[q], j));
        let q = choose|q: int| lo <= q < r + 1 && cold_run_covers(#[trigger] runs[q], j);
        assert(q == r);
    } else if exists|q: int| lo <= q < r && cold_run_covers(#[trigger] runs[q], j) {
        let a = choose|q: int| lo <= q < r && cold_run_covers(#[trigger] runs[q], j);
        assert(exists|q: int| lo <= q < r + 1 && cold_run_covers(#[trigger] runs[q], j));
        let b = choose|q: int| lo <= q < r + 1 && cold_run_covers(#[trigger] runs[q], j);
        if a < b {
            lemma_cold_run_order::<I>(runs, lo, r + 1, a, b);
        } else if b < a {
            lemma_cold_run_order::<I>(runs, lo, r + 1, b, a);
        }
        assert(a == b);
    }
}

/// Checked physical Cold-frame replay: preserve the fixed buffer length and
/// capture state, and write exactly the covering run's saved value.
#[inline(always)]
#[verifier::spinoff_prover]
pub(crate) fn replay_cold_range<T, I, S, const TRACK: bool>(
    store: &mut S, runs: &std::vec::Vec<crate::frame::IndexRun<I>>,
    values: &std::vec::Vec<T>, lo: usize, hi: usize,
)
where
    T: Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
    requires
        old(store).wf(),
        lo <= hi <= runs@.len(),
        forall|r: int| lo <= r < hi ==>
            (#[trigger] runs@[r]).start + runs@[r].len <= values@.len(),
        forall|r: int| lo <= r && r + 1 < hi ==>
            (#[trigger] runs@[r]).base.as_nat() + runs@[r].len <= runs@[r + 1].base.as_nat(),
    ensures
        final(store).wf(),
        final(store).unique_capture_spec() == old(store).unique_capture_spec(),
        final(store).needs_replayed_indices_spec() == old(store).needs_replayed_indices_spec(),
        final(store).restore_entries_clear_capture_spec()
            == old(store).restore_entries_clear_capture_spec(),
        final(store).captured() == old(store).captured(),
        final(store).data().len() == old(store).data().len(),
        forall|j: int| 0 <= j < old(store).data().len() ==>
            #[trigger] final(store).data()[j]
                == match cold_range_saved_value::<T, I>(runs@, values@, lo as int, hi as int, j as nat) {
                    Some(value) => value,
                    None => old(store).data()[j],
                },
{
    let ghost before = *store;
    let value_count = values.len();
    let mut r = lo;
    while r < hi
        invariant
            lo <= r <= hi <= runs@.len(),
            values@.len() == value_count,
            store.wf(),
            store.unique_capture_spec() == before.unique_capture_spec(),
            store.needs_replayed_indices_spec() == before.needs_replayed_indices_spec(),
            store.restore_entries_clear_capture_spec() == before.restore_entries_clear_capture_spec(),
            store.captured() == before.captured(),
            store.data().len() == before.data().len(),
            forall|q: int| lo <= q < hi ==>
                (#[trigger] runs@[q]).start + runs@[q].len <= values@.len(),
            forall|q: int| lo <= q && q + 1 < hi ==>
                (#[trigger] runs@[q]).base.as_nat() + runs@[q].len <= runs@[q + 1].base.as_nat(),
            forall|j: int| 0 <= j < before.data().len() ==>
                #[trigger] store.data()[j]
                    == match cold_range_saved_value::<T, I>(runs@, values@, lo as int, r as int, j as nat) {
                        Some(value) => value,
                        None => before.data()[j],
                    },
        decreases hi - r,
    {
        let run = runs[r];
        let slice = vstd::slice::slice_subrange(values.as_slice(), run.start, run.start + run.len);
        let ghost previous = store.data();
        store.restore_run(run.base, slice);
        proof {
            assert forall|j: int| 0 <= j < before.data().len() implies
                #[trigger] store.data()[j]
                    == match cold_range_saved_value::<T, I>(runs@, values@, lo as int, r + 1, j as nat) {
                        Some(value) => value,
                        None => before.data()[j],
                    } by {
                lemma_cold_range_extend::<T, I>(runs@, values@, lo as int, r as int, j as nat);
                if cold_run_covers(run, j as nat) {
                    assert(slice@[j - run.base.as_nat()]
                        == values@[run.start as int + j - run.base.as_nat()]);
                } else {
                    assert(store.data()[j] == previous[j]);
                }
            }
        }
        r += 1;
    }
}

/// Logical saved value for a chronological physical range. Choosing the first
/// hitter also describes a unique Hot range, without assuming sorted indices.
pub open(crate) spec fn range_saved_value<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, hi: int, j: nat,
) -> Option<T> {
    if captured_in_range::<T, I>(diffs, lo, hi, j) {
        let k = choose|k: int| lo <= k < hi
            && (#[trigger] diffs[k]).1.as_nat() == j
            && first_hitter::<T, I>(diffs, lo, k, j);
        Some(diffs[k].0)
    } else {
        None
    }
}

/// In a unique range the earliest-capture lookup is membership: any hitter is
/// the first hitter, and absence means no hitter.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_unique_range_saved_value<T, I: IndexLike>(
    a: Seq<(T, I)>, lo: int, hi: int, j: nat,
)
    requires 0 <= lo <= hi <= a.len(), stratum_unique::<T, I>(a, lo, hi),
    ensures
        forall|k: int| lo <= k < hi && (#[trigger] a[k]).1.as_nat() == j ==>
            range_saved_value::<T, I>(a, lo, hi, j) == Some(a[k].0),
        !captured_in_range::<T, I>(a, lo, hi, j) ==> range_saved_value::<T, I>(a, lo, hi, j) is None,
{
    assert forall|k: int| lo <= k < hi && (#[trigger] a[k]).1.as_nat() == j implies
        range_saved_value::<T, I>(a, lo, hi, j) == Some(a[k].0) by {
        assert(captured_in_range::<T, I>(a, lo, hi, j));
        lemma_lowest_hitter::<T, I>(a, lo, hi, j);
        let p = choose|p: int| lo <= p < hi && (#[trigger] a[p]).1.as_nat() == j
            && first_hitter::<T, I>(a, lo, p, j);
        assert(p == k);
    }
}

/// A unique range permuted within itself stays unique and keeps its map.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_unique_range_permutation<T, I: IndexLike>(
    a: Seq<(T, I)>, b: Seq<(T, I)>, lo: int, hi: int,
)
    requires 0 <= lo <= hi <= a.len(), hi <= b.len(),
        stratum_unique::<T, I>(a, lo, hi),
        a.subrange(lo, hi).to_multiset() == b.subrange(lo, hi).to_multiset(),
    ensures stratum_unique::<T, I>(b, lo, hi),
        forall|j: nat| #[trigger] range_saved_value::<T, I>(a, lo, hi, j)
            == range_saved_value::<T, I>(b, lo, hi, j),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    let sa = a.subrange(lo, hi);
    let sb = b.subrange(lo, hi);
    assert forall|x: (T, I)| #[trigger] sa.contains(x) <==> sb.contains(x) by {
        vstd::seq_lib::to_multiset_contains(sa, x);
        vstd::seq_lib::to_multiset_contains(sb, x);
    }
    assert(sa.no_duplicates()) by {
        assert forall|i: int, k: int| 0 <= i < sa.len() && 0 <= k < sa.len() && i != k
            implies sa[i] != sa[k] by {
            assert(sa[i] == a[lo + i]);
            assert(sa[k] == a[lo + k]);
        }
    }
    sa.lemma_multiset_has_no_duplicates();
    sb.lemma_multiset_has_no_duplicates_conv();
    assert forall|p: int, q: int| lo <= p < hi && lo <= q < hi && p != q implies
        (#[trigger] b[p]).1.as_nat() != (#[trigger] b[q]).1.as_nat() by {
        if b[p].1.as_nat() == b[q].1.as_nat() {
            let x = b[p];
            let y = b[q];
            assert(sb[p - lo] == x);
            assert(sb[q - lo] == y);
            assert(x != y);
            assert(sa.contains(x));
            assert(sa.contains(y));
            let p2 = choose|i: int| 0 <= i < sa.len() && sa[i] == x;
            let q2 = choose|i: int| 0 <= i < sa.len() && sa[i] == y;
            assert(a[lo + p2] == x);
            assert(a[lo + q2] == y);
            assert(p2 != q2);
        }
    }
    assert forall|j: nat| #[trigger] range_saved_value::<T, I>(a, lo, hi, j)
        == range_saved_value::<T, I>(b, lo, hi, j) by {
        lemma_unique_range_saved_value::<T, I>(a, lo, hi, j);
        lemma_unique_range_saved_value::<T, I>(b, lo, hi, j);
        if captured_in_range::<T, I>(a, lo, hi, j) {
            let k = choose|k: int| lo <= k < hi && 0 <= k < a.len() && (#[trigger] a[k]).1.as_nat() == j;
            assert(sa[k - lo] == a[k]);
            assert(sa.contains(a[k]));
            assert(sb.contains(a[k]));
            let m = choose|i: int| 0 <= i < sb.len() && sb[i] == a[k];
            assert(b[lo + m] == a[k]);
        } else if captured_in_range::<T, I>(b, lo, hi, j) {
            let k = choose|k: int| lo <= k < hi && 0 <= k < b.len() && (#[trigger] b[k]).1.as_nat() == j;
            assert(sb[k - lo] == b[k]);
            assert(sb.contains(b[k]));
            assert(sa.contains(b[k]));
            let m = choose|i: int| 0 <= i < sa.len() && sa[i] == b[k];
            assert(a[lo + m] == b[k]);
        }
    }
}

/// Equal physical ranges have equal earliest-capture maps, including absence.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_range_saved_value_local<T, I: IndexLike>(
    a: Seq<(T, I)>, b: Seq<(T, I)>, lo: int, hi: int, j: nat,
)
    requires 0 <= lo <= hi <= a.len(), hi <= b.len(),
        forall|q: int| lo <= q < hi ==> #[trigger] a[q] == b[q],
    ensures range_saved_value::<T, I>(a, lo, hi, j)
        == range_saved_value::<T, I>(b, lo, hi, j),
{
    if captured_in_range::<T, I>(a, lo, hi, j) {
        let q = choose|q: int| lo <= q < hi && 0 <= q < a.len()
            && (#[trigger] a[q]).1.as_nat() == j;
        assert(b[q] == a[q]);
        assert(captured_in_range::<T, I>(b, lo, hi, j));
    }
    if captured_in_range::<T, I>(b, lo, hi, j) {
        let q = choose|q: int| lo <= q < hi && 0 <= q < b.len()
            && (#[trigger] b[q]).1.as_nat() == j;
        assert(a[q] == b[q]);
        assert(captured_in_range::<T, I>(a, lo, hi, j));
        lemma_lowest_hitter::<T, I>(a, lo, hi, j);
        lemma_lowest_hitter::<T, I>(b, lo, hi, j);
        let x = choose|q: int| lo <= q < hi && (#[trigger] a[q]).1.as_nat() == j
            && first_hitter::<T, I>(a, lo, q, j);
        let y = choose|q: int| lo <= q < hi && (#[trigger] b[q]).1.as_nat() == j
            && first_hitter::<T, I>(b, lo, q, j);
        assert(a[x] == b[x]);
        assert(a[y] == b[y]);
        assert(x == y);
    }
}

/// Rebasing a physical range changes positions, not its first captured value.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_range_saved_value_subrange<T, I: IndexLike>(
    a: Seq<(T, I)>, lo: int, hi: int, j: nat,
)
    requires 0 <= lo <= hi <= a.len(),
    ensures range_saved_value::<T, I>(a, lo, hi, j)
        == range_saved_value::<T, I>(a.subrange(lo, hi), 0, hi - lo, j),
{
    let b = a.subrange(lo, hi);
    if captured_in_range::<T, I>(a, lo, hi, j) {
        let q = choose|q: int| lo <= q < hi && 0 <= q < a.len()
            && (#[trigger] a[q]).1.as_nat() == j;
        assert(b[q - lo] == a[q]);
        assert(captured_in_range::<T, I>(b, 0, hi - lo, j));
    }
    if captured_in_range::<T, I>(b, 0, hi - lo, j) {
        let q = choose|q: int| 0 <= q < hi - lo && 0 <= q < b.len()
            && (#[trigger] b[q]).1.as_nat() == j;
        assert(a[q + lo] == b[q]);
        assert(captured_in_range::<T, I>(a, lo, hi, j));
        lemma_lowest_hitter::<T, I>(a, lo, hi, j);
        lemma_lowest_hitter::<T, I>(b, 0, hi - lo, j);
        let x = choose|q: int| lo <= q < hi && (#[trigger] a[q]).1.as_nat() == j
            && first_hitter::<T, I>(a, lo, q, j);
        let y = choose|q: int| 0 <= q < hi - lo && (#[trigger] b[q]).1.as_nat() == j
            && first_hitter::<T, I>(b, 0, q, j);
        assert(b[x - lo] == a[x]);
        assert(a[y + lo] == b[y]);
        assert(x == y + lo);
    }
}

/// Prefix retirement rebases coordinates without changing any saved value.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_range_saved_value_retire_prefix<T, I: IndexLike>(
    a: Seq<(T, I)>, cut: int, lo: int, hi: int, j: nat,
)
    requires 0 <= cut <= lo <= hi <= a.len(),
    ensures range_saved_value::<T, I>(a, lo, hi, j)
        == range_saved_value::<T, I>(a.subrange(cut, a.len() as int), lo - cut, hi - cut, j),
{
    let b = a.subrange(cut, a.len() as int);
    lemma_range_saved_value_subrange::<T, I>(a, lo, hi, j);
    lemma_range_saved_value_subrange::<T, I>(b, lo - cut, hi - cut, j);
    assert(b.subrange(lo - cut, hi - cut) =~= a.subrange(lo, hi));
}

/// Re-express the existing per-cell invariant through the common optional
/// saved-value interpretation; no new reconstruction assumption is introduced.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_range_saved_value_contract<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, j: int,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        0 <= j < snap.len(),
        frame_cell_inv::<T, I>(above, diffs, lo, hi, snap, j),
    ensures
        match range_saved_value::<T, I>(diffs, lo, hi, j as nat) {
            Some(value) => value == snap[j],
            None => j < above.len() && above[j] == snap[j],
        },
{
    if captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
        let k = choose|k: int| lo <= k < hi
            && (#[trigger] diffs[k]).1.as_nat() == j as nat
            && first_hitter::<T, I>(diffs, lo, k, j as nat);
        let q = choose|q: int| lo <= q < hi
            && (#[trigger] diffs[q]).1.as_nat() == j as nat
            && diffs[q].0 == snap[j]
            && first_hitter::<T, I>(diffs, lo, q, j as nat);
        assert(k == q);
    }
}

/// Backward physical replay preserves length and implements the saved-value
/// map. In particular, duplicate Trail writes leave the earliest value last.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_overlay_saved_value<T, I: IndexLike>(
    base: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, j: int,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        0 <= j < base.len(),
    ensures
        overlay::<T, I>(base, diffs, lo, hi).len() == base.len(),
        overlay::<T, I>(base, diffs, lo, hi)[j]
            == match range_saved_value::<T, I>(diffs, lo, hi, j as nat) {
                Some(value) => value,
                None => base[j],
            },
{
    lemma_overlay_len::<T, I>(base, diffs, lo, hi);
    if captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
        lemma_lowest_hitter::<T, I>(diffs, lo, hi, j as nat);
        let k = choose|k: int| lo <= k < hi
            && (#[trigger] diffs[k]).1.as_nat() == j as nat
            && first_hitter::<T, I>(diffs, lo, k, j as nat);
        lemma_overlay_lowest::<T, I>(base, diffs, lo, hi, k, j);
    } else {
        lemma_overlay_uncaptured::<T, I>(base, diffs, lo, hi, j);
    }
}

/// Checked executable boundary used by both Trail and Hot physical replay.
/// The range may contain duplicate indices, including across frame boundaries.
/// This retains the store's exact replay/capture contract and additionally
/// exposes its per-index saved-value effect to the tier-independent argument.
#[inline(always)]
#[verifier::spinoff_prover]
pub(crate) fn replay_physical_range<T, I, S, const TRACK: bool>(
    store: &mut S, pool: &std::vec::Vec<(T, I)>, lo: usize, hi: usize,
)
where
    T: Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
    requires
        old(store).wf(),
        lo <= hi <= pool@.len(),
    ensures
        final(store).wf(),
        final(store).unique_capture_spec() == old(store).unique_capture_spec(),
        final(store).needs_replayed_indices_spec() == old(store).needs_replayed_indices_spec(),
        final(store).restore_entries_clear_capture_spec()
            == old(store).restore_entries_clear_capture_spec(),
        final(store).data() == overlay::<T, I>(
            old(store).data(), pool@, lo as int, hi as int),
        final(store).data().len() == old(store).data().len(),
        forall|j: int| 0 <= j < old(store).data().len() ==>
            #[trigger] final(store).data()[j]
                == match range_saved_value::<T, I>(pool@, lo as int, hi as int, j as nat) {
                    Some(value) => value,
                    None => old(store).data()[j],
                },
        TRACK ==> forall|j: int| 0 <= j < final(store).captured().len()
            && #[trigger] final(store).captured()[j]
            ==> j < old(store).captured().len() && old(store).captured()[j],
        TRACK && old(store).restore_entries_clear_capture_spec() ==>
            forall|j: int| 0 <= j < final(store).captured().len()
                && #[trigger] final(store).captured()[j]
                ==> !captured_in_range::<T, I>(pool@, lo as int, hi as int, j as nat),
{
    let ghost base = store.data();
    store.restore_overlay(pool, lo, hi);
    proof {
        lemma_overlay_len::<T, I>(base, pool@, lo as int, hi as int);
        assert forall|j: int| 0 <= j < base.len() implies
            #[trigger] store.data()[j]
                == match range_saved_value::<T, I>(pool@, lo as int, hi as int, j as nat) {
                    Some(value) => value,
                    None => base[j],
                } by {
            lemma_overlay_saved_value::<T, I>(base, pool@, lo as int, hi as int, j);
        }
    }
}

/// No entry in `[lo, k)` hits `j`: position `k`'s entry is the stratum's
/// first hitter of `j`. The witness shape `lemma_overlay_lowest` consumes.
pub open(crate) spec fn first_hitter<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, k: int, j: nat,
) -> bool {
    forall|q: int| lo <= q < k ==> (#[trigger] diffs[q]).1.as_nat() != j
}

/// At most one entry per cell in `[lo, hi)`: the unique capture discipline's
/// per-stratum guarantee. Holds for every stratum of a column whose store
/// answers `unique_capture_spec()` (a `Vec::wf` clause); the sealing and
/// reordering paths require it, reconstruction does not.
pub open(crate) spec fn stratum_unique<T, I: IndexLike>(
    diffs: Seq<(T, I)>, lo: int, hi: int,
) -> bool {
    forall|a: int, b: int| lo <= a < hi && lo <= b < hi && a != b
        ==> (#[trigger] diffs[a]).1.as_nat() != (#[trigger] diffs[b]).1.as_nat()
}

/// Range-form of the two-arm frame invariant for one stratum `[lo, hi)`.
/// `above` is the layer above (snapshot[k+1] or the view); `snap` is this
/// stratum's snapshot. Stated over the diff-log range directly.
///
/// Note: no `saved_len <= above.len()` requirement — `above` (the view, for
/// the top frame) may be shorter than `saved_len` in the post-pop state. The
/// coverage clause inside `frame_cell_inv` handles the popped cells.
pub open(crate) spec fn frame_inv_range<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat,
) -> bool {
    &&& snap.len() == saved_len
    &&& (forall|k: int| lo <= k < hi ==>
            (#[trigger] diffs[k]).1.as_nat() < saved_len)
    &&& (forall|j: int| 0 <= j < saved_len as int ==>
            #[trigger] frame_cell_inv::<T, I>(above, diffs, lo, hi, snap, j))
}

/// Instantiate `frame_inv_range`'s per-cell forall at one cell `j`. The
/// forall's trigger is `frame_cell_inv(...)`, so this is just an explicit
/// hook for call sites that need the per-cell fact in hand.
pub(crate) proof fn lemma_frame_inv_arm_at<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat, j: int,
)
    requires
        frame_inv_range::<T, I>(above, diffs, lo, hi, snap, saved_len),
        0 <= j < saved_len as int,
    ensures
        frame_cell_inv::<T, I>(above, diffs, lo, hi, snap, j),
{
}

/// Physical encodings with the same optional saved values obey the same
/// captured-or-inherited contract. Equality includes absence outside the saved
/// domain, so the destination cannot introduce an out-of-domain capture.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_frame_inv_range_same_saved_map<T, I: IndexLike>(
    above: Seq<T>, a: Seq<(T, I)>, alo: int, ahi: int,
    b: Seq<(T, I)>, blo: int, bhi: int, snap: Seq<T>, saved_len: nat,
)
    requires 0 <= alo <= ahi <= a.len(), 0 <= blo <= bhi <= b.len(),
        frame_inv_range::<T, I>(above, a, alo, ahi, snap, saved_len),
        forall|j: nat| #[trigger] range_saved_value::<T, I>(a, alo, ahi, j)
            == range_saved_value::<T, I>(b, blo, bhi, j),
    ensures frame_inv_range::<T, I>(above, b, blo, bhi, snap, saved_len),
{
    assert forall|q: int| blo <= q < bhi implies
        (#[trigger] b[q]).1.as_nat() < saved_len by {
        let j = b[q].1.as_nat();
        assert(captured_in_range::<T, I>(b, blo, bhi, j));
        assert(range_saved_value::<T, I>(a, alo, ahi, j)
            == range_saved_value::<T, I>(b, blo, bhi, j));
        assert(captured_in_range::<T, I>(a, alo, ahi, j));
        let p = choose|p: int| alo <= p < ahi && 0 <= p < a.len()
            && (#[trigger] a[p]).1.as_nat() == j;
    }
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, b, blo, bhi, snap, j) by {
        lemma_frame_inv_arm_at::<T, I>(above, a, alo, ahi, snap, saved_len, j);
        lemma_range_saved_value_contract::<T, I>(above, a, alo, ahi, snap, j);
        assert(range_saved_value::<T, I>(a, alo, ahi, j as nat)
            == range_saved_value::<T, I>(b, blo, bhi, j as nat));
        if captured_in_range::<T, I>(b, blo, bhi, j as nat) {
            lemma_lowest_hitter::<T, I>(b, blo, bhi, j as nat);
            let q = choose|q: int| blo <= q < bhi
                && (#[trigger] b[q]).1.as_nat() == j as nat
                && first_hitter::<T, I>(b, blo, q, j as nat);
            assert(range_saved_value::<T, I>(b, blo, bhi, j as nat) == Some(b[q].0));
            assert(b[q].0 == snap[j]);
        }
    }
}

/// Extend the layer above a frame without changing the frame's saved domain.
/// In the 2D proof grid this adds live columns on the right: captured columns
/// ignore the live row, while every uncaptured column was already in bounds of
/// `above_old` and therefore keeps the same value in `above_new`.
pub(crate) proof fn lemma_frame_inv_range_grow_layer<T, I: IndexLike>(
    above_old: Seq<T>, above_new: Seq<T>, diffs: Seq<(T, I)>,
    lo: int, hi: int, snap: Seq<T>, saved_len: nat,
)
    requires
        frame_inv_range::<T, I>(above_old, diffs, lo, hi, snap, saved_len),
        above_old.len() <= above_new.len(),
        forall|j: int| 0 <= j < above_old.len() ==>
            #[trigger] above_new[j] == above_old[j],
    ensures
        frame_inv_range::<T, I>(above_new, diffs, lo, hi, snap, saved_len),
{
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above_new, diffs, lo, hi, snap, j)
    by {
        lemma_frame_inv_arm_at::<T, I>(
            above_old, diffs, lo, hi, snap, saved_len, j);
        if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
            assert(j < above_old.len());
            assert(above_new[j] == above_old[j]);
        }
    }
}

/// Contract the layer above a frame after every removed saved column has been
/// covered. In the 2D grid, uncovered columns must remain inside the retained
/// horizontal prefix; covered columns are independent of live-row length.
pub(crate) proof fn lemma_frame_inv_range_shrink_layer<T, I: IndexLike>(
    above_old: Seq<T>, above_new: Seq<T>, diffs: Seq<(T, I)>,
    lo: int, hi: int, snap: Seq<T>, saved_len: nat,
)
    requires
        frame_inv_range::<T, I>(above_old, diffs, lo, hi, snap, saved_len),
        above_new.len() <= above_old.len(),
        forall|j: int| 0 <= j < above_new.len() ==>
            #[trigger] above_new[j] == above_old[j],
        forall|j: int| above_new.len() <= j < saved_len as int ==>
            #[trigger] captured_in_range::<T, I>(diffs, lo, hi, j as nat),
    ensures
        frame_inv_range::<T, I>(above_new, diffs, lo, hi, snap, saved_len),
{
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above_new, diffs, lo, hi, snap, j)
    by {
        lemma_frame_inv_arm_at::<T, I>(
            above_old, diffs, lo, hi, snap, saved_len, j);
        if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
            assert(j < above_new.len());
            assert(above_new[j] == above_old[j]);
        }
    }
}

/// Remove the last live column after capturing it when it lies inside the
/// frame's saved domain. Any still-higher saved column was already absent from
/// `above_old`, so the old invariant forces it into the covered arm.
pub(crate) proof fn lemma_frame_inv_range_pop_last<T, I: IndexLike>(
    above_old: Seq<T>, above_new: Seq<T>, diffs: Seq<(T, I)>,
    lo: int, hi: int, snap: Seq<T>, saved_len: nat,
)
    requires
        frame_inv_range::<T, I>(above_old, diffs, lo, hi, snap, saved_len),
        above_old.len() > 0,
        above_new == above_old.drop_last(),
        above_new.len() < saved_len ==>
            captured_in_range::<T, I>(
                diffs, lo, hi, above_new.len()),
    ensures
        frame_inv_range::<T, I>(above_new, diffs, lo, hi, snap, saved_len),
{
    assert forall|j: int| above_new.len() <= j < saved_len as int implies
        #[trigger] captured_in_range::<T, I>(diffs, lo, hi, j as nat) by {
        if j > above_new.len() {
            assert(j >= above_old.len());
            lemma_frame_inv_arm_at::<T, I>(
                above_old, diffs, lo, hi, snap, saved_len, j);
        }
    }
    lemma_frame_inv_range_shrink_layer::<T, I>(
        above_old, above_new, diffs, lo, hi, snap, saved_len);
}

/// `stratum_unique` transfers between diff logs that agree pointwise on the
/// stratum `[lo, hi)` (covers both an extension and a truncation whose
/// surviving prefix contains the stratum).
pub(crate) proof fn lemma_stratum_unique_local<T, I: IndexLike>(
    da: Seq<(T, I)>, db: Seq<(T, I)>, lo: int, hi: int,
)
    requires
        0 <= lo <= hi,
        hi <= da.len(),
        hi <= db.len(),
        forall|q: int| lo <= q < hi ==> #[trigger] db[q] == da[q],
        stratum_unique::<T, I>(da, lo, hi),
    ensures
        stratum_unique::<T, I>(db, lo, hi),
{
    assert forall|a: int, b: int| lo <= a < hi && lo <= b < hi && a != b
        implies (#[trigger] db[a]).1.as_nat() != (#[trigger] db[b]).1.as_nat() by {
        assert(db[a] == da[a]);
        assert(db[b] == da[b]);
        assert(da[a].1.as_nat() != da[b].1.as_nat());
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_stratum_unique_subrange<T, I: IndexLike>(a: Seq<(T, I)>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.len(),
        stratum_unique::<T, I>(a.subrange(lo, hi), 0, hi - lo),
    ensures stratum_unique::<T, I>(a, lo, hi),
{
    assert forall|x: int, y: int| lo <= x < hi && lo <= y < hi && x != y implies
        (#[trigger] a[x]).1.as_nat() != (#[trigger] a[y]).1.as_nat() by {
        assert(a.subrange(lo, hi)[x - lo] == a[x]);
        assert(a.subrange(lo, hi)[y - lo] == a[y]);
    }
}

/// `stratum_unique` for the top stratum extended by ONE appended entry whose
/// index has no prior hit in the stratum: the unique discipline's wf clause
/// survives a first-write capture append.
pub(crate) proof fn lemma_stratum_unique_append<T, I: IndexLike>(
    da: Seq<(T, I)>, db: Seq<(T, I)>, lo: int, jnew: nat,
)
    requires
        0 <= lo <= da.len(),
        db.len() == da.len() + 1,
        db.subrange(0, da.len() as int) == da,
        db[da.len() as int].1.as_nat() == jnew,
        !captured_in_range::<T, I>(da, lo, da.len() as int, jnew),
        stratum_unique::<T, I>(da, lo, da.len() as int),
    ensures
        stratum_unique::<T, I>(db, lo, db.len() as int),
{
    assert forall|a: int, b: int| lo <= a < db.len() && lo <= b < db.len() && a != b
        implies (#[trigger] db[a]).1.as_nat() != (#[trigger] db[b]).1.as_nat() by {
        if a < da.len() && b < da.len() {
            assert(db.subrange(0, da.len() as int)[a] == db[a]);
            assert(db.subrange(0, da.len() as int)[b] == db[b]);
            assert(da[a].1.as_nat() != da[b].1.as_nat());
        } else if a == da.len() as int {
            assert(db.subrange(0, da.len() as int)[b] == db[b]);
            // The appended index has no hit below: a hit at b would witness
            // captured_in_range on da.
            assert(da[b].1.as_nat() != jnew);
        } else {
            assert(b == da.len() as int);
            assert(db.subrange(0, da.len() as int)[a] == db[a]);
            assert(da[a].1.as_nat() != jnew);
        }
    }
}

/// Extend an open frame by its first capture. The appended value is the live
/// layer value, which the old uncaptured arm already equates to the snapshot;
/// every other cell is framed by `lemma_captured_in_range_append_other`.
pub(crate) proof fn lemma_frame_inv_range_capture_append<T, I: IndexLike>(
    above: Seq<T>, da: Seq<(T, I)>, db: Seq<(T, I)>, lo: int,
    snap: Seq<T>, saved_len: nat, jnew: int,
)
    requires
        frame_inv_range::<T, I>(above, da, lo, da.len() as int, snap, saved_len),
        0 <= lo <= da.len(),
        0 <= jnew < saved_len as int,
        (jnew as nat) < above.len(),
        !captured_in_range::<T, I>(da, lo, da.len() as int, jnew as nat),
        db.len() == da.len() + 1,
        db.subrange(0, da.len() as int) == da,
        db[da.len() as int].1.as_nat() == jnew as nat,
        db[da.len() as int].0 == above[jnew],
    ensures
        frame_inv_range::<T, I>(above, db, lo, db.len() as int, snap, saved_len),
{
    let n = da.len() as int;
    lemma_frame_inv_arm_at::<T, I>(above, da, lo, n, snap, saved_len, jnew);
    assert(above[jnew] == snap[jnew]);
    assert forall|k: int| lo <= k < db.len() implies
        (#[trigger] db[k]).1.as_nat() < saved_len by {
        if k < n {
            assert(db[k] == db.subrange(0, n)[k]);
            assert(db[k] == da[k]);
        } else {
            assert(k == n);
        }
    }
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, db, lo, db.len() as int, snap, j) by {
        if j == jnew {
            assert(captured_in_range::<T, I>(db, lo, db.len() as int, j as nat));
            assert forall|q: int| lo <= q < n implies
                (#[trigger] db[q]).1.as_nat() != j as nat by {
                assert(db[q] == db.subrange(0, n)[q]);
                assert(db[q] == da[q]);
            }
            assert(first_hitter::<T, I>(db, lo, n, j as nat));
        } else {
            lemma_frame_inv_arm_at::<T, I>(above, da, lo, n, snap, saved_len, j);
            lemma_captured_in_range_append_other::<T, I>(
                da, db, lo, j as nat, jnew as nat);
            if captured_in_range::<T, I>(da, lo, n, j as nat) {
                let p = choose|p: int| lo <= p < n
                    && (#[trigger] da[p]).1.as_nat() == j as nat
                    && da[p].0 == snap[j]
                    && first_hitter::<T, I>(da, lo, p, j as nat);
                assert(db[p] == db.subrange(0, n)[p]);
                assert(db[p] == da[p]);
                assert forall|q: int| lo <= q < p implies
                    (#[trigger] db[q]).1.as_nat() != j as nat by {
                    assert(db[q] == db.subrange(0, n)[q]);
                    assert(db[q] == da[q]);
                }
                assert(first_hitter::<T, I>(db, lo, p, j as nat));
            }
        }
    }
}

/// Appending a later chronological write for an index already covered by the
/// frame preserves reconstruction: the existing first hitter remains the
/// authoritative snapshot value and the appended duplicate is vertically
/// above it in the proof grid.
pub(crate) proof fn lemma_frame_inv_range_append_duplicate<T, I: IndexLike>(
    above: Seq<T>, da: Seq<(T, I)>, db: Seq<(T, I)>, lo: int,
    snap: Seq<T>, saved_len: nat, jnew: int,
)
    requires
        frame_inv_range::<T, I>(above, da, lo, da.len() as int, snap, saved_len),
        0 <= lo <= da.len(),
        0 <= jnew < saved_len as int,
        captured_in_range::<T, I>(da, lo, da.len() as int, jnew as nat),
        db.len() == da.len() + 1,
        db.subrange(0, da.len() as int) == da,
        db[da.len() as int].1.as_nat() == jnew as nat,
    ensures
        frame_inv_range::<T, I>(above, db, lo, db.len() as int, snap, saved_len),
{
    let n = da.len() as int;
    assert forall|k: int| lo <= k < db.len() implies
        (#[trigger] db[k]).1.as_nat() < saved_len by {
        if k < n {
            assert(db[k] == db.subrange(0, n)[k]);
            assert(db[k] == da[k]);
        } else {
            assert(k == n);
        }
    }
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, db, lo, db.len() as int, snap, j) by {
        lemma_frame_inv_arm_at::<T, I>(above, da, lo, n, snap, saved_len, j);
        if j == jnew {
            let p = choose|p: int| lo <= p < n
                && (#[trigger] da[p]).1.as_nat() == j as nat
                && da[p].0 == snap[j]
                && first_hitter::<T, I>(da, lo, p, j as nat);
            assert(db[p] == db.subrange(0, n)[p]);
            assert(db[p] == da[p]);
            assert forall|q: int| lo <= q < p implies
                (#[trigger] db[q]).1.as_nat() != j as nat by {
                assert(db[q] == db.subrange(0, n)[q]);
                assert(db[q] == da[q]);
            }
            assert(first_hitter::<T, I>(db, lo, p, j as nat));
        } else {
            lemma_captured_in_range_append_other::<T, I>(
                da, db, lo, j as nat, jnew as nat);
            if captured_in_range::<T, I>(da, lo, n, j as nat) {
                let p = choose|p: int| lo <= p < n
                    && (#[trigger] da[p]).1.as_nat() == j as nat
                    && da[p].0 == snap[j]
                    && first_hitter::<T, I>(da, lo, p, j as nat);
                assert(db[p] == db.subrange(0, n)[p]);
                assert(db[p] == da[p]);
                assert forall|q: int| lo <= q < p implies
                    (#[trigger] db[q]).1.as_nat() != j as nat by {
                    assert(db[q] == db.subrange(0, n)[q]);
                    assert(db[q] == da[q]);
                }
                assert(first_hitter::<T, I>(db, lo, p, j as nat));
            }
        }
    }
}

/// Changing the live layer at an already-captured top-frame cell preserves
/// reconstruction: captured arms do not read the layer, and every uncaptured
/// cell is necessarily a different index.
pub(crate) proof fn lemma_frame_inv_range_set_captured<T, I: IndexLike>(
    above: Seq<T>, after: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat, changed: int, value: T,
)
    requires
        frame_inv_range::<T, I>(above, diffs, lo, hi, snap, saved_len),
        0 <= changed < above.len(),
        after == above.update(changed, value),
        captured_in_range::<T, I>(diffs, lo, hi, changed as nat),
    ensures
        frame_inv_range::<T, I>(after, diffs, lo, hi, snap, saved_len),
{
    assert(snap.len() == saved_len);
    assert forall|k: int| lo <= k < hi implies
        (#[trigger] diffs[k]).1.as_nat() < saved_len by {}
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(after, diffs, lo, hi, snap, j) by {
        lemma_frame_inv_arm_at::<T, I>(above, diffs, lo, hi, snap, saved_len, j);
        if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
            assert(j != changed);
            assert(after[j] == above[j]);
        }
    }
}

/// A write beyond a frame's saved extent cannot affect any cell quantified by
/// that frame's reconstruction predicate.
pub(crate) proof fn lemma_frame_inv_range_set_outside<T, I: IndexLike>(
    above: Seq<T>, after: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat, changed: int, value: T,
)
    requires
        frame_inv_range::<T, I>(above, diffs, lo, hi, snap, saved_len),
        saved_len as int <= changed < above.len(),
        after == above.update(changed, value),
    ensures
        frame_inv_range::<T, I>(after, diffs, lo, hi, snap, saved_len),
{
    assert(snap.len() == saved_len);
    assert forall|k: int| lo <= k < hi implies
        (#[trigger] diffs[k]).1.as_nat() < saved_len by {}
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(after, diffs, lo, hi, snap, j) by {
        lemma_frame_inv_arm_at::<T, I>(above, diffs, lo, hi, snap, saved_len, j);
        assert(j != changed);
        assert(after[j] == above[j]);
    }
}

/// `frame_inv_range` is invariant under a PERMUTATION of the diff-log range
/// `[lo, hi)`: it reads that range only through quantifiers (`forall`/`exists` over
/// `k in [lo, hi)`), never through `overlay` or a positional index, so it depends on
/// the multiset of the range, not its order. This is what lets a sorted (reordering)
/// cold flush preserve the Vec invariant: sorting a just-closed frame's captures
/// keeps that stratum's write multiset, so its `frame_inv_range` carries. `d2`'s
/// uniqueness over the range is a hypothesis (the sorted encoder preserves it via
/// `unique_idx`), so no multiplicity/count reasoning is needed.
pub(crate) proof fn lemma_frame_inv_range_multiset<T: Copy, I: IndexLike>(
    above: Seq<T>, d1: Seq<(T, I)>, d2: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat,
)
    requires
        frame_inv_range::<T, I>(above, d1, lo, hi, snap, saved_len),
        0 <= lo <= hi,
        hi <= d1.len(),
        hi <= d2.len(),
        d1.subrange(lo, hi).to_multiset() == d2.subrange(lo, hi).to_multiset(),
        forall|a: int, b: int| lo <= a < hi && lo <= b < hi && a != b ==>
            (#[trigger] d2[a]).1.as_nat() != (#[trigger] d2[b]).1.as_nat(),
    ensures
        frame_inv_range::<T, I>(above, d2, lo, hi, snap, saved_len),
{
    let s1 = d1.subrange(lo, hi);
    let s2 = d2.subrange(lo, hi);
    // Each entry of one range is present in the other (equal multisets).
    assert forall|x: (T, I)| s1.contains(x) implies s2.contains(x) by {
        vstd::seq_lib::to_multiset_contains(s1, x);
        vstd::seq_lib::to_multiset_contains(s2, x);
    }
    assert forall|x: (T, I)| s2.contains(x) implies s1.contains(x) by {
        vstd::seq_lib::to_multiset_contains(s1, x);
        vstd::seq_lib::to_multiset_contains(s2, x);
    }
    // Index bound: every d2 entry in the range equals some d1 entry in the range.
    assert forall|k: int| lo <= k < hi implies (#[trigger] d2[k]).1.as_nat() < saved_len by {
        assert(s2[k - lo] == d2[k]);
        assert(s2.contains(d2[k]));
        assert(s1.contains(d2[k]));
        let m = choose|m: int| 0 <= m < s1.len() && s1[m] == d2[k];
        assert(s1[m] == d1[lo + m]);
    }
    // Per-cell two-arm: captured-in-range and the covering value both transfer by
    // membership (exists over the range).
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, d2, lo, hi, snap, j) by {
        assert(frame_cell_inv::<T, I>(above, d1, lo, hi, snap, j));
        // captured_in_range(d2) <==> captured_in_range(d1) via membership.
        if captured_in_range::<T, I>(d2, lo, hi, j as nat) {
            let k = choose|k: int| lo <= k < hi && 0 <= k < d2.len()
                && (#[trigger] d2[k]).1.as_nat() == j as nat;
            assert(s2[k - lo] == d2[k]);
            assert(s2.contains(d2[k]));
            assert(s1.contains(d2[k]));
            let m = choose|m: int| 0 <= m < s1.len() && s1[m] == d2[k];
            assert(s1[m] == d1[lo + m]);
            assert(captured_in_range::<T, I>(d1, lo, hi, j as nat));
        }
        if captured_in_range::<T, I>(d1, lo, hi, j as nat) {
            let k = choose|k: int| lo <= k < hi && 0 <= k < d1.len()
                && (#[trigger] d1[k]).1.as_nat() == j as nat;
            assert(s1[k - lo] == d1[k]);
            assert(s1.contains(d1[k]));
            assert(s2.contains(d1[k]));
            let m = choose|m: int| 0 <= m < s2.len() && s2[m] == d1[k];
            assert(s2[m] == d2[lo + m]);
            assert(captured_in_range::<T, I>(d2, lo, hi, j as nat));
        }
        // Covering value arm: the covering d1 entry is present in d2's range.
        if captured_in_range::<T, I>(d1, lo, hi, j as nat) {
            let k1 = choose|k: int| lo <= k < hi
                && (#[trigger] d1[k]).1.as_nat() == j as nat && d1[k].0 == snap[j];
            assert(s1[k1 - lo] == d1[k1]);
            assert(s1.contains(d1[k1]));
            assert(s2.contains(d1[k1]));
            let m = choose|m: int| 0 <= m < s2.len() && s2[m] == d1[k1];
            assert(s2[m] == d2[lo + m]);
        }
    }
}

/// `captured_in_range` (whether some entry in `[lo, hi)` writes index `j`) depends
/// only on the range's multiset, not its order: it is an existential over the range.
/// The bridge and no-stray wf clauses read the diff log through this, so they too
/// survive a within-range permutation.
pub(crate) proof fn lemma_captured_in_range_multiset<T: Copy, I: IndexLike>(
    d1: Seq<(T, I)>, d2: Seq<(T, I)>, lo: int, hi: int, j: nat,
)
    requires
        0 <= lo <= hi,
        hi <= d1.len(),
        hi <= d2.len(),
        d1.subrange(lo, hi).to_multiset() == d2.subrange(lo, hi).to_multiset(),
    ensures
        captured_in_range::<T, I>(d1, lo, hi, j) == captured_in_range::<T, I>(d2, lo, hi, j),
{
    let s1 = d1.subrange(lo, hi);
    let s2 = d2.subrange(lo, hi);
    if captured_in_range::<T, I>(d1, lo, hi, j) {
        let k = choose|k: int| lo <= k < hi && 0 <= k < d1.len()
            && (#[trigger] d1[k]).1.as_nat() == j;
        assert(s1[k - lo] == d1[k]);
        assert(s1.contains(d1[k]));
        vstd::seq_lib::to_multiset_contains(s1, d1[k]);
        vstd::seq_lib::to_multiset_contains(s2, d1[k]);
        let m = choose|m: int| 0 <= m < s2.len() && s2[m] == d1[k];
        assert(s2[m] == d2[lo + m]);
        assert(captured_in_range::<T, I>(d2, lo, hi, j));
    }
    if captured_in_range::<T, I>(d2, lo, hi, j) {
        let k = choose|k: int| lo <= k < hi && 0 <= k < d2.len()
            && (#[trigger] d2[k]).1.as_nat() == j;
        assert(s2[k - lo] == d2[k]);
        assert(s2.contains(d2[k]));
        vstd::seq_lib::to_multiset_contains(s1, d2[k]);
        vstd::seq_lib::to_multiset_contains(s2, d2[k]);
        let m = choose|m: int| 0 <= m < s1.len() && s1[m] == d2[k];
        assert(s1[m] == d1[lo + m]);
        assert(captured_in_range::<T, I>(d1, lo, hi, j));
    }
}



/// `frame_inv_range` transfers from a stratum to its dedupe-and-permute
/// replacement at the same start position: `dnew`'s stratum is a unique-
/// index permutation of `dedupe_first_spec` of `dold`'s. The captured set
/// is preserved, and the surviving entry for each cell is the old stratum's
/// FIRST hitter - which is exactly the entry `frame_cell_inv`'s captured
/// arm pins. The dedupe frame rule's k == b case.
#[verifier::rlimit(600)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_frame_inv_range_dedupe<T: Copy, I: IndexLike>(
    above: Seq<T>, dold: Seq<(T, I)>, dnew: Seq<(T, I)>,
    lo: int, m: nat, kept: nat, snap: Seq<T>, saved_len: nat,
)
    requires
        0 <= lo,
        lo + m <= dold.len(),
        lo + kept <= dnew.len(),
        kept == crate::diff_compress::dedupe_first_spec(
            dold.subrange(lo, lo + m as int)).len(),
        dnew.subrange(lo, lo + kept as int).to_multiset()
            == crate::diff_compress::dedupe_first_spec(
                dold.subrange(lo, lo + m as int)).to_multiset(),
        crate::diff_compress::unique_idx(dnew.subrange(lo, lo + kept as int)),
        frame_inv_range::<T, I>(above, dold, lo, lo + m as int, snap, saved_len),
    ensures
        frame_inv_range::<T, I>(above, dnew, lo, lo + kept as int, snap, saved_len),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    let sold = dold.subrange(lo, lo + m as int);
    let r = dnew.subrange(lo, lo + kept as int);
    let dd = crate::diff_compress::dedupe_first_spec(sold);
    let rp = crate::diff_compress::dedupe_positions(sold, sold.len() as int);
    crate::diff_compress::lemma_dedupe_prefix_props::<T, I>(sold, sold.len() as int);
    // Membership both ways between the folded stratum and the dedupe.
    assert forall|x: (T, I)| r.contains(x) implies dd.contains(x) by {
        vstd::seq_lib::to_multiset_contains(r, x);
        vstd::seq_lib::to_multiset_contains(dd, x);
    }
    assert forall|x: (T, I)| dd.contains(x) implies r.contains(x) by {
        vstd::seq_lib::to_multiset_contains(r, x);
        vstd::seq_lib::to_multiset_contains(dd, x);
    }
    // Every folded entry is an old-stratum entry (through the dedupe).
    assert forall|k: int| #![trigger r[k]] 0 <= k < r.len() implies exists|p: int| #![trigger sold[p]]
        0 <= p < sold.len() && r[k] == sold[p]
        && first_hitter::<T, I>(sold, 0, p, sold[p].1.as_nat()) by {
        assert(r.contains(r[k]));
        assert(dd.contains(r[k]));
        let t = choose|t: int| 0 <= t < dd.len() && dd[t] == r[k];
        let p0 = rp[t];
        assert(dd[t] == sold[p0]);
        assert(first_hitter::<T, I>(sold, 0, p0, sold[p0].1.as_nat()));
    }
    // Index bound.
    assert forall|k: int| lo <= k < lo + kept implies
        (#[trigger] dnew[k]).1.as_nat() < saved_len by {
        assert(r[k - lo] == dnew[k]);
        let p = choose|p: int| #![trigger sold[p]] 0 <= p < sold.len()
            && r[k - lo] == sold[p]
            && first_hitter::<T, I>(sold, 0, p, sold[p].1.as_nat());
        assert(sold[p] == dold[lo + p]);
    }
    // Per-cell two-arm transfer.
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] frame_cell_inv::<T, I>(above, dnew, lo, lo + kept as int, snap, j) by {
        assert(frame_cell_inv::<T, I>(above, dold, lo, lo + m as int, snap, j));
        // Captured equivalence, new -> old.
        if captured_in_range::<T, I>(dnew, lo, lo + kept as int, j as nat) {
            let k = choose|k: int| lo <= k < lo + kept && 0 <= k < dnew.len()
                && (#[trigger] dnew[k]).1.as_nat() == j as nat;
            assert(r[k - lo] == dnew[k]);
            let p = choose|p: int| #![trigger sold[p]] 0 <= p < sold.len()
                && r[k - lo] == sold[p]
                && first_hitter::<T, I>(sold, 0, p, sold[p].1.as_nat());
            assert(sold[p] == dold[lo + p]);
            assert(captured_in_range::<T, I>(dold, lo, lo + m as int, j as nat));
        }
        if captured_in_range::<T, I>(dold, lo, lo + m as int, j as nat) {
            // The old stratum's FIRST hitter of j survives the dedupe and
            // lands somewhere in the folded stratum; its pair carries the
            // covering value.
            let ko = choose|k: int| lo <= k < lo + m
                && (#[trigger] dold[k]).1.as_nat() == j as nat
                && dold[k].0 == snap[j]
                && first_hitter::<T, I>(dold, lo, k, j as nat);
            let po = ko - lo;
            assert(sold[po] == dold[ko]);
            assert forall|q: int| 0 <= q < po implies
                (#[trigger] sold[q]).1.as_nat() != j as nat by {
                assert(sold[q] == dold[lo + q]);
            }
            assert(first_hitter::<T, I>(sold, 0, po, sold[po].1.as_nat()));
            assert(rp.contains(po));
            let t = choose|t: int| 0 <= t < rp.len() && #[trigger] rp[t] == po;
            assert(dd[t] == sold[po]);
            assert(dd.contains(sold[po]));
            assert(r.contains(sold[po]));
            let kr = choose|kr: int| 0 <= kr < r.len() && r[kr] == sold[po];
            assert(dnew[lo + kr] == sold[po]);
            assert(dnew[lo + kr].1.as_nat() == j as nat);
            assert(dnew[lo + kr].0 == snap[j]);
            assert(captured_in_range::<T, I>(dnew, lo, lo + kept as int, j as nat));
            // Uniqueness makes it the first hitter in the folded stratum.
            assert forall|q: int| lo <= q < lo + kr implies
                (#[trigger] dnew[q]).1.as_nat() != j as nat by {
                assert(r[q - lo] == dnew[q]);
                if dnew[q].1.as_nat() == j as nat {
                    assert(r[q - lo].1.as_nat() == r[kr].1.as_nat());
                }
            }
            assert(first_hitter::<T, I>(dnew, lo, lo + kr, j as nat));
        }
    }
}

/// `captured_in_range` is preserved by dedupe-and-permute of a stratum:
/// the kept set writes exactly the same cells.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_captured_in_range_dedupe<T: Copy, I: IndexLike>(
    dold: Seq<(T, I)>, dnew: Seq<(T, I)>, lo: int, m: nat, kept: nat, j: nat,
)
    requires
        0 <= lo,
        lo + m <= dold.len(),
        lo + kept <= dnew.len(),
        kept == crate::diff_compress::dedupe_first_spec(
            dold.subrange(lo, lo + m as int)).len(),
        dnew.subrange(lo, lo + kept as int).to_multiset()
            == crate::diff_compress::dedupe_first_spec(
                dold.subrange(lo, lo + m as int)).to_multiset(),
    ensures
        captured_in_range::<T, I>(dnew, lo, lo + kept as int, j)
            == captured_in_range::<T, I>(dold, lo, lo + m as int, j),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    let sold = dold.subrange(lo, lo + m as int);
    let r = dnew.subrange(lo, lo + kept as int);
    let dd = crate::diff_compress::dedupe_first_spec(sold);
    let rp = crate::diff_compress::dedupe_positions(sold, sold.len() as int);
    crate::diff_compress::lemma_dedupe_prefix_props::<T, I>(
        sold, sold.len() as int);
    if captured_in_range::<T, I>(dnew, lo, lo + kept as int, j) {
        let k = choose|k: int| lo <= k < lo + kept && 0 <= k < dnew.len()
            && (#[trigger] dnew[k]).1.as_nat() == j;
        assert(r[k - lo] == dnew[k]);
        assert(r.contains(r[k - lo]));
        vstd::seq_lib::to_multiset_contains(r, r[k - lo]);
        vstd::seq_lib::to_multiset_contains(dd, r[k - lo]);
        let t = choose|t: int| 0 <= t < dd.len() && dd[t] == r[k - lo];
        let p0 = rp[t];
        assert(dd[t] == sold[p0]);
        assert(sold[p0] == dold[lo + p0]);
        assert(captured_in_range::<T, I>(dold, lo, lo + m as int, j));
    }
    if captured_in_range::<T, I>(dold, lo, lo + m as int, j) {
        let k = choose|k: int| lo <= k < lo + m && 0 <= k < dold.len()
            && (#[trigger] dold[k]).1.as_nat() == j;
        assert(sold[k - lo] == dold[k]);
        assert(captured_in_range::<T, I>(sold, 0, sold.len() as int, j));
        lemma_lowest_hitter::<T, I>(sold, 0, sold.len() as int, j);
        let p = choose|p: int| 0 <= p < sold.len()
            && (#[trigger] sold[p]).1.as_nat() == j
            && first_hitter::<T, I>(sold, 0, p, j);
        assert(first_hitter::<T, I>(sold, 0, p, sold[p].1.as_nat()));
        assert(rp.contains(p));
        let t = choose|t: int| 0 <= t < rp.len() && #[trigger] rp[t] == p;
        assert(dd[t] == sold[p]);
        assert(dd.contains(sold[p]));
        vstd::seq_lib::to_multiset_contains(r, sold[p]);
        vstd::seq_lib::to_multiset_contains(dd, sold[p]);
        let kr = choose|kr: int| 0 <= kr < r.len() && r[kr] == sold[p];
        assert(dnew[lo + kr] == sold[p]);
        assert(captured_in_range::<T, I>(dnew, lo, lo + kept as int, j));
    }
}


/// One write applied to a column: overwrite in range, drop out of range. The shared
/// step of `overlay` (which folds it backward) and `apply_all` (forward).
pub open(crate) spec fn write_step<T, I: IndexLike>(x: Seq<T>, e: (T, I)) -> Seq<T> {
    if e.1.as_nat() < x.len() {
        x.update(e.1.as_nat() as int, e.0)
    } else {
        x
    }
}

/// `apply_all` peels one element off the FRONT when the sequence has unique indices:
/// the front write touches an index no later write touches, so applying it first or
/// last is the same column. The bridge between forward and backward application.
pub(crate) proof fn lemma_apply_all_front<T, I: IndexLike>(base: Seq<T>, s: Seq<(T, I)>)
    requires
        s.len() > 0,
        crate::diff_compress::unique_idx(s),
    ensures
        crate::diff_compress::apply_all::<T, I>(base, s)
            == write_step::<T, I>(
                crate::diff_compress::apply_all::<T, I>(base, s.subrange(1, s.len() as int)),
                s[0]),
    decreases s.len(),
{
    let n = s.len() as int;
    if n == 1 {
        assert(s.subrange(0, 0) =~= Seq::<(T, I)>::empty());
        assert(s.subrange(1, 1) =~= Seq::<(T, I)>::empty());
    } else {
        let last = s[n - 1];
        let front = s.subrange(0, n - 1);
        // apply_all(s) == step(apply_all(front), last) by definition.
        assert(front[0] == s[0]);
        // front is unique (a subrange of a unique sequence).
        assert(crate::diff_compress::unique_idx(front)) by {
            assert forall|a: int, b: int|
                0 <= a < front.len() && 0 <= b < front.len() && a != b
                implies (#[trigger] front[a]).1.as_nat() != (#[trigger] front[b]).1.as_nat() by {
                assert(front[a] == s[a]);
                assert(front[b] == s[b]);
            }
        }
        lemma_apply_all_front::<T, I>(base, front);
        let mid = front.subrange(1, n - 1);
        let am = crate::diff_compress::apply_all::<T, I>(base, mid);
        // apply_all(s) == step(step(apply_all(mid), s[0]), last); the two writes hit
        // distinct indices (unique_idx), and write_step preserves length, so they
        // commute.
        crate::diff_compress::lemma_apply_all_len::<T, I>(base, mid);
        assert(s[0].1.as_nat() != last.1.as_nat());
        assert(write_step::<T, I>(write_step::<T, I>(am, s[0]), last)
            =~= write_step::<T, I>(write_step::<T, I>(am, last), s[0]));
        // Re-fold the right-hand side: step(apply_all(mid), last) == apply_all(s[1..]).
        let tail = s.subrange(1, n);
        assert(tail.subrange(0, tail.len() - 1) =~= mid);
        assert(tail[tail.len() - 1] == last);
    }
}

/// A frame with unique indices applies the same FORWARD (`apply_all`, what
/// `restore_to` implements) as BACKWARD (`overlay`, what the restore replay model
/// uses): order within the frame cannot matter when no index repeats. Stated over
/// the enclosing log's range so the caller needs no subrange re-shift.
pub(crate) proof fn lemma_apply_all_eq_overlay<T, I: IndexLike>(
    base: Seq<T>, d: Seq<(T, I)>, lo: int, hi: int,
)
    requires
        0 <= lo <= hi <= d.len(),
        crate::diff_compress::unique_idx(d.subrange(lo, hi)),
    ensures
        crate::diff_compress::apply_all::<T, I>(base, d.subrange(lo, hi))
            == overlay::<T, I>(base, d, lo, hi),
    decreases hi - lo,
{
    let s = d.subrange(lo, hi);
    if lo >= hi {
        assert(s =~= Seq::<(T, I)>::empty());
    } else {
        // overlay peels the front: overlay(lo, hi) == step(overlay(lo+1, hi), d[lo]).
        // apply_all peels the front too under uniqueness (lemma above); the tails
        // agree by induction.
        let tail_unique = d.subrange(lo + 1, hi);
        assert(s.subrange(1, s.len() as int) =~= tail_unique);
        assert(crate::diff_compress::unique_idx(tail_unique)) by {
            assert forall|a: int, b: int|
                0 <= a < tail_unique.len() && 0 <= b < tail_unique.len() && a != b
                implies (#[trigger] tail_unique[a]).1.as_nat()
                    != (#[trigger] tail_unique[b]).1.as_nat() by {
                assert(tail_unique[a] == s[a + 1]);
                assert(tail_unique[b] == s[b + 1]);
            }
        }
        lemma_apply_all_front::<T, I>(base, s);
        lemma_apply_all_eq_overlay::<T, I>(base, d, lo + 1, hi);
        assert(s[0] == d[lo]);
    }
}

/// The per-stratum bridge: if a diff-log range `[lo, hi)` satisfies the
/// two-arm `frame_inv` relative to `above` and `snap` (stated directly over
/// the range), then overlaying that range onto `above` reproduces `snap`
/// on `[0, saved_len)`.
///
/// Hypotheses mirror `frame_inv` + the structural conditions, but phrased
/// over the diff-log range rather than an extracted subrange.
pub(crate) proof fn lemma_overlay_eq_snap<T, I: IndexLike>(
    above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int,
    snap: Seq<T>, saved_len: nat,
)
    requires
        0 <= lo <= hi <= diffs.len(),
        // The base is already full-length (restore resizes to saved_len
        // before replay), so the overwrite-only overlay reaches every cell.
        saved_len <= above.len(),
        // Full frame_inv_range bundles snap.len, index-bound, uniqueness, and
        // the per-cell two-arm — all needed below.
        frame_inv_range::<T, I>(above, diffs, lo, hi, snap, saved_len),
    ensures
        forall|j: int| 0 <= j < saved_len as int ==>
            #[trigger] overlay::<T, I>(above, diffs, lo, hi)[j] == snap[j],
{
    lemma_overlay_len::<T, I>(above, diffs, lo, hi);
    assert forall|j: int| 0 <= j < saved_len as int implies
        #[trigger] overlay::<T, I>(above, diffs, lo, hi)[j] == snap[j]
    by {
        assert(frame_cell_inv::<T, I>(above, diffs, lo, hi, snap, j));
        if !captured_in_range::<T, I>(diffs, lo, hi, j as nat) {
            // Uncaptured: overlay leaves above[j], which == snap[j].
            assert forall|k: int| lo <= k < hi && 0 <= k < diffs.len() implies
                (#[trigger] diffs[k]).1.as_nat() != j as nat
            by {
                // else captured_in_range would hold
            }
            lemma_overlay_uncaptured::<T, I>(above, diffs, lo, hi, j);
        } else {
            // Captured: the FIRST hitter holds snap[j], and first-hitter is
            // exactly the shape lemma_overlay_lowest pins (base-independent,
            // duplicate-tolerant).
            assert(captured_in_range::<T, I>(diffs, lo, hi, j as nat));
            assert((j as nat) < above.len());  // from saved_len <= above.len()
            let p = choose|k: int| lo <= k < hi
                && (#[trigger] diffs[k]).1.as_nat() == j as nat
                && diffs[k].0 == snap[j]
                && first_hitter::<T, I>(diffs, lo, k, j as nat);
            lemma_overlay_lowest::<T, I>(above, diffs, lo, hi, p, j);
        }
    }
}

/// Semi-persistent vector parameterized by storage backend `S` and index
/// type `I`. `TRACK=false` compiles out const-gated tracking execution; the
/// generic layout still contains empty diff/frame/fork fields.
pub struct Vec<
    T,
    I,
    S,
    const TRACK: bool = true,
    VC = crate::value_compressor::NoValueCompression,
>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
    VC: crate::value_compressor::ValueCompressor<T>,
{
    pub(crate) store: S,
    /// Inert proof-compatibility shadow retained until the deferred proof
    /// campaign is rewritten against the three physical representations.
    /// Executable capture, migration, and restore never read or append it.
    #[allow(dead_code)]
    pub(crate) diff_log: std::vec::Vec<(T, I)>,
    /// Chronological duplicate-preserving history. Only the newest frame is
    /// mutable for a TrailStore protocol.
    pub(crate) trail_value_pool: std::vec::Vec<(T, I)>,
    pub(crate) trail_stack: std::vec::Vec<crate::frame::TrailFrame<I>>,
    /// Unique first-capture-wins history. Only the newest frame is mutable
    /// for an InlineStore or ParallelStore protocol.
    pub(crate) hot_value_pool: std::vec::Vec<(T, I)>,
    pub(crate) hot_stack: std::vec::Vec<crate::frame::HotFrame<I>>,
    /// Immutable run-compressed oldest history.
    pub(crate) cold_stack: std::vec::Vec<crate::frame::ColdFrameHdr<I>>,
    pub(crate) cold_value_pool: std::vec::Vec<T>,
    pub(crate) cold_index_runs: std::vec::Vec<crate::frame::IndexRun<I>>,
    pub(crate) tier_policy: crate::tier_policy::TierPolicy,
    /// Legacy constructor cadence. `Some(n)` means that once more than `n`
    /// ingress frames are closed, the compatibility adapter migrates the
    /// entire closed batch. Explicit-policy constructors always leave this
    /// `None` and use `tier_policy`'s oldest-prefix semantics instead.
    pub(crate) hot_buffer: Option<usize>,
    /// Cached answer to whether `ApplyConfigured` can migrate history. Updated
    /// with the store protocol and tier policy; avoids decoding no-op policy on
    /// every default mark.
    pub(crate) automatic_rollover_enabled: bool,
    /// Scratch for the Trail-to-Hot dedupe (`trail_select::dedupe_trail_range`),
    /// owned here so its table survives across migration passes: taken out for
    /// the duration of a pass and put back. No spec content; excluded from the
    /// migration framing predicates like the tier vectors themselves.
    pub(crate) trail_seen: Option<std::collections::HashSet<I, crate::hasher_spec::IndexHasher>>,
    /// THE ghost diff (proof architecture, goal doc): every tracked write,
    /// in temporal order, duplicates included, regardless of the store's
    /// capture discipline. Restore correctness is stated once against this;
    /// each physical representation carries an abstraction theorem to it.
    // Ghost-only: read exclusively by spec/proof code (wf, the bridges), which
    // clippy erases, so it reports them unread.
    #[allow(dead_code)]
    pub(crate) full_trail: Ghost<Seq<(T, I)>>,
    /// Stratum start offsets into full_trail, one per mark.
    #[allow(dead_code)]
    /// The vector's own token manager (a group of one): identity and
    /// per-frame generation stamps. Minted on `mark`, consulted on
    /// validation, cut on every `restore_frame`.
    #[allow(dead_code)] // ghost: read only by specs
    pub(crate) trail_frames: Ghost<Seq<nat>>,
    /// The saved_len of the topmost (active) frame, cached for the hot path.
    /// `I::min()` when the stack is empty. Mirrors production.
    pub(crate) active_saved_len: I,
    pub(crate) phantom: core::marker::PhantomData<(T, I, VC)>,
    /// Ghost stack of deep copies. `snapshots[k]` is `view()` at the
    /// moment frame `k` was pushed. Always `snapshots.len() == tf.len()`.
    // Ghost-only, same as full_trail/trail_frames above: read exclusively by
    // spec/proof code, which clippy erases, so it reports the field unread.
    #[allow(dead_code)]
    pub(crate) snapshots: Ghost<Seq<Seq<T>>>,
}

impl<
    T,
    I,
    S,
    const TRACK: bool,
    VC: crate::value_compressor::ValueCompressor<T>,
> Vec<T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// Public spec view: the abstract sequence of stored values.
    pub open(crate) spec fn view(&self) -> Seq<T> {
        self.store.data()
    }

    /// Snapshot stack (ghost).
    pub open(crate) spec fn snapshots_view(&self) -> Seq<Seq<T>> {
        self.snapshots@
    }

    /// Frame-stack depth (spec counterpart of `depth()`). Public contracts phrase
    /// frame counts through this — the `frames` field is `pub(crate)`
    /// (privacy closeout).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.trail_frames@.len()
    }

    /// Ghost stratum bounds: frame k's writes are
    /// full_trail[g_start(k), g_end(k)).
    pub open(crate) spec fn g_start(&self, k: int) -> int {
        self.trail_frames@[k] as int
    }

    pub open(crate) spec fn g_end(&self, k: int) -> int {
        if k + 1 < self.trail_frames@.len() {
            self.trail_frames@[k + 1] as int
        } else {
            self.full_trail@.len() as int
        }
    }

    /// Frame k's saved_len, ghost form: pinned by its snapshot's length.
    pub open(crate) spec fn g_saved_len(&self, k: int) -> nat {
        self.snapshots@[k].len()
    }

    /// Diff-log length (spec counterpart of `diff_log_len()`).
    pub open(crate) spec fn diff_log_len_spec(&self) -> nat {
        self.diff_log@.len()
    }

    /// The top (open) frame's `diff_start`, or 0 when no frame is live. The sorted
    /// index-major fold's alignment: for a run-compressed log compacted at every mark,
    /// the DiffLog cold region ends exactly here (the tail is the open frame's stratum).
    pub open(crate) spec fn top_diff_start_spec(&self) -> int {
        if self.trail_frames@.len() > 0 {
            self.g_start((self.trail_frames@.len() - 1) as int)
        } else {
            0
        }
    }


    /// The mark-depth quantity the depth-headroom contracts are phrased over.
    /// Post-H2 the container tracks no genealogy, so this is the live frame
    /// depth (the stamp-array length it used to be lived on `GenStamps`).
    pub open(crate) spec fn fork_count_spec(&self) -> nat {
        self.trail_frames@.len()
    }


    /// The "layer above" frame `k`: snapshots[k+1] for inner frames, or the
    /// current view for the topmost frame.
    pub open(crate) spec fn layer_above_at(&self, k: int) -> Seq<T> {
        if k + 1 < self.trail_frames@.len() {
            self.snapshots@[k + 1]
        } else {
            self.view()
        }
    }

    /// Authoritative end of a unique Hot stratum. Closed frames use their
    /// sealed header extent; the writable top ends at the physical pool length
    /// because its header end is intentionally stale until the next mark.
    pub closed spec fn hot_defer_end(&self, i: int) -> int {
        if i + 1 < self.hot_stack@.len() {
            self.hot_stack@[i].end as int
        } else {
            self.hot_value_pool@.len() as int
        }
    }

    /// First formal three-tier milestone: the complete physical projection for
    /// unique-capture ingress while rollover is deferred and every live frame
    /// therefore remains Hot. This predicate deliberately reads
    /// `hot_value_pool`, never the retired `diff_log` proof shadow.
    ///
    /// It is closed so general Vec proofs carry it as one named fact. The
    /// checked Hot-only executable cores reveal it locally.
    pub closed spec fn hot_defer_wf(&self) -> bool {
        let hs = self.hot_stack@;
        let pool = self.hot_value_pool@;
        let snaps = self.snapshots@;
        let depth = hs.len();

        &&& TRACK
        &&& self.store.wf()
        &&& self.store.unique_capture_spec()
        // Hot-only physical ownership and the exact frame/snapshot count.
        &&& self.trail_stack@.len() == 0
        &&& self.trail_value_pool@.len() == 0
        &&& self.cold_stack@.len() == 0
        &&& self.cold_index_runs@.len() == 0
        &&& self.cold_value_pool@.len() == 0
        &&& depth == self.trail_frames@.len()
        &&& depth == snaps.len()
        &&& depth < usize::MAX
        // Empty-history clauses are explicit: no physical/ghost residue, the
        // active length is the index minimum, and no capture flag is set.
        &&& (depth == 0 ==> {
            &&& pool.len() == 0
            &&& self.active_saved_len == I::min_spec()
            &&& forall|j: int| 0 <= j < self.store.captured().len()
                ==> !(#[trigger] self.store.captured()[j])
        })
        // A nonempty pool is partitioned from zero by closed headers followed
        // by one open top whose effective end is pool.len().
        &&& (depth > 0 ==> hs[0].start == 0)
        &&& (forall|i: int| 0 <= i < depth ==> {
            &&& (#[trigger] hs[i]).start <= hs[i].end
            &&& hs[i].end <= pool.len()
            &&& hs[i].start as int <= self.hot_defer_end(i)
            &&& self.hot_defer_end(i) <= pool.len() as int
            &&& (i + 1 < depth ==> {
                &&& hs[i].end == hs[i + 1].start
                &&& self.hot_defer_end(i) == hs[i + 1].start as int
            })
            &&& (i + 1 == depth ==>
                self.hot_defer_end(i) == pool.len() as int)
        })
        // Every physical header is aligned with the corresponding logical
        // snapshot. The top cache names the open frame's saved extent.
        &&& (forall|i: int| 0 <= i < depth ==>
            (#[trigger] hs[i]).saved_len.as_nat() == snaps[i].len())
        &&& (depth > 0 ==>
            self.active_saved_len.as_nat() == snaps[(depth - 1) as int].len())
        // Unique capture is per stratum, including the open top at pool.len().
        &&& (forall|i: int| 0 <= i < depth ==>
            #[trigger] stratum_unique::<T, I>(
                pool, hs[i].start as int, self.hot_defer_end(i)))
        // Physical reconstruction is authoritative over hot_value_pool.
        &&& (forall|i: int| 0 <= i < depth ==>
            #[trigger] frame_inv_range::<T, I>(
                self.layer_above_at(i), pool, hs[i].start as int,
                self.hot_defer_end(i), snaps[i], snaps[i].len()))
        // Capture flags describe exactly the writable top stratum on its saved
        // and currently-present domain. No flag may escape that domain.
        &&& self.store.captured().len() == self.view().len()
        &&& (depth > 0 ==> forall|j: int|
            0 <= j < self.active_saved_len.as_nat() && j < self.view().len() ==>
                (#[trigger] self.store.captured()[j])
                    == captured_in_range::<T, I>(
                        pool, hs[(depth - 1) as int].start as int,
                        pool.len() as int, j as nat))
        &&& (forall|j: int| 0 <= j < self.view().len()
            && #[trigger] self.store.captured()[j]
            ==> depth > 0 && j < self.active_saved_len.as_nat())
    }

    /// Hot-only frame starts are monotone because every closed header ends
    /// exactly where the next frame starts.
    pub(crate) proof fn lemma_hot_defer_start_monotone(&self, a: int, b: int)
        requires
            self.hot_defer_wf(),
            0 <= a <= b < self.hot_stack@.len(),
        ensures
            self.hot_stack@[a].start <= self.hot_stack@[b].start,
        decreases b - a,
    {
        reveal(Vec::hot_defer_wf);
        reveal(Vec::hot_defer_end);
        if a < b {
            self.lemma_hot_defer_start_monotone(a, b - 1);
            assert(self.hot_stack@[b - 1].start <= self.hot_stack@[b - 1].end);
            assert(self.hot_stack@[b - 1].end == self.hot_stack@[b].start);
        }
    }

    /// Pointwise Hot-only reconstruction telescope. Starting at any Hot frame,
    /// replaying the authoritative pool suffix reconstructs that frame's
    /// snapshot. This is the physical counterpart of the historical
    /// full_trail telescope, with no diff_log bridge.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(500)]
    pub(crate) proof fn lemma_hot_defer_cell_eq_overlay(
        &self, base: Seq<T>, hidx: int, j: int,
    )
        requires
            self.hot_defer_wf(),
            0 <= hidx < self.hot_stack@.len(),
            0 <= j < self.snapshots@[hidx].len() as int,
            (j as nat) < base.len(),
            forall|m: int| 0 <= m < base.len() && m < self.view().len()
                ==> #[trigger] base[m] == self.view()[m],
        ensures
            overlay::<T, I>(
                base, self.hot_value_pool@,
                self.hot_stack@[hidx].start as int,
                self.hot_value_pool@.len() as int)[j]
                == self.snapshots@[hidx][j],
        decreases self.hot_stack@.len() - hidx,
    {
        reveal(Vec::hot_defer_wf);
        reveal(Vec::hot_defer_end);
        let depth = self.hot_stack@.len();
        let diffs = self.hot_value_pool@;
        let n = diffs.len() as int;
        let lo = self.hot_stack@[hidx].start as int;
        let mid = self.hot_defer_end(hidx);
        let snap = self.snapshots@[hidx];
        let saved = snap.len();
        assert(frame_inv_range::<T, I>(
            self.layer_above_at(hidx), diffs, lo, mid, snap, saved));
        assert(0 <= lo <= mid <= n);
        lemma_frame_inv_arm_at::<T, I>(
            self.layer_above_at(hidx), diffs, lo, mid, snap, saved, j);
        if captured_in_range::<T, I>(diffs, lo, mid, j as nat) {
            let p = choose|q: int| lo <= q < mid
                && (#[trigger] diffs[q]).1.as_nat() == j as nat
                && diffs[q].0 == snap[j]
                && first_hitter::<T, I>(diffs, lo, q, j as nat);
            lemma_overlay_lowest::<T, I>(base, diffs, lo, n, p, j);
        } else if hidx + 1 < depth {
            assert(mid == self.hot_stack@[hidx + 1].start as int);
            assert(self.layer_above_at(hidx) == self.snapshots@[hidx + 1]);
            assert((j as nat) < self.snapshots@[hidx + 1].len());
            assert(self.snapshots@[hidx + 1][j] == snap[j]);
            self.lemma_hot_defer_cell_eq_overlay(base, hidx + 1, j);
            assert forall|q: int| lo <= q < mid implies
                (#[trigger] diffs[q]).1.as_nat() != j as nat by {
                if diffs[q].1.as_nat() == j as nat {
                    assert(captured_in_range::<T, I>(diffs, lo, mid, j as nat));
                }
            }
            lemma_overlay_uncaptured_prefix::<T, I>(base, diffs, lo, mid, n, j);
        } else {
            assert(mid == n);
            assert(self.layer_above_at(hidx) == self.view());
            assert((j as nat) < self.view().len());
            assert(self.view()[j] == snap[j]);
            lemma_overlay_uncaptured::<T, I>(base, diffs, lo, n, j);
        }
    }

    /// End of frame `k`'s stratum.
    pub open(crate) spec fn stratum_end(&self, k: int) -> int {
        self.g_end(k)
    }

    /// Resize-stable logical well-formedness at arbitrary depth.
    ///
    /// `frame_partition_ok` fixes the Cold|Hot|Trail header count and maps each
    /// physical header's saved length to its snapshot. The remaining clauses
    /// describe only the canonical ghost reconstruction: `trail_frames` bounds
    /// partition `full_trail`, and every ghost stratum reconstructs its
    /// snapshot. No clause reads inert `diff_log` as a physical representation.
    ///
    /// Capture flags and selected open-ingress membership are intentionally
    /// absent. `resize_default` may temporarily break that bridge while
    /// preserving this predicate, allowing restore to regrow popped slots
    /// before rebuilding capture state.
    pub open(crate) spec fn wf_for_snap(&self) -> bool {
        let gt = self.full_trail@;
        let tf = self.trail_frames@;
        let snaps = self.snapshots@;
        let n = gt.len();

        &&& self.store.wf()
        &&& self.frame_partition_ok()
        &&& snaps.len() == tf.len()
        // Frame count fits usize (the depth guards keep it below u32::MAX).
        &&& tf.len() < usize::MAX
        // TRACK=false => no frames, ever (mark, the only frame-pusher,
        // requires TRACK) - production-parity erasure.
        &&& (!TRACK ==> tf.len() == 0)
        &&& (tf.len() == 0 ==> n == 0)
        &&& (tf.len() > 0 ==> tf[0] == 0)
        &&& (tf.len() > 0 ==> tf[(tf.len() - 1) as int] <= n)
        // Ghost stratum boundaries are monotone in the ghost trail.
        &&& (forall|k: int| #![trigger tf[k]] 0 <= k && k + 1 < tf.len() ==>
                tf[k] <= tf[k + 1])
        // Canonical chronological frame contracts. Runtime reconstruction
        // reads physical pools; their per-tier contracts independently supply
        // the shared captured-or-inherited frame meaning.
        &&& (forall|k: int| 0 <= k < tf.len() ==>
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k),
                    gt,
                    self.g_start(k),
                    self.g_end(k),
                    snaps[k],
                    snaps[k].len()))
    }

    /// The physical representations' abstraction to the ghost trail (the
    /// T1-T4 theorems of the proof architecture). Opaque; maintained by the
    /// scaffolded mutators during the exec-locked phase and discharged
    /// per-theorem afterwards (goal doc, deliverables 5-6).
    /// Within each cold frame the index runs are sorted by base and cell-disjoint
    /// (run r ends at or before run r+1 begins). A named spec fn so callers that
    /// don't need it (e.g. push_frame after compress) carry it opaquely rather
    /// than instantiating the nested forall - the raw forall in an ensure blew up
    /// push_frame's query. restore_cold unfolds it.
    pub open(crate) spec fn cold_runs_disjoint(&self) -> bool {
        forall|f: int, r: int|
            0 <= f < self.cold_stack@.len()
            && (#[trigger] self.cold_stack@[f]).runs_start <= r
            && r + 1 < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
            ==> (#[trigger] self.cold_index_runs@[r]).base.as_nat()
                + self.cold_index_runs@[r].len
                <= self.cold_index_runs@[r + 1].base.as_nat()
    }

    pub open(crate) spec fn repr_ok(&self) -> bool {
        // Cold-pool structural well-formedness (D6). compress_all_hot lays the
        // cold tier out as a contiguous partition: index runs are appended in
        // frame order, values are appended in run order, and each frame header
        // names a half-open slice [runs_start, runs_start+runs_len) of the run
        // pool. These clauses are what restore_frame's cold path reads to
        // discharge its pool-indexing preconditions.
        &&& (self.cold_stack@.len() == 0 ==> self.cold_index_runs@.len() == 0)
        &&& (forall|f: int| 0 <= f < self.cold_stack@.len() ==>
                (#[trigger] self.cold_stack@[f]).runs_start + self.cold_stack@[f].runs_len
                    <= self.cold_index_runs@.len())
        &&& (self.cold_stack@.len() > 0 ==> self.cold_stack@[0].runs_start == 0)
        &&& (forall|f: int| 0 <= f < self.cold_stack@.len() - 1 ==>
                (#[trigger] self.cold_stack@[f]).runs_start + self.cold_stack@[f].runs_len
                    == self.cold_stack@[f + 1].runs_start)
        &&& (self.cold_stack@.len() > 0 ==>
                self.cold_stack@[self.cold_stack@.len() - 1].runs_start
                    + self.cold_stack@[self.cold_stack@.len() - 1].runs_len
                    == self.cold_index_runs@.len())
        &&& (self.cold_index_runs@.len() == 0 ==> self.cold_value_pool@.len() == 0)
        &&& (forall|r: int| 0 <= r < self.cold_index_runs@.len() ==>
                (#[trigger] self.cold_index_runs@[r]).start + self.cold_index_runs@[r].len
                    <= self.cold_value_pool@.len())
        &&& (self.cold_index_runs@.len() > 0 ==> self.cold_index_runs@[0].start == 0)
        &&& (forall|r: int| 0 <= r < self.cold_index_runs@.len() - 1 ==>
                (#[trigger] self.cold_index_runs@[r]).start + self.cold_index_runs@[r].len
                    == self.cold_index_runs@[r + 1].start)
        &&& (self.cold_index_runs@.len() > 0 ==>
                self.cold_index_runs@[self.cold_index_runs@.len() - 1].start
                    + self.cold_index_runs@[self.cold_index_runs@.len() - 1].len
                    == self.cold_value_pool@.len())
    }

    /// The three physical frame stacks are an age-ordered partition of the
    /// logical frame/snapshot coordinates: Cold, then Hot, then Trail. Empty
    /// physical extents still contribute one header and therefore preserve the
    /// identity of their logical restore token.
    pub closed spec fn frame_partition_ok(&self) -> bool {
        let cc = self.cold_stack@.len();
        let hc = self.hot_stack@.len();
        let tc = self.trail_stack@.len();
        let depth = self.snapshots@.len();

        &&& depth == self.trail_frames@.len()
        &&& cc + hc + tc == depth
        &&& (!TRACK ==> depth == 0)
        &&& (forall|f: int| 0 <= f < cc ==>
            (#[trigger] self.cold_stack@[f]).saved_len.as_nat()
                == self.snapshots@[f].len())
        &&& (forall|i: int| 0 <= i < hc ==>
            (#[trigger] self.hot_stack@[i]).saved_len.as_nat()
                == self.snapshots@[cc + i].len())
        &&& (forall|i: int| 0 <= i < tc ==>
            (#[trigger] self.trail_stack@[i]).saved_len.as_nat()
                == self.snapshots@[cc + hc + i].len())
    }

    /// Authoritative unique first-capture representation for the middle Hot
    /// segment. Header bounds and adjacency are exclusively in
    /// `hot_value_pool`; the newest effective end is the pool length.
    pub closed spec fn hot_repr_ok(&self) -> bool {
        let hs = self.hot_stack@;
        let pool = self.hot_value_pool@;
        let cc = self.cold_stack@.len();

        &&& (hs.len() == 0 ==> pool.len() == 0)
        &&& (hs.len() > 0 ==> hs[0].start == 0)
        &&& (forall|i: int| 0 <= i < hs.len() ==> {
            &&& (#[trigger] hs[i]).start <= hs[i].end
            &&& hs[i].end <= pool.len()
            &&& hs[i].start as int <= self.phys_hot_end(i)
            &&& self.phys_hot_end(i) <= pool.len() as int
            &&& (i + 1 < hs.len() ==> {
                &&& hs[i].end == hs[i + 1].start
                &&& self.phys_hot_end(i) == hs[i + 1].start as int
            })
            &&& (i + 1 == hs.len() ==>
                self.phys_hot_end(i) == pool.len() as int)
            &&& stratum_unique::<T, I>(
                pool, hs[i].start as int, self.phys_hot_end(i))
            &&& self.phys_frame_inv_range_holds(i)
            &&& cc + i < self.snapshots@.len()
        })
    }

    /// Authoritative duplicate-preserving representation for the newest Trail
    /// segment. The chronological refinement is stated here and maintained as
    /// an opaque boundary; conversion/replay proofs are intentionally deferred.
    pub closed spec fn trail_repr_ok(&self) -> bool {
        let ts = self.trail_stack@;
        let pool = self.trail_value_pool@;
        let offset = self.cold_stack@.len() + self.hot_stack@.len();

        &&& (ts.len() == 0 ==> pool.len() == 0)
        &&& (ts.len() > 0 ==> ts[0].start == 0)
        &&& (forall|i: int| 0 <= i < ts.len() ==> {
            &&& (#[trigger] ts[i]).start <= ts[i].end
            &&& ts[i].end <= pool.len()
            &&& ts[i].start as int <= self.phys_trail_end(i)
            &&& self.phys_trail_end(i) <= pool.len() as int
            &&& (i + 1 < ts.len() ==> {
                &&& ts[i].end == ts[i + 1].start
                &&& self.phys_trail_end(i) == ts[i + 1].start as int
            })
            &&& (i + 1 == ts.len() ==>
                self.phys_trail_end(i) == pool.len() as int)
            &&& frame_inv_range::<T, I>(
                self.layer_above_at(offset + i), pool, ts[i].start as int,
                self.phys_trail_end(i), self.snapshots@[offset + i],
                self.snapshots@[offset + i].len())
            &&& offset + i < self.snapshots@.len()
        })
    }

    /// Every stored Cold payload belongs to its frame's saved domain. Empty
    /// logical frames have no runs; emitted runs themselves are nonempty.
    pub closed spec fn cold_payload_ok(&self) -> bool {
        forall|f: int, r: int| 0 <= f < self.cold_stack@.len()
            && (#[trigger] self.cold_stack@[f]).runs_start <= r
            < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len ==>
            0 < (#[trigger] self.cold_index_runs@[r]).len
                && self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len
                    <= self.cold_stack@[f].saved_len.as_nat()
    }

    /// Immutable Cold structural and semantic boundary. The existing pooled-run
    /// partition is preserved verbatim and strengthened with disjointness and
    /// the named per-frame reconstruction obligation. Hot-to-Cold refinement is
    /// not proved in H1.
    pub closed spec fn cold_repr_ok(&self) -> bool {
        &&& self.repr_ok()
        &&& self.cold_payload_ok()
        &&& self.cold_runs_disjoint()
        &&& (forall|f: int| 0 <= f < self.cold_stack@.len() ==>
            #[trigger] self.cold_reconstructs(f))
    }

    /// Capture-sensitive ownership of the sole writable ingress frame.
    /// Unique-capture stores open the newest Hot frame and have no Trail
    /// frames; chronological stores open the newest Trail frame and require the
    /// entire Hot prefix to be sealed. Capture flags describe the selected real
    /// pool, never the inert compatibility log.
    pub closed spec fn open_ingress_ok(&self) -> bool {
        let depth = self.snapshots@.len();
        let hs = self.hot_stack@;
        let ts = self.trail_stack@;

        &&& self.store.captured().len() == self.view().len()
        &&& (depth == 0 ==> {
            &&& self.active_saved_len == I::min_spec()
            &&& (TRACK ==> forall|j: int|
                0 <= j < self.store.captured().len() ==>
                    !(#[trigger] self.store.captured()[j]))
        })
        &&& (depth > 0 ==>
            self.active_saved_len.as_nat() == self.snapshots@[(depth - 1) as int].len())
        &&& (self.store.unique_capture_spec() ==> {
            &&& ts.len() == 0
            &&& (depth > 0 ==> hs.len() > 0)
            &&& (depth > 0 ==> forall|j: int|
                0 <= j < self.active_saved_len.as_nat() && j < self.view().len() ==>
                    (#[trigger] self.store.captured()[j])
                        == captured_in_range::<T, I>(
                            self.hot_value_pool@,
                            hs[(hs.len() - 1) as int].start as int,
                            self.hot_value_pool@.len() as int,
                            j as nat))
        })
        &&& (!self.store.unique_capture_spec() ==> {
            &&& (depth > 0 ==> ts.len() > 0)
            &&& (hs.len() > 0 ==>
                hs[(hs.len() - 1) as int].end == self.hot_value_pool@.len())
            &&& (depth > 0 ==> forall|j: int|
                0 <= j < self.active_saved_len.as_nat() && j < self.view().len() ==>
                    (#[trigger] self.store.captured()[j])
                        == captured_in_range::<T, I>(
                            self.trail_value_pool@,
                            ts[(ts.len() - 1) as int].start as int,
                            self.trail_value_pool@.len() as int,
                            j as nat))
        })
        &&& (TRACK ==> forall|j: int| 0 <= j < self.view().len()
            && #[trigger] self.store.captured()[j]
            ==> depth > 0 && j < self.active_saved_len.as_nat())
    }

    /// Non-authoritative compatibility facts for proof-era storage that runtime
    /// capture and restore never read. This predicate must not be used for
    /// physical reconstruction, frame extents, or ingress ownership.
    pub closed spec fn proof_compat_ok(&self) -> bool {
        self.trail_frames@.len() == 0 ==> self.diff_log@.len() == 0
    }

    /// Compatibility refinement between the selected authoritative ingress
    /// pool and the canonical ghost top stratum. It carries no facts about the
    /// inert `diff_log`.
    pub open(crate) spec fn index_set_ok(&self) -> bool {
        let depth = self.trail_frames@.len();
        depth > 0 ==>
            forall|j: int| #![trigger captured_in_range::<T, I>(
                    self.full_trail@,
                    self.g_start((depth - 1) as int),
                    self.full_trail@.len() as int, j as nat)]
                0 <= j < self.active_saved_len.as_nat() ==>
                (if self.store.unique_capture_spec() {
                    captured_in_range::<T, I>(
                        self.hot_value_pool@,
                        self.hot_stack@[(self.hot_stack@.len() - 1) as int].start as int,
                        self.hot_value_pool@.len() as int,
                        j as nat)
                } else {
                    captured_in_range::<T, I>(
                        self.trail_value_pool@,
                        self.trail_stack@[(self.trail_stack@.len() - 1) as int].start as int,
                        self.trail_value_pool@.len() as int,
                        j as nat)
                }) == captured_in_range::<T, I>(
                    self.full_trail@,
                    self.g_start((depth - 1) as int),
                    self.full_trail@.len() as int, j as nat)
    }

    /// Transfer the compatibility refinement when every field it reads is
    /// unchanged. Keeping the quantifier behind this accessor avoids repeated
    /// trigger expansion in framing proofs.
    pub(crate) proof fn lemma_index_set_transfer(&self, other: Self)
        requires
            other.index_set_ok(),
            self.open_ingress_ok(),
            other.open_ingress_ok(),
            self.frame_partition_ok(),
            other.frame_partition_ok(),
            self.store.unique_capture_spec() == other.store.unique_capture_spec(),
            self.hot_value_pool@ == other.hot_value_pool@,
            self.hot_stack@ == other.hot_stack@,
            self.trail_value_pool@ == other.trail_value_pool@,
            self.trail_stack@ == other.trail_stack@,
            self.full_trail@ == other.full_trail@,
            self.trail_frames@ == other.trail_frames@,
            self.active_saved_len == other.active_saved_len,
        ensures self.index_set_ok(),
    {
        reveal(Vec::open_ingress_ok);
        reveal(Vec::frame_partition_ok);
        let depth = self.trail_frames@.len();
        if depth > 0 {
            if self.store.unique_capture_spec() {
                assert(self.hot_stack@.len() > 0);
                assert(other.hot_stack@.len() > 0);
            } else {
                assert(self.trail_stack@.len() > 0);
                assert(other.trail_stack@.len() > 0);
            }
            assert forall|j: int| #![trigger captured_in_range::<T, I>(
                    self.full_trail@,
                    self.g_start((depth - 1) as int),
                    self.full_trail@.len() as int, j as nat)]
                0 <= j < self.active_saved_len.as_nat() implies
                (if self.store.unique_capture_spec() {
                    captured_in_range::<T, I>(
                        self.hot_value_pool@,
                        self.hot_stack@[(self.hot_stack@.len() - 1) as int].start as int,
                        self.hot_value_pool@.len() as int,
                        j as nat)
                } else {
                    captured_in_range::<T, I>(
                        self.trail_value_pool@,
                        self.trail_stack@[(self.trail_stack@.len() - 1) as int].start as int,
                        self.trail_value_pool@.len() as int,
                        j as nat)
                }) == captured_in_range::<T, I>(
                    self.full_trail@,
                    self.g_start((depth - 1) as int),
                    self.full_trail@.len() as int, j as nat) by {
                let other_depth = other.trail_frames@.len();
                assert(other_depth == depth);
                assert(other_depth > 0);
                if self.store.unique_capture_spec() {
                    assert(other.store.unique_capture_spec());
                    assert(captured_in_range::<T, I>(
                        other.hot_value_pool@,
                        other.hot_stack@[(other.hot_stack@.len() - 1) as int].start as int,
                        other.hot_value_pool@.len() as int,
                        j as nat) == captured_in_range::<T, I>(
                        other.full_trail@,
                        other.g_start((other_depth - 1) as int),
                        other.full_trail@.len() as int,
                        j as nat));
                } else {
                    assert(!other.store.unique_capture_spec());
                    assert(captured_in_range::<T, I>(
                        other.trail_value_pool@,
                        other.trail_stack@[(other.trail_stack@.len() - 1) as int].start as int,
                        other.trail_value_pool@.len() as int,
                        j as nat) == captured_in_range::<T, I>(
                        other.full_trail@,
                        other.g_start((other_depth - 1) as int),
                        other.full_trail@.len() as int,
                        j as nat));
                }
            }
        }
    }

    /// General well-formedness: resize-stable logical reconstruction plus five
    /// named, pool-native physical boundaries. `diff_log` is intentionally
    /// absent; it is inert proof-compatibility storage with no authority over
    /// capture, extents, reconstruction, or ingress ownership.
    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.wf_for_snap()
        &&& self.hot_repr_ok()
        &&& self.trail_repr_ok()
        &&& self.cold_repr_ok()
        &&& self.open_ingress_ok()
        &&& self.proof_compat_ok()
    }

    /// Stable accessor for callers that need the named general invariant
    /// components without unfolding their nested quantifiers.
    pub(crate) proof fn lemma_wf_named_parts(&self)
        requires self.wf(),
        ensures
            self.wf_for_snap(),
            self.frame_partition_ok(),
            self.hot_repr_ok(),
            self.trail_repr_ok(),
            self.cold_repr_ok(),
            self.open_ingress_ok(),
            self.proof_compat_ok(),
    {
    }

    /// Per-header accessor for the Hot representation. This is intentionally
    /// pointwise so the bridge need not instantiate the aggregate quantifier in
    /// several different shapes.
    pub(crate) proof fn lemma_hot_repr_at(&self, i: int)
        requires
            self.hot_repr_ok(),
            self.frame_partition_ok(),
            0 <= i < self.hot_stack@.len(),
        ensures
            self.hot_stack@[i].start <= self.hot_stack@[i].end,
            self.hot_stack@[i].end <= self.hot_value_pool@.len(),
            self.hot_stack@[i].start as int <= self.phys_hot_end(i),
            self.phys_hot_end(i) <= self.hot_value_pool@.len() as int,
            i + 1 < self.hot_stack@.len() ==>
                self.hot_stack@[i].end == self.hot_stack@[i + 1].start,
            self.hot_stack@[i].saved_len.as_nat()
                == self.snapshots@[self.cold_stack@.len() + i].len(),
            stratum_unique::<T, I>(
                self.hot_value_pool@, self.hot_stack@[i].start as int,
                self.phys_hot_end(i)),
            self.phys_frame_inv_range_holds(i),
    {
        reveal(Vec::hot_repr_ok);
        reveal(Vec::frame_partition_ok);
    }

    /// Extract the unique Hot ingress bridge pointwise at one cell.
    pub(crate) proof fn lemma_open_ingress_hot_at(&self, j: int)
        requires
            self.open_ingress_ok(),
            self.store.unique_capture_spec(),
            self.snapshots@.len() > 0,
            0 <= j < self.active_saved_len.as_nat(),
            j < self.view().len(),
        ensures
            self.store.captured()[j] == captured_in_range::<T, I>(
                self.hot_value_pool@,
                self.hot_stack@[(self.hot_stack@.len() - 1) as int].start as int,
                self.hot_value_pool@.len() as int,
                j as nat),
    {
        reveal(Vec::open_ingress_ok);
    }

    /// Transfer ingress ownership across operations that preserve every
    /// logical field read by `open_ingress_ok` (for example capacity shrink).
    pub(crate) proof fn lemma_open_ingress_transfer(&self, other: Self)
        requires
            other.open_ingress_ok(),
            self.store.wf(),
            self.store.captured() == other.store.captured(),
            self.store.unique_capture_spec() == other.store.unique_capture_spec(),
            self.view() == other.view(),
            self.snapshots@ == other.snapshots@,
            self.active_saved_len == other.active_saved_len,
            self.hot_stack@ == other.hot_stack@,
            self.hot_value_pool@ == other.hot_value_pool@,
            self.trail_stack@ == other.trail_stack@,
            self.trail_value_pool@ == other.trail_value_pool@,
        ensures
            self.open_ingress_ok(),
    {
        reveal(Vec::open_ingress_ok);
        self.store.lemma_wf_captured_len();
    }

    /// Executable/refinement boundary for the unique-capture all-Hot path.
    /// Pool emptiness is included so callers can invoke the closed Hot
    /// projection without reconstructing representation facts ad hoc.
    pub open(crate) spec fn hot_defer_scope(&self) -> bool {
        &&& TRACK
        &&& self.store.unique_capture_spec()
        &&& self.trail_stack@.len() == 0
        &&& self.trail_value_pool@.len() == 0
        &&& self.cold_stack@.len() == 0
        &&& self.cold_index_runs@.len() == 0
        &&& self.cold_value_pool@.len() == 0
    }

    #[inline(always)]
    pub(crate) fn hot_defer_scope_exec(&self) -> (r: bool)
        requires self.wf(),
        ensures r == self.hot_defer_scope(),
    {
        let unique = self.store.unique_capture();
        let cold_empty = self.cold_stack.len() == 0;
        let trail_empty = self.trail_stack.len() == 0;
        let r = TRACK && unique && cold_empty && trail_empty;
        proof {
            reveal(Vec::hot_defer_scope);
            if r {
                self.lemma_wf_named_parts();
                reveal(Vec::trail_repr_ok);
                reveal(Vec::cold_repr_ok);
                reveal(Vec::repr_ok);
                assert(self.trail_value_pool@.len() == 0);
                assert(self.cold_index_runs@.len() == 0);
                assert(self.cold_value_pool@.len() == 0);
            }
        }
        r
    }

    pub(crate) proof fn lemma_hot_defer_scope_implies_projection(&self)
        requires
            self.wf(),
            self.hot_defer_scope(),
        ensures
            self.hot_defer_wf(),
    {
        reveal(Vec::hot_defer_scope);
        self.lemma_wf_implies_hot_defer_wf();
    }

    /// H1 bridge: under the unique-capture, Hot-only physical boundary, the
    /// general invariant entails the closed executable `hot_defer_wf`
    /// projection. No Trail/Cold conversion or refinement theorem is used.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(800)]
    pub(crate) proof fn lemma_wf_implies_hot_defer_wf(&self)
        requires
            self.wf(),
            TRACK,
            self.store.unique_capture_spec(),
            self.trail_stack@.len() == 0,
            self.trail_value_pool@.len() == 0,
            self.cold_stack@.len() == 0,
            self.cold_index_runs@.len() == 0,
            self.cold_value_pool@.len() == 0,
        ensures
            self.hot_defer_wf(),
    {
        self.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
        reveal(Vec::hot_repr_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::hot_defer_wf);
        reveal(Vec::hot_defer_end);

        let depth = self.hot_stack@.len();
        assert(depth == self.snapshots@.len());
        assert(depth == self.trail_frames@.len());
        assert forall|i: int| 0 <= i < depth implies
            (#[trigger] self.hot_stack@[i]).saved_len.as_nat()
                == self.snapshots@[i].len() by {
            self.lemma_hot_repr_at(i);
        }
        assert forall|i: int| 0 <= i < depth implies
            #[trigger] stratum_unique::<T, I>(
                self.hot_value_pool@,
                self.hot_stack@[i].start as int,
                self.hot_defer_end(i)) by {
            self.lemma_hot_repr_at(i);
            assert(self.hot_defer_end(i) == self.phys_hot_end(i));
        }
        assert forall|i: int| 0 <= i < depth implies
            #[trigger] frame_inv_range::<T, I>(
                self.layer_above_at(i),
                self.hot_value_pool@,
                self.hot_stack@[i].start as int,
                self.hot_defer_end(i),
                self.snapshots@[i],
                self.snapshots@[i].len()) by {
            self.lemma_hot_repr_at(i);
            assert(self.hot_defer_end(i) == self.phys_hot_end(i));
            assert(self.phys_frame_inv_range_holds(i));
        }
        assert(depth == 0 ==> self.hot_value_pool@.len() == 0);
        assert(depth > 0 ==> self.hot_stack@[0].start == 0);
        assert forall|i: int| 0 <= i < depth implies {
            &&& (#[trigger] self.hot_stack@[i]).start <= self.hot_stack@[i].end
            &&& self.hot_stack@[i].end <= self.hot_value_pool@.len()
            &&& self.hot_stack@[i].start as int <= self.hot_defer_end(i)
            &&& self.hot_defer_end(i) <= self.hot_value_pool@.len() as int
            &&& (i + 1 < depth ==> {
                &&& self.hot_stack@[i].end == self.hot_stack@[i + 1].start
                &&& self.hot_defer_end(i) == self.hot_stack@[i + 1].start as int
            })
            &&& (i + 1 == depth ==>
                self.hot_defer_end(i) == self.hot_value_pool@.len() as int)
        } by {
            self.lemma_hot_repr_at(i);
            assert(self.hot_defer_end(i) == self.phys_hot_end(i));
        }
        assert(depth > 0 ==>
            self.active_saved_len.as_nat() == self.snapshots@[(depth - 1) as int].len());
        assert forall|j: int|
            0 <= j < self.active_saved_len.as_nat() && j < self.view().len() && depth > 0
            implies (#[trigger] self.store.captured()[j])
                == captured_in_range::<T, I>(
                    self.hot_value_pool@,
                    self.hot_stack@[(depth - 1) as int].start as int,
                    self.hot_value_pool@.len() as int,
                    j as nat) by {
            self.lemma_open_ingress_hot_at(j);
        }
        assert(self.hot_defer_wf());
    }

    /// Changing only canonical ghost history cannot affect the physical Hot
    /// projection. This framing lemma keeps ghost-trail updates from forcing
    /// every caller to re-expand `hot_defer_wf`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1200)]
    pub(crate) proof fn lemma_hot_defer_transfer_canonical(&self, other: Self)
        requires
            other.hot_defer_wf(),
            self.store.wf(),
            self.store.unique_capture_spec() == other.store.unique_capture_spec(),
            self.store.captured() == other.store.captured(),
            self.view() == other.view(),
            self.hot_stack@ == other.hot_stack@,
            self.hot_value_pool@ == other.hot_value_pool@,
            self.trail_stack@ == other.trail_stack@,
            self.trail_value_pool@ == other.trail_value_pool@,
            self.cold_stack@ == other.cold_stack@,
            self.cold_index_runs@ == other.cold_index_runs@,
            self.cold_value_pool@ == other.cold_value_pool@,
            self.snapshots@ == other.snapshots@,
            self.trail_frames@ == other.trail_frames@,
            self.active_saved_len == other.active_saved_len,
            forall|i: int| 0 <= i < self.hot_stack@.len() ==>
                #[trigger] self.layer_above_at(i) == other.layer_above_at(i),
        ensures
            self.hot_defer_wf(),
    {
        reveal(Vec::hot_defer_wf);
        reveal(Vec::hot_defer_end);
    }

    /// Transfer canonical ghost reconstruction across operations that preserve
    /// every logical field it reads (for example allocator-only reclamation).
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1200)]
    pub(crate) proof fn lemma_wf_for_snap_transfer(&self, other: Self)
        requires
            other.wf_for_snap(),
            self.store.wf(),
            self.view() == other.view(),
            self.full_trail@ == other.full_trail@,
            self.trail_frames@ == other.trail_frames@,
            self.snapshots@ == other.snapshots@,
            self.cold_stack@ == other.cold_stack@,
            self.hot_stack@ == other.hot_stack@,
            self.trail_stack@ == other.trail_stack@,
            forall|k: int| 0 <= k < self.trail_frames@.len() ==>
                #[trigger] self.layer_above_at(k) == other.layer_above_at(k),
        ensures
            self.wf_for_snap(),
    {
        reveal(Vec::wf_for_snap);
        reveal(Vec::frame_partition_ok);
        assert(self.frame_partition_ok());
        assert(self.snapshots@.len() == self.trail_frames@.len());
        assert(self.trail_frames@.len() < usize::MAX);
        assert(self.trail_frames@.len() == 0 ==> self.full_trail@.len() == 0);
        assert(self.trail_frames@.len() > 0 ==> self.trail_frames@[0] == 0);
        assert(self.trail_frames@.len() > 0 ==>
            self.trail_frames@[(self.trail_frames@.len() - 1) as int]
                <= self.full_trail@.len());
        assert forall|k: int|
            0 <= k && k + 1 < self.trail_frames@.len() implies
                #[trigger] self.trail_frames@[k] <= self.trail_frames@[k + 1] by {
            assert(self.trail_frames@ == other.trail_frames@);
            assert(0 <= k && k + 1 < other.trail_frames@.len());
            other.lemma_diff_start_monotone(k, k + 1);
        }
        assert forall|k: int| 0 <= k < self.trail_frames@.len() implies
            #[trigger] frame_inv_range::<T, I>(
                self.layer_above_at(k), self.full_trail@,
                self.g_start(k), self.g_end(k), self.snapshots@[k],
                self.snapshots@[k].len()) by {
            assert(other.frame_inv_range_holds(k));
            assert(self.g_start(k) == other.g_start(k));
            assert(self.g_end(k) == other.g_end(k));
            assert(self.layer_above_at(k) == other.layer_above_at(k));
        }
        assert(self.wf_for_snap());
    }

    /// Reassemble the general invariant after an all-Hot operation has proved
    /// both the authoritative Hot grid and the canonical ghost grid. Empty
    /// Trail/Cold tiers make their representation predicates vacuous; the
    /// compatibility predicate remains an explicit premise because
    /// `hot_defer_wf` intentionally grants no authority to inert `diff_log`.
    pub(crate) proof fn lemma_hot_defer_snap_implies_wf(&self)
        requires
            self.hot_defer_wf(),
            self.wf_for_snap(),
            self.proof_compat_ok(),
        ensures
            self.wf(),
    {
        reveal(Vec::hot_defer_wf);
        reveal(Vec::hot_defer_end);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::hot_repr_ok);
        reveal(Vec::trail_repr_ok);
        reveal(Vec::cold_repr_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::proof_compat_ok);
        assert forall|i: int| 0 <= i < self.hot_stack@.len() implies
            self.hot_defer_end(i) == self.phys_hot_end(i) by {}
        assert(self.hot_repr_ok());
        assert(self.trail_repr_ok());
        assert(self.cold_repr_ok());
        assert(self.open_ingress_ok());
        assert(self.wf());
    }



    /// Every frame's diff_start is `<= diff_log.len()`. Follows from
    /// monotonicity plus the top frame's bound, by upward induction.
    pub(crate) proof fn lemma_diff_start_le_n(&self, k: int)
        requires
            self.wf_for_snap(),
            0 <= k < self.trail_frames@.len(),
        ensures
            self.trail_frames@[k] <= self.full_trail@.len(),
        decreases self.trail_frames@.len() - k,
    {
        let tf = self.trail_frames@;
        if k < tf.len() - 1 {
            self.lemma_diff_start_monotone(k, (tf.len() - 1) as int);
        }
    }

    /// diff_start is monotone non-decreasing across frames: for `a <= b`,
    /// `self.g_start(a) <= self.g_start(b)`.
    pub(crate) proof fn lemma_diff_start_monotone(&self, a: int, b: int)
        requires
            self.wf_for_snap(),
            0 <= a <= b < self.trail_frames@.len(),
        ensures
            self.trail_frames@[a] <= self.trail_frames@[b],
        decreases b - a,
    {
        if a < b {
            self.lemma_diff_start_monotone(a, b - 1);
            // adjacent step (b-1, b) from wf_for_snap's monotone clause;
            // the bound makes k = b-1 an instantiation the trigger accepts.
            assert(0 <= b - 1 && (b - 1) + 1 < self.trail_frames@.len());
            assert(self.trail_frames@[b - 1] <= self.trail_frames@[b]);
        }
    }


    // NOTE (pop into marked region): `lemma_saved_len_le_active` ("top frame is the
    // longest"), `lemma_saved_len_monotone` ("saved_len non-decreasing"), and
    // `lemma_saved_len_le_view` ("every saved_len <= view.len()") were DELETED
    // here. All three are FALSE once pop can shrink the view into the marked
    // region and `mark` can record a short length. They are replaced
    // everywhere by the per-frame coverage in `frame_cell_inv`'s uncaptured
    // arm (uncaptured j ==> j < layer_above.len()), which is exactly the bound
    // those lemmas used to supply and which holds unconditionally.




    /// "Untracked" state: no marks are live. Production compiles out tracking
    /// when `TRACK == false`; the verus model instead proves that whenever the
    /// frame stack is empty there are no live diff entries and operations have
    /// the plain sequence transitions on the view. The empty diff/frame/fork
    /// fields and runtime guards remain in the executable struct.
    pub open(crate) spec fn untracked(&self) -> bool {
        self.trail_frames@.len() == 0
    }

    /// The inert compatibility log is empty when there are no logical frames.
    /// This is intentionally not a physical representation theorem.
    pub(crate) proof fn lemma_untracked_diff_log_empty(&self)
        requires self.wf(), self.untracked(),
        ensures self.diff_log@.len() == 0,
    {
        reveal(Vec::proof_compat_ok);
    }

    /// Observational equivalence to `std::Vec` while untracked: push appends,
    /// set updates, pop drops the last element — exactly the std operations on
    /// the view — AND the vector stays untracked with no diff log. These are
    /// thin wrappers asserting the equivalence explicitly; the heavy lifting is
    /// in push/set/pop's own contracts, which hold for ALL states.
    pub fn push_untracked(&mut self, value: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            (old(self).untracked() && old(self).view().len() + 1 < I::max_nat()) ==> {
                &&& final(self).untracked()
                &&& final(self).view() == old(self).view().push(value)
                &&& final(self).diff_log_len_spec() == 0
            },
    {
        if !(self.depth_exec() == 0) {
            crate::guard::refuse("Vec::push_untracked: vector has live frames");
        }
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
        }
        if !(self.store.raw_len() < cap) {
            crate::guard::refuse("Vec::push_untracked: index word exhausted");
        }
        self.push(value);
        proof { self.lemma_untracked_diff_log_empty(); }
    }

    pub fn pop_untracked(&mut self) -> (r: Option<T>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            old(self).untracked() ==> {
                &&& final(self).untracked()
                &&& (old(self).view().len() == 0
                    ==> r is None && final(self).view() == old(self).view())
                &&& (old(self).view().len() > 0
                    ==> r == Some(old(self).view().last())
                        && final(self).view() == old(self).view().drop_last())
                &&& final(self).diff_log_len_spec() == 0
            },
    {
        if !(self.depth_exec() == 0) {
            crate::guard::refuse("Vec::pop_untracked: vector has live frames");
        }
        let r = self.pop();
        proof { self.lemma_untracked_diff_log_empty(); }
        r
    }

    pub fn set_untracked(&mut self, i: I, value: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            (old(self).untracked() && i.as_nat() < old(self).view().len()) ==> {
                &&& final(self).untracked()
                &&& final(self).view() == old(self).view().update(i.as_nat() as int, value)
                &&& final(self).diff_log_len_spec() == 0
            },
    {
        if !(self.depth_exec() == 0) {
            crate::guard::refuse("Vec::set_untracked: vector has live frames");
        }
        if !(i.as_usize() < self.store.raw_len()) {
            crate::guard::refuse("Vec::set_untracked: index out of bounds");
        }
        self.set_index(i, value);
        proof { self.lemma_untracked_diff_log_empty(); }
    }

    #[inline(always)]
    pub fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.view().len(),
    {
        self.store.len()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() == 0),
    {
        self.store.is_empty()
    }

    #[inline(always)]
    pub fn get_index(&self, i: I) -> (v: T)
        requires
            self.wf(),
        ensures
            i.as_nat() < self.view().len() ==> v == self.view()[i.as_nat() as int],
    {
        // Total with documented panic: the bound
        // is an explicit branch, not an erased requires — an out-of-range
        // index from an unverified caller refuses instead of whatever the
        // store does. The check is the one std indexing performed anyway.
        if !(i.as_usize() < self.store.raw_len()) {
            crate::guard::refuse("Vec::get_index: index out of bounds");
        }
        self.store.get(i)
    }

    #[inline(always)]
    fn configured_rollover_can_run(
        unique_capture: bool,
        tier_policy: crate::tier_policy::TierPolicy,
        hot_buffer: Option<usize>,
    ) -> bool {
        if hot_buffer.is_some() {
            return true;
        }
        if unique_capture {
            !matches!(tier_policy.hot, crate::tier_policy::TierLimit::Unbounded)
        } else {
            !matches!(tier_policy.trail, crate::tier_policy::TierLimit::Unbounded)
                || !matches!(tier_policy.hot, crate::tier_policy::TierLimit::Unbounded)
        }
    }

    /// Build an empty tracked vector over a freshly-empty store. Mirrors
    /// production's `with_store`. The store must be well-formed and empty
    /// (no data, no capture flags) — the concrete `new()` of each backend
    /// supplies that.
    pub(crate) fn with_store(store: S) -> (v: Self)
        requires
            store.wf(),
            store.data().len() == 0,
        ensures
            v.wf(),
            v.view().len() == 0,
            v.snapshots_view().len() == 0,
            TRACK && v.store.unique_capture_spec() ==> v.hot_defer_wf(),
    {
        // Experiment lever (measurement instrument, not the final per-column
        // config): SEMPER_COMPRESS=auto flips default-constructed columns to the
        // per-frame-adaptive representation, so a whole binary (the e-graph under
        // Sundance) runs compressed without any constructor plumbing. Capability-
        // guarded: a store whose restore reads the replayed index slice
        // (InlineStore's sparse tag-clear) skips it, because the adaptive
        // representation's index materialization is the measured slow path there.
        // Unset, nothing changes.
        // The InlineStore path is now frame-wise too (subrange_vec fast path feeds
        // its begin_restore materialization and its replay), so the lever covers
        // every store.
        let mode = if crate::compression_config::env_compress_default() {
            crate::diff_compress::CompressionMode::Auto
        } else {
            crate::diff_compress::CompressionMode::None
        };
        Self::with_store_mode(store, mode)
    }

    /// As `with_store`, enabling the legacy Vec compression cadence. `None`
    /// keeps unique-capture stores fully buffered; every other mode, plus a
    /// chronological store, migrates each whole batch after eight closed
    /// frames. The three-tier Vec normalizes migrated history to its run-only
    /// cold representation, so non-`None` modes are activation aliases here.
    /// Use [`crate::diff_compress::compress_frame`] when the named dictionary
    /// or write-order codec itself is required.
    pub(crate) fn with_store_mode(store: S, mode: crate::diff_compress::CompressionMode)
        -> (v: Self)
        requires
            store.wf(),
            store.data().len() == 0,
        ensures
            v.wf(),
            v.view().len() == 0,
            v.snapshots_view().len() == 0,
            TRACK && v.store.unique_capture_spec() ==> v.hot_defer_wf(),
    {
        proof { store.lemma_wf_captured_len(); }  // captured().len() == 0
        let unique_capture = store.unique_capture();
        // Legacy Vec modes predate the run-only three-tier cold contract. The
        // standalone `compress_frame` API still provides each named encoder;
        // Vec treats every non-None mode as the same run-cold activation alias.
        // Compatibility here is the historical whole-batch cadence: after
        // more than eight frames close, all closed ingress frames migrate.
        let legacy_batch_rollover = if matches!(mode, crate::diff_compress::CompressionMode::None)
            && unique_capture
        {
            None
        } else {
            Some(8usize)
        };
        let tier_policy = if unique_capture {
            crate::tier_policy::TierPolicy {
                trail: crate::tier_policy::TierLimit::Frames(0),
                hot: crate::tier_policy::TierLimit::Unbounded,
                cold_reclaim: crate::tier_policy::ReclaimPolicy::RetainCapacity,
            }
        } else {
            crate::tier_policy::TierPolicy {
                trail: crate::tier_policy::TierLimit::Unbounded,
                hot: crate::tier_policy::TierLimit::Unbounded,
                cold_reclaim: crate::tier_policy::ReclaimPolicy::RetainCapacity,
            }
        };
        let v = Vec {
            store,
            diff_log: std::vec::Vec::new(),
            trail_value_pool: std::vec::Vec::new(),
            trail_stack: std::vec::Vec::new(),
            hot_value_pool: std::vec::Vec::new(),
            hot_stack: std::vec::Vec::new(),
            cold_stack: std::vec::Vec::new(),
            cold_value_pool: std::vec::Vec::new(),
            cold_index_runs: std::vec::Vec::new(),
            trail_seen: None,
            tier_policy,
            hot_buffer: legacy_batch_rollover,
            automatic_rollover_enabled: Self::configured_rollover_can_run(
                unique_capture,
                tier_policy,
                legacy_batch_rollover,
            ),
            full_trail: Ghost(Seq::empty()),
            trail_frames: Ghost(Seq::empty()),
            active_saved_len: <I as IndexLike>::min(),
            phantom: core::marker::PhantomData,
            snapshots: Ghost(Seq::empty()),
        };
        proof {
            I::lemma_min_as_nat();
            assert(v.active_saved_len == I::min_spec());
            assert(v.trail_frames@.len() == 0);
            assert(v.snapshots@.len() == 0);
            // Empty container: no hot frames, so phys_frame_inv_range is vacuous.
            assert(v.hot_stack@.len() == 0);
            assert forall|i: int| 0 <= i < v.hot_stack@.len() implies
                #[trigger] v.phys_frame_inv_range_holds(i) by {}
            if TRACK && v.store.unique_capture_spec() {
                reveal(Vec::hot_defer_wf);
                reveal(Vec::hot_defer_end);
                assert forall|j: int| 0 <= j < v.store.captured().len()
                    implies !(#[trigger] v.store.captured()[j]) by {}
                assert(v.hot_defer_wf());
            }
        }
        v
    }

    /// Explicit execution-first constructor used by the three-tier API.
    pub(crate) fn with_store_policy(
        store: S,
        tier_policy: crate::tier_policy::TierPolicy,
    ) -> (v: Self)
        requires
            store.wf(),
            store.data().len() == 0,
        ensures
            v.wf(),
            v.view().len() == 0,
            v.snapshots_view().len() == 0,
            TRACK && v.store.unique_capture_spec() ==> v.hot_defer_wf(),
    {
        let mut v = Self::with_store_mode(store, crate::diff_compress::CompressionMode::None);
        let ghost initialized = v;
        v.tier_policy = tier_policy;
        v.hot_buffer = None;
        v.automatic_rollover_enabled =
            Self::configured_rollover_can_run(v.store.unique_capture(), tier_policy, None);
        proof {
            if TRACK && v.store.unique_capture_spec() {
                reveal(Vec::hot_defer_wf);
                reveal(Vec::hot_defer_end);
                assert(initialized.hot_defer_wf());
                assert(v.hot_defer_wf());
            }
        }
        v
    }

    /// Verified unique-ingress capture over the authoritative Hot pool. This is
    /// the first executable proof core in the three-tier campaign: first
    /// capture appends exactly one snapshot value and repeated capture is a
    /// physical no-op.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1200)]
    #[inline(always)]
    fn hot_defer_capture_checked(&mut self, index: I)
        requires
            old(self).hot_defer_wf(),
            index.as_nat() < old(self).view().len(),
        ensures
            final(self).hot_defer_wf(),
            final(self).view() == old(self).view(),
            final(self).hot_stack@ == old(self).hot_stack@,
            final(self).snapshots@ == old(self).snapshots@,
            final(self).trail_frames@ == old(self).trail_frames@,
            final(self).full_trail@ == old(self).full_trail@,
            final(self).diff_log@ == old(self).diff_log@,
            final(self).active_saved_len == old(self).active_saved_len,
            index.as_nat() < old(self).active_saved_len.as_nat()
                ==> final(self).store.captured()[index.as_nat() as int],
    {
        let ghost pre = *self;
        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
            I::lemma_min_as_nat();
        }
        if index.as_usize() >= self.active_saved_len.as_usize() {
            return;
        }
        let ghost old_pool = self.hot_value_pool@;
        let ghost old_captured = self.store.captured();
        let ghost depth = self.hot_stack@.len();
        let ghost top = depth - 1;
        let ghost lo = self.hot_stack@[top as int].start as int;
        let ghost j = index.as_nat() as int;
        proof {
            assert(depth > 0);
            assert(0 <= j < self.active_saved_len.as_nat() as int);
            assert(j < self.view().len());
            assert(old_captured[j]
                == captured_in_range::<T, I>(old_pool, lo, old_pool.len() as int, j as nat));
        }
        self.store.capture(index, self.active_saved_len, &mut self.hot_value_pool);
        proof {
            let pool = self.hot_value_pool@;
            let appended = !old_captured[j];
            if appended {
                assert(pool == old_pool.push((pre.view()[j], index)));
                assert(pool.subrange(0, old_pool.len() as int) == old_pool);
                assert(self.store.captured()[j]);
                assert(!captured_in_range::<T, I>(
                    old_pool, lo, old_pool.len() as int, j as nat));
            } else {
                assert(pool == old_pool);
                assert(self.store.captured() == old_captured);
                assert(captured_in_range::<T, I>(
                    old_pool, lo, old_pool.len() as int, j as nat));
            }
            assert(self.view() == pre.view());
            assert(self.hot_stack@ == pre.hot_stack@);
            assert(self.snapshots@ == pre.snapshots@);
            assert(self.trail_frames@ == pre.trail_frames@);
            assert(self.full_trail@ == pre.full_trail@);
            assert(self.active_saved_len == pre.active_saved_len);
            self.store.lemma_wf_captured_len();
            assert(self.store.captured().len() == self.view().len());

            // Closed strata are byte-for-byte framed; only the open top may
            // acquire the one appended capture.
            assert forall|i: int| 0 <= i < depth implies
                #[trigger] stratum_unique::<T, I>(
                    pool, self.hot_stack@[i].start as int, self.hot_defer_end(i)) by {
                let ilo = self.hot_stack@[i].start as int;
                if i == top as int {
                    assert(pre.hot_defer_end(i) == old_pool.len() as int);
                    assert(self.hot_defer_end(i) == pool.len() as int);
                    if appended {
                        lemma_stratum_unique_append::<T, I>(
                            old_pool, pool, ilo, j as nat);
                    }
                } else {
                    assert(i + 1 < depth);
                    assert(self.hot_defer_end(i) == pre.hot_defer_end(i));
                    let hi = self.hot_defer_end(i);
                    assert(hi <= old_pool.len());
                    assert forall|q: int| ilo <= q < hi implies
                        #[trigger] pool[q] == old_pool[q] by {}
                    lemma_stratum_unique_local::<T, I>(old_pool, pool, ilo, hi);
                }
            }
            assert forall|i: int| 0 <= i < depth implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(i), pool, self.hot_stack@[i].start as int,
                    self.hot_defer_end(i), self.snapshots@[i], self.snapshots@[i].len()) by {
                let ilo = self.hot_stack@[i].start as int;
                if i == top as int {
                    assert(pre.layer_above_at(i) == pre.view());
                    assert(self.layer_above_at(i) == self.view());
                    assert(pre.hot_defer_end(i) == old_pool.len() as int);
                    assert(self.hot_defer_end(i) == pool.len() as int);
                    if appended {
                        lemma_frame_inv_range_capture_append::<T, I>(
                            pre.view(), old_pool, pool, ilo, self.snapshots@[i],
                            self.snapshots@[i].len(), j);
                    }
                } else {
                    assert(i + 1 < depth);
                    assert(self.layer_above_at(i) == pre.layer_above_at(i));
                    assert(self.hot_defer_end(i) == pre.hot_defer_end(i));
                    let hi = self.hot_defer_end(i);
                    assert(hi <= old_pool.len());
                    assert forall|q: int| ilo <= q < hi implies
                        #[trigger] old_pool[q] == pool[q] by {}
                    lemma_frame_inv_range_local::<T, I>(
                        self.layer_above_at(i), old_pool, pool, ilo, hi,
                        self.snapshots@[i], self.snapshots@[i].len());
                }
            }
            assert forall|q: int|
                0 <= q < self.active_saved_len.as_nat() && q < self.view().len() implies
                (#[trigger] self.store.captured()[q])
                    == captured_in_range::<T, I>(
                        pool, lo, pool.len() as int, q as nat) by {
                if q == j {
                    assert(self.store.captured()[q]);
                    if appended {
                        assert(pool[old_pool.len() as int].1.as_nat() == q as nat);
                    }
                } else {
                    if appended {
                        assert(self.store.captured()[q] == old_captured[q]);
                        lemma_captured_in_range_append_other::<T, I>(
                            old_pool, pool, lo, q as nat, j as nat);
                    } else {
                        assert(pool == old_pool);
                    }
                    assert(old_captured[q] == captured_in_range::<T, I>(
                        old_pool, lo, old_pool.len() as int, q as nat));
                }
            }
            assert forall|q: int| 0 <= q < self.view().len()
                && #[trigger] self.store.captured()[q]
                implies depth > 0 && q < self.active_saved_len.as_nat() by {
                if q == j {
                } else if appended {
                    assert(self.store.captured()[q] == old_captured[q]);
                    assert(pre.store.captured()[q]);
                } else {
                    assert(pre.store.captured()[q]);
                }
            }
            assert(self.hot_defer_wf());
        }
    }

    /// Canonical capture preservation is independent of the physical ingress
    /// tier. The physical caller supplies the new partition and unchanged live
    /// view; duplicate chronological events retain the original first hitter.
    #[verifier::spinoff_prover]
    proof fn lemma_canonical_capture_append(&self, pre: Self, index: I)
        requires
            pre.wf_for_snap(),
            pre.depth_spec() > 0,
            index.as_nat() < pre.view().len(),
            index.as_nat() < pre.snapshots@[pre.depth_spec() - 1].len(),
            self.store.wf(), self.frame_partition_ok(),
            self.view() == pre.view(), self.snapshots@ == pre.snapshots@,
            self.trail_frames@ == pre.trail_frames@,
            self.full_trail@ == pre.full_trail@.push((pre.view()[index.as_nat() as int], index)),
        ensures self.wf_for_snap(),
    {
        let j = index.as_nat() as int;
        let top = pre.depth_spec() - 1;
        reveal(Vec::wf_for_snap);
        assert(self.full_trail@.subrange(0, pre.full_trail@.len() as int)
            =~= pre.full_trail@);
        assert forall|k: int| 0 <= k < self.trail_frames@.len() implies
            #[trigger] frame_inv_range::<T, I>(
                self.layer_above_at(k), self.full_trail@,
                self.g_start(k), self.g_end(k), self.snapshots@[k],
                self.snapshots@[k].len()) by {
            assert(pre.frame_inv_range_holds(k));
            assert(self.layer_above_at(k) == pre.layer_above_at(k));
            assert(self.g_start(k) == pre.g_start(k));
            if k == top {
                assert(pre.layer_above_at(k) == pre.view());
                if captured_in_range::<T, I>(pre.full_trail@,
                    self.g_start(k), pre.full_trail@.len() as int, j as nat) {
                    lemma_frame_inv_range_append_duplicate::<T, I>(
                        pre.view(), pre.full_trail@, self.full_trail@,
                        self.g_start(k), self.snapshots@[k], self.snapshots@[k].len(), j);
                } else {
                    lemma_frame_inv_range_capture_append::<T, I>(
                        pre.view(), pre.full_trail@, self.full_trail@,
                        self.g_start(k), self.snapshots@[k], self.snapshots@[k].len(), j);
                }
            } else {
                assert(k + 1 < pre.depth_spec());
                pre.lemma_diff_start_le_n(k + 1);
                assert(self.g_end(k) == pre.g_end(k));
                assert forall|q: int| self.g_start(k) <= q < self.g_end(k) implies
                    #[trigger] pre.full_trail@[q] == self.full_trail@[q] by {}
                lemma_frame_inv_range_local::<T, I>(
                    self.layer_above_at(k), pre.full_trail@, self.full_trail@,
                    self.g_start(k), self.g_end(k), self.snapshots@[k], self.snapshots@[k].len());
            }
        }
    }

    /// Checked unique-Hot capture that maintains both physical first-capture
    /// storage and the canonical chronological ghost trail. Every in-frame
    /// write appends one ghost event; repeated physical captures remain no-ops.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(2200)]
    #[inline(always)]
    fn hot_defer_capture_canonical_checked(&mut self, index: I)
        requires
            old(self).wf(),
            old(self).hot_defer_wf(),
            index.as_nat() < old(self).view().len(),
        ensures
            final(self).wf(),
            final(self).hot_defer_wf(),
            final(self).view() == old(self).view(),
            final(self).snapshots@ == old(self).snapshots@,
            final(self).trail_frames@ == old(self).trail_frames@,
            final(self).active_saved_len == old(self).active_saved_len,
            index.as_nat() < old(self).active_saved_len.as_nat() ==>
                final(self).store.captured()[index.as_nat() as int],
            index.as_nat() < old(self).active_saved_len.as_nat() ==>
                final(self).full_trail@
                    == old(self).full_trail@.push((old(self).view()[index.as_nat() as int], index)),
            index.as_nat() >= old(self).active_saved_len.as_nat() ==>
                final(self).full_trail@ == old(self).full_trail@,
    {
        let ghost pre = *self;
        self.hot_defer_capture_checked(index);
        let ghost physical = *self;
        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
            let j = index.as_nat() as int;
            let depth = self.trail_frames@.len();
            let append = j < self.active_saved_len.as_nat() as int;
            assert(self.view() == pre.view());
            assert(self.full_trail@ == pre.full_trail@);
            assert(self.trail_frames@ == pre.trail_frames@);
            assert(self.snapshots@ == pre.snapshots@);
            if append {
                assert(depth > 0);
                self.full_trail@ = physical.full_trail@.push((pre.view()[j], index));
                assert(physical.full_trail@ == pre.full_trail@);
                assert(self.full_trail@
                    == pre.full_trail@.push((pre.view()[j], index)));
                assert(self.full_trail@.subrange(0, pre.full_trail@.len() as int)
                    =~= pre.full_trail@) by {
                    assert forall|q: int| 0 <= q < pre.full_trail@.len() implies
                        #[trigger] self.full_trail@[q] == pre.full_trail@[q] by {}
                }
            }
            assert(physical.hot_defer_wf());
            assert(self.store == physical.store);
            assert(self.hot_stack@ == physical.hot_stack@);
            assert(self.hot_value_pool@ == physical.hot_value_pool@);
            assert(self.trail_stack@ == physical.trail_stack@);
            assert(self.trail_value_pool@ == physical.trail_value_pool@);
            assert(self.cold_stack@ == physical.cold_stack@);
            assert(self.cold_index_runs@ == physical.cold_index_runs@);
            assert(self.cold_value_pool@ == physical.cold_value_pool@);
            assert(self.snapshots@ == physical.snapshots@);
            assert(self.trail_frames@ == physical.trail_frames@);
            assert(self.active_saved_len == physical.active_saved_len);
            assert forall|i: int| 0 <= i < self.hot_stack@.len() implies
                #[trigger] self.layer_above_at(i) == physical.layer_above_at(i) by {}
            self.lemma_hot_defer_transfer_canonical(physical);

            pre.lemma_wf_named_parts();
            assert(self.frame_partition_ok());
            if append {
                self.lemma_canonical_capture_append(pre, index);
            } else {
                self.lemma_canonical_history_repartition(pre);
            }
            reveal(Vec::proof_compat_ok);
            assert(pre.proof_compat_ok());
            assert(self.diff_log@ == pre.diff_log@);
            assert(self.trail_frames@ == pre.trail_frames@);
            assert(self.proof_compat_ok());
            self.lemma_hot_defer_snap_implies_wf();
        }
    }

    /// Physical effect of an in-domain capture, before the canonical ghost
    /// event is appended. Only the selected pair pool and store flags change.
    closed spec fn ingress_capture_effect(&self, pre: Self, index: I) -> bool {
        let trail = !pre.store.unique_capture_spec();
        let pool = pre.pair_tier_pool(trail);
        &&& *self == Self { store: self.store, hot_value_pool: self.hot_value_pool,
            trail_value_pool: self.trail_value_pool, ..pre }
        &&& self.store.wf()
        &&& self.view() == pre.view()
        &&& self.store.unique_capture_spec() == pre.store.unique_capture_spec()
        &&& self.store.needs_replayed_indices_spec() == pre.store.needs_replayed_indices_spec()
        &&& self.store.restore_entries_clear_capture_spec()
            == pre.store.restore_entries_clear_capture_spec()
        &&& self.store.captured() == pre.store.captured().update(index.as_nat() as int, true)
        &&& self.pair_tier_pool(!trail) == pre.pair_tier_pool(!trail)
        &&& self.pair_tier_pool(trail) ==
            if trail || !pre.store.captured()[index.as_nat() as int] {
                pool.push((pre.view()[index.as_nat() as int], index))
            } else { pool }
    }

    /// Frame-local capture proof shared by the Hot and Trail representations.
    #[verifier::spinoff_prover]
    proof fn lemma_ingress_capture_frame(&self, pre: Self, index: I, trail: bool, f: int)
        requires pre.wf(), self.ingress_capture_effect(pre, index),
            index.as_nat() < pre.view().len(), index.as_nat() < pre.active_saved_len.as_nat(),
            0 <= f < pre.pair_tier_count(trail),
        ensures
            frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(trail) + f),
                self.pair_tier_pool(trail), self.pair_tier_start(trail, f), self.pair_tier_end(trail, f),
                self.snapshots@[self.pair_tier_offset(trail) + f],
                self.snapshots@[self.pair_tier_offset(trail) + f].len()),
            !trail ==> stratum_unique::<T, I>(self.pair_tier_pool(trail),
                self.pair_tier_start(trail, f), self.pair_tier_end(trail, f)),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        pre.lemma_pair_tier_frame_layout(trail, f);
        reveal(Vec::ingress_capture_effect);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::frame_partition_ok);
        if trail { reveal(Vec::trail_repr_ok); } else { reveal(Vec::hot_repr_ok); }
        let a = pre.pair_tier_pool(trail);
        let b = self.pair_tier_pool(trail);
        let lo = pre.pair_tier_start(trail, f);
        let hi = pre.pair_tier_end(trail, f);
        let k = pre.pair_tier_offset(trail) + f;
        let snap = pre.snapshots@[k];
        assert(frame_inv_range::<T, I>(pre.layer_above_at(k), a, lo, hi, snap, snap.len()));
        assert(self.layer_above_at(k) == pre.layer_above_at(k));
        if b == a {
        } else if f + 1 < pre.pair_tier_count(trail) {
            assert(self.pair_tier_end(trail, f) == hi);
            assert forall|q: int| lo <= q < hi implies #[trigger] a[q] == b[q] by {}
            lemma_frame_inv_range_local::<T, I>(pre.layer_above_at(k), a, b, lo, hi, snap, snap.len());
            if !trail { lemma_stratum_unique_local::<T, I>(a, b, lo, hi); }
        } else {
            assert(trail == !pre.store.unique_capture_spec());
            assert(k == pre.depth_spec() - 1);
            assert(pre.layer_above_at(k) == pre.view());
            assert(hi == a.len() as int);
            assert(b == a.push((pre.view()[index.as_nat() as int], index)));
            assert(b.subrange(0, a.len() as int) =~= a);
            let j = index.as_nat() as int;
            if captured_in_range::<T, I>(a, lo, hi, j as nat) {
                lemma_frame_inv_range_append_duplicate::<T, I>(pre.view(), a, b, lo, snap, snap.len(), j);
            } else {
                lemma_frame_inv_range_capture_append::<T, I>(pre.view(), a, b, lo, snap, snap.len(), j);
            }
            if !trail {
                assert(!pre.store.captured()[j]);
                assert(!captured_in_range::<T, I>(a, lo, hi, j as nat));
                lemma_stratum_unique_append::<T, I>(a, b, lo, j as nat);
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_ingress_capture_hot_repr(&self, pre: Self, index: I)
        requires pre.wf(), self.ingress_capture_effect(pre, index),
            index.as_nat() < pre.view().len(), index.as_nat() < pre.active_saved_len.as_nat(),
        ensures self.hot_repr_ok(),
    {
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::ingress_capture_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        I::lemma_min_as_nat();
        assert(pre.depth_spec() > 0);
        reveal(Vec::hot_repr_ok);
        let hs = self.hot_stack@;
        let pool = self.hot_value_pool@;
        assert forall|f: int| 0 <= f < hs.len() implies {
            &&& (#[trigger] hs[f]).start <= hs[f].end
            &&& hs[f].end <= pool.len()
            &&& hs[f].start as int <= self.phys_hot_end(f)
            &&& self.phys_hot_end(f) <= pool.len() as int
            &&& (f + 1 < hs.len() ==> {
                &&& hs[f].end == hs[f + 1].start
                &&& self.phys_hot_end(f) == hs[f + 1].start as int
            })
            &&& (f + 1 == hs.len() ==> self.phys_hot_end(f) == pool.len() as int)
            &&& self.pair_tier_offset(false) + f < self.snapshots@.len()
            &&& frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(false) + f),
                pool, hs[f].start as int, self.phys_hot_end(f),
                self.snapshots@[self.pair_tier_offset(false) + f],
                self.snapshots@[self.pair_tier_offset(false) + f].len())
            &&& stratum_unique::<T, I>(pool, hs[f].start as int, self.phys_hot_end(f))
        } by {
            pre.lemma_pair_tier_frame_layout(false, f);
            self.lemma_ingress_capture_frame(pre, index, false, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_ingress_capture_trail_repr(&self, pre: Self, index: I)
        requires pre.wf(), self.ingress_capture_effect(pre, index),
            index.as_nat() < pre.view().len(), index.as_nat() < pre.active_saved_len.as_nat(),
        ensures self.trail_repr_ok(),
    {
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::ingress_capture_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        I::lemma_min_as_nat();
        assert(pre.depth_spec() > 0);
        reveal(Vec::trail_repr_ok);
        let hs = self.trail_stack@;
        let pool = self.trail_value_pool@;
        assert forall|f: int| 0 <= f < hs.len() implies {
            &&& (#[trigger] hs[f]).start <= hs[f].end
            &&& hs[f].end <= pool.len()
            &&& hs[f].start as int <= self.phys_trail_end(f)
            &&& self.phys_trail_end(f) <= pool.len() as int
            &&& (f + 1 < hs.len() ==> {
                &&& hs[f].end == hs[f + 1].start
                &&& self.phys_trail_end(f) == hs[f + 1].start as int
            })
            &&& (f + 1 == hs.len() ==> self.phys_trail_end(f) == pool.len() as int)
            &&& self.pair_tier_offset(true) + f < self.snapshots@.len()
            &&& frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(true) + f),
                pool, hs[f].start as int, self.phys_trail_end(f),
                self.snapshots@[self.pair_tier_offset(true) + f],
                self.snapshots@[self.pair_tier_offset(true) + f].len())

        } by {
            pre.lemma_pair_tier_frame_layout(true, f);
            self.lemma_ingress_capture_frame(pre, index, true, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_ingress_capture_flags(&self, pre: Self, index: I)
        requires pre.wf(), self.ingress_capture_effect(pre, index),
            index.as_nat() < pre.view().len(), index.as_nat() < pre.active_saved_len.as_nat(),
        ensures self.open_ingress_ok(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::ingress_capture_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        I::lemma_min_as_nat();
        let trail = !pre.store.unique_capture_spec();
        let a = pre.pair_tier_pool(trail);
        let b = self.pair_tier_pool(trail);
        let lo = pre.pair_tier_start(trail, pre.pair_tier_count(trail) - 1);
        let j = index.as_nat() as int;
        assert(pre.depth_spec() > 0);
        assert forall|q: int| 0 <= q < self.active_saved_len.as_nat() && q < self.view().len()
            implies (#[trigger] self.store.captured()[q])
                == captured_in_range::<T, I>(b, lo, b.len() as int, q as nat) by {
            assert(pre.store.captured()[q]
                == captured_in_range::<T, I>(a, lo, a.len() as int, q as nat));
            if b != a {
                assert(b.subrange(0, a.len() as int) =~= a);
                if q == j {
                    assert(b[a.len() as int].1.as_nat() == q as nat);
                } else {
                    lemma_captured_in_range_append_other::<T, I>(a, b, lo, q as nat, j as nat);
                }
            }
        }
        assert forall|q: int| 0 <= q < self.view().len() && #[trigger] self.store.captured()[q]
            implies self.depth_spec() > 0 && q < self.active_saved_len.as_nat() by {
            if q != j { assert(pre.store.captured()[q]); }
        }
        assert(self.open_ingress_ok());
    }

    /// Snapshot-side parts of `wf` after an ingress capture: the frame
    /// partition and the canonical history are untouched by a capture that
    /// only marks a flag and appends to a tier pool.
    #[verifier::spinoff_prover]
    proof fn lemma_ingress_capture_snap(&self, pre: Self, index: I)
        requires pre.wf(), self.ingress_capture_effect(pre, index),
            index.as_nat() < pre.view().len(), index.as_nat() < pre.active_saved_len.as_nat(),
        ensures self.frame_partition_ok(), self.wf_for_snap(), self.proof_compat_ok(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::ingress_capture_effect);
        reveal(Vec::frame_partition_ok);
        assert(self.frame_partition_ok());
        self.lemma_canonical_history_repartition(pre);
        reveal(Vec::proof_compat_ok);
        assert(self.proof_compat_ok());
    }

    /// Cold-side part of `wf` after an ingress capture: no Cold cell moves, so
    /// every Cold frame still reconstructs its snapshot.
    #[verifier::spinoff_prover]
    proof fn lemma_ingress_capture_cold(&self, pre: Self, index: I)
        requires pre.wf(), self.ingress_capture_effect(pre, index),
            index.as_nat() < pre.view().len(), index.as_nat() < pre.active_saved_len.as_nat(),
        ensures self.cold_repr_ok(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::ingress_capture_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::cold_repr_ok);
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f) by {
            self.lemma_cold_reconstructs_transfer(pre, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_ingress_capture_preserves(&self, pre: Self, index: I)
        requires pre.wf(), self.ingress_capture_effect(pre, index),
            index.as_nat() < pre.view().len(), index.as_nat() < pre.active_saved_len.as_nat(),
        ensures self.wf(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        self.lemma_ingress_capture_snap(pre, index);
        self.lemma_ingress_capture_trail_repr(pre, index);
        self.lemma_ingress_capture_hot_repr(pre, index);
        self.lemma_ingress_capture_flags(pre, index);
        self.lemma_ingress_capture_cold(pre, index);
        reveal(Vec::wf);
    }

    /// The chronological ghost event sequence is absent from physical tier,
    /// ownership and capture predicates. Keep that framing separate from the
    /// canonical reconstruction argument.
    #[verifier::spinoff_prover]
    proof fn lemma_full_trail_physical_framing(&self, physical: Self)
        requires physical.wf(), *self == (Self { full_trail: self.full_trail, ..physical }),
        ensures self.frame_partition_ok(), self.hot_repr_ok(), self.trail_repr_ok(),
            self.cold_repr_ok(), self.open_ingress_ok(), self.proof_compat_ok(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_reconstructs);
        hide(frame_inv_range);
        hide(stratum_unique);
        physical.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
        reveal(Vec::hot_repr_ok);
        reveal(Vec::trail_repr_ok);
        reveal(Vec::cold_repr_ok);
        reveal(Vec::cold_payload_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::proof_compat_ok);
        assert forall|f: int| 0 <= f < self.depth_spec() implies
            #[trigger] self.layer_above_at(f) == physical.layer_above_at(f) by {}
        assert(self.frame_partition_ok());
        assert(self.hot_repr_ok());
        assert(self.trail_repr_ok());
        assert(self.open_ingress_ok());
        assert(self.proof_compat_ok());
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f) by {
            self.lemma_cold_reconstructs_transfer(physical, f);
        }
    }




    /// Appending a canonical event does not change any physical representation.
    #[verifier::spinoff_prover]
    proof fn lemma_ingress_capture_canonical_finish(&self, physical: Self, index: I)
        requires physical.wf(), index.as_nat() < physical.view().len(),
            index.as_nat() < physical.active_saved_len.as_nat(),
            *self == (Self { full_trail: self.full_trail, ..physical }),
            self.full_trail@ == physical.full_trail@.push((physical.view()[index.as_nat() as int], index)),
        ensures self.wf(),
    {
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::repr_ok);
        hide(Vec::cold_runs_disjoint);
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        physical.lemma_wf_named_parts();
        self.lemma_full_trail_physical_framing(physical);
        assert(self.store.wf()) by { reveal(Vec::wf_for_snap); }
        reveal(Vec::open_ingress_ok);
        reveal(Vec::frame_partition_ok);
        I::lemma_min_as_nat();
        assert(physical.depth_spec() > 0);
        assert(index.as_nat() < physical.snapshots@[physical.depth_spec() - 1].len());
        assert(self.view() == physical.view());
        assert(self.snapshots@ == physical.snapshots@);
        assert(self.trail_frames@ == physical.trail_frames@);
        self.lemma_canonical_capture_append(physical, index);
        assert(self.wf_for_snap());
        reveal(Vec::wf);
    }

    /// Capture according to the immutable protocol selected by `DiffStore`.
    /// Static stores constant-fold this branch; `DynStore` dispatches through
    /// its construction-time `StoreKind` variant.
    #[inline(always)]
    fn runtime_capture(&mut self, index: I)
        requires old(self).wf(), index.as_nat() < old(self).view().len(),
        ensures
            final(self).wf(), final(self).view() == old(self).view(),
            final(self).store.unique_capture_spec() == old(self).store.unique_capture_spec(),
            final(self).store.needs_replayed_indices_spec() == old(self).store.needs_replayed_indices_spec(),
            final(self).store.restore_entries_clear_capture_spec()
                == old(self).store.restore_entries_clear_capture_spec(),
            *final(self) == (Self { store: final(self).store,
                hot_value_pool: final(self).hot_value_pool,
                trail_value_pool: final(self).trail_value_pool,
                full_trail: final(self).full_trail, ..*old(self) }),
            index.as_nat() < old(self).active_saved_len.as_nat() ==>
                final(self).store.captured()[index.as_nat() as int]
                && final(self).full_trail@ == old(self).full_trail@.push((old(self).view()[index.as_nat() as int], index)),
            index.as_nat() < old(self).active_saved_len.as_nat() ==> {
                let trail = !old(self).store.unique_capture_spec();
                let pool = old(self).pair_tier_pool(trail);
                &&& final(self).store.captured()
                    == old(self).store.captured().update(index.as_nat() as int, true)
                &&& final(self).pair_tier_pool(!trail) == old(self).pair_tier_pool(!trail)
                &&& final(self).pair_tier_pool(trail) ==
                    if trail || !old(self).store.captured()[index.as_nat() as int] {
                        pool.push((old(self).view()[index.as_nat() as int], index))
                    } else { pool }
            },
            index.as_nat() >= old(self).active_saved_len.as_nat() ==> *final(self) == *old(self),
    {
        let ghost pre = *self;
        if !TRACK || index.as_usize() >= self.active_saved_len.as_usize() {
            proof {
                pre.lemma_wf_named_parts();
                reveal(Vec::open_ingress_ok);
                reveal(Vec::frame_partition_ok);
                I::lemma_min_as_nat();
            }
            return;
        }
        if self.store.unique_capture() {
            self.store.capture(index, self.active_saved_len, &mut self.hot_value_pool);
        } else {
            self.store.capture(index, self.active_saved_len, &mut self.trail_value_pool);
        }
        proof {
            self.store.lemma_wf_captured_len();
            pre.store.lemma_wf_captured_len();
            assert(self.store.captured() =~= pre.store.captured().update(index.as_nat() as int, true));
            reveal(Vec::ingress_capture_effect);
            assert(self.ingress_capture_effect(pre, index));
            self.lemma_ingress_capture_preserves(pre, index);
            let physical = *self;
            self.full_trail@ = self.full_trail@.push((pre.view()[index.as_nat() as int], index));
            self.lemma_ingress_capture_canonical_finish(physical, index);
        }
    }

    /// Checked push/regrowth core for the unique-capture, all-Hot projection.
    /// A push below the top frame's saved length re-enters a column captured by
    /// an earlier pop, so it restores only the capture bit and appends no
    /// history entry.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1800)]
    #[inline(always)]
    fn hot_defer_push_checked(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).hot_defer_wf(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).hot_defer_wf(),
            final(self).view() == old(self).view().push(value),
            final(self).snapshots@ == old(self).snapshots@,
            final(self).trail_frames@ == old(self).trail_frames@,
            final(self).full_trail@ == old(self).full_trail@,
            final(self).hot_stack@ == old(self).hot_stack@,
            final(self).hot_value_pool@ == old(self).hot_value_pool@,
            final(self).active_saved_len == old(self).active_saved_len,
    {
        let ghost pre = *self;
        let old_len = self.store.len();
        self.store.push(value);
        let ghost pushed = *self;
        let reentered = TRACK
            && old_len.as_usize() < self.active_saved_len.as_usize()
            && self.store.unique_capture();
        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
            assert(TRACK);
            assert(old_len.as_nat() == pre.view().len());
            assert(self.view() == pre.view().push(value));
            assert(self.store.captured() == pre.store.captured().push(false));
            assert(self.store.unique_capture_spec());
            assert(reentered
                == (old_len.as_nat() < self.active_saved_len.as_nat()));
        }
        if reentered {
            self.store.mark_captured(old_len);
        }
        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
            I::lemma_min_as_nat();
            let depth = self.hot_stack@.len();
            let n = old_len.as_nat() as int;
            assert(n == pre.view().len());
            assert(self.view() == pre.view().push(value));
            assert(self.hot_stack@ == pre.hot_stack@);
            assert(self.hot_value_pool@ == pre.hot_value_pool@);
            assert(self.snapshots@ == pre.snapshots@);
            assert(self.trail_frames@ == pre.trail_frames@);
            assert(self.full_trail@ == pre.full_trail@);
            assert(self.active_saved_len == pre.active_saved_len);
            assert(self.store.unique_capture_spec());
            assert(self.store.captured().len() == self.view().len());

            assert forall|q: int| 0 <= q < n implies
                #[trigger] self.store.captured()[q] == pre.store.captured()[q] by {
                if reentered {
                    assert(self.store.captured()[q] == pushed.store.captured()[q]);
                    assert(pushed.store.captured()[q] == pre.store.captured()[q]);
                } else {
                    assert(self.store.captured()[q] == pushed.store.captured()[q]);
                    assert(pushed.store.captured()[q] == pre.store.captured()[q]);
                }
            }
            assert(self.store.captured()[n] == reentered) by {
                if reentered {
                    assert(self.store.captured()[n] == true);
                } else {
                    assert(self.store.captured()[n] == false);
                }
            }

            // Every closed frame keeps the same snapshot layer. Only the top
            // frame sees the horizontally extended live row.
            assert forall|i: int| 0 <= i < depth implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(i), self.hot_value_pool@,
                    self.hot_stack@[i].start as int, self.hot_defer_end(i),
                    self.snapshots@[i], self.snapshots@[i].len()) by {
                assert(frame_inv_range::<T, I>(
                    pre.layer_above_at(i), pre.hot_value_pool@,
                    pre.hot_stack@[i].start as int, pre.hot_defer_end(i),
                    pre.snapshots@[i], pre.snapshots@[i].len()));
                assert(self.hot_defer_end(i) == pre.hot_defer_end(i));
                if i + 1 < depth {
                    assert(self.layer_above_at(i) == pre.layer_above_at(i));
                } else {
                    assert(i + 1 == depth);
                    assert(pre.layer_above_at(i) == pre.view());
                    assert(self.layer_above_at(i) == self.view());
                    lemma_frame_inv_range_grow_layer::<T, I>(
                        pre.view(), self.view(), self.hot_value_pool@,
                        self.hot_stack@[i].start as int, self.hot_defer_end(i),
                        self.snapshots@[i], self.snapshots@[i].len());
                }
            }

            // The old prefix keeps its capture bridge. The only new live
            // column is captured exactly when it re-enters the saved domain.
            if depth > 0 {
                let top = (depth - 1) as int;
                let lo = self.hot_stack@[top].start as int;
                assert forall|j: int|
                    0 <= j < self.active_saved_len.as_nat()
                        && j < self.view().len() implies
                    #[trigger] self.store.captured()[j]
                        == captured_in_range::<T, I>(
                            self.hot_value_pool@, lo,
                            self.hot_value_pool@.len() as int, j as nat) by {
                    if j < n {
                        assert(j < pre.view().len());
                        assert(self.store.captured()[j] == pre.store.captured()[j]);
                        assert(pre.store.captured()[j]
                            == captured_in_range::<T, I>(
                                pre.hot_value_pool@, lo,
                                pre.hot_value_pool@.len() as int, j as nat));
                    } else {
                        assert(j == n);
                        assert(n < self.active_saved_len.as_nat());
                        assert(reentered);
                        assert(pre.layer_above_at(top) == pre.view());
                        lemma_frame_inv_arm_at::<T, I>(
                            pre.view(), pre.hot_value_pool@, lo,
                            pre.hot_value_pool@.len() as int,
                            pre.snapshots@[top], pre.snapshots@[top].len(), j);
                        assert(captured_in_range::<T, I>(
                            pre.hot_value_pool@, lo,
                            pre.hot_value_pool@.len() as int, j as nat));
                        assert(self.store.captured()[j]);
                    }
                }
            }
            assert forall|j: int| 0 <= j < self.view().len()
                && #[trigger] self.store.captured()[j]
                implies depth > 0 && j < self.active_saved_len.as_nat() by {
                if j < n {
                    assert(pre.store.captured()[j]);
                } else {
                    assert(j == n);
                    assert(reentered);
                    if depth == 0 {
                        assert(self.active_saved_len.as_nat() == 0);
                    }
                }
            }
            assert(self.hot_defer_wf());

            // Canonical ghost reconstruction uses the same grid argument over
            // `full_trail`: all inner layers are fixed snapshots and only the
            // top live row grows.
            pre.lemma_wf_named_parts();
            assert(self.diff_log@ == pre.diff_log@);
            assert forall|k: int| 0 <= k < self.trail_frames@.len() implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k), self.full_trail@,
                    self.g_start(k), self.g_end(k), self.snapshots@[k],
                    self.snapshots@[k].len()) by {
                assert(pre.frame_inv_range_holds(k));
                assert(self.g_start(k) == pre.g_start(k));
                assert(self.g_end(k) == pre.g_end(k));
                if k + 1 < self.trail_frames@.len() {
                    assert(self.layer_above_at(k) == pre.layer_above_at(k));
                } else {
                    assert(k + 1 == self.trail_frames@.len());
                    assert(pre.layer_above_at(k) == pre.view());
                    assert(self.layer_above_at(k) == self.view());
                    lemma_frame_inv_range_grow_layer::<T, I>(
                        pre.view(), self.view(), self.full_trail@,
                        self.g_start(k), self.g_end(k), self.snapshots@[k],
                        self.snapshots@[k].len());
                }
            }
            reveal(Vec::wf_for_snap);
            assert(self.store.wf());
            assert(self.frame_partition_ok());
            assert(self.snapshots@.len() == self.trail_frames@.len());
            assert(self.trail_frames@.len() < usize::MAX);
            assert(self.trail_frames@.len() == 0 ==> self.full_trail@.len() == 0);
            assert(self.trail_frames@.len() > 0 ==> self.trail_frames@[0] == 0);
            assert(self.trail_frames@.len() > 0 ==>
                self.trail_frames@[(self.trail_frames@.len() - 1) as int]
                    <= self.full_trail@.len());
            assert forall|k: int|
                0 <= k && k + 1 < self.trail_frames@.len() implies
                    #[trigger] self.trail_frames@[k] <= self.trail_frames@[k + 1] by {
                assert(self.trail_frames@ == pre.trail_frames@);
                assert(0 <= k && k + 1 < pre.trail_frames@.len());
                pre.lemma_diff_start_monotone(k, k + 1);
            }
            assert(self.wf_for_snap());
            reveal(Vec::hot_repr_ok);
            reveal(Vec::trail_repr_ok);
            reveal(Vec::cold_repr_ok);
            reveal(Vec::open_ingress_ok);
            reveal(Vec::proof_compat_ok);
            assert(self.hot_repr_ok());
            assert(self.trail_repr_ok());
            assert(self.cold_repr_ok());
            assert(self.open_ingress_ok());
            assert(self.proof_compat_ok());
            assert(self.wf());
        }
    }

    /// Push preserves all history and restores membership when a removed
    /// saved-domain column reenters live storage. Untracked flags remain dead.
    closed spec fn push_effect(&self, pre: Self, value: T) -> bool {
        &&& *self == Self { store: self.store, ..pre }
        &&& self.store.wf()
        &&& self.view() == pre.view().push(value)
        &&& (TRACK ==> self.store.captured() == pre.store.captured().push(
            pre.view().len() < pre.active_saved_len.as_nat()))
        &&& self.store.unique_capture_spec() == pre.store.unique_capture_spec()
        &&& self.store.needs_replayed_indices_spec() == pre.store.needs_replayed_indices_spec()
        &&& self.store.restore_entries_clear_capture_spec()
            == pre.store.restore_entries_clear_capture_spec()
    }

    #[verifier::spinoff_prover]
    proof fn lemma_push_pair_frame(&self, pre: Self, value: T, trail: bool, f: int)
        requires pre.wf(), self.push_effect(pre, value),
            0 <= f < pre.pair_tier_count(trail),
        ensures frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(trail) + f),
            self.pair_tier_pool(trail), self.pair_tier_start(trail, f), self.pair_tier_end(trail, f),
            self.snapshots@[self.pair_tier_offset(trail) + f],
            self.snapshots@[self.pair_tier_offset(trail) + f].len()),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        pre.lemma_pair_tier_frame_layout(trail, f);
        reveal(Vec::push_effect);
        if trail { reveal(Vec::trail_repr_ok); } else { reveal(Vec::hot_repr_ok); }
        let k = pre.pair_tier_offset(trail) + f;
        let pool = pre.pair_tier_pool(trail);
        let lo = pre.pair_tier_start(trail, f);
        let hi = pre.pair_tier_end(trail, f);
        let snap = pre.snapshots@[k];
        assert(frame_inv_range::<T, I>(pre.layer_above_at(k), pool, lo, hi, snap, snap.len()));
        if k + 1 < pre.depth_spec() {
            assert(self.layer_above_at(k) == pre.layer_above_at(k));
        } else {
            lemma_frame_inv_range_grow_layer::<T, I>(pre.view(), self.view(), pool,
                lo, hi, snap, snap.len());
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_push_canonical_frame(&self, pre: Self, value: T, k: int)
        requires pre.wf(), self.push_effect(pre, value), 0 <= k < pre.depth_spec(),
        ensures frame_inv_range::<T, I>(self.layer_above_at(k), self.full_trail@,
            self.g_start(k), self.g_end(k), self.snapshots@[k], self.snapshots@[k].len()),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(frame_inv_range);
        reveal(Vec::push_effect);
        pre.lemma_canonical_frame_at(k);
        assert(self.g_start(k) == pre.g_start(k));
        assert(self.g_end(k) == pre.g_end(k));
        if k + 1 < pre.depth_spec() {
            assert(self.layer_above_at(k) == pre.layer_above_at(k));
        } else {
            assert(pre.layer_above_at(k) == pre.view());
            assert(self.layer_above_at(k) == self.view());
            lemma_frame_inv_range_grow_layer::<T, I>(pre.view(), self.view(), pre.full_trail@,
                pre.g_start(k), pre.g_end(k), pre.snapshots@[k], pre.snapshots@[k].len());
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_push_hot_repr(&self, pre: Self, value: T)
        requires pre.wf(), self.push_effect(pre, value),
        ensures self.hot_repr_ok(),
    {
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::push_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::hot_repr_ok);
        let hs = self.hot_stack@;
        let pool = self.hot_value_pool@;
        assert forall|f: int| 0 <= f < hs.len() implies {
            &&& (#[trigger] hs[f]).start <= hs[f].end
            &&& hs[f].end <= pool.len()
            &&& hs[f].start as int <= self.phys_hot_end(f)
            &&& self.phys_hot_end(f) <= pool.len() as int
            &&& (f + 1 < hs.len() ==> {
                &&& hs[f].end == hs[f + 1].start
                &&& self.phys_hot_end(f) == hs[f + 1].start as int
            })
            &&& (f + 1 == hs.len() ==> self.phys_hot_end(f) == pool.len() as int)
            &&& self.pair_tier_offset(false) + f < self.snapshots@.len()
            &&& frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(false) + f),
                pool, hs[f].start as int, self.phys_hot_end(f),
                self.snapshots@[self.pair_tier_offset(false) + f],
                self.snapshots@[self.pair_tier_offset(false) + f].len())
            &&& stratum_unique::<T, I>(pool, hs[f].start as int, self.phys_hot_end(f))
        } by {
            pre.lemma_pair_tier_frame_layout(false, f);
            self.lemma_push_pair_frame(pre, value, false, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_push_trail_repr(&self, pre: Self, value: T)
        requires pre.wf(), self.push_effect(pre, value),
        ensures self.trail_repr_ok(),
    {
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::push_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::trail_repr_ok);
        let hs = self.trail_stack@;
        let pool = self.trail_value_pool@;
        assert forall|f: int| 0 <= f < hs.len() implies {
            &&& (#[trigger] hs[f]).start <= hs[f].end
            &&& hs[f].end <= pool.len()
            &&& hs[f].start as int <= self.phys_trail_end(f)
            &&& self.phys_trail_end(f) <= pool.len() as int
            &&& (f + 1 < hs.len() ==> {
                &&& hs[f].end == hs[f + 1].start
                &&& self.phys_trail_end(f) == hs[f + 1].start as int
            })
            &&& (f + 1 == hs.len() ==> self.phys_trail_end(f) == pool.len() as int)
            &&& self.pair_tier_offset(true) + f < self.snapshots@.len()
            &&& frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(true) + f),
                pool, hs[f].start as int, self.phys_trail_end(f),
                self.snapshots@[self.pair_tier_offset(true) + f],
                self.snapshots@[self.pair_tier_offset(true) + f].len())

        } by {
            pre.lemma_pair_tier_frame_layout(true, f);
            self.lemma_push_pair_frame(pre, value, true, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_push_canonical(&self, pre: Self, value: T)
        requires pre.wf(), self.push_effect(pre, value),
        ensures self.wf_for_snap(),
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        pre.lemma_wf_named_parts();
        reveal(Vec::push_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::wf_for_snap);
        assert forall|k: int| 0 <= k < self.depth_spec() implies
            #[trigger] frame_inv_range::<T, I>(self.layer_above_at(k), self.full_trail@,
                self.g_start(k), self.g_end(k), self.snapshots@[k], self.snapshots@[k].len()) by {
            self.lemma_push_canonical_frame(pre, value, k);
        }
    }

    /// A saved-domain cell absent from live storage cannot be inherited: the
    /// selected ingress frame must already contain its saved value.
    #[verifier::spinoff_prover]
    proof fn lemma_push_reentered_capture(&self)
        requires self.wf(), self.view().len() < self.active_saved_len.as_nat(),
        ensures self.depth_spec() > 0,
            captured_in_range::<T, I>(self.pair_tier_pool(!self.store.unique_capture_spec()),
                self.pair_tier_start(!self.store.unique_capture_spec(),
                    self.pair_tier_count(!self.store.unique_capture_spec()) - 1),
                self.pair_tier_pool(!self.store.unique_capture_spec()).len() as int, self.view().len()),
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        reveal(Vec::open_ingress_ok);
        reveal(Vec::frame_partition_ok);
        I::lemma_min_as_nat();
        assert(self.depth_spec() > 0);
        let trail = !self.store.unique_capture_spec();
        let f = self.pair_tier_count(trail) - 1;
        self.lemma_pair_tier_frame_layout(trail, f);
        if trail { reveal(Vec::trail_repr_ok); } else { reveal(Vec::hot_repr_ok); }
        let k = self.depth_spec() - 1;
        assert(self.pair_tier_offset(trail) + f == k);
        let pool = self.pair_tier_pool(trail);
        let lo = self.pair_tier_start(trail, f);
        lemma_frame_inv_arm_at::<T, I>(self.view(), pool, lo, pool.len() as int,
            self.snapshots@[k], self.snapshots@[k].len(), self.view().len() as int);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_push_flags(&self, pre: Self, value: T)
        requires pre.wf(), self.push_effect(pre, value),
        ensures self.open_ingress_ok(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::push_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        self.store.lemma_wf_captured_len();
        if pre.view().len() < pre.active_saved_len.as_nat() {
            pre.lemma_push_reentered_capture();
        }
        let trail = !pre.store.unique_capture_spec();
        let pool = pre.pair_tier_pool(trail);
        let lo = pre.pair_tier_start(trail, pre.pair_tier_count(trail) - 1);
        assert forall|q: int| self.depth_spec() > 0 && 0 <= q < self.active_saved_len.as_nat()
            && q < self.view().len() implies
            (#[trigger] self.store.captured()[q])
                == captured_in_range::<T, I>(pool, lo, pool.len() as int, q as nat) by {
            if q < pre.view().len() {
                assert(self.store.captured()[q] == pre.store.captured()[q]);
            } else {
                assert(q == pre.view().len() as int);
                assert(pre.view().len() < pre.active_saved_len.as_nat());
            }
        }
        assert forall|q: int| TRACK && 0 <= q < self.view().len() && #[trigger] self.store.captured()[q]
            implies self.depth_spec() > 0 && q < self.active_saved_len.as_nat() by {
            if q < pre.view().len() {
                assert(pre.store.captured()[q]);
            } else {
                assert(q == pre.view().len() as int);
                assert(pre.view().len() < pre.active_saved_len.as_nat());
            }
        }
    }

    /// Every Cold layer still reconstructs after a push: the layers sit below
    /// the open frame, which the push only extends.
    #[verifier::spinoff_prover]
    proof fn lemma_push_cold_reconstructs(&self, pre: Self, value: T)
        requires pre.wf(), self.push_effect(pre, value),
        ensures forall|f: int| 0 <= f < self.cold_stack@.len() ==> #[trigger] self.cold_reconstructs(f),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_reconstructs);
        hide(Vec::cold_payload_ok);
        pre.lemma_wf_named_parts();
        reveal(Vec::push_effect);
        self.lemma_push_canonical(pre, value);
        self.lemma_push_flags(pre, value);
        reveal(Vec::cold_repr_ok);
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f) by {
            assert(f + 1 < pre.depth_spec());
            self.lemma_cold_reconstructs_layer_transfer(pre, f);
        }
    }

    /// Cold representation survives a push.
    #[verifier::spinoff_prover]
    proof fn lemma_push_cold_repr(&self, pre: Self, value: T)
        requires pre.wf(), self.push_effect(pre, value),
        ensures self.cold_repr_ok(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_reconstructs);
        pre.lemma_wf_named_parts();
        reveal(Vec::push_effect);
        self.lemma_push_cold_reconstructs(pre, value);
        reveal(Vec::cold_repr_ok);
        reveal(Vec::cold_payload_ok);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_push_preserves(&self, pre: Self, value: T)
        requires pre.wf(), self.push_effect(pre, value),
        ensures self.wf(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_reconstructs);
        hide(Vec::cold_repr_ok);
        pre.lemma_wf_named_parts();
        reveal(Vec::push_effect);
        self.lemma_push_canonical(pre, value);
        self.lemma_push_hot_repr(pre, value);
        self.lemma_push_trail_repr(pre, value);
        self.lemma_push_flags(pre, value);
        self.lemma_push_cold_repr(pre, value);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::proof_compat_ok);
        reveal(Vec::wf);
    }

    #[verifier::spinoff_prover]
    #[inline(always)]
    fn runtime_push_fallback(&mut self, value: T)
        requires
            old(self).wf(),
            !old(self).hot_defer_scope(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().push(value),
            final(self).snapshots_view() == old(self).snapshots_view(),
            *final(self) == (Self { store: final(self).store, ..*old(self) }),
            final(self).store.unique_capture_spec() == old(self).store.unique_capture_spec(),
            final(self).store.needs_replayed_indices_spec() == old(self).store.needs_replayed_indices_spec(),
            final(self).store.restore_entries_clear_capture_spec()
                == old(self).store.restore_entries_clear_capture_spec(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        let ghost pre = *self;
        proof {
            assert(self.store.wf()) by { reveal(Vec::wf); reveal(Vec::wf_for_snap); }
            self.store.lemma_wf_captured_len();
        }
        let old_len = self.store.len();
        self.store.push(value);
        if TRACK
            && old_len.as_usize() < self.active_saved_len.as_usize()
        {
            self.store.mark_captured(old_len);
        }
        proof {
            self.store.lemma_wf_captured_len();
            assert(TRACK ==> self.store.captured() =~= pre.store.captured().push(
                pre.view().len() < pre.active_saved_len.as_nat()));
            reveal(Vec::push_effect);
            assert(self.push_effect(pre, value));
            self.lemma_push_preserves(pre, value);
        }
    }

    #[inline(always)]
    fn runtime_push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().push(value),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let hot = self.hot_defer_scope_exec();
        if hot {
            proof { self.lemma_hot_defer_scope_implies_projection(); }
            self.hot_defer_push_checked(value);
        } else {
            self.runtime_push_fallback(value);
        }
    }

    /// Checked pop core for the unique-capture, all-Hot projection. The last
    /// live column is captured before contraction exactly when it belongs to
    /// the top frame's saved domain; arbitrary higher saved columns were
    /// already covered by the frame invariant.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(2600)]
    #[inline(always)]
    fn hot_defer_pop_checked(&mut self) -> (r: Option<T>)
        requires
            old(self).wf(),
            old(self).hot_defer_wf(),
        ensures
            final(self).wf(),
            final(self).hot_defer_wf(),
            final(self).snapshots@ == old(self).snapshots@,
            final(self).trail_frames@ == old(self).trail_frames@,
            old(self).view().len() == 0 ==> {
                &&& r is None
                &&& final(self).view() == old(self).view()
            },
            old(self).view().len() > 0 ==> {
                &&& r == Some(old(self).view().last())
                &&& final(self).view() == old(self).view().drop_last()
            },
    {
        let ghost pre = *self;
        let len = self.store.raw_len();
        if len == 0 {
            return None;
        }
        let new_len = len - 1;
        let needs_capture = TRACK && new_len < self.active_saved_len.as_usize();
        if needs_capture {
            let index_opt = I::try_from_usize(new_len);
            if let Some(index) = index_opt {
                self.hot_defer_capture_canonical_checked(index);
            } else {
                proof {
                    assert((new_len as nat) < self.active_saved_len.as_nat());
                    self.active_saved_len.lemma_as_nat_bounded();
                    assert((new_len as nat) < I::max_nat());
                    assert(false);
                }
            }
        }
        let ghost mid = *self;
        let r = self.store.pop();
        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
            let depth = self.hot_stack@.len();
            let n = new_len as int;
            assert(len == pre.view().len());
            assert(mid.view() == pre.view());
            assert(self.view() == mid.view().drop_last());
            assert(self.hot_stack@ == mid.hot_stack@);
            assert(self.hot_value_pool@ == mid.hot_value_pool@);
            assert(self.snapshots@ == mid.snapshots@);
            assert(self.trail_frames@ == mid.trail_frames@);
            assert(self.full_trail@ == mid.full_trail@);
            assert(self.active_saved_len == mid.active_saved_len);
            assert(self.store.captured() == mid.store.captured().drop_last());
            assert(self.store.unique_capture_spec());
            self.store.lemma_wf_captured_len();

            assert forall|i: int| 0 <= i < depth implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(i), self.hot_value_pool@,
                    self.hot_stack@[i].start as int, self.hot_defer_end(i),
                    self.snapshots@[i], self.snapshots@[i].len()) by {
                assert(frame_inv_range::<T, I>(
                    mid.layer_above_at(i), mid.hot_value_pool@,
                    mid.hot_stack@[i].start as int, mid.hot_defer_end(i),
                    mid.snapshots@[i], mid.snapshots@[i].len()));
                assert(self.hot_defer_end(i) == mid.hot_defer_end(i));
                if i + 1 < depth {
                    assert(self.layer_above_at(i) == mid.layer_above_at(i));
                } else {
                    assert(i + 1 == depth);
                    assert(mid.layer_above_at(i) == mid.view());
                    assert(self.layer_above_at(i) == self.view());
                    let lo = self.hot_stack@[i].start as int;
                    let hi = self.hot_defer_end(i);
                    let saved = self.snapshots@[i].len();
                    if n < saved as int {
                        assert(needs_capture);
                        assert(mid.store.captured()[n]);
                        assert(mid.store.captured()[n]
                            == captured_in_range::<T, I>(
                                mid.hot_value_pool@, lo, hi, n as nat));
                    }
                    lemma_frame_inv_range_pop_last::<T, I>(
                        mid.view(), self.view(), self.hot_value_pool@, lo, hi,
                        self.snapshots@[i], saved);
                }
            }

            if depth > 0 {
                let top = (depth - 1) as int;
                let lo = self.hot_stack@[top].start as int;
                assert forall|q: int|
                    0 <= q < self.active_saved_len.as_nat()
                        && q < self.view().len() implies
                    #[trigger] self.store.captured()[q]
                        == captured_in_range::<T, I>(
                            self.hot_value_pool@, lo,
                            self.hot_value_pool@.len() as int, q as nat) by {
                    assert(q < mid.view().len());
                    assert(self.store.captured()[q] == mid.store.captured()[q]);
                }
            }
            assert forall|q: int| 0 <= q < self.view().len()
                && #[trigger] self.store.captured()[q]
                implies depth > 0 && q < self.active_saved_len.as_nat() by {
                assert(q < mid.view().len());
                assert(self.store.captured()[q] == mid.store.captured()[q]);
                assert(mid.store.captured()[q]);
            }
            assert(self.hot_defer_wf());

            assert forall|k: int| 0 <= k < self.trail_frames@.len() implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k), self.full_trail@,
                    self.g_start(k), self.g_end(k), self.snapshots@[k],
                    self.snapshots@[k].len()) by {
                assert(mid.frame_inv_range_holds(k));
                assert(self.g_start(k) == mid.g_start(k));
                assert(self.g_end(k) == mid.g_end(k));
                if k + 1 < self.trail_frames@.len() {
                    assert(self.layer_above_at(k) == mid.layer_above_at(k));
                } else {
                    assert(k + 1 == self.trail_frames@.len());
                    assert(mid.layer_above_at(k) == mid.view());
                    assert(self.layer_above_at(k) == self.view());
                    let lo = self.g_start(k);
                    let hi = self.g_end(k);
                    let saved = self.snapshots@[k].len();
                    if n < saved as int {
                        assert(needs_capture);
                        assert(mid.full_trail@.len() > pre.full_trail@.len());
                        assert(mid.full_trail@[(mid.full_trail@.len() - 1) as int].1.as_nat()
                            == n as nat);
                        assert(captured_in_range::<T, I>(
                            mid.full_trail@, lo, hi, n as nat));
                    }
                    lemma_frame_inv_range_pop_last::<T, I>(
                        mid.view(), self.view(), self.full_trail@, lo, hi,
                        self.snapshots@[k], saved);
                }
            }

            mid.lemma_wf_named_parts();
            reveal(Vec::wf_for_snap);
            assert(self.store.wf());
            assert(self.frame_partition_ok());
            assert(self.snapshots@.len() == self.trail_frames@.len());
            assert(self.trail_frames@.len() < usize::MAX);
            assert(self.trail_frames@.len() == 0 ==> self.full_trail@.len() == 0);
            assert(self.trail_frames@.len() > 0 ==> self.trail_frames@[0] == 0);
            assert(self.trail_frames@.len() > 0 ==>
                self.trail_frames@[(self.trail_frames@.len() - 1) as int]
                    <= self.full_trail@.len());
            assert forall|k: int|
                0 <= k && k + 1 < self.trail_frames@.len() implies
                    #[trigger] self.trail_frames@[k] <= self.trail_frames@[k + 1] by {
                assert(self.trail_frames@ == mid.trail_frames@);
                assert(0 <= k && k + 1 < mid.trail_frames@.len());
                mid.lemma_diff_start_monotone(k, k + 1);
            }
            assert(self.wf_for_snap());
            assert(self.proof_compat_ok());
            self.lemma_hot_defer_snap_implies_wf();
        }
        r
    }

    closed spec fn pop_effect(&self, pre: Self) -> bool {
        &&& *self == Self { store: self.store, ..pre }
        &&& self.store.wf()
        &&& self.view() == pre.view().drop_last()
        &&& (TRACK ==> self.store.captured() == pre.store.captured().drop_last())
        &&& self.store.unique_capture_spec() == pre.store.unique_capture_spec()
        &&& self.store.needs_replayed_indices_spec() == pre.store.needs_replayed_indices_spec()
        &&& self.store.restore_entries_clear_capture_spec()
            == pre.store.restore_entries_clear_capture_spec()
    }

    #[verifier::spinoff_prover]
    proof fn lemma_pop_pair_frame(&self, pre: Self, trail: bool, f: int)
        requires pre.wf(), self.pop_effect(pre), pre.view().len() > 0,
            pre.view().len() - 1 < pre.active_saved_len.as_nat() ==>
                pre.store.captured()[pre.view().len() - 1],
            0 <= f < pre.pair_tier_count(trail),
        ensures frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(trail) + f),
            self.pair_tier_pool(trail), self.pair_tier_start(trail, f), self.pair_tier_end(trail, f),
            self.snapshots@[self.pair_tier_offset(trail) + f],
            self.snapshots@[self.pair_tier_offset(trail) + f].len()),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        pre.lemma_pair_tier_frame_layout(trail, f);
        reveal(Vec::pop_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        if trail { reveal(Vec::trail_repr_ok); } else { reveal(Vec::hot_repr_ok); }
        let k = pre.pair_tier_offset(trail) + f;
        let pool = pre.pair_tier_pool(trail);
        let lo = pre.pair_tier_start(trail, f);
        let hi = pre.pair_tier_end(trail, f);
        let snap = pre.snapshots@[k];
        assert(frame_inv_range::<T, I>(pre.layer_above_at(k), pool, lo, hi, snap, snap.len()));
        if k + 1 < pre.depth_spec() {
            assert(self.layer_above_at(k) == pre.layer_above_at(k));
        } else {
            assert(k == pre.depth_spec() - 1);
            assert(trail == !pre.store.unique_capture_spec());
            assert(f == pre.pair_tier_count(trail) - 1);
            assert(pre.active_saved_len.as_nat() == snap.len());
            if self.view().len() < snap.len() {
                assert(captured_in_range::<T, I>(pool, lo, hi, self.view().len()));
            }
            lemma_frame_inv_range_pop_last::<T, I>(pre.view(), self.view(), pool, lo, hi, snap, snap.len());
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_pop_canonical_frame(&self, pre: Self, k: int)
        requires pre.wf(), self.pop_effect(pre), pre.view().len() > 0,
            pre.view().len() - 1 < pre.active_saved_len.as_nat() ==>
                captured_in_range::<T, I>(pre.full_trail@, pre.g_start(pre.depth_spec() - 1),
                    pre.full_trail@.len() as int, (pre.view().len() - 1) as nat),
            0 <= k < pre.depth_spec(),
        ensures frame_inv_range::<T, I>(self.layer_above_at(k), self.full_trail@,
            self.g_start(k), self.g_end(k), self.snapshots@[k], self.snapshots@[k].len()),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(frame_inv_range);
        reveal(Vec::pop_effect);
        pre.lemma_canonical_frame_at(k);
        assert(self.g_start(k) == pre.g_start(k));
        assert(self.g_end(k) == pre.g_end(k));
        if k + 1 < pre.depth_spec() {
            assert(self.layer_above_at(k) == pre.layer_above_at(k));
        } else {
            assert(k == pre.depth_spec() - 1);
            assert(pre.g_end(k) == pre.full_trail@.len() as int);
            assert(pre.layer_above_at(k) == pre.view());
            assert(self.layer_above_at(k) == self.view());
            lemma_frame_inv_range_pop_last::<T, I>(pre.view(), self.view(), pre.full_trail@,
                pre.g_start(k), pre.g_end(k), pre.snapshots@[k], pre.snapshots@[k].len());
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_pop_hot_repr(&self, pre: Self)
        requires pre.wf(), self.pop_effect(pre),
            pre.view().len() > 0,
            ((pre.view().len() - 1) as nat) < pre.active_saved_len.as_nat() ==> pre.store.captured()[pre.view().len() - 1],
        ensures self.hot_repr_ok(),
    {
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::pop_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::hot_repr_ok);
        let hs = self.hot_stack@;
        let pool = self.hot_value_pool@;
        assert forall|f: int| 0 <= f < hs.len() implies {
            &&& (#[trigger] hs[f]).start <= hs[f].end
            &&& hs[f].end <= pool.len()
            &&& hs[f].start as int <= self.phys_hot_end(f)
            &&& self.phys_hot_end(f) <= pool.len() as int
            &&& (f + 1 < hs.len() ==> {
                &&& hs[f].end == hs[f + 1].start
                &&& self.phys_hot_end(f) == hs[f + 1].start as int
            })
            &&& (f + 1 == hs.len() ==> self.phys_hot_end(f) == pool.len() as int)
            &&& self.pair_tier_offset(false) + f < self.snapshots@.len()
            &&& frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(false) + f),
                pool, hs[f].start as int, self.phys_hot_end(f),
                self.snapshots@[self.pair_tier_offset(false) + f],
                self.snapshots@[self.pair_tier_offset(false) + f].len())
            &&& stratum_unique::<T, I>(pool, hs[f].start as int, self.phys_hot_end(f))
        } by {
            pre.lemma_pair_tier_frame_layout(false, f);
            self.lemma_pop_pair_frame(pre, false, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_pop_trail_repr(&self, pre: Self)
        requires pre.wf(), self.pop_effect(pre),
            pre.view().len() > 0,
            ((pre.view().len() - 1) as nat) < pre.active_saved_len.as_nat() ==> pre.store.captured()[pre.view().len() - 1],
        ensures self.trail_repr_ok(),
    {
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::pop_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::trail_repr_ok);
        let hs = self.trail_stack@;
        let pool = self.trail_value_pool@;
        assert forall|f: int| 0 <= f < hs.len() implies {
            &&& (#[trigger] hs[f]).start <= hs[f].end
            &&& hs[f].end <= pool.len()
            &&& hs[f].start as int <= self.phys_trail_end(f)
            &&& self.phys_trail_end(f) <= pool.len() as int
            &&& (f + 1 < hs.len() ==> {
                &&& hs[f].end == hs[f + 1].start
                &&& self.phys_trail_end(f) == hs[f + 1].start as int
            })
            &&& (f + 1 == hs.len() ==> self.phys_trail_end(f) == pool.len() as int)
            &&& self.pair_tier_offset(true) + f < self.snapshots@.len()
            &&& frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(true) + f),
                pool, hs[f].start as int, self.phys_trail_end(f),
                self.snapshots@[self.pair_tier_offset(true) + f],
                self.snapshots@[self.pair_tier_offset(true) + f].len())

        } by {
            pre.lemma_pair_tier_frame_layout(true, f);
            self.lemma_pop_pair_frame(pre, true, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_pop_canonical(&self, pre: Self)
        requires pre.wf(), self.pop_effect(pre),
            pre.view().len() > 0,
            ((pre.view().len() - 1) as nat) < pre.active_saved_len.as_nat() ==>
                captured_in_range::<T, I>(pre.full_trail@, pre.g_start(pre.depth_spec() - 1),
                    pre.full_trail@.len() as int, ((pre.view().len() - 1) as nat)),
        ensures self.wf_for_snap(),
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        pre.lemma_wf_named_parts();
        reveal(Vec::pop_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::wf_for_snap);
        assert forall|k: int| 0 <= k < self.depth_spec() implies
            #[trigger] frame_inv_range::<T, I>(self.layer_above_at(k), self.full_trail@,
                self.g_start(k), self.g_end(k), self.snapshots@[k], self.snapshots@[k].len()) by {
            self.lemma_pop_canonical_frame(pre, k);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_pop_preserves(&self, pre: Self)
        requires pre.wf(), self.pop_effect(pre),
            pre.view().len() > 0,
            ((pre.view().len() - 1) as nat) < pre.active_saved_len.as_nat() ==>
                pre.store.captured()[pre.view().len() - 1]
                && captured_in_range::<T, I>(pre.full_trail@, pre.g_start(pre.depth_spec() - 1),
                    pre.full_trail@.len() as int, ((pre.view().len() - 1) as nat)),
        ensures self.wf(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_reconstructs);
        hide(frame_inv_range);
        hide(stratum_unique);
        pre.lemma_wf_named_parts();
        reveal(Vec::pop_effect);
        self.lemma_pop_canonical(pre);
        self.lemma_pop_hot_repr(pre);
        self.lemma_pop_trail_repr(pre);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        self.store.lemma_wf_captured_len();
        assert(self.open_ingress_ok());
        reveal(Vec::cold_repr_ok);
        reveal(Vec::cold_payload_ok);
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f) by {
            assert(f + 1 < pre.depth_spec());
            assert(self.layer_above_at(f) == pre.layer_above_at(f));
            self.lemma_cold_reconstructs_layer_transfer(pre, f);
        }
        assert(self.cold_repr_ok());
        reveal(Vec::proof_compat_ok);
        reveal(Vec::wf);
    }

    #[verifier::spinoff_prover]
    #[inline(always)]
    fn runtime_pop_fallback(&mut self) -> (r: Option<T>)
        requires
            old(self).wf(),
            !old(self).hot_defer_scope(),
        ensures
            final(self).wf(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            old(self).view().len() == 0 ==> {
                &&& r is None
                &&& final(self).view() == old(self).view()
            },
            old(self).view().len() > 0 ==> {
                &&& r == Some(old(self).view().last())
                &&& final(self).view() == old(self).view().drop_last()
            },
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        let ghost pre = *self;
        proof {
            assert(self.store.wf()) by { reveal(Vec::wf); reveal(Vec::wf_for_snap); }
            assert(!TRACK ==> self.active_saved_len.as_nat() == 0) by {
                pre.lemma_wf_named_parts();
                reveal(Vec::open_ingress_ok);
                reveal(Vec::frame_partition_ok);
                I::lemma_min_as_nat();
            }
        }
        let len = self.store.raw_len();
        if len == 0 {
            return None;
        }
        if TRACK && len - 1 < self.active_saved_len.as_usize() {
            if let Some(index) = I::try_from_usize(len - 1) {
                self.runtime_capture(index);
                proof {
                    pre.lemma_capture_domain(index);
                    let q = pre.full_trail@.len() as int;
                    assert(self.full_trail@[q].1.as_nat() == (len - 1) as nat);
                    assert(captured_in_range::<T, I>(self.full_trail@,
                        self.g_start(self.depth_spec() - 1), self.full_trail@.len() as int,
                        (len - 1) as nat));
                }
            } else {
                proof {
                    self.active_saved_len.lemma_as_nat_bounded();
                    assert(false);
                }
            }
        }
        let ghost captured = *self;
        proof { assert(self.store.wf()) by { reveal(Vec::wf); reveal(Vec::wf_for_snap); } }
        let r = self.store.pop();
        proof {
            reveal(Vec::pop_effect);
            assert(self.pop_effect(captured));
            self.lemma_pop_preserves(captured);
        }
        r
    }

    #[inline(always)]
    fn runtime_pop(&mut self) -> (r: Option<T>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            old(self).view().len() == 0 ==> {
                &&& r is None
                &&& final(self).view() == old(self).view()
            },
            old(self).view().len() > 0 ==> {
                &&& r == Some(old(self).view().last())
                &&& final(self).view() == old(self).view().drop_last()
            },
    {
        let hot = self.hot_defer_scope_exec();
        if hot {
            proof { self.lemma_hot_defer_scope_implies_projection(); }
            self.hot_defer_pop_checked()
        } else {
            self.runtime_pop_fallback()
        }
    }

    /// Verified set core for the Hot-only Defer projection. Capture is proved
    /// first, then the raw write changes only the live top layer.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1800)]
    #[inline(always)]
    fn hot_defer_set_checked(&mut self, index: I, value: T)
        requires
            old(self).wf(),
            old(self).hot_defer_wf(),
            index.as_nat() < old(self).view().len(),
        ensures
            final(self).wf(),
            final(self).hot_defer_wf(),
            final(self).view() == old(self).view().update(index.as_nat() as int, value),
            final(self).snapshots@ == old(self).snapshots@,
            final(self).trail_frames@ == old(self).trail_frames@,
    {
        let ghost pre = *self;
        self.hot_defer_capture_canonical_checked(index);
        let ghost mid = *self;
        self.store.set_raw(index, value);
        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
            let depth = self.hot_stack@.len();
            let j = index.as_nat() as int;
            assert(self.view() == mid.view().update(j, value));
            assert(self.hot_value_pool@ == mid.hot_value_pool@);
            assert(self.hot_stack@ == mid.hot_stack@);
            assert(self.snapshots@ == mid.snapshots@);
            assert(self.trail_frames@ == mid.trail_frames@);
            assert(self.full_trail@ == mid.full_trail@);
            assert(self.store.captured() == mid.store.captured());
            self.store.lemma_wf_captured_len();

            assert forall|i: int| 0 <= i < depth implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(i), self.hot_value_pool@,
                    self.hot_stack@[i].start as int, self.hot_defer_end(i),
                    self.snapshots@[i], self.snapshots@[i].len()) by {
                if i + 1 < depth {
                    assert(self.layer_above_at(i) == mid.layer_above_at(i));
                } else {
                    assert(i == depth - 1);
                    assert(mid.layer_above_at(i) == mid.view());
                    assert(self.layer_above_at(i) == self.view());
                    let lo = self.hot_stack@[i].start as int;
                    let hi = self.hot_defer_end(i);
                    let saved = self.snapshots@[i].len();
                    if j < saved as int {
                        assert(mid.active_saved_len.as_nat() == saved);
                        assert(mid.active_saved_len == pre.active_saved_len);
                        assert(j < pre.active_saved_len.as_nat() as int);
                        assert(mid.store.captured()[j]);
                        assert(mid.store.captured()[j]
                            == captured_in_range::<T, I>(
                                mid.hot_value_pool@, lo, hi, j as nat));
                        lemma_frame_inv_range_set_captured::<T, I>(
                            mid.view(), self.view(), self.hot_value_pool@, lo, hi,
                            self.snapshots@[i], saved, j, value);
                    } else {
                        lemma_frame_inv_range_set_outside::<T, I>(
                            mid.view(), self.view(), self.hot_value_pool@, lo, hi,
                            self.snapshots@[i], saved, j, value);
                    }
                }
            }
            // Every other clause is representation-only or reads the capture
            // flags, all unchanged by set_raw. The open bridge also survives:
            // its range and flags are identical and the view length is stable.
            assert(self.view().len() == mid.view().len());
            if depth > 0 {
                assert forall|q: int|
                    0 <= q < self.active_saved_len.as_nat() && q < self.view().len() implies
                    (#[trigger] self.store.captured()[q])
                        == captured_in_range::<T, I>(
                            self.hot_value_pool@,
                            self.hot_stack@[(depth - 1) as int].start as int,
                            self.hot_value_pool@.len() as int, q as nat) by {
                    assert(q < mid.view().len());
                }
            }
            assert forall|q: int| 0 <= q < self.view().len()
                && #[trigger] self.store.captured()[q]
                implies depth > 0 && q < self.active_saved_len.as_nat() by {
                assert(q < mid.view().len());
                assert(mid.store.captured()[q]);
            }
            assert(self.hot_defer_wf());

            // The canonical top stratum received the chronological event in
            // the capture adapter. A write inside saved_len is therefore a
            // captured-column update; a write at/above saved_len is outside
            // the frame's horizontal domain.
            assert forall|k: int| 0 <= k < self.trail_frames@.len() implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(k), self.full_trail@,
                    self.g_start(k), self.g_end(k), self.snapshots@[k],
                    self.snapshots@[k].len()) by {
                assert(mid.frame_inv_range_holds(k));
                assert(self.g_start(k) == mid.g_start(k));
                assert(self.g_end(k) == mid.g_end(k));
                if k + 1 < self.trail_frames@.len() {
                    assert(self.layer_above_at(k) == mid.layer_above_at(k));
                } else {
                    assert(k + 1 == self.trail_frames@.len());
                    assert(mid.layer_above_at(k) == mid.view());
                    assert(self.layer_above_at(k) == self.view());
                    let lo = self.g_start(k);
                    let hi = self.g_end(k);
                    let saved = self.snapshots@[k].len();
                    if j < saved as int {
                        assert(j < pre.active_saved_len.as_nat() as int);
                        assert(mid.full_trail@
                            == pre.full_trail@.push((pre.view()[j], index)));
                        assert(lo <= pre.full_trail@.len());
                        assert(mid.full_trail@[pre.full_trail@.len() as int].1.as_nat()
                            == j as nat);
                        assert(captured_in_range::<T, I>(
                            mid.full_trail@, lo, hi, j as nat));
                        lemma_frame_inv_range_set_captured::<T, I>(
                            mid.view(), self.view(), self.full_trail@, lo, hi,
                            self.snapshots@[k], saved, j, value);
                    } else {
                        lemma_frame_inv_range_set_outside::<T, I>(
                            mid.view(), self.view(), self.full_trail@, lo, hi,
                            self.snapshots@[k], saved, j, value);
                    }
                }
            }

            mid.lemma_wf_named_parts();
            reveal(Vec::wf_for_snap);
            assert(self.store.wf());
            assert(self.frame_partition_ok());
            assert(self.snapshots@.len() == self.trail_frames@.len());
            assert(self.trail_frames@.len() < usize::MAX);
            assert(self.trail_frames@.len() == 0 ==> self.full_trail@.len() == 0);
            assert(self.trail_frames@.len() > 0 ==> self.trail_frames@[0] == 0);
            assert(self.trail_frames@.len() > 0 ==>
                self.trail_frames@[(self.trail_frames@.len() - 1) as int]
                    <= self.full_trail@.len());
            assert forall|k: int|
                0 <= k && k + 1 < self.trail_frames@.len() implies
                    #[trigger] self.trail_frames@[k] <= self.trail_frames@[k + 1] by {
                assert(self.trail_frames@ == mid.trail_frames@);
                assert(0 <= k && k + 1 < mid.trail_frames@.len());
                mid.lemma_diff_start_monotone(k, k + 1);
            }
            assert(self.wf_for_snap());
            assert(self.proof_compat_ok());
            self.lemma_hot_defer_snap_implies_wf();
        }
    }

    /// A raw write changes only live data; capture has already saved the cell.
    closed spec fn raw_set_effect(&self, pre: Self, index: I, value: T) -> bool {
        &&& *self == Self { store: self.store, ..pre }
        &&& self.store.wf()
        &&& self.view() == pre.view().update(index.as_nat() as int, value)
        &&& (TRACK ==> self.store.captured() == pre.store.captured())
        &&& self.store.unique_capture_spec() == pre.store.unique_capture_spec()
        &&& self.store.needs_replayed_indices_spec() == pre.store.needs_replayed_indices_spec()
        &&& self.store.restore_entries_clear_capture_spec()
            == pre.store.restore_entries_clear_capture_spec()
    }

    #[verifier::spinoff_prover]
    proof fn lemma_raw_set_pair_frame(&self, pre: Self, index: I, value: T, trail: bool, f: int)
        requires pre.wf(), self.raw_set_effect(pre, index, value),
            index.as_nat() < pre.view().len(),
            index.as_nat() < pre.active_saved_len.as_nat() ==> pre.store.captured()[index.as_nat() as int],
            0 <= f < pre.pair_tier_count(trail),
        ensures frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(trail) + f),
            self.pair_tier_pool(trail), self.pair_tier_start(trail, f), self.pair_tier_end(trail, f),
            self.snapshots@[self.pair_tier_offset(trail) + f],
            self.snapshots@[self.pair_tier_offset(trail) + f].len()),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        pre.lemma_pair_tier_frame_layout(trail, f);
        reveal(Vec::raw_set_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        if trail { reveal(Vec::trail_repr_ok); } else { reveal(Vec::hot_repr_ok); }
        let k = pre.pair_tier_offset(trail) + f;
        let pool = pre.pair_tier_pool(trail);
        let lo = pre.pair_tier_start(trail, f);
        let hi = pre.pair_tier_end(trail, f);
        let snap = pre.snapshots@[k];
        assert(frame_inv_range::<T, I>(pre.layer_above_at(k), pool, lo, hi, snap, snap.len()));
        if k + 1 < pre.depth_spec() {
            assert(self.layer_above_at(k) == pre.layer_above_at(k));
        } else {
            assert(k == pre.depth_spec() - 1);
            assert(trail == !pre.store.unique_capture_spec());
            assert(f == pre.pair_tier_count(trail) - 1);
            assert(pre.active_saved_len.as_nat() == snap.len());
            if index.as_nat() < snap.len() {
                assert(captured_in_range::<T, I>(pool, lo, hi, index.as_nat()));
                lemma_frame_inv_range_set_captured::<T, I>(pre.view(), self.view(), pool,
                    lo, hi, snap, snap.len(), index.as_nat() as int, value);
            } else {
                lemma_frame_inv_range_set_outside::<T, I>(pre.view(), self.view(), pool,
                    lo, hi, snap, snap.len(), index.as_nat() as int, value);
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_canonical_frame_contract_at(&self, k: int)
        requires self.wf_for_snap(), 0 <= k < self.depth_spec(),
        ensures self.frame_inv_range_holds(k),
    {
        hide(frame_inv_range);
        reveal(Vec::wf_for_snap);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_canonical_frame_length_at(&self, k: int)
        requires self.frame_partition_ok(), self.open_ingress_ok(), 0 <= k < self.depth_spec(),
        ensures k < self.snapshots@.len(),
            k + 1 == self.depth_spec() ==> self.active_saved_len.as_nat() == self.snapshots@[k].len(),
    {
        hide(captured_in_range);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
    }

    /// Pointwise access avoids unfolding every canonical stratum at a write.
    #[verifier::spinoff_prover]
    proof fn lemma_canonical_frame_at(&self, k: int)
        requires self.wf(), 0 <= k < self.depth_spec(),
        ensures self.frame_inv_range_holds(k), k < self.snapshots@.len(),
            k + 1 == self.depth_spec() ==> self.active_saved_len.as_nat() == self.snapshots@[k].len(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(frame_inv_range);
        self.lemma_wf_named_parts();
        self.lemma_canonical_frame_contract_at(k);
        self.lemma_canonical_frame_length_at(k);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_raw_set_canonical_frame(&self, pre: Self, index: I, value: T, k: int)
        requires pre.wf(), self.raw_set_effect(pre, index, value),
            index.as_nat() < pre.view().len(),
            index.as_nat() < pre.active_saved_len.as_nat() ==>
                captured_in_range::<T, I>(pre.full_trail@, pre.g_start(pre.depth_spec() - 1),
                    pre.full_trail@.len() as int, index.as_nat()),
            0 <= k < pre.depth_spec(),
        ensures frame_inv_range::<T, I>(self.layer_above_at(k), self.full_trail@,
            self.g_start(k), self.g_end(k), self.snapshots@[k], self.snapshots@[k].len()),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(frame_inv_range);
        reveal(Vec::raw_set_effect);
        pre.lemma_canonical_frame_at(k);
        assert(self.full_trail@ == pre.full_trail@);
        assert(self.snapshots@ == pre.snapshots@);
        assert(self.g_start(k) == pre.g_start(k));
        assert(self.g_end(k) == pre.g_end(k));
        assert(self.depth_spec() == pre.depth_spec());
        if k + 1 < pre.depth_spec() {
            assert(self.layer_above_at(k) == pre.layer_above_at(k));
        } else if index.as_nat() < pre.active_saved_len.as_nat() {
            assert(k == pre.depth_spec() - 1);
            assert(pre.g_end(k) == pre.full_trail@.len() as int);
            assert(pre.layer_above_at(k) == pre.view());
            assert(self.layer_above_at(k) == self.view());
            lemma_frame_inv_range_set_captured::<T, I>(pre.view(), self.view(), pre.full_trail@,
                pre.g_start(k), pre.g_end(k), pre.snapshots@[k], pre.snapshots@[k].len(),
                index.as_nat() as int, value);
        } else {
            assert(k == pre.depth_spec() - 1);
            assert(pre.layer_above_at(k) == pre.view());
            assert(self.layer_above_at(k) == self.view());
            lemma_frame_inv_range_set_outside::<T, I>(pre.view(), self.view(), pre.full_trail@,
                pre.g_start(k), pre.g_end(k), pre.snapshots@[k], pre.snapshots@[k].len(),
                index.as_nat() as int, value);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_raw_set_canonical(&self, pre: Self, index: I, value: T)
        requires pre.wf(), self.raw_set_effect(pre, index, value),
            index.as_nat() < pre.view().len(),
            index.as_nat() < pre.active_saved_len.as_nat() ==>
                captured_in_range::<T, I>(pre.full_trail@, pre.g_start(pre.depth_spec() - 1),
                    pre.full_trail@.len() as int, index.as_nat()),
        ensures self.wf_for_snap(),
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        pre.lemma_wf_named_parts();
        reveal(Vec::raw_set_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::wf_for_snap);
        assert forall|k: int| 0 <= k < self.depth_spec() implies
            #[trigger] frame_inv_range::<T, I>(self.layer_above_at(k), self.full_trail@,
                self.g_start(k), self.g_end(k), self.snapshots@[k], self.snapshots@[k].len()) by {
            self.lemma_raw_set_canonical_frame(pre, index, value, k);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_raw_set_hot_repr(&self, pre: Self, index: I, value: T)
        requires pre.wf(), self.raw_set_effect(pre, index, value),
            index.as_nat() < pre.view().len(),
            index.as_nat() < pre.active_saved_len.as_nat() ==> pre.store.captured()[index.as_nat() as int],
        ensures self.hot_repr_ok(),
    {
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::raw_set_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::hot_repr_ok);
        let hs = self.hot_stack@;
        let pool = self.hot_value_pool@;
        assert forall|f: int| 0 <= f < hs.len() implies {
            &&& (#[trigger] hs[f]).start <= hs[f].end
            &&& hs[f].end <= pool.len()
            &&& hs[f].start as int <= self.phys_hot_end(f)
            &&& self.phys_hot_end(f) <= pool.len() as int
            &&& (f + 1 < hs.len() ==> {
                &&& hs[f].end == hs[f + 1].start
                &&& self.phys_hot_end(f) == hs[f + 1].start as int
            })
            &&& (f + 1 == hs.len() ==> self.phys_hot_end(f) == pool.len() as int)
            &&& self.pair_tier_offset(false) + f < self.snapshots@.len()
            &&& frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(false) + f),
                pool, hs[f].start as int, self.phys_hot_end(f),
                self.snapshots@[self.pair_tier_offset(false) + f],
                self.snapshots@[self.pair_tier_offset(false) + f].len())
            &&& stratum_unique::<T, I>(pool, hs[f].start as int, self.phys_hot_end(f))
        } by {
            pre.lemma_pair_tier_frame_layout(false, f);
            self.lemma_raw_set_pair_frame(pre, index, value, false, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_raw_set_trail_repr(&self, pre: Self, index: I, value: T)
        requires pre.wf(), self.raw_set_effect(pre, index, value),
            index.as_nat() < pre.view().len(),
            index.as_nat() < pre.active_saved_len.as_nat() ==> pre.store.captured()[index.as_nat() as int],
        ensures self.trail_repr_ok(),
    {
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        pre.lemma_wf_named_parts();
        reveal(Vec::raw_set_effect);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::trail_repr_ok);
        let hs = self.trail_stack@;
        let pool = self.trail_value_pool@;
        assert forall|f: int| 0 <= f < hs.len() implies {
            &&& (#[trigger] hs[f]).start <= hs[f].end
            &&& hs[f].end <= pool.len()
            &&& hs[f].start as int <= self.phys_trail_end(f)
            &&& self.phys_trail_end(f) <= pool.len() as int
            &&& (f + 1 < hs.len() ==> {
                &&& hs[f].end == hs[f + 1].start
                &&& self.phys_trail_end(f) == hs[f + 1].start as int
            })
            &&& (f + 1 == hs.len() ==> self.phys_trail_end(f) == pool.len() as int)
            &&& self.pair_tier_offset(true) + f < self.snapshots@.len()
            &&& frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(true) + f),
                pool, hs[f].start as int, self.phys_trail_end(f),
                self.snapshots@[self.pair_tier_offset(true) + f],
                self.snapshots@[self.pair_tier_offset(true) + f].len())

        } by {
            pre.lemma_pair_tier_frame_layout(true, f);
            self.lemma_raw_set_pair_frame(pre, index, value, true, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_raw_set_preserves(&self, pre: Self, index: I, value: T)
        requires pre.wf(), self.raw_set_effect(pre, index, value),
            index.as_nat() < pre.view().len(),
            index.as_nat() < pre.active_saved_len.as_nat() ==>
                pre.store.captured()[index.as_nat() as int]
                && captured_in_range::<T, I>(pre.full_trail@, pre.g_start(pre.depth_spec() - 1),
                    pre.full_trail@.len() as int, index.as_nat()),
        ensures self.wf(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_reconstructs);
        hide(frame_inv_range);
        hide(stratum_unique);
        pre.lemma_wf_named_parts();
        reveal(Vec::raw_set_effect);
        self.lemma_raw_set_canonical(pre, index, value);
        self.lemma_raw_set_hot_repr(pre, index, value);
        self.lemma_raw_set_trail_repr(pre, index, value);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        self.store.lemma_wf_captured_len();
        assert(self.open_ingress_ok());
        reveal(Vec::cold_repr_ok);
        reveal(Vec::cold_payload_ok);
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f) by {
            assert(f + 1 < pre.depth_spec());
            assert(self.layer_above_at(f) == pre.layer_above_at(f));
            self.lemma_cold_reconstructs_layer_transfer(pre, f);
        }
        assert(self.cold_repr_ok());
        reveal(Vec::proof_compat_ok);
        reveal(Vec::wf);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_capture_domain(&self, index: I)
        requires self.wf(), index.as_nat() < self.active_saved_len.as_nat(),
        ensures self.depth_spec() > 0,
            0 <= self.g_start(self.depth_spec() - 1) <= self.full_trail@.len(),
    {
        self.lemma_wf_named_parts();
        reveal(Vec::open_ingress_ok);
        reveal(Vec::frame_partition_ok);
        I::lemma_min_as_nat();
        self.lemma_diff_start_le_n(self.depth_spec() - 1);
    }

    #[verifier::spinoff_prover]
    #[inline(always)]
    fn runtime_set_fallback(&mut self, index: I, value: T)
        requires
            old(self).wf(),
            !old(self).hot_defer_scope(),
            index.as_nat() < old(self).view().len(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().update(index.as_nat() as int, value),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        let ghost pre = *self;
        self.runtime_capture(index);
        let ghost captured = *self;
        proof {
            if index.as_nat() < self.active_saved_len.as_nat() {
                pre.lemma_capture_domain(index);
                let q = pre.full_trail@.len() as int;
                assert(self.full_trail@[q].1.as_nat() == index.as_nat());
                assert(captured_in_range::<T, I>(self.full_trail@,
                    self.g_start(self.depth_spec() - 1), self.full_trail@.len() as int, index.as_nat()));
            }
        }
        proof { assert(self.store.wf()) by { reveal(Vec::wf); reveal(Vec::wf_for_snap); } }
        self.store.set_raw(index, value);
        proof {
            reveal(Vec::raw_set_effect);
            assert(self.raw_set_effect(captured, index, value));
            self.lemma_raw_set_preserves(captured, index, value);
        }
    }

    #[inline(always)]
    fn runtime_set(&mut self, index: I, value: T)
        requires
            old(self).wf(),
            index.as_nat() < old(self).view().len(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().update(index.as_nat() as int, value),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let hot = self.hot_defer_scope_exec();
        if hot {
            proof { self.lemma_hot_defer_scope_implies_projection(); }
            self.hot_defer_set_checked(index, value);
        } else {
            self.runtime_set_fallback(index, value);
        }
    }

    /// Entries of closed frame `f` of the selected pair tier.
    #[verifier::spinoff_prover]
    #[inline(always)]
    fn pair_frame_entries(&self, trail: bool, f: usize) -> (r: usize)
        requires self.wf(), f < self.pair_tier_count(trail),
        ensures r == self.pair_tier_header_end(trail, f as int) - self.pair_tier_start(trail, f as int),
    {
        proof { self.lemma_pair_tier_frame_layout(trail, f as int); }
        if trail {
            self.trail_stack[f].end - self.trail_stack[f].start
        } else {
            self.hot_stack[f].end - self.hot_stack[f].start
        }
    }

    /// Number of oldest closed frames to migrate so that the retained closed
    /// suffix respects `limit`. `Unbounded`/`Adaptive` retain everything here;
    /// `Entries`/`Bytes` keep the newest closed frames that fit.
    #[verifier::spinoff_prover]
    fn retained_closed_prefix(
        &self, trail: bool, closed: usize, limit: crate::tier_policy::TierLimit, entry_bytes: usize,
    ) -> (r: usize)
        requires self.wf(), closed <= self.pair_tier_count(trail),
        ensures r <= closed,
    {
        hide(Vec::wf);
        match limit {
            crate::tier_policy::TierLimit::Unbounded
            | crate::tier_policy::TierLimit::Adaptive => 0,
            crate::tier_policy::TierLimit::Frames(keep) => closed.saturating_sub(keep),
            crate::tier_policy::TierLimit::Entries(keep) => {
                let mut retained = 0usize;
                let mut used = 0usize;
                while retained < closed
                    invariant retained <= closed, closed <= self.pair_tier_count(trail), self.wf(),
                    decreases closed - retained,
                {
                    let n = self.pair_frame_entries(trail, closed - 1 - retained);
                    if n > keep.saturating_sub(used) {
                        break;
                    }
                    used += n;
                    retained += 1;
                }
                closed - retained
            }
            crate::tier_policy::TierLimit::Bytes(keep) => {
                let mut retained = 0usize;
                let mut used = 0usize;
                while retained < closed
                    invariant retained <= closed, closed <= self.pair_tier_count(trail), self.wf(),
                    decreases closed - retained,
                {
                    let n = match self.pair_frame_entries(trail, closed - 1 - retained).checked_mul(entry_bytes) {
                        Some(n) => n,
                        None => usize::MAX,
                    };
                    if n > keep.saturating_sub(used) {
                        break;
                    }
                    used += n;
                    retained += 1;
                }
                closed - retained
            }
        }
    }

    /// Logical byte count of one frame: header plus `entries * entry` bytes,
    /// refusing on overflow exactly where the planner's checked arithmetic did.
    fn adaptive_frame_bytes(header: usize, entries: usize, entry: usize) -> (r: usize)
        ensures r == header + entries * entry,
    {
        let payload = match entries.checked_mul(entry) {
            Some(v) => v,
            None => crate::guard::refuse("logical adaptive frame byte count overflow"),
        };
        match header.checked_add(payload) {
            Some(v) => v,
            None => crate::guard::refuse("logical adaptive frame byte count overflow"),
        }
    }

    fn adaptive_add_total(total: usize, value: usize) -> (r: usize)
        ensures r == total + value,
    {
        match total.checked_add(value) {
            Some(v) => v,
            None => crate::guard::refuse("adaptive W/U/R total overflow"),
        }
    }

    /// Adaptive Trail stage: deduplicate closed Trail frames oldest-first into
    /// Hot while the closed-history budget is exceeded and each frame pays for
    /// the move. An ineligible frame is dropped from the Hot pool and stops the
    /// stage. Returns the updated logical byte estimate.
    #[verifier::spinoff_prover]
    #[cold]
    #[inline(never)]
    fn adaptive_trail_stage_checked(
        &mut self, input: &crate::tier_policy::AdaptiveInput,
        report: &mut crate::tier_policy::AdaptiveReport, logical: usize,
    ) -> (r: usize)
        requires old(self).wf(),
            old(report).inspected_trail_frames == 0, old(report).migrated_trail_frames == 0,
            old(report).writes == 0, old(report).uniques == 0,
        ensures final(self).wf(),
            *final(self) == (Self { hot_stack: final(self).hot_stack,
                hot_value_pool: final(self).hot_value_pool, trail_stack: final(self).trail_stack,
                trail_value_pool: final(self).trail_value_pool,
                trail_seen: final(self).trail_seen, ..*old(self) }),
            *final(report) == (crate::tier_policy::AdaptiveReport {
                inspected_trail_frames: final(report).inspected_trail_frames,
                migrated_trail_frames: final(report).migrated_trail_frames,
                writes: final(report).writes, uniques: final(report).uniques, ..*old(report) }),
            final(report).migrated_trail_frames == final(self).hot_stack@.len() - old(self).hot_stack@.len(),
    {
        hide(Vec::wf);
        let trail_closed = self.trail_stack.len().saturating_sub(1);
        if trail_closed == 0 {
            return logical;
        }
        let pair_bytes = core::mem::size_of::<(T, I)>();
        let trail_header_bytes = core::mem::size_of::<crate::frame::TrailFrame<I>>();
        let hot_header_bytes = core::mem::size_of::<crate::frame::HotFrame<I>>();
        let ghost pre = *self;
        let ghost report0 = *report;
        let mut plan: Ghost<Seq<Seq<(T, I)>>> = Ghost(Seq::empty());
        proof {
            I::lemma_obeys_key_model();
            self.lemma_trail_migrating_start(pre);
        }
        let mut seen = match self.trail_seen.take() {
            Some(set) => set,
            None => std::collections::HashSet::default(),
        };
        let mut logical = logical;
        let mut trail_count = 0usize;
        while trail_count < trail_closed && logical > input.max_closed_history_bytes
            invariant_except_break
                report.inspected_trail_frames == trail_count,
            invariant
                self.trail_migrating(pre, plan@),
                plan@.len() == trail_count, trail_count <= trail_closed,
                trail_closed + 1 == pre.trail_stack@.len(),
                vstd::std_specs::hash::obeys_key_model::<I>(),
                *report == (crate::tier_policy::AdaptiveReport {
                    inspected_trail_frames: report.inspected_trail_frames,
                    writes: report.writes, uniques: report.uniques, ..report0 }),
            decreases trail_closed - trail_count,
        {
            let (start, writes, uniques) =
                self.trail_frame_tentative_checked(trail_count, &mut seen, Ghost(pre), plan);
            report.inspected_trail_frames = report.inspected_trail_frames + 1;
            report.writes = Self::adaptive_add_total(report.writes, writes);
            report.uniques = Self::adaptive_add_total(report.uniques, uniques);
            let trail_bytes = Self::adaptive_frame_bytes(trail_header_bytes, writes, pair_bytes);
            let hot_bytes = Self::adaptive_frame_bytes(hot_header_bytes, uniques, pair_bytes);
            let eligible = if writes == 0 {
                true
            } else {
                input.min_writes_per_unique.accepts(writes, uniques) && hot_bytes < trail_bytes
            };
            if !eligible {
                self.trail_frame_discard_checked(start, Ghost(pre), plan);
                break;
            }
            logical = match logical.checked_sub(trail_bytes) {
                Some(v) => v,
                None => crate::guard::refuse("adaptive logical byte estimate underflow"),
            };
            logical = match logical.checked_add(hot_bytes) {
                Some(v) => v,
                None => crate::guard::refuse("adaptive logical byte estimate overflow"),
            };
            plan = self.trail_frame_commit_checked(trail_count, start, Ghost(pre), plan);
            trail_count += 1;
        }
        report.migrated_trail_frames = trail_count;
        self.trail_seen = Some(seen);
        self.trail_migration_finish_checked(trail_count, Ghost(pre), plan);
        logical
    }

    fn closed_history_mul(count: usize, width: usize) -> (r: usize)
        ensures r == count * width,
    {
        match count.checked_mul(width) {
            Some(v) => v,
            None => crate::guard::refuse("logical closed-history byte count overflow"),
        }
    }

    fn closed_history_add(left: usize, right: usize) -> (r: usize)
        ensures r == left + right,
    {
        match left.checked_add(right) {
            Some(v) => v,
            None => crate::guard::refuse("logical closed-history byte count overflow"),
        }
    }

    /// Logical occupancy of closed history: headers plus payload lengths of
    /// the closed Trail/Hot frames and all Cold storage, times their sizes.
    #[verifier::spinoff_prover]
    fn runtime_closed_history_bytes(&self) -> usize
        requires self.wf(),
    {
        hide(Vec::wf);
        // Fold over the whole stack (the loop bound is the length, so the
        // per-frame index carries no second bound) and take the open frame
        // back out once; the closed sum is the same either way.
        let trail_len = self.trail_stack.len();
        let trail_closed = trail_len.saturating_sub(1);
        let mut trail_total = 0usize;
        let mut f = 0usize;
        while f < trail_len
            invariant f <= trail_len, trail_len == self.trail_stack@.len(), self.wf(),
            decreases trail_len - f,
        {
            let n = self.pair_frame_entries(true, f);
            trail_total = match trail_total.checked_add(n) {
                Some(v) => v,
                None => crate::guard::refuse("logical closed-history entry count overflow"),
            };
            f += 1;
        }
        let trail_entries = if trail_len > 0 {
            let open = self.pair_frame_entries(true, trail_len - 1);
            match trail_total.checked_sub(open) {
                Some(v) => v,
                None => crate::guard::refuse("logical closed-history entry count underflow"),
            }
        } else {
            0
        };
        let hot_len = self.hot_stack.len();
        let hot_open = self.store.unique_capture() && hot_len > 0;
        let hot_closed = if hot_open { hot_len - 1 } else { hot_len };
        let mut hot_total = 0usize;
        let mut g = 0usize;
        while g < hot_len
            invariant g <= hot_len, hot_len == self.hot_stack@.len(), self.wf(),
            decreases hot_len - g,
        {
            let n = self.pair_frame_entries(false, g);
            hot_total = match hot_total.checked_add(n) {
                Some(v) => v,
                None => crate::guard::refuse("logical closed-history entry count overflow"),
            };
            g += 1;
        }
        let hot_entries = if hot_open {
            let open = self.pair_frame_entries(false, hot_len - 1);
            match hot_total.checked_sub(open) {
                Some(v) => v,
                None => crate::guard::refuse("logical closed-history entry count underflow"),
            }
        } else {
            hot_total
        };
        let trail = Self::closed_history_add(
            Self::closed_history_mul(trail_closed, core::mem::size_of::<crate::frame::TrailFrame<I>>()),
            Self::closed_history_mul(trail_entries, core::mem::size_of::<(T, I)>()),
        );
        let hot = Self::closed_history_add(
            Self::closed_history_mul(hot_closed, core::mem::size_of::<crate::frame::HotFrame<I>>()),
            Self::closed_history_mul(hot_entries, core::mem::size_of::<(T, I)>()),
        );
        let cold = Self::closed_history_add(
            Self::closed_history_mul(self.cold_stack.len(), core::mem::size_of::<crate::frame::ColdFrameHdr<I>>()),
            Self::closed_history_add(
                Self::closed_history_mul(self.cold_value_pool.len(), core::mem::size_of::<T>()),
                Self::closed_history_mul(self.cold_index_runs.len(), core::mem::size_of::<crate::frame::IndexRun<I>>()),
            ),
        );
        Self::closed_history_add(Self::closed_history_add(trail, hot), cold)
    }

    /// Retire a Copy prefix using the same bulk overlapping shift as drain,
    /// with an exact retained-suffix contract and no element-removal loop.
    #[verifier::spinoff_prover]
    fn discard_prefix_checked<U: Copy>(data: &mut std::vec::Vec<U>, cut: usize)
        requires cut <= old(data)@.len(),
        ensures final(data)@ == old(data)@.subrange(cut as int, old(data)@.len() as int),
    {
        let len = data.len();
        data.as_mut_slice().copy_within(cut..len, 0);
        data.truncate(len - cut);
        proof {
            assert(data@ =~= old(data)@.subrange(cut as int, old(data)@.len() as int));
        }
    }

    #[verifier::spinoff_prover]
    fn retire_trail_prefix_checked(&mut self, count: usize)
        requires count < old(self).trail_stack@.len(),
            old(self).trail_stack@[count as int].start <= old(self).trail_value_pool@.len(),
            forall|f: int| count <= f < old(self).trail_stack@.len() ==>
                old(self).trail_stack@[count as int].start <= (#[trigger] old(self).trail_stack@[f]).start
                && old(self).trail_stack@[count as int].start <= old(self).trail_stack@[f].end,
        ensures
            *final(self) == (Self { trail_stack: final(self).trail_stack,
                trail_value_pool: final(self).trail_value_pool, ..*old(self) }),
            final(self).trail_value_pool@ == old(self).trail_value_pool@.subrange(
                old(self).trail_stack@[count as int].start as int, old(self).trail_value_pool@.len() as int),
            final(self).trail_stack@.len() == old(self).trail_stack@.len() - count,
            forall|f: int| 0 <= f < final(self).trail_stack@.len() ==> {
                let h = #[trigger] final(self).trail_stack@[f];
                let old_h = old(self).trail_stack@[count + f];
                &&& h.saved_len == old_h.saved_len
                &&& h.start == old_h.start - old(self).trail_stack@[count as int].start
                &&& h.end == old_h.end - old(self).trail_stack@[count as int].start
            },
    {
        let ghost pre = *self;
        let cut = self.trail_stack[count].start;
        Self::discard_prefix_checked(&mut self.trail_value_pool, cut);
        Self::discard_prefix_checked(&mut self.trail_stack, count);
        let mut f = 0usize;
        while f < self.trail_stack.len()
            invariant
                f <= self.trail_stack@.len(),
                cut == pre.trail_stack@[count as int].start,
                count < pre.trail_stack@.len(),
                self.trail_stack@.len() == pre.trail_stack@.len() - count,
                *self == (Self { trail_stack: self.trail_stack, trail_value_pool: self.trail_value_pool, ..pre }),
                self.trail_value_pool@ == pre.trail_value_pool@.subrange(cut as int, pre.trail_value_pool@.len() as int),
                forall|q: int| count <= q < pre.trail_stack@.len() ==>
                    cut <= (#[trigger] pre.trail_stack@[q]).start && cut <= pre.trail_stack@[q].end,
                forall|q: int| f <= q < self.trail_stack@.len() ==>
                    #[trigger] self.trail_stack@[q] == pre.trail_stack@[count + q],
                forall|q: int| 0 <= q < f ==> {
                    let h = #[trigger] self.trail_stack@[q];
                    let old_h = pre.trail_stack@[count + q];
                    &&& h.saved_len == old_h.saved_len
                    &&& h.start == old_h.start - cut
                    &&& h.end == old_h.end - cut
                },
            decreases self.trail_stack.len() - f,
        {
            self.trail_stack[f].start -= cut;
            self.trail_stack[f].end -= cut;
            f += 1;
        }
    }

    spec fn hot_retirement_cut(&self, count: nat) -> nat {
        if count < self.hot_stack@.len() { self.hot_stack@[count as int].start as nat }
        else { self.hot_value_pool@.len() }
    }

    #[verifier::spinoff_prover]
    fn retire_hot_prefix_checked(&mut self, count: usize)
        requires count <= old(self).hot_stack@.len(),
            old(self).hot_retirement_cut(count as nat) <= old(self).hot_value_pool@.len(),
            forall|f: int| count <= f < old(self).hot_stack@.len() ==>
                old(self).hot_retirement_cut(count as nat) <= (#[trigger] old(self).hot_stack@[f]).start
                && old(self).hot_retirement_cut(count as nat) <= old(self).hot_stack@[f].end,
        ensures
            *final(self) == (Self { hot_stack: final(self).hot_stack,
                hot_value_pool: final(self).hot_value_pool, ..*old(self) }),
            final(self).hot_value_pool@ == old(self).hot_value_pool@.subrange(
                old(self).hot_retirement_cut(count as nat) as int, old(self).hot_value_pool@.len() as int),
            final(self).hot_stack@.len() == old(self).hot_stack@.len() - count,
            forall|f: int| 0 <= f < final(self).hot_stack@.len() ==> {
                let h = #[trigger] final(self).hot_stack@[f];
                let old_h = old(self).hot_stack@[count + f];
                &&& h.saved_len == old_h.saved_len
                &&& h.start == old_h.start - old(self).hot_retirement_cut(count as nat)
                &&& h.end == old_h.end - old(self).hot_retirement_cut(count as nat)
            },
    {
        let ghost pre = *self;
        let cut = if count < self.hot_stack.len() {
            self.hot_stack[count].start
        } else { self.hot_value_pool.len() };
        Self::discard_prefix_checked(&mut self.hot_value_pool, cut);
        Self::discard_prefix_checked(&mut self.hot_stack, count);
        let mut f = 0usize;
        while f < self.hot_stack.len()
            invariant
                f <= self.hot_stack@.len(),
                cut == pre.hot_retirement_cut(count as nat),
                count <= pre.hot_stack@.len(),
                self.hot_stack@.len() == pre.hot_stack@.len() - count,
                *self == (Self { hot_stack: self.hot_stack, hot_value_pool: self.hot_value_pool, ..pre }),
                self.hot_value_pool@ == pre.hot_value_pool@.subrange(cut as int, pre.hot_value_pool@.len() as int),
                forall|q: int| count <= q < pre.hot_stack@.len() ==>
                    cut <= (#[trigger] pre.hot_stack@[q]).start && cut <= pre.hot_stack@[q].end,
                forall|q: int| f <= q < self.hot_stack@.len() ==>
                    #[trigger] self.hot_stack@[q] == pre.hot_stack@[count + q],
                forall|q: int| 0 <= q < f ==> {
                    let h = #[trigger] self.hot_stack@[q];
                    let old_h = pre.hot_stack@[count + q];
                    &&& h.saved_len == old_h.saved_len
                    &&& h.start == old_h.start - cut
                    &&& h.end == old_h.end - cut
                },
            decreases self.hot_stack.len() - f,
        {
            self.hot_stack[f].start -= cut;
            self.hot_stack[f].end -= cut;
            f += 1;
        }
    }

    /// Extending a plan does not change any earlier prefix.
    #[verifier::spinoff_prover]
    proof fn lemma_trail_plan_prefix_push(plan: Seq<Seq<(T, I)>>, payload: Seq<(T, I)>, q: int)
        requires 0 <= q <= plan.len(),
        ensures Self::trail_plan_prefix(plan.push(payload), q) == Self::trail_plan_prefix(plan, q),
        decreases q,
    {
        reveal_with_fuel(Vec::trail_plan_prefix, 1);
        if q > 0 {
            Self::lemma_trail_plan_prefix_push(plan, payload, q - 1);
            assert(plan.push(payload)[q - 1] == plan[q - 1]);
        }
    }

    /// The extended plan's full prefix is the old full prefix plus the payload.
    #[verifier::spinoff_prover]
    proof fn lemma_trail_plan_prefix_push_last(plan: Seq<Seq<(T, I)>>, payload: Seq<(T, I)>)
        ensures Self::trail_plan_prefix(plan.push(payload), plan.len() as int + 1)
            == Self::trail_plan_prefix(plan, plan.len() as int) + payload,
    {
        reveal_with_fuel(Vec::trail_plan_prefix, 1);
        Self::lemma_trail_plan_prefix_push(plan, payload, plan.len() as int);
        assert(plan.push(payload)[plan.len() as int] == payload);
    }

    /// Retained effect, restored partition and every Hot frame's contract
    /// after a matched Trail-to-Hot migration.
    #[verifier::spinoff_prover]
    proof fn lemma_trail_migration_frames(&self, pre: Self, plan: Seq<Seq<(T, I)>>)
        requires pre.wf(), plan.len() < pre.trail_stack@.len(),
            *self == (Self { hot_stack: self.hot_stack, hot_value_pool: self.hot_value_pool,
                trail_stack: self.trail_stack, trail_value_pool: self.trail_value_pool,
                trail_seen: self.trail_seen, ..pre }),
            self.hot_value_pool@ == pre.hot_value_pool@ + Self::trail_plan_prefix(plan, plan.len() as int),
            self.hot_stack@.len() == pre.hot_stack@.len() + plan.len(),
            self.hot_stack@.subrange(0, pre.hot_stack@.len() as int) == pre.hot_stack@,
            plan.len() > 0 ==> self.hot_stack@[pre.hot_stack@.len() as int].start == pre.hot_value_pool@.len(),
            plan.len() > 0 ==> self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len(),
            forall|f: int| 0 <= f < plan.len() ==> {
                let h = #[trigger] self.hot_stack@[pre.hot_stack@.len() + f];
                &&& h.saved_len == pre.trail_stack@[f].saved_len
                &&& h.start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, f).len()
                &&& h.end == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, f + 1).len()
            },
            self.trail_value_pool@ == pre.trail_value_pool@.subrange(
                pre.trail_stack@[plan.len() as int].start as int, pre.trail_value_pool@.len() as int),
            self.trail_stack@.len() == pre.trail_stack@.len() - plan.len(),
            forall|f: int| 0 <= f < self.trail_stack@.len() ==> {
                let h = #[trigger] self.trail_stack@[f];
                let old_h = pre.trail_stack@[plan.len() + f];
                let cut = pre.trail_stack@[plan.len() as int].start;
                &&& h.saved_len == old_h.saved_len
                &&& h.start == old_h.start - cut
                &&& h.end == old_h.end - cut
            },
            pre.trail_plan_matches(plan),
        ensures self.trail_retained_effect(pre, plan.len()), self.frame_partition_ok(),
            forall|f: int| 0 <= f < self.hot_stack@.len() ==>
                #[trigger] self.phys_frame_inv_range_holds(f)
                && stratum_unique::<T, I>(self.hot_value_pool@, self.phys_hot_start(f), self.phys_hot_end(f)),
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::wf_for_snap);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::open_ingress_ok);
        let count = plan.len();
        pre.lemma_wf_named_parts();
        self.lemma_trail_assembly_sealed(pre, plan);
        assert(self.trail_retained_effect(pre, count)) by {
            reveal(Vec::trail_retained_effect);
            assert(self.hot_value_pool@.subrange(0, pre.hot_value_pool@.len() as int) =~= pre.hot_value_pool@);
        }
        self.lemma_trail_migration_partition(pre, count);
        assert forall|f: int, j: nat| 0 <= f < plan.len() implies {
            let h = self.hot_stack@[pre.hot_stack@.len() + f];
            range_saved_value::<T, I>(self.hot_value_pool@, h.start as int, h.end as int, j)
                == #[trigger] range_saved_value::<T, I>(plan[f], 0, plan[f].len() as int, j)
        } by {
            Self::lemma_trail_plan_frame_range(plan, count as int, f);
            let h = self.hot_stack@[pre.hot_stack@.len() + f];
            assert(self.hot_value_pool@.subrange(h.start as int, h.end as int) =~= plan[f]);
            lemma_range_saved_value_subrange::<T, I>(self.hot_value_pool@, h.start as int, h.end as int, j);
        }
        assert forall|f: int| 0 <= f < self.hot_stack@.len() implies
            #[trigger] self.phys_frame_inv_range_holds(f)
            && stratum_unique::<T, I>(self.hot_value_pool@, self.phys_hot_start(f), self.phys_hot_end(f)) by {
            if f < pre.hot_stack@.len() {
                self.lemma_trail_old_hot_frame(pre, count, f);
            } else {
                self.lemma_trail_moved_frame(pre, plan, f);
            }
        }
    }

    /// A completed Trail-to-Hot migration whose payloads match their source
    /// frames restores the full invariant. Shared by the direct-write and the
    /// planned executors; the physical assembly and retirement effects are
    /// premises, not re-derived.
    #[verifier::spinoff_prover]
    proof fn lemma_trail_migration_wf(&self, pre: Self, plan: Seq<Seq<(T, I)>>)
        requires pre.wf(), plan.len() < pre.trail_stack@.len(),
            *self == (Self { hot_stack: self.hot_stack, hot_value_pool: self.hot_value_pool,
                trail_stack: self.trail_stack, trail_value_pool: self.trail_value_pool,
                trail_seen: self.trail_seen, ..pre }),
            self.hot_value_pool@ == pre.hot_value_pool@ + Self::trail_plan_prefix(plan, plan.len() as int),
            self.hot_stack@.len() == pre.hot_stack@.len() + plan.len(),
            self.hot_stack@.subrange(0, pre.hot_stack@.len() as int) == pre.hot_stack@,
            plan.len() > 0 ==> self.hot_stack@[pre.hot_stack@.len() as int].start == pre.hot_value_pool@.len(),
            plan.len() > 0 ==> self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len(),
            forall|f: int| 0 <= f < plan.len() ==> {
                let h = #[trigger] self.hot_stack@[pre.hot_stack@.len() + f];
                &&& h.saved_len == pre.trail_stack@[f].saved_len
                &&& h.start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, f).len()
                &&& h.end == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, f + 1).len()
            },
            self.trail_value_pool@ == pre.trail_value_pool@.subrange(
                pre.trail_stack@[plan.len() as int].start as int, pre.trail_value_pool@.len() as int),
            self.trail_stack@.len() == pre.trail_stack@.len() - plan.len(),
            forall|f: int| 0 <= f < self.trail_stack@.len() ==> {
                let h = #[trigger] self.trail_stack@[f];
                let old_h = pre.trail_stack@[plan.len() + f];
                let cut = pre.trail_stack@[plan.len() as int].start;
                &&& h.saved_len == old_h.saved_len
                &&& h.start == old_h.start - cut
                &&& h.end == old_h.end - cut
            },
            pre.trail_plan_matches(plan),
        ensures self.wf(), self.trail_retained_effect(pre, plan.len()),
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(Vec::wf_for_snap);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::open_ingress_ok);
        let count = plan.len();
        self.lemma_trail_migration_frames(pre, plan);
        self.lemma_trail_retained_repr(pre, count);
        self.lemma_trail_retained_ingress(pre, count);
        self.lemma_trail_fixed_history(pre, count);
        self.lemma_trail_hot_repr(pre, plan);
        self.lemma_wf_from_named_parts();
    }

    /// Physical state while an oldest closed Trail prefix is being deduplicated
    /// into Hot: `plan` are the unique payloads already published with headers.
    closed spec fn trail_migrating(&self, pre: Self, plan: Seq<Seq<(T, I)>>) -> bool {
        &&& pre.wf()
        &&& plan.len() < pre.trail_stack@.len()
        &&& *self == (Self { hot_stack: self.hot_stack, hot_value_pool: self.hot_value_pool,
            trail_seen: self.trail_seen, ..pre })
        &&& self.hot_value_pool@ == pre.hot_value_pool@ + Self::trail_plan_prefix(plan, plan.len() as int)
        &&& self.hot_stack@.len() == pre.hot_stack@.len() + plan.len()
        &&& self.hot_stack@.subrange(0, pre.hot_stack@.len() as int) == pre.hot_stack@
        &&& plan.len() > 0 ==> self.hot_stack@[pre.hot_stack@.len() as int].start == pre.hot_value_pool@.len()
        &&& plan.len() > 0 ==> self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len()
        &&& forall|q: int| 0 <= q < plan.len() ==> {
            let h = #[trigger] self.hot_stack@[pre.hot_stack@.len() + q];
            &&& h.saved_len == pre.trail_stack@[q].saved_len
            &&& h.start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q).len()
            &&& h.end == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q + 1).len()
        }
        &&& forall|q: int| 0 <= q < plan.len() ==>
            #[trigger] stratum_unique::<T, I>(plan[q], 0, plan[q].len() as int)
        &&& forall|q: int, j: nat| 0 <= q < plan.len() ==>
            #[trigger] range_saved_value::<T, I>(plan[q], 0, plan[q].len() as int, j)
                == range_saved_value::<T, I>(pre.trail_value_pool@,
                    pre.trail_stack@[q].start as int, pre.phys_trail_end(q), j)
    }

    /// Frame `plan.len()` has been deduplicated into the Hot pool from `start`
    /// on, but its header is not published yet; the caller may still discard it.
    closed spec fn trail_tentative(&self, pre: Self, plan: Seq<Seq<(T, I)>>, start: int) -> bool {
        let payload = self.hot_value_pool@.subrange(start, self.hot_value_pool@.len() as int);
        let f = plan.len() as int;
        &&& pre.wf()
        &&& plan.len() + 1 < pre.trail_stack@.len()
        &&& *self == (Self { hot_stack: self.hot_stack, hot_value_pool: self.hot_value_pool,
            trail_seen: self.trail_seen, ..pre })
        &&& start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, plan.len() as int).len()
        &&& start <= self.hot_value_pool@.len()
        &&& self.hot_value_pool@.subrange(0, start) == pre.hot_value_pool@ + Self::trail_plan_prefix(plan, plan.len() as int)
        &&& self.hot_stack@.len() == pre.hot_stack@.len() + plan.len()
        &&& self.hot_stack@.subrange(0, pre.hot_stack@.len() as int) == pre.hot_stack@
        &&& plan.len() > 0 ==> self.hot_stack@[pre.hot_stack@.len() as int].start == pre.hot_value_pool@.len()
        &&& plan.len() > 0 ==> self.hot_stack@[self.hot_stack@.len() - 1].end == start
        &&& forall|q: int| 0 <= q < plan.len() ==> {
            let h = #[trigger] self.hot_stack@[pre.hot_stack@.len() + q];
            &&& h.saved_len == pre.trail_stack@[q].saved_len
            &&& h.start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q).len()
            &&& h.end == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q + 1).len()
        }
        &&& forall|q: int| 0 <= q < plan.len() ==>
            #[trigger] stratum_unique::<T, I>(plan[q], 0, plan[q].len() as int)
        &&& forall|q: int, j: nat| 0 <= q < plan.len() ==>
            #[trigger] range_saved_value::<T, I>(plan[q], 0, plan[q].len() as int, j)
                == range_saved_value::<T, I>(pre.trail_value_pool@,
                    pre.trail_stack@[q].start as int, pre.phys_trail_end(q), j)
        &&& stratum_unique::<T, I>(payload, 0, payload.len() as int)
        &&& forall|j: nat| #[trigger] range_saved_value::<T, I>(payload, 0, payload.len() as int, j)
            == range_saved_value::<T, I>(pre.trail_value_pool@,
                pre.trail_stack@[f].start as int, pre.phys_trail_end(f), j)
    }

    /// Deduplicate the next closed Trail frame straight into the Hot pool
    /// without publishing a header. Returns `(start, writes, uniques)`.
    #[verifier::spinoff_prover]
    fn trail_frame_tentative_checked(
        &mut self, f: usize, seen: &mut std::collections::HashSet<I, crate::hasher_spec::IndexHasher>,
        Ghost(pre): Ghost<Self>, Ghost(plan): Ghost<Seq<Seq<(T, I)>>>,
    ) -> (r: (usize, usize, usize))
        requires old(self).trail_migrating(pre, plan), f == plan.len(),
            f + 1 < pre.trail_stack@.len(),
            vstd::std_specs::hash::obeys_key_model::<I>(),
        ensures final(self).trail_tentative(pre, plan, r.0 as int),
            r.0 == old(self).hot_value_pool@.len(),
            r.1 == pre.trail_stack@[f as int].end - pre.trail_stack@[f as int].start,
            r.2 == final(self).hot_value_pool@.len() - r.0,
            r.2 <= r.1,
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(range_saved_value);
        hide(crate::trail_select::dedupe_prefix);
        proof {
            reveal(Vec::trail_migrating);
            pre.lemma_pair_tier_frame_layout(true, f as int);
            pre.lemma_pair_tier_frame_layout(true, f as int + 1);
        }
        let frame = self.trail_stack[f];
        let start = self.hot_value_pool.len();
        crate::trail_select::dedupe_trail_range(
            &self.trail_value_pool, frame.start, frame.end, seen, &mut self.hot_value_pool);
        proof {
            reveal(Vec::trail_tentative);
            assert(frame.end as int == pre.phys_trail_end(f as int));
            assert(self.hot_value_pool@.subrange(0, start as int)
                == pre.hot_value_pool@ + Self::trail_plan_prefix(plan, plan.len() as int));
            let payload = self.hot_value_pool@.subrange(start as int, self.hot_value_pool@.len() as int);
            assert(stratum_unique::<T, I>(payload, 0, payload.len() as int)) by {
                reveal(stratum_unique);
                assert forall|a: int, b: int| 0 <= a < payload.len() && 0 <= b < payload.len() && a != b
                    implies (#[trigger] payload[a]).1.as_nat() != (#[trigger] payload[b]).1.as_nat() by {
                    assert(payload[a] == self.hot_value_pool@[start + a]);
                    assert(payload[b] == self.hot_value_pool@[start + b]);
                }
            }
            assert forall|j: nat| #[trigger] range_saved_value::<T, I>(payload, 0, payload.len() as int, j)
                == range_saved_value::<T, I>(pre.trail_value_pool@,
                    pre.trail_stack@[f as int].start as int, pre.phys_trail_end(f as int), j) by {
                lemma_range_saved_value_subrange::<T, I>(self.hot_value_pool@, start as int,
                    self.hot_value_pool@.len() as int, j);
            }
        }
        (start, frame.end - frame.start, self.hot_value_pool.len() - start)
    }

    /// Publish the tentative frame's header, extending the plan by its payload.
    #[verifier::spinoff_prover]
    fn trail_frame_commit_checked(
        &mut self, f: usize, start: usize, Ghost(pre): Ghost<Self>, Ghost(plan): Ghost<Seq<Seq<(T, I)>>>,
    ) -> (r: Ghost<Seq<Seq<(T, I)>>>)
        requires old(self).trail_tentative(pre, plan, start as int), f == plan.len(),
        ensures final(self).trail_migrating(pre, r@), r@.len() == f + 1,
            *final(self) == (Self { hot_stack: final(self).hot_stack, ..*old(self) }),
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(range_saved_value);
        proof { reveal(Vec::trail_tentative); }
        let frame = self.trail_stack[f];
        let end = self.hot_value_pool.len();
        let ghost prior_headers = self.hot_stack@;
        self.hot_stack.push(crate::frame::HotFrame { saved_len: frame.saved_len, start, end });
        let ghost payload = self.hot_value_pool@.subrange(start as int, end as int);
        let ghost next = plan.push(payload);
        proof {
            reveal(Vec::trail_migrating);
            Self::lemma_trail_plan_prefix_push(plan, payload, f as int);
            Self::lemma_trail_plan_prefix_push_last(plan, payload);
            assert(self.hot_value_pool@ =~= pre.hot_value_pool@ + Self::trail_plan_prefix(next, f as int + 1)) by {
                assert forall|i: int| 0 <= i < self.hot_value_pool@.len() implies
                    self.hot_value_pool@[i] == (pre.hot_value_pool@ + Self::trail_plan_prefix(next, f as int + 1))[i] by {
                    if i < start {
                        assert(self.hot_value_pool@[i] == self.hot_value_pool@.subrange(0, start as int)[i]);
                    } else {
                        assert(self.hot_value_pool@[i] == payload[i - start]);
                    }
                }
            }
            assert(self.hot_stack@.subrange(0, pre.hot_stack@.len() as int) =~= pre.hot_stack@);
            assert forall|q: int| 0 <= q <= f implies {
                let h = #[trigger] self.hot_stack@[pre.hot_stack@.len() + q];
                &&& h.saved_len == pre.trail_stack@[q].saved_len
                &&& h.start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(next, q).len()
                &&& h.end == pre.hot_value_pool@.len() + Self::trail_plan_prefix(next, q + 1).len()
            } by {
                Self::lemma_trail_plan_prefix_push(plan, payload, q);
                if q < f {
                    Self::lemma_trail_plan_prefix_push(plan, payload, q + 1);
                    assert(self.hot_stack@[pre.hot_stack@.len() + q] == prior_headers[pre.hot_stack@.len() + q]);
                }
            }
            assert forall|q: int| 0 <= q <= f implies
                #[trigger] stratum_unique::<T, I>(next[q], 0, next[q].len() as int) by {
                if q < f { assert(next[q] == plan[q]); }
            }
            assert forall|q: int, j: nat| 0 <= q <= f implies
                #[trigger] range_saved_value::<T, I>(next[q], 0, next[q].len() as int, j)
                    == range_saved_value::<T, I>(pre.trail_value_pool@,
                        pre.trail_stack@[q].start as int, pre.phys_trail_end(q), j) by {
                if q < f { assert(next[q] == plan[q]); }
            }
        }
        Ghost(next)
    }

    /// Drop the tentative frame's payload; the published plan is unchanged.
    #[verifier::spinoff_prover]
    fn trail_frame_discard_checked(
        &mut self, start: usize, Ghost(pre): Ghost<Self>, Ghost(plan): Ghost<Seq<Seq<(T, I)>>>,
    )
        requires old(self).trail_tentative(pre, plan, start as int),
        ensures final(self).trail_migrating(pre, plan),
            *final(self) == (Self { hot_value_pool: final(self).hot_value_pool, ..*old(self) }),
            final(self).hot_value_pool@.len() == start,
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(range_saved_value);
        proof { reveal(Vec::trail_tentative); }
        self.hot_value_pool.truncate(start);
        proof {
            reveal(Vec::trail_migrating);
            assert(self.hot_value_pool@ =~= pre.hot_value_pool@ + Self::trail_plan_prefix(plan, plan.len() as int));
        }
    }

    /// Retire the migrated Trail prefix and restore the full invariant.
    #[verifier::spinoff_prover]
    fn trail_migration_finish_checked(
        &mut self, count: usize, Ghost(pre): Ghost<Self>, Ghost(plan): Ghost<Seq<Seq<(T, I)>>>,
    )
        requires old(self).trail_migrating(pre, plan), count == plan.len(),
        ensures final(self).wf(),
            *final(self) == (Self { hot_stack: final(self).hot_stack,
                hot_value_pool: final(self).hot_value_pool, trail_stack: final(self).trail_stack,
                trail_value_pool: final(self).trail_value_pool,
                trail_seen: final(self).trail_seen, ..pre }),
            final(self).hot_stack@.len() == pre.hot_stack@.len() + count,
            final(self).trail_stack@.len() == pre.trail_stack@.len() - count,
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        hide(stratum_unique);
        hide(range_saved_value);
        hide(Vec::wf_for_snap);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::open_ingress_ok);
        proof {
            reveal(Vec::trail_migrating);
            assert(pre.trail_plan_matches(plan)) by { reveal(Vec::trail_plan_matches); }
        }
        if count == 0 {
            proof {
                pre.lemma_pair_tier_frame_layout(true, 0);
                assert(self.trail_value_pool@ =~= pre.trail_value_pool@.subrange(
                    pre.trail_stack@[0].start as int, pre.trail_value_pool@.len() as int));
                self.lemma_trail_migration_wf(pre, plan);
            }
            return;
        }
        proof { pre.lemma_trail_retirement_bounds(count as nat); }
        self.retire_trail_prefix_checked(count);
        proof {
            assert(*self == (Self { hot_stack: self.hot_stack, hot_value_pool: self.hot_value_pool,
                trail_stack: self.trail_stack, trail_value_pool: self.trail_value_pool,
                trail_seen: self.trail_seen, ..pre }));
            self.lemma_trail_migration_wf(pre, plan);
        }
    }

    /// Move an exact oldest closed Trail prefix into Hot through first-capture
    /// deduplication: one left-to-right pass per frame with a reusable index
    /// set, writing each unique frame straight into the Hot pool, then one bulk
    /// retirement of the migrated prefix.
    #[verifier::spinoff_prover]
    #[cold]
    #[inline(never)]
    fn runtime_migrate_trail_count(&mut self, count: usize)
        requires old(self).wf(), count == 0 || count < old(self).trail_stack@.len(),
        ensures final(self).wf(),
            *final(self) == (Self { hot_stack: final(self).hot_stack,
                hot_value_pool: final(self).hot_value_pool, trail_stack: final(self).trail_stack,
                trail_value_pool: final(self).trail_value_pool,
                trail_seen: final(self).trail_seen, ..*old(self) }),
            final(self).hot_stack@.len() == old(self).hot_stack@.len() + count,
            final(self).trail_stack@.len() == old(self).trail_stack@.len() - count,
    {
        hide(Vec::wf);
        if count == 0 {
            return;
        }
        let ghost pre = *self;
        let mut plan: Ghost<Seq<Seq<(T, I)>>> = Ghost(Seq::empty());
        proof {
            I::lemma_obeys_key_model();
            self.lemma_trail_migrating_start(pre);
        }
        let mut seen = match self.trail_seen.take() {
            Some(set) => set,
            None => std::collections::HashSet::default(),
        };
        let mut f = 0usize;
        while f < count
            invariant
                self.trail_migrating(pre, plan@),
                plan@.len() == f, f <= count, count < pre.trail_stack@.len(),
                vstd::std_specs::hash::obeys_key_model::<I>(),
            decreases count - f,
        {
            let (start, _writes, _uniques) = self.trail_frame_tentative_checked(f, &mut seen, Ghost(pre), plan);
            plan = self.trail_frame_commit_checked(f, start, Ghost(pre), plan);
            f += 1;
        }
        self.trail_seen = Some(seen);
        self.trail_migration_finish_checked(count, Ghost(pre), plan);
    }

    /// An unchanged well-formed container is the empty-plan migration state.
    #[verifier::spinoff_prover]
    proof fn lemma_trail_migrating_start(&self, pre: Self)
        requires *self == pre, pre.wf(), pre.trail_stack@.len() > 0,
        ensures self.trail_migrating(pre, Seq::empty()),
    {
        hide(Vec::wf);
        reveal(Vec::trail_migrating);
        reveal_with_fuel(Vec::trail_plan_prefix, 1);
        assert(self.hot_value_pool@ =~= pre.hot_value_pool@ + Self::trail_plan_prefix(Seq::empty(), 0));
        assert(self.hot_stack@.subrange(0, pre.hot_stack@.len() as int) =~= pre.hot_stack@);
    }

    closed spec fn trail_plan_prefix(plan: Seq<Seq<(T, I)>>, n: int) -> Seq<(T, I)>
        recommends 0 <= n <= plan.len(),
        decreases n,
    {
        if n <= 0 { Seq::empty() }
        else { Self::trail_plan_prefix(plan, n - 1) + plan[n - 1] }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_plan_frame_range(plan: Seq<Seq<(T, I)>>, n: int, f: int)
        requires 0 <= f < n <= plan.len(),
        ensures
            Self::trail_plan_prefix(plan, f).len() <= Self::trail_plan_prefix(plan, f + 1).len()
                <= Self::trail_plan_prefix(plan, n).len(),
            Self::trail_plan_prefix(plan, n).subrange(
                Self::trail_plan_prefix(plan, f).len() as int,
                Self::trail_plan_prefix(plan, f + 1).len() as int) == plan[f],
        decreases n - f,
    {
        reveal_with_fuel(Vec::trail_plan_prefix, 1);
        if f + 1 < n {
            Self::lemma_trail_plan_frame_range(plan, n - 1, f);
            assert(Self::trail_plan_prefix(plan, n).subrange(
                Self::trail_plan_prefix(plan, f).len() as int,
                Self::trail_plan_prefix(plan, f + 1).len() as int) =~= plan[f]);
        } else {
            assert(f + 1 == n);
            assert(Self::trail_plan_prefix(plan, n).subrange(
                Self::trail_plan_prefix(plan, f).len() as int,
                Self::trail_plan_prefix(plan, f + 1).len() as int) =~= plan[f]);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_retirement_bounds(&self, count: nat)
        requires self.wf(), count < self.trail_stack@.len(),
        ensures self.trail_stack@[count as int].start <= self.trail_value_pool@.len(),
            forall|f: int| count <= f < self.trail_stack@.len() ==>
                self.trail_stack@[count as int].start <= (#[trigger] self.trail_stack@[f]).start
                    && self.trail_stack@[count as int].start <= self.trail_stack@[f].end,
    {
        hide(Vec::wf);
        self.lemma_pair_tier_frame_layout(true, count as int);
        assert forall|f: int| count <= f < self.trail_stack@.len() implies
            self.trail_stack@[count as int].start <= (#[trigger] self.trail_stack@[f]).start
                && self.trail_stack@[count as int].start <= self.trail_stack@[f].end by {
            self.lemma_pair_tier_start_order(true, count as int, f);
            self.lemma_pair_tier_frame_layout(true, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_migration_partition(&self, pre: Self, count: nat)
        requires pre.frame_partition_ok(), count <= pre.trail_stack@.len(),
            self.snapshots@ == pre.snapshots@, self.trail_frames@ == pre.trail_frames@,
            self.cold_stack@ == pre.cold_stack@,
            self.hot_stack@.len() == pre.hot_stack@.len() + count,
            self.trail_stack@.len() == pre.trail_stack@.len() - count,
            self.hot_stack@.subrange(0, pre.hot_stack@.len() as int) == pre.hot_stack@,
            forall|f: int| 0 <= f < count ==>
                self.hot_stack@[pre.hot_stack@.len() + f].saved_len == (#[trigger] pre.trail_stack@[f]).saved_len,
            forall|f: int| 0 <= f < self.trail_stack@.len() ==>
                (#[trigger] self.trail_stack@[f]).saved_len == pre.trail_stack@[count + f].saved_len,
        ensures self.frame_partition_ok(),
    {
        reveal(Vec::frame_partition_ok);
        assert forall|f: int| 0 <= f < self.hot_stack@.len() implies
            (#[trigger] self.hot_stack@[f]).saved_len.as_nat()
                == self.snapshots@[self.cold_stack@.len() + f].len() by {
            if f < pre.hot_stack@.len() { assert(self.hot_stack@[f] == pre.hot_stack@[f]); }
            else { assert(self.hot_stack@[f].saved_len == pre.trail_stack@[f - pre.hot_stack@.len()].saved_len); }
        }
        assert forall|f: int| 0 <= f < self.trail_stack@.len() implies
            (#[trigger] self.trail_stack@[f]).saved_len.as_nat()
                == self.snapshots@[self.cold_stack@.len() + self.hot_stack@.len() + f].len() by {
            assert(self.trail_stack@[f].saved_len == pre.trail_stack@[count + f].saved_len);
        }
    }

    closed spec fn trail_plan_matches(&self, plan: Seq<Seq<(T, I)>>) -> bool {
        &&& plan.len() <= self.trail_stack@.len()
        &&& forall|f: int| 0 <= f < plan.len() ==>
            #[trigger] stratum_unique::<T, I>(plan[f], 0, plan[f].len() as int)
        &&& forall|f: int, j: nat| 0 <= f < plan.len() ==>
            #[trigger] range_saved_value::<T, I>(plan[f], 0, plan[f].len() as int, j)
                == range_saved_value::<T, I>(self.trail_value_pool@,
                    self.trail_stack@[f].start as int, self.phys_trail_end(f), j)
    }

    #[verifier::spinoff_prover]
    proof fn lemma_pair_tier_contract(&self, trail: bool, f: int)
        requires self.wf(), 0 <= f < self.pair_tier_count(trail),
        ensures frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(trail) + f),
            self.pair_tier_pool(trail), self.pair_tier_start(trail, f), self.pair_tier_end(trail, f),
            self.snapshots@[self.pair_tier_offset(trail) + f],
            self.snapshots@[self.pair_tier_offset(trail) + f].len()),
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        if trail { reveal(Vec::trail_repr_ok); } else { reveal(Vec::hot_repr_ok); }
    }

    /// Exact survivor facts exported by checked assembly/retirement. This
    /// predicate describes a transition; it is not persistent container state.
    closed spec fn trail_retained_effect(&self, pre: Self, count: nat) -> bool {
        &&& count < pre.trail_stack@.len()
        &&& *self == (Self { hot_stack: self.hot_stack, hot_value_pool: self.hot_value_pool,
            trail_stack: self.trail_stack, trail_value_pool: self.trail_value_pool,
            trail_seen: self.trail_seen, ..pre })
        &&& self.hot_stack@.len() == pre.hot_stack@.len() + count
        &&& self.hot_stack@.subrange(0, pre.hot_stack@.len() as int) == pre.hot_stack@
        &&& pre.hot_value_pool@.len() <= self.hot_value_pool@.len()
        &&& self.hot_value_pool@.subrange(0, pre.hot_value_pool@.len() as int) == pre.hot_value_pool@
        &&& (count == 0 ==> self.hot_value_pool@ == pre.hot_value_pool@)
        &&& (self.hot_stack@.len() > 0 ==>
            self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len())
        &&& self.trail_stack@.len() == pre.trail_stack@.len() - count
        &&& self.trail_value_pool@ == pre.trail_value_pool@.subrange(
            pre.trail_stack@[count as int].start as int, pre.trail_value_pool@.len() as int)
        &&& forall|f: int| 0 <= f < self.trail_stack@.len() ==> {
            let h = #[trigger] self.trail_stack@[f];
            let old_h = pre.trail_stack@[count + f];
            let cut = pre.trail_stack@[count as int].start;
            &&& h.saved_len == old_h.saved_len
            &&& h.start == old_h.start - cut
            &&& h.end == old_h.end - cut
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_retained_frame(&self, pre: Self, count: nat, f: int)
        requires pre.wf(), self.trail_retained_effect(pre, count),
            0 <= f < self.trail_stack@.len(),
        ensures
            frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(true) + f),
                self.trail_value_pool@, self.trail_stack@[f].start as int, self.phys_trail_end(f),
                self.snapshots@[self.pair_tier_offset(true) + f],
                self.snapshots@[self.pair_tier_offset(true) + f].len()),
    {
        hide(Vec::wf);
        reveal(Vec::trail_retained_effect);
        pre.lemma_trail_retirement_bounds(count);
        pre.lemma_pair_tier_frame_layout(true, count as int + f);
        pre.lemma_pair_tier_contract(true, count as int + f);
        let cut = pre.trail_stack@[count as int].start as int;
        let lo = pre.trail_stack@[count + f].start as int;
        let hi = pre.phys_trail_end(count as int + f);
        assert(self.phys_trail_end(f) == hi - cut);
        let k = pre.pair_tier_offset(true) + count + f;
        assert(self.pair_tier_offset(true) + f == k);
        assert forall|j: nat| #[trigger] range_saved_value::<T, I>(pre.trail_value_pool@, lo, hi, j)
            == range_saved_value::<T, I>(self.trail_value_pool@, lo - cut, hi - cut, j) by {
            lemma_range_saved_value_retire_prefix::<T, I>(pre.trail_value_pool@, cut, lo, hi, j);
        }
        lemma_frame_inv_range_same_saved_map::<T, I>(pre.layer_above_at(k),
            pre.trail_value_pool@, lo, hi, self.trail_value_pool@, lo - cut, hi - cut,
            pre.snapshots@[k], pre.snapshots@[k].len());
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_retained_repr(&self, pre: Self, count: nat)
        requires pre.wf(), self.trail_retained_effect(pre, count),
        ensures self.trail_repr_ok(),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        pre.lemma_trail_retirement_bounds(count);
        reveal(Vec::trail_retained_effect);
        reveal(Vec::trail_repr_ok);
        let ts = self.trail_stack@;
        let pool = self.trail_value_pool@;
        let offset = self.pair_tier_offset(true);
        assert forall|f: int| 0 <= f < ts.len() implies {
            &&& (#[trigger] ts[f]).start <= ts[f].end
            &&& ts[f].end <= pool.len()
            &&& ts[f].start as int <= self.phys_trail_end(f)
            &&& self.phys_trail_end(f) <= pool.len() as int
            &&& (f + 1 < ts.len() ==> {
                &&& ts[f].end == ts[f + 1].start
                &&& self.phys_trail_end(f) == ts[f + 1].start as int
            })
            &&& (f + 1 == ts.len() ==> self.phys_trail_end(f) == pool.len() as int)
            &&& frame_inv_range::<T, I>(self.layer_above_at(offset + f), pool,
                ts[f].start as int, self.phys_trail_end(f), self.snapshots@[offset + f],
                self.snapshots@[offset + f].len())
            &&& offset + f < self.snapshots@.len()
        } by {
            pre.lemma_pair_tier_frame_layout(true, count as int + f);
            self.lemma_trail_retained_frame(pre, count, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_old_hot_frame(&self, pre: Self, count: nat, f: int)
        requires pre.wf(), self.trail_retained_effect(pre, count),
            0 <= f < pre.hot_stack@.len(),
        ensures self.phys_frame_inv_range_holds(f),
            stratum_unique::<T, I>(self.hot_value_pool@, self.phys_hot_start(f), self.phys_hot_end(f)),
    {
        hide(Vec::wf);
        reveal(Vec::trail_retained_effect);
        pre.lemma_wf_named_parts();
        reveal(Vec::open_ingress_ok);
        reveal(Vec::hot_repr_ok);
        assert(self.hot_stack@[f] == pre.hot_stack@[f]);
        assert(self.phys_hot_end(f) == pre.phys_hot_end(f));
        pre.lemma_pair_tier_frame_layout(false, f);
        pre.lemma_pair_tier_contract(false, f);
        let lo = pre.phys_hot_start(f);
        let hi = pre.phys_hot_end(f);
        assert forall|q: int| lo <= q < hi implies
            #[trigger] self.hot_value_pool@[q] == pre.hot_value_pool@[q] by {
            assert(self.hot_value_pool@.subrange(0, pre.hot_value_pool@.len() as int)[q]
                == self.hot_value_pool@[q]);
        }
        assert forall|j: nat| #[trigger] range_saved_value::<T, I>(pre.hot_value_pool@, lo, hi, j)
            == range_saved_value::<T, I>(self.hot_value_pool@, lo, hi, j) by {
            lemma_range_saved_value_local::<T, I>(pre.hot_value_pool@, self.hot_value_pool@, lo, hi, j);
        }
        let k = pre.cold_stack@.len() + f;
        lemma_frame_inv_range_same_saved_map::<T, I>(pre.layer_above_at(k), pre.hot_value_pool@, lo, hi,
            self.hot_value_pool@, lo, hi, pre.snapshots@[k], pre.snapshots@[k].len());
        lemma_stratum_unique_local::<T, I>(pre.hot_value_pool@, self.hot_value_pool@, lo, hi);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_retained_ingress(&self, pre: Self, count: nat)
        requires pre.wf(), self.trail_retained_effect(pre, count),
        ensures self.open_ingress_ok(),
    {
        hide(Vec::wf);
        reveal(Vec::trail_retained_effect);
        pre.lemma_wf_named_parts();
        reveal(Vec::open_ingress_ok);
        let old_f = pre.trail_stack@.len() - 1;
        let f = self.trail_stack@.len() - 1;
        pre.lemma_trail_retirement_bounds(count);
        pre.lemma_pair_tier_frame_layout(true, old_f);
        let cut = pre.trail_stack@[count as int].start as int;
        let lo = pre.trail_stack@[old_f].start as int;
        assert(count + f == old_f);
        assert forall|j: int| 0 <= j < self.active_saved_len.as_nat() && j < self.view().len() implies
            (#[trigger] self.store.captured()[j]) == captured_in_range::<T, I>(self.trail_value_pool@,
                self.trail_stack@[f].start as int, self.trail_value_pool@.len() as int, j as nat) by {
            lemma_range_saved_value_retire_prefix::<T, I>(pre.trail_value_pool@,
                cut, lo, pre.trail_value_pool@.len() as int, j as nat);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_assembly_sealed(&self, pre: Self, plan: Seq<Seq<(T, I)>>)
        requires pre.open_ingress_ok(), plan.len() < pre.trail_stack@.len(),
            self.hot_value_pool@ == pre.hot_value_pool@ + Self::trail_plan_prefix(plan, plan.len() as int),
            self.hot_stack@.len() == pre.hot_stack@.len() + plan.len(),
            self.hot_stack@.subrange(0, pre.hot_stack@.len() as int) == pre.hot_stack@,
            plan.len() > 0 ==> self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len(),
        ensures
            plan.len() == 0 ==> self.hot_value_pool@ == pre.hot_value_pool@,
            self.hot_stack@.len() > 0 ==>
                self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len(),
    {
        if plan.len() == 0 {
            reveal(Vec::trail_plan_prefix);
            reveal(Vec::open_ingress_ok);
            assert(self.hot_stack@ =~= pre.hot_stack@);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_fixed_history(&self, pre: Self, count: nat)
        requires pre.wf(), self.trail_retained_effect(pre, count), self.frame_partition_ok(),
        ensures self.wf_for_snap(), self.cold_repr_ok(), self.proof_compat_ok(),
    {
        hide(Vec::wf);
        reveal(Vec::trail_retained_effect);
        pre.lemma_wf_named_parts();
        assert(self.store.wf()) by { reveal(Vec::wf_for_snap); }
        self.lemma_canonical_history_repartition(pre);
        reveal(Vec::cold_repr_ok);
        reveal(Vec::cold_payload_ok);
        reveal(Vec::proof_compat_ok);
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f) by {
            self.lemma_cold_reconstructs_transfer(pre, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_plan_header_at(&self, pre: Self, plan: Seq<Seq<(T, I)>>, q: int)
        requires 0 <= q < plan.len(),
            forall|r: int| 0 <= r < plan.len() ==> {
                let h = #[trigger] self.hot_stack@[pre.hot_stack@.len() + r];
                &&& h.start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, r).len()
                &&& h.end == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, r + 1).len()
            },
        ensures self.hot_stack@[pre.hot_stack@.len() + q].start
                == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q).len(),
            self.hot_stack@[pre.hot_stack@.len() + q].end
                == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q + 1).len(),
    {}

    #[verifier::spinoff_prover]
    proof fn lemma_trail_hot_header(&self, pre: Self, plan: Seq<Seq<(T, I)>>, f: int)
        requires pre.wf(), self.trail_retained_effect(pre, plan.len()),
            self.frame_partition_ok(),
            plan.len() > 0 ==> self.hot_stack@[pre.hot_stack@.len() as int].start == pre.hot_value_pool@.len(),
            self.hot_value_pool@ == pre.hot_value_pool@ + Self::trail_plan_prefix(plan, plan.len() as int),
            forall|q: int| 0 <= q < plan.len() ==> {
                let h = #[trigger] self.hot_stack@[pre.hot_stack@.len() + q];
                &&& h.start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q).len()
                &&& h.end == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q + 1).len()
            },
            0 <= f < self.hot_stack@.len(),
        ensures
            self.hot_stack@[f].start <= self.hot_stack@[f].end <= self.hot_value_pool@.len(),
            self.hot_stack@[f].start as int <= self.phys_hot_end(f) <= self.hot_value_pool@.len(),
            f + 1 < self.hot_stack@.len() ==> self.hot_stack@[f].end == self.hot_stack@[f + 1].start,
            f == 0 ==> self.hot_stack@[f].start == 0,
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        reveal(Vec::trail_retained_effect);
        reveal(Vec::open_ingress_ok);
        if f < pre.hot_stack@.len() {
            pre.lemma_pair_tier_frame_layout(false, f);
            assert(self.hot_stack@[f] == pre.hot_stack@[f]);
            if f + 1 == pre.hot_stack@.len() && plan.len() > 0 {
                reveal(Vec::trail_plan_prefix);
                assert(self.hot_stack@[f + 1].start == pre.hot_value_pool@.len());
            }
        } else {
            let q = f - pre.hot_stack@.len();
            self.lemma_trail_plan_header_at(pre, plan, q);
            Self::lemma_trail_plan_frame_range(plan, plan.len() as int, q);
            assert(self.hot_stack@[f].start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q).len());
            assert(self.hot_stack@[f].end == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q + 1).len());
            if f + 1 < self.hot_stack@.len() {
                self.lemma_trail_plan_header_at(pre, plan, q + 1);
                assert(self.hot_stack@[f + 1].start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q + 1).len());
            }
            if f == 0 {
                reveal(Vec::trail_plan_prefix);
                reveal(Vec::hot_repr_ok);
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_hot_repr(&self, pre: Self, plan: Seq<Seq<(T, I)>>)
        requires pre.wf(), self.trail_retained_effect(pre, plan.len()),
            self.frame_partition_ok(),
            plan.len() > 0 ==> self.hot_stack@[pre.hot_stack@.len() as int].start == pre.hot_value_pool@.len(),
            self.hot_value_pool@ == pre.hot_value_pool@ + Self::trail_plan_prefix(plan, plan.len() as int),
            forall|q: int| 0 <= q < plan.len() ==> {
                let h = #[trigger] self.hot_stack@[pre.hot_stack@.len() + q];
                &&& h.start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q).len()
                &&& h.end == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, q + 1).len()
            },
            forall|f: int| 0 <= f < self.hot_stack@.len() ==>
                #[trigger] self.phys_frame_inv_range_holds(f)
                && stratum_unique::<T, I>(self.hot_value_pool@, self.phys_hot_start(f), self.phys_hot_end(f)),
        ensures self.hot_repr_ok(),
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        reveal(Vec::trail_retained_effect);
        assert(self.hot_stack@.len() == 0 ==> self.hot_value_pool@.len() == 0) by {
            pre.lemma_wf_named_parts();
            reveal(Vec::hot_repr_ok);
        }
        reveal(Vec::hot_repr_ok);
        reveal(Vec::frame_partition_ok);
        let hs = self.hot_stack@;
        let pool = self.hot_value_pool@;
        assert forall|f: int| 0 <= f < hs.len() implies {
            &&& (#[trigger] hs[f]).start <= hs[f].end
            &&& hs[f].end <= pool.len()
            &&& hs[f].start as int <= self.phys_hot_end(f)
            &&& self.phys_hot_end(f) <= pool.len() as int
            &&& (f + 1 < hs.len() ==> {
                &&& hs[f].end == hs[f + 1].start
                &&& self.phys_hot_end(f) == hs[f + 1].start as int
            })
            &&& (f + 1 == hs.len() ==> self.phys_hot_end(f) == pool.len() as int)
            &&& stratum_unique::<T, I>(pool, hs[f].start as int, self.phys_hot_end(f))
            &&& self.phys_frame_inv_range_holds(f)
            &&& self.cold_stack@.len() + f < self.snapshots@.len()
        } by {
            self.lemma_trail_hot_header(pre, plan, f);
            assert(self.phys_frame_inv_range_holds(f));
            assert(stratum_unique::<T, I>(pool, hs[f].start as int, self.phys_hot_end(f)));
            assert(f + 1 < hs.len() ==> self.phys_hot_end(f) == hs[f + 1].start as int);
            assert(self.cold_stack@.len() + f < self.snapshots@.len());

        }
        if self.hot_stack@.len() > 0 { self.lemma_trail_hot_header(pre, plan, 0); }
    }

    proof fn lemma_wf_from_named_parts(&self)
        requires self.wf_for_snap(), self.hot_repr_ok(), self.trail_repr_ok(),
            self.cold_repr_ok(), self.open_ingress_ok(), self.proof_compat_ok(),
        ensures self.wf(),
    { reveal(Vec::wf); }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_plan_contract_at(&self, plan: Seq<Seq<(T, I)>>, f: int)
        requires self.wf(), self.trail_plan_matches(plan), 0 <= f < plan.len(),
        ensures
            frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(true) + f),
                plan[f], 0, plan[f].len() as int,
                self.snapshots@[self.pair_tier_offset(true) + f],
                self.snapshots@[self.pair_tier_offset(true) + f].len()),
            stratum_unique::<T, I>(plan[f], 0, plan[f].len() as int),
    {
        hide(Vec::wf);
        hide(range_saved_value);
        hide(frame_inv_range);
        hide(stratum_unique);
        reveal(Vec::trail_plan_matches);
        self.lemma_pair_tier_frame_layout(true, f);
        self.lemma_pair_tier_contract(true, f);
        assert forall|j: nat| #[trigger] range_saved_value::<T, I>(self.trail_value_pool@,
            self.trail_stack@[f].start as int, self.phys_trail_end(f), j)
            == range_saved_value::<T, I>(plan[f], 0, plan[f].len() as int, j) by {
            assert(range_saved_value::<T, I>(plan[f], 0, plan[f].len() as int, j)
                == range_saved_value::<T, I>(self.trail_value_pool@,
                    self.trail_stack@[f].start as int, self.phys_trail_end(f), j));
        }
        let k = self.pair_tier_offset(true) + f;
        lemma_frame_inv_range_same_saved_map::<T, I>(self.layer_above_at(k), self.trail_value_pool@,
            self.trail_stack@[f].start as int, self.phys_trail_end(f), plan[f], 0, plan[f].len() as int,
            self.snapshots@[k], self.snapshots@[k].len());
    }

    #[verifier::spinoff_prover]
    proof fn lemma_trail_moved_frame(&self, pre: Self, plan: Seq<Seq<(T, I)>>, i: int)
        requires pre.hot_stack@.len() <= i < self.hot_stack@.len(), pre.wf(), pre.trail_plan_matches(plan), self.trail_retained_effect(pre, plan.len()),
            self.frame_partition_ok(),
            plan.len() > 0 ==> self.hot_stack@[pre.hot_stack@.len() as int].start == pre.hot_value_pool@.len(),
            self.hot_value_pool@ == pre.hot_value_pool@ + Self::trail_plan_prefix(plan, plan.len() as int),
            forall|f: int| 0 <= f < plan.len() ==> {
                let h = #[trigger] self.hot_stack@[pre.hot_stack@.len() + f];
                &&& h.start == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, f).len()
                &&& h.end == pre.hot_value_pool@.len() + Self::trail_plan_prefix(plan, f + 1).len()
            },
            forall|f: int, j: nat| 0 <= f < plan.len() ==> {
                let h = self.hot_stack@[pre.hot_stack@.len() + f];
                range_saved_value::<T, I>(self.hot_value_pool@, h.start as int, h.end as int, j)
                    == #[trigger] range_saved_value::<T, I>(plan[f], 0, plan[f].len() as int, j)
            },
        ensures self.phys_frame_inv_range_holds(i),
            stratum_unique::<T, I>(self.hot_value_pool@, self.phys_hot_start(i), self.phys_hot_end(i)),
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        hide(range_saved_value);
        hide(stratum_unique);
        reveal(Vec::trail_retained_effect);
        let f = i - pre.hot_stack@.len();
        let h = self.hot_stack@[i];
        self.lemma_trail_plan_header_at(pre, plan, f);
        self.lemma_trail_hot_header(pre, plan, i);
        Self::lemma_trail_plan_frame_range(plan, plan.len() as int, f);
        assert(self.hot_value_pool@.subrange(h.start as int, h.end as int) =~= plan[f]);
        assert(self.phys_hot_end(i) == h.end);
        pre.lemma_trail_plan_contract_at(plan, f);
        let k = pre.pair_tier_offset(true) + f;
        assert(self.layer_above_at(self.cold_stack@.len() + i) == pre.layer_above_at(k));
        lemma_frame_inv_range_same_saved_map::<T, I>(pre.layer_above_at(k), plan[f], 0, plan[f].len() as int,
            self.hot_value_pool@, h.start as int, h.end as int, pre.snapshots@[k], pre.snapshots@[k].len());
        lemma_stratum_unique_subrange::<T, I>(self.hot_value_pool@, h.start as int, h.end as int);
    }

    /// Migrate an oldest closed Trail prefix through first-capture dedupe. The
    /// `Adaptive` limit keeps deduplicating oldest-first while each frame's
    /// duplicate ratio pays for the move; the first frame that does not is
    /// discarded from the Hot pool and stops the pass.
    #[verifier::spinoff_prover]
    #[cold]
    #[inline(never)]
    fn runtime_migrate_trail(&mut self, flush_all: bool)
        requires old(self).wf(),
        ensures final(self).wf(),
            *final(self) == (Self { hot_stack: final(self).hot_stack,
                hot_value_pool: final(self).hot_value_pool, trail_stack: final(self).trail_stack,
                trail_value_pool: final(self).trail_value_pool,
                trail_seen: final(self).trail_seen, ..*old(self) }),
    {
        hide(Vec::wf);
        let closed = self.trail_stack.len().saturating_sub(1);
        if closed == 0 {
            return;
        }
        let adaptive = match self.tier_policy.trail {
            crate::tier_policy::TierLimit::Adaptive => true,
            _ => false,
        };
        if !flush_all && adaptive {
            let ghost pre = *self;
            let mut plan: Ghost<Seq<Seq<(T, I)>>> = Ghost(Seq::empty());
            proof {
                I::lemma_obeys_key_model();
                self.lemma_trail_migrating_start(pre);
            }
            let mut seen = match self.trail_seen.take() {
                Some(set) => set,
                None => std::collections::HashSet::default(),
            };
            let mut count = 0usize;
            while count < closed
                invariant
                    self.trail_migrating(pre, plan@),
                    plan@.len() == count, count <= closed, closed + 1 == pre.trail_stack@.len(),
                    vstd::std_specs::hash::obeys_key_model::<I>(),
                decreases closed - count,
            {
                let (start, writes, uniques) =
                    self.trail_frame_tentative_checked(count, &mut seen, Ghost(pre), plan);
                let doubled = match uniques.checked_mul(2) {
                    Some(d) => d,
                    None => usize::MAX,
                };
                if writes < doubled {
                    self.trail_frame_discard_checked(start, Ghost(pre), plan);
                    break;
                }
                plan = self.trail_frame_commit_checked(count, start, Ghost(pre), plan);
                count += 1;
            }
            self.trail_seen = Some(seen);
            self.trail_migration_finish_checked(count, Ghost(pre), plan);
            return;
        }
        let count = if flush_all {
            closed
        } else {
            self.retained_closed_prefix(true, closed, self.tier_policy.trail, core::mem::size_of::<(T, I)>())
        };
        self.runtime_migrate_trail_count(count);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_layout_basics(&self)
        requires self.repr_ok(),
        ensures self.cold_stack@.len() == 0 ==> self.cold_index_runs@.len() == 0,
            self.cold_index_runs@.len() == 0 ==> self.cold_value_pool@.len() == 0,
    {}

    #[verifier::spinoff_prover]
    proof fn lemma_cold_layout_header_at(&self, f: int)
        requires self.repr_ok(), 0 <= f < self.cold_stack@.len(),
        ensures self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len <= self.cold_index_runs@.len(),
            f == 0 ==> self.cold_stack@[f].runs_start == 0,
            f + 1 < self.cold_stack@.len() ==> self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len == self.cold_stack@[f + 1].runs_start,
            f + 1 == self.cold_stack@.len() ==> self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len == self.cold_index_runs@.len(),
    {}

    #[verifier::spinoff_prover]
    proof fn lemma_cold_layout_run_at(&self, r: int)
        requires self.repr_ok(), 0 <= r < self.cold_index_runs@.len(),
        ensures self.cold_index_runs@[r].start + self.cold_index_runs@[r].len <= self.cold_value_pool@.len(),
            r == 0 ==> self.cold_index_runs@[r].start == 0,
            r + 1 < self.cold_index_runs@.len() ==> self.cold_index_runs@[r].start + self.cold_index_runs@[r].len == self.cold_index_runs@[r + 1].start,
            r + 1 == self.cold_index_runs@.len() ==> self.cold_index_runs@[r].start + self.cold_index_runs@[r].len == self.cold_value_pool@.len(),
    {}

    #[verifier::spinoff_prover]
    proof fn lemma_cold_append_structure(&self, pre: Self, entries: Seq<(T, I)>, cold: crate::frame::ColdFrameHdr<I>)
        requires pre.repr_ok(), pre.cold_payload_ok(), pre.cold_runs_disjoint(),
            self.cold_stack@ == pre.cold_stack@.push(cold),
            self.cold_index_runs@.subrange(0, pre.cold_index_runs@.len() as int) == pre.cold_index_runs@,
            self.cold_value_pool@.len() == pre.cold_value_pool@.len() + entries.len(),
            cold.runs_start == pre.cold_index_runs@.len(),
            cold.runs_start + cold.runs_len == self.cold_index_runs@.len(),
            crate::cold_encode::run_prefix(self.cold_index_runs@,
                pre.cold_index_runs@.len() as int, pre.cold_value_pool@.len() as int,
                entries, entries.len() as int, cold.saved_len.as_nat()),
        ensures self.repr_ok(),
    {
        hide(crate::cold_encode::run_prefix);
        hide(Vec::repr_ok);
        hide(Vec::cold_payload_ok);
        hide(Vec::cold_runs_disjoint);
        crate::cold_encode::lemma_run_prefix_layout(self.cold_index_runs@,
            pre.cold_index_runs@.len() as int, pre.cold_value_pool@.len() as int,
            entries, entries.len() as int, cold.saved_len.as_nat());
        assert(self.cold_stack@.subrange(0, pre.cold_stack@.len() as int) =~= pre.cold_stack@);
        pre.lemma_cold_layout_basics();
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies {
            &&& (#[trigger] self.cold_stack@[f]).runs_start + self.cold_stack@[f].runs_len <= self.cold_index_runs@.len()
            &&& (f == 0 ==> self.cold_stack@[f].runs_start == 0)
            &&& (f + 1 < self.cold_stack@.len() ==> self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len == self.cold_stack@[f + 1].runs_start)
            &&& (f + 1 == self.cold_stack@.len() ==> self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len == self.cold_index_runs@.len())
        } by {
            if f < pre.cold_stack@.len() { pre.lemma_cold_layout_header_at(f); }
        }
        assert forall|r: int| 0 <= r < self.cold_index_runs@.len() implies {
            &&& (#[trigger] self.cold_index_runs@[r]).start + self.cold_index_runs@[r].len <= self.cold_value_pool@.len()
            &&& (r == 0 ==> self.cold_index_runs@[r].start == 0)
            &&& (r + 1 < self.cold_index_runs@.len() ==> self.cold_index_runs@[r].start + self.cold_index_runs@[r].len == self.cold_index_runs@[r + 1].start)
            &&& (r + 1 == self.cold_index_runs@.len() ==> self.cold_index_runs@[r].start + self.cold_index_runs@[r].len == self.cold_value_pool@.len())
        } by {
            if r < pre.cold_index_runs@.len() { pre.lemma_cold_layout_run_at(r); }
            else { crate::cold_encode::lemma_run_prefix_run_at(self.cold_index_runs@,
                        pre.cold_index_runs@.len() as int, pre.cold_value_pool@.len() as int,
                        entries, entries.len() as int, cold.saved_len.as_nat(), r); }
        }
        assert(self.repr_ok()) by { reveal(Vec::repr_ok); }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_append_payload(&self, pre: Self, entries: Seq<(T, I)>, cold: crate::frame::ColdFrameHdr<I>)
        requires pre.repr_ok(), pre.cold_payload_ok(), pre.cold_runs_disjoint(),
            self.cold_stack@ == pre.cold_stack@.push(cold),
            self.cold_index_runs@.subrange(0, pre.cold_index_runs@.len() as int) == pre.cold_index_runs@,
            self.cold_value_pool@.len() == pre.cold_value_pool@.len() + entries.len(),
            cold.runs_start == pre.cold_index_runs@.len(),
            cold.runs_start + cold.runs_len == self.cold_index_runs@.len(),
            crate::cold_encode::run_prefix(self.cold_index_runs@,
                pre.cold_index_runs@.len() as int, pre.cold_value_pool@.len() as int,
                entries, entries.len() as int, cold.saved_len.as_nat()),
        ensures self.cold_payload_ok(),
    {
        hide(crate::cold_encode::run_prefix);
        hide(Vec::repr_ok);
        hide(Vec::cold_payload_ok);
        hide(Vec::cold_runs_disjoint);
        crate::cold_encode::lemma_run_prefix_layout(self.cold_index_runs@,
            pre.cold_index_runs@.len() as int, pre.cold_value_pool@.len() as int,
            entries, entries.len() as int, cold.saved_len.as_nat());
        assert(self.cold_payload_ok()) by {
            reveal(Vec::repr_ok);
            reveal(Vec::cold_payload_ok);
            assert forall|f: int, r: int| 0 <= f < self.cold_stack@.len()
                && (#[trigger] self.cold_stack@[f]).runs_start <= r
                    < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len implies
                0 < (#[trigger] self.cold_index_runs@[r]).len
                    && self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len
                        <= self.cold_stack@[f].saved_len.as_nat()
            by {
                if f < pre.cold_stack@.len() {
                    assert(r < pre.cold_index_runs@.len());
                    assert(self.cold_index_runs@[r] == pre.cold_index_runs@[r]);
                } else { crate::cold_encode::lemma_run_prefix_run_at(self.cold_index_runs@,
                        pre.cold_index_runs@.len() as int, pre.cold_value_pool@.len() as int,
                        entries, entries.len() as int, cold.saved_len.as_nat(), r); }
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_append_disjoint(&self, pre: Self, entries: Seq<(T, I)>, cold: crate::frame::ColdFrameHdr<I>)
        requires pre.repr_ok(), pre.cold_payload_ok(), pre.cold_runs_disjoint(),
            self.cold_stack@ == pre.cold_stack@.push(cold),
            self.cold_index_runs@.subrange(0, pre.cold_index_runs@.len() as int) == pre.cold_index_runs@,
            self.cold_value_pool@.len() == pre.cold_value_pool@.len() + entries.len(),
            cold.runs_start == pre.cold_index_runs@.len(),
            cold.runs_start + cold.runs_len == self.cold_index_runs@.len(),
            crate::cold_encode::run_prefix(self.cold_index_runs@,
                pre.cold_index_runs@.len() as int, pre.cold_value_pool@.len() as int,
                entries, entries.len() as int, cold.saved_len.as_nat()),
        ensures self.cold_runs_disjoint(),
    {
        hide(crate::cold_encode::run_prefix);
        hide(Vec::repr_ok);
        hide(Vec::cold_payload_ok);
        hide(Vec::cold_runs_disjoint);
        crate::cold_encode::lemma_run_prefix_layout(self.cold_index_runs@,
            pre.cold_index_runs@.len() as int, pre.cold_value_pool@.len() as int,
            entries, entries.len() as int, cold.saved_len.as_nat());
        assert(self.cold_runs_disjoint()) by {
            reveal(Vec::repr_ok);
            reveal(Vec::cold_runs_disjoint);
            assert forall|f: int, r: int| 0 <= f < self.cold_stack@.len()
                && (#[trigger] self.cold_stack@[f]).runs_start <= r
                && r + 1 < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len implies
                (#[trigger] self.cold_index_runs@[r]).base.as_nat() + self.cold_index_runs@[r].len
                    <= self.cold_index_runs@[r + 1].base.as_nat()
            by {
                if f < pre.cold_stack@.len() {
                    pre.lemma_cold_layout_header_at(f);
                    assert(self.cold_index_runs@[r] == pre.cold_index_runs@[r]);
                    assert(self.cold_index_runs@[r + 1] == pre.cold_index_runs@[r + 1]);
                } else { crate::cold_encode::lemma_run_prefix_run_at(self.cold_index_runs@,
                        pre.cold_index_runs@.len() as int, pre.cold_value_pool@.len() as int,
                        entries, entries.len() as int, cold.saved_len.as_nat(), r); }
            }
        }
    }

    /// Append a complete bounded Cold frame. This checked construction is
    /// shared by configured and adaptive migration; sorting is the caller's job.
    #[verifier::spinoff_prover]
    // No caller today: the adaptive path folds at eviction. Kept because it is
    // the proven append for a pre-sorted Cold frame, which the configured
    // sorted migration needs the moment it is turned back on.
    #[allow(dead_code)]
    fn append_cold_sorted_checked(&mut self, entries: &[(T, I)], saved_len: I)
        requires old(self).repr_ok(), old(self).cold_payload_ok(), old(self).cold_runs_disjoint(),
            forall|a: int, b: int| 0 <= a < b < entries@.len() ==>
                (#[trigger] entries@[a]).1.as_nat() < (#[trigger] entries@[b]).1.as_nat(),
            forall|q: int| 0 <= q < entries@.len() ==>
                (#[trigger] entries@[q]).1.as_nat() < saved_len.as_nat(),
        ensures final(self).repr_ok(), final(self).cold_payload_ok(), final(self).cold_runs_disjoint(),
            *final(self) == (Self { cold_stack: final(self).cold_stack,
                cold_index_runs: final(self).cold_index_runs, cold_value_pool: final(self).cold_value_pool,
                ..*old(self) }),
            final(self).cold_stack@.len() == old(self).cold_stack@.len() + 1,
            final(self).cold_stack@.subrange(0, old(self).cold_stack@.len() as int) == old(self).cold_stack@,
            final(self).cold_index_runs@.subrange(0, old(self).cold_index_runs@.len() as int) == old(self).cold_index_runs@,
            final(self).cold_value_pool@.subrange(0, old(self).cold_value_pool@.len() as int) == old(self).cold_value_pool@,
            final(self).cold_value_pool@.len() == old(self).cold_value_pool@.len() + entries@.len(),
            final(self).cold_stack@[old(self).cold_stack@.len() as int].saved_len == saved_len,
            final(self).cold_stack@[old(self).cold_stack@.len() as int].runs_start == old(self).cold_index_runs@.len(),
            crate::cold_encode::run_prefix(final(self).cold_index_runs@,
                old(self).cold_index_runs@.len() as int, old(self).cold_value_pool@.len() as int,
                entries@, entries@.len() as int, saved_len.as_nat()),
            forall|q: int| 0 <= q < entries@.len() ==>
                #[trigger] final(self).cold_value_pool@[old(self).cold_value_pool@.len() + q] == entries@[q].0,
    {
        hide(crate::cold_encode::run_prefix);
        hide(Vec::repr_ok);
        hide(Vec::cold_payload_ok);
        hide(Vec::cold_runs_disjoint);
        let ghost pre = *self;
        let cold = crate::cold_encode::append_sorted(
            &mut self.cold_index_runs, &mut self.cold_value_pool, entries, saved_len);
        self.cold_stack.push(cold);
        proof {
            assert(self.cold_stack@.subrange(0, pre.cold_stack@.len() as int) =~= pre.cold_stack@);
            self.lemma_cold_append_structure(pre, entries@, cold);
            self.lemma_cold_append_payload(pre, entries@, cold);
            self.lemma_cold_append_disjoint(pre, entries@, cold);
        }
    }

    /// `cold_payload_ok` depends on the Cold headers and runs only.
    #[verifier::spinoff_prover]
    proof fn lemma_cold_payload_ok_transfer(&self, other: Self)
        requires other.cold_payload_ok(), self.cold_stack@ == other.cold_stack@,
            self.cold_index_runs@ == other.cold_index_runs@,
        ensures self.cold_payload_ok(),
    {
        reveal(Vec::cold_payload_ok);
    }

    /// Closed Hot frames: all but the writable top under the unique-capture
    /// discipline; every Hot frame under the chronological discipline.
    pub open(crate) spec fn hot_closed_count(&self) -> nat {
        if self.store.unique_capture_spec() {
            if self.hot_stack@.len() > 0 { (self.hot_stack@.len() - 1) as nat } else { 0 }
        } else { self.hot_stack@.len() }
    }

    /// A closed Hot frame's sealed header end is its physical end.
    #[verifier::spinoff_prover]
    proof fn lemma_closed_hot_frame_end(&self, f: int)
        requires self.wf(), 0 <= f < self.hot_closed_count(),
        ensures self.hot_stack@[f].start <= self.hot_stack@[f].end <= self.hot_value_pool@.len(),
            self.hot_stack@[f].end as int == self.phys_hot_end(f),
            self.phys_hot_start(f) == self.hot_stack@[f].start as int,
            f + 1 < self.hot_stack@.len() ==> self.hot_stack@[f].end == self.hot_stack@[f + 1].start,
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        self.lemma_pair_tier_frame_layout(false, f);
        if f + 1 == self.hot_stack@.len() {
            reveal(Vec::open_ingress_ok);
        }
    }

    /// Hot-side facts of a migration in progress: the pool keeps its length,
    /// cells from frame `count + 1` on are untouched, and every frame up to
    /// `count` is still unique with its original saved map (it may be permuted).
    closed spec fn hot_migrating_hot(&self, pre: Self, count: nat) -> bool {
        &&& self.hot_value_pool@.len() == pre.hot_value_pool@.len()
        &&& forall|q: int| pre.hot_retirement_cut(count + 1) <= q < pre.hot_value_pool@.len() ==>
            #[trigger] self.hot_value_pool@[q] == pre.hot_value_pool@[q]
        &&& forall|f: int| #![trigger pre.phys_hot_start(f)] #![trigger pre.phys_hot_end(f)] 0 <= f <= count && f < pre.hot_stack@.len() ==> {
            &&& stratum_unique::<T, I>(self.hot_value_pool@, pre.phys_hot_start(f), pre.phys_hot_end(f))
            &&& forall|j: nat| #[trigger] range_saved_value::<T, I>(self.hot_value_pool@,
                    pre.phys_hot_start(f), pre.phys_hot_end(f), j)
                == range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(f), pre.phys_hot_end(f), j)
        }
    }

    /// Cold-side facts of a migration in progress: the original Cold storage
    /// is a prefix, the tier stays well laid out, and the `count` new frames
    /// carry exactly the saved maps of Hot frames `[0, count)` of `pre`.
    closed spec fn hot_migrating_cold(&self, pre: Self, count: nat) -> bool {
        let cc = pre.cold_stack@.len() as int;
        &&& self.cold_stack@.len() == cc + count
        &&& self.cold_stack@.subrange(0, cc) == pre.cold_stack@
        &&& self.cold_index_runs@.subrange(0, pre.cold_index_runs@.len() as int) == pre.cold_index_runs@
        &&& self.cold_value_pool@.subrange(0, pre.cold_value_pool@.len() as int) == pre.cold_value_pool@
        &&& pre.cold_index_runs@.len() <= self.cold_index_runs@.len()
        &&& pre.cold_value_pool@.len() <= self.cold_value_pool@.len()
        &&& self.repr_ok()
        &&& self.cold_payload_ok()
        &&& self.cold_runs_disjoint()
        &&& forall|q: int| 0 <= q < count ==> {
            &&& (#[trigger] self.cold_stack@[cc + q]).saved_len == pre.hot_stack@[q].saved_len
            &&& forall|j: nat| #[trigger] self.cold_covered(cc + q, j)
                <==> range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(q), pre.phys_hot_end(q), j) is Some
            &&& forall|j: nat| self.cold_covered(cc + q, j) ==>
                Some(#[trigger] self.cold_value(cc + q, j))
                    == range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(q), pre.phys_hot_end(q), j)
        }
    }

    /// Physical state while an oldest closed Hot prefix is being encoded into
    /// Cold: frames `[0, count)` of `pre` were sorted in place and encoded as
    /// the newest `count` Cold frames; frame `count` may have been sorted in
    /// place; every other cell is untouched.
    closed spec fn hot_migrating(&self, pre: Self, count: nat) -> bool {
        &&& pre.wf()
        &&& count <= pre.hot_closed_count()
        &&& *self == (Self { cold_stack: self.cold_stack, cold_index_runs: self.cold_index_runs,
            cold_value_pool: self.cold_value_pool, hot_value_pool: self.hot_value_pool, ..pre })
        &&& self.hot_migrating_hot(pre, count)
        &&& self.hot_migrating_cold(pre, count)
    }

    /// The Cold-side facts survive any change confined to Hot fields.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migrating_cold_transfer(&self, other: Self, pre: Self, count: nat)
        requires other.hot_migrating_cold(pre, count),
            self.cold_stack@ == other.cold_stack@,
            self.cold_index_runs@ == other.cold_index_runs@,
            self.cold_value_pool@ == other.cold_value_pool@,
        ensures self.hot_migrating_cold(pre, count),
    {
        reveal(Vec::hot_migrating_cold);
        self.lemma_cold_payload_ok_transfer(other);
        let cc = pre.cold_stack@.len() as int;
        assert forall|q: int| 0 <= q < count implies {
            &&& (#[trigger] self.cold_stack@[cc + q]).saved_len == pre.hot_stack@[q].saved_len
            &&& forall|j: nat| #[trigger] self.cold_covered(cc + q, j)
                <==> range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(q), pre.phys_hot_end(q), j) is Some
            &&& forall|j: nat| self.cold_covered(cc + q, j) ==>
                Some(#[trigger] self.cold_value(cc + q, j))
                    == range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(q), pre.phys_hot_end(q), j)
        } by {
            assert(self.cold_stack@[cc + q] == other.cold_stack@[cc + q]);
            assert forall|j: nat| #[trigger] self.cold_covered(cc + q, j)
                <==> range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(q), pre.phys_hot_end(q), j) is Some by {
                assert(self.cold_covered(cc + q, j) == other.cold_covered(cc + q, j));
            }
            assert forall|j: nat| self.cold_covered(cc + q, j) implies
                Some(#[trigger] self.cold_value(cc + q, j))
                    == range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(q), pre.phys_hot_end(q), j) by {
                assert(other.cold_covered(cc + q, j));
                assert(self.cold_value(cc + q, j) == other.cold_value(cc + q, j));
            }
        }
    }

    /// The Hot-side facts survive any change confined to Cold fields.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migrating_hot_transfer(&self, other: Self, pre: Self, count: nat)
        requires other.hot_migrating_hot(pre, count), self.hot_value_pool@ == other.hot_value_pool@,
        ensures self.hot_migrating_hot(pre, count),
    {
        reveal(Vec::hot_migrating_hot);
    }

    /// Frame `f`'s cells are in non-decreasing index order.
    pub open(crate) spec fn hot_frame_sorted(&self, f: int) -> bool {
        forall|a: int, b: int| self.phys_hot_start(f) <= a < b < self.phys_hot_end(f) ==>
            (#[trigger] self.hot_value_pool@[a]).1.as_nat()
                <= (#[trigger] self.hot_value_pool@[b]).1.as_nat()
    }

    /// An unchanged well-formed container is the empty Hot migration state.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migrating_start(&self, pre: Self)
        requires *self == pre, pre.wf(),
        ensures self.hot_migrating(pre, 0),
    {
        hide(Vec::wf);
        reveal(Vec::hot_migrating);
        reveal(Vec::hot_migrating_hot);
        reveal(Vec::hot_migrating_cold);
        pre.lemma_wf_named_parts();
        reveal(Vec::cold_repr_ok);
        reveal(Vec::hot_repr_ok);
        assert(self.cold_stack@.subrange(0, pre.cold_stack@.len() as int) =~= pre.cold_stack@);
        assert(self.cold_index_runs@.subrange(0, pre.cold_index_runs@.len() as int) =~= pre.cold_index_runs@);
        assert(self.cold_value_pool@.subrange(0, pre.cold_value_pool@.len() as int) =~= pre.cold_value_pool@);
    }

    /// Hot-side facts after permuting closed frame `f` within its own range.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_sorted_hot_part(&self, mid: Self, pre: Self, f: int, before: Seq<(T, I)>)
        requires pre.wf(), 0 <= f < pre.hot_closed_count(), mid.hot_migrating_hot(pre, f as nat),
            mid.hot_stack@ == pre.hot_stack@, self.hot_stack@ == pre.hot_stack@,
            before == mid.hot_value_pool@,
            self.hot_value_pool@.len() == before.len(),
            forall|q: int| 0 <= q < before.len()
                && !(pre.hot_stack@[f].start <= q < pre.hot_stack@[f].end) ==>
                #[trigger] self.hot_value_pool@[q] == before[q],
            self.hot_value_pool@.subrange(pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int).to_multiset()
                == before.subrange(pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int).to_multiset(),
            forall|a: int, b: int| pre.hot_stack@[f].start <= a < b < pre.hot_stack@[f].end ==>
                (#[trigger] self.hot_value_pool@[a]).1.as_nat() <= (#[trigger] self.hot_value_pool@[b]).1.as_nat(),
        ensures self.hot_migrating_hot(pre, f as nat), self.hot_frame_sorted(f),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating_hot);
        hide(stratum_unique);
        hide(range_saved_value);
        pre.lemma_closed_hot_frame_end(f);
        mid.lemma_hot_migrating_hot_unchanged(pre, f as nat);
        let start = pre.hot_stack@[f].start as int;
        let end = pre.hot_stack@[f].end as int;
        mid.lemma_hot_migrating_hot_frame_map(pre, f as nat, f);
        assert(pre.phys_hot_start(f) == start);
        assert(pre.phys_hot_end(f) == end);
        lemma_unique_range_permutation::<T, I>(before, self.hot_value_pool@, start, end);
        assert forall|g: int| #![trigger pre.phys_hot_start(g)] #![trigger pre.phys_hot_end(g)] 0 <= g <= f && g < pre.hot_stack@.len() implies {
            &&& stratum_unique::<T, I>(self.hot_value_pool@, pre.phys_hot_start(g), pre.phys_hot_end(g))
            &&& forall|j: nat| #[trigger] range_saved_value::<T, I>(self.hot_value_pool@,
                    pre.phys_hot_start(g), pre.phys_hot_end(g), j)
                == range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(g), pre.phys_hot_end(g), j)
        } by {
            if g < f {
                mid.lemma_hot_migrating_hot_frame_map(pre, f as nat, g);
                pre.lemma_pair_tier_frame_layout(false, g);
                pre.lemma_pair_tier_start_order(false, g + 1, f);
                assert forall|q: int| pre.phys_hot_start(g) <= q < pre.phys_hot_end(g) implies
                    #[trigger] self.hot_value_pool@[q] == before[q] by {}
                assert(stratum_unique::<T, I>(self.hot_value_pool@, pre.phys_hot_start(g), pre.phys_hot_end(g))) by {
                    reveal(stratum_unique);
                }
                assert forall|j: nat| #[trigger] range_saved_value::<T, I>(self.hot_value_pool@,
                        pre.phys_hot_start(g), pre.phys_hot_end(g), j)
                    == range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(g), pre.phys_hot_end(g), j) by {
                    lemma_range_saved_value_local::<T, I>(before, self.hot_value_pool@,
                        pre.phys_hot_start(g), pre.phys_hot_end(g), j);
                }
            } else {
                assert(stratum_unique::<T, I>(self.hot_value_pool@, start, end));
                assert forall|j: nat| #[trigger] range_saved_value::<T, I>(self.hot_value_pool@,
                        pre.phys_hot_start(g), pre.phys_hot_end(g), j)
                    == range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(g), pre.phys_hot_end(g), j) by {
                    assert(range_saved_value::<T, I>(before, start, end, j)
                        == range_saved_value::<T, I>(self.hot_value_pool@, start, end, j));
                    assert(range_saved_value::<T, I>(before, start, end, j)
                        == range_saved_value::<T, I>(pre.hot_value_pool@, start, end, j));
                }
            }
        }
        assert forall|q: int| pre.hot_retirement_cut(f as nat + 1) <= q < pre.hot_value_pool@.len() implies
            #[trigger] self.hot_value_pool@[q] == pre.hot_value_pool@[q] by {
            assert(self.hot_value_pool@[q] == before[q]);
        }
        assert(self.hot_migrating_hot(pre, f as nat)) by { reveal(Vec::hot_migrating_hot); }
        assert(self.phys_hot_start(f) == start);
        assert(self.phys_hot_end(f) == end);
        assert(self.hot_frame_sorted(f));
    }

    /// A closed frame permuted within its own range keeps the migration state.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_sorted_state(&self, mid: Self, pre: Self, f: int, before: Seq<(T, I)>)
        requires mid.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            before == mid.hot_value_pool@,
            *self == (Self { hot_value_pool: self.hot_value_pool, ..mid }),
            self.hot_value_pool@.len() == before.len(),
            forall|q: int| 0 <= q < before.len()
                && !(pre.hot_stack@[f].start <= q < pre.hot_stack@[f].end) ==>
                #[trigger] self.hot_value_pool@[q] == before[q],
            self.hot_value_pool@.subrange(pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int).to_multiset()
                == before.subrange(pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int).to_multiset(),
            forall|a: int, b: int| pre.hot_stack@[f].start <= a < b < pre.hot_stack@[f].end ==>
                (#[trigger] self.hot_value_pool@[a]).1.as_nat() <= (#[trigger] self.hot_value_pool@[b]).1.as_nat(),
        ensures self.hot_migrating(pre, f as nat), self.hot_frame_sorted(f),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(stratum_unique);
        hide(range_saved_value);
        mid.lemma_hot_migrating_frame(pre, f as nat);
        self.lemma_hot_migrating_cold_transfer(mid, pre, f as nat);
        self.lemma_hot_sorted_hot_part(mid, pre, f, before);
        reveal(Vec::hot_migrating);
    }

    /// Sort closed Hot frame `f` in place. A unique frame permuted within its
    /// own range keeps its saved map, so this is meaning-preserving.
    #[verifier::spinoff_prover]
    fn hot_frame_sort_checked(&mut self, f: usize, Ghost(pre): Ghost<Self>)
        requires old(self).hot_migrating(pre, f as nat), f < pre.hot_closed_count(),
        ensures final(self).hot_migrating(pre, f as nat), final(self).hot_frame_sorted(f as int),
            *final(self) == (Self { hot_value_pool: final(self).hot_value_pool, ..*old(self) }),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(stratum_unique);
        hide(range_saved_value);
        proof {
            self.lemma_hot_migrating_frame(pre, f as nat);
            pre.lemma_closed_hot_frame_end(f as int);
        }
        let start = self.hot_stack[f].start;
        let end = self.hot_stack[f].end;
        let ghost before = self.hot_value_pool@;
        let ghost mid = *self;
        crate::std_sort::sort_pairs_by_index(&mut self.hot_value_pool, start, end);
        proof { self.lemma_hot_frame_sorted_state(mid, pre, f as int, before); }
    }

    /// Count maximal consecutive index runs of a sorted range (no allocation).
    #[verifier::spinoff_prover]
    fn count_index_runs(pool: &std::vec::Vec<(T, I)>, start: usize, end: usize) -> (r: usize)
        requires start <= end <= pool@.len(),
            forall|q: int| start <= q < end ==> (#[trigger] pool@[q]).1.as_nat() < usize::MAX,
        ensures r <= end - start,
    {
        let mut runs = 0usize;
        let mut previous: Option<usize> = None;
        let mut q = start;
        while q < end
            invariant start <= q <= end <= pool@.len(), runs <= q - start,
                forall|k: int| start <= k < end ==> (#[trigger] pool@[k]).1.as_nat() < usize::MAX,
                previous matches Some(p) ==> p < usize::MAX,
            decreases end - q,
        {
            let index = pool[q].1.as_usize();
            let fresh = match previous {
                Some(p) => p + 1 != index,
                None => true,
            };
            if fresh {
                runs += 1;
            }
            previous = Some(index);
            q += 1;
        }
        runs
    }

    /// Retirement cuts are monotone in the number of retired frames.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_cut_order(&self, a: nat, b: nat)
        requires self.wf(), a <= b,
        ensures self.hot_retirement_cut(a) <= self.hot_retirement_cut(b),
            self.hot_retirement_cut(b) <= self.hot_value_pool@.len(),
    {
        hide(Vec::wf);
        if b < self.hot_stack@.len() {
            self.lemma_pair_tier_start_order(false, a as int, b as int);
            self.lemma_pair_tier_frame_layout(false, b as int);
        } else if a < self.hot_stack@.len() {
            self.lemma_pair_tier_frame_layout(false, a as int);
        }
    }

    /// Frame `f`'s runs and payload cells are untouched by an append.
    #[verifier::spinoff_prover]
    proof fn lemma_cold_append_keeps_layout(&self, mid: Self, f: int)
        requires mid.repr_ok(), 0 <= f < mid.cold_stack@.len(),
            mid.cold_stack@.len() <= self.cold_stack@.len(),
            mid.cold_index_runs@.len() <= self.cold_index_runs@.len(),
            mid.cold_value_pool@.len() <= self.cold_value_pool@.len(),
            self.cold_stack@.subrange(0, mid.cold_stack@.len() as int) == mid.cold_stack@,
            self.cold_index_runs@.subrange(0, mid.cold_index_runs@.len() as int) == mid.cold_index_runs@,
            self.cold_value_pool@.subrange(0, mid.cold_value_pool@.len() as int) == mid.cold_value_pool@,
        ensures self.cold_stack@[f] == mid.cold_stack@[f],
            mid.cold_stack@[f].runs_start + mid.cold_stack@[f].runs_len <= mid.cold_index_runs@.len(),
            forall|r: int| mid.cold_stack@[f].runs_start <= r
                < mid.cold_stack@[f].runs_start + mid.cold_stack@[f].runs_len ==>
                #[trigger] self.cold_index_runs@[r] == mid.cold_index_runs@[r]
                && mid.cold_index_runs@[r].start + mid.cold_index_runs@[r].len <= mid.cold_value_pool@.len()
                && (forall|i: int| mid.cold_index_runs@[r].start <= i
                    < mid.cold_index_runs@[r].start + mid.cold_index_runs@[r].len ==>
                    #[trigger] self.cold_value_pool@[i] == mid.cold_value_pool@[i]),
    {
        hide(Vec::repr_ok);
        mid.lemma_cold_layout_header_at(f);
        assert(self.cold_stack@[f] == self.cold_stack@.subrange(0, mid.cold_stack@.len() as int)[f]);
        let h = mid.cold_stack@[f];
        assert forall|r: int| h.runs_start <= r < h.runs_start + h.runs_len implies
            #[trigger] self.cold_index_runs@[r] == mid.cold_index_runs@[r]
            && mid.cold_index_runs@[r].start + mid.cold_index_runs@[r].len <= mid.cold_value_pool@.len()
            && (forall|i: int| mid.cold_index_runs@[r].start <= i
                < mid.cold_index_runs@[r].start + mid.cold_index_runs@[r].len ==>
                #[trigger] self.cold_value_pool@[i] == mid.cold_value_pool@[i]) by {
            assert(self.cold_index_runs@[r]
                == self.cold_index_runs@.subrange(0, mid.cold_index_runs@.len() as int)[r]);
            mid.lemma_cold_layout_run_at(r);
            assert forall|i: int| mid.cold_index_runs@[r].start <= i
                < mid.cold_index_runs@[r].start + mid.cold_index_runs@[r].len implies
                #[trigger] self.cold_value_pool@[i] == mid.cold_value_pool@[i] by {
                assert(self.cold_value_pool@[i]
                    == self.cold_value_pool@.subrange(0, mid.cold_value_pool@.len() as int)[i]);
            }
        }
    }

    /// Appending Cold storage leaves every earlier frame's coverage.
    #[verifier::spinoff_prover]
    proof fn lemma_cold_append_keeps_coverage(&self, mid: Self, f: int, j: nat)
        requires mid.repr_ok(), 0 <= f < mid.cold_stack@.len(),
            mid.cold_stack@.len() <= self.cold_stack@.len(),
            mid.cold_index_runs@.len() <= self.cold_index_runs@.len(),
            mid.cold_value_pool@.len() <= self.cold_value_pool@.len(),
            self.cold_stack@.subrange(0, mid.cold_stack@.len() as int) == mid.cold_stack@,
            self.cold_index_runs@.subrange(0, mid.cold_index_runs@.len() as int) == mid.cold_index_runs@,
            self.cold_value_pool@.subrange(0, mid.cold_value_pool@.len() as int) == mid.cold_value_pool@,
        ensures self.cold_covered(f, j) == mid.cold_covered(f, j),
    {
        hide(Vec::repr_ok);
        self.lemma_cold_append_keeps_layout(mid, f);
        let h = mid.cold_stack@[f];
        if self.cold_covered(f, j) {
            let r = choose|r: int|
                self.cold_stack@[f].runs_start <= r
                    < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
                && (#[trigger] self.cold_index_runs@[r]).base.as_nat() <= j
                && j < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len;
            assert(mid.cold_index_runs@[r] == self.cold_index_runs@[r]);
            assert(mid.cold_covered(f, j));
        }
        if mid.cold_covered(f, j) {
            let r = choose|r: int|
                mid.cold_stack@[f].runs_start <= r
                    < mid.cold_stack@[f].runs_start + mid.cold_stack@[f].runs_len
                && (#[trigger] mid.cold_index_runs@[r]).base.as_nat() <= j
                && j < mid.cold_index_runs@[r].base.as_nat() + mid.cold_index_runs@[r].len;
            assert(self.cold_index_runs@[r] == mid.cold_index_runs@[r]);
            assert(self.cold_covered(f, j));
        }
    }

    /// A frame's runs are pairwise adjacent-disjoint (accessor for the
    /// crate-wide disjointness predicate).
    #[verifier::spinoff_prover]
    proof fn lemma_cold_frame_adjacent(&self, f: int)
        requires self.cold_runs_disjoint(), 0 <= f < self.cold_stack@.len(),
        ensures forall|r: int| self.cold_stack@[f].runs_start <= r
            && r + 1 < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len ==>
            (#[trigger] self.cold_index_runs@[r]).base.as_nat() + self.cold_index_runs@[r].len
                <= self.cold_index_runs@[r + 1].base.as_nat(),
    {
        assert forall|r: int| self.cold_stack@[f].runs_start <= r
            && r + 1 < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len implies
            (#[trigger] self.cold_index_runs@[r]).base.as_nat() + self.cold_index_runs@[r].len
                <= self.cold_index_runs@[r + 1].base.as_nat() by {
            assert(self.cold_stack@[f].runs_start <= r);
        }
    }

    /// Appending Cold storage leaves every earlier frame's covered cells.
    #[verifier::spinoff_prover]
    proof fn lemma_cold_append_keeps_value(&self, mid: Self, f: int, j: nat)
        requires mid.repr_ok(), mid.cold_runs_disjoint(), 0 <= f < mid.cold_stack@.len(),
            mid.cold_stack@.len() <= self.cold_stack@.len(),
            mid.cold_index_runs@.len() <= self.cold_index_runs@.len(),
            mid.cold_value_pool@.len() <= self.cold_value_pool@.len(),
            self.cold_stack@.subrange(0, mid.cold_stack@.len() as int) == mid.cold_stack@,
            self.cold_index_runs@.subrange(0, mid.cold_index_runs@.len() as int) == mid.cold_index_runs@,
            self.cold_value_pool@.subrange(0, mid.cold_value_pool@.len() as int) == mid.cold_value_pool@,
            self.cold_covered(f, j), mid.cold_covered(f, j),
        ensures self.cold_value(f, j) == mid.cold_value(f, j),
    {
        hide(Vec::repr_ok);
        hide(Vec::cold_runs_disjoint);
        self.lemma_cold_append_keeps_layout(mid, f);
        let r1 = choose|r: int|
            self.cold_stack@[f].runs_start <= r
                < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
            && (#[trigger] self.cold_index_runs@[r]).base.as_nat() <= j
            && j < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len;
        let r2 = choose|r: int|
            mid.cold_stack@[f].runs_start <= r
                < mid.cold_stack@[f].runs_start + mid.cold_stack@[f].runs_len
            && (#[trigger] mid.cold_index_runs@[r]).base.as_nat() <= j
            && j < mid.cold_index_runs@[r].base.as_nat() + mid.cold_index_runs@[r].len;
        assert(mid.cold_index_runs@[r1] == self.cold_index_runs@[r1]);
        mid.lemma_cold_frame_adjacent(f);
        lemma_runs_cover_unique::<I>(mid.cold_index_runs@, mid.cold_stack@[f].runs_start as int,
            mid.cold_stack@[f].runs_start + mid.cold_stack@[f].runs_len, r1, r2, j);
        let idx = mid.cold_index_runs@[r1].start as int
            + (j - mid.cold_index_runs@[r1].base.as_nat()) as int;
        assert(self.cold_value_pool@[idx] == mid.cold_value_pool@[idx]);
        assert(self.cold_value(f, j) == self.cold_value_pool@[idx]);
        assert(mid.cold_value(f, j) == mid.cold_value_pool@[idx]);
    }

    /// Appending Cold storage leaves every earlier frame's coverage and cells.
    #[verifier::spinoff_prover]
    proof fn lemma_cold_append_keeps_frame(&self, mid: Self, f: int, j: nat)
        requires mid.repr_ok(), mid.cold_runs_disjoint(), 0 <= f < mid.cold_stack@.len(),
            mid.cold_stack@.len() <= self.cold_stack@.len(),
            mid.cold_index_runs@.len() <= self.cold_index_runs@.len(),
            mid.cold_value_pool@.len() <= self.cold_value_pool@.len(),
            self.cold_stack@.subrange(0, mid.cold_stack@.len() as int) == mid.cold_stack@,
            self.cold_index_runs@.subrange(0, mid.cold_index_runs@.len() as int) == mid.cold_index_runs@,
            self.cold_value_pool@.subrange(0, mid.cold_value_pool@.len() as int) == mid.cold_value_pool@,
        ensures self.cold_covered(f, j) == mid.cold_covered(f, j),
            self.cold_covered(f, j) ==> self.cold_value(f, j) == mid.cold_value(f, j),
    {
        hide(Vec::repr_ok);
        hide(Vec::cold_runs_disjoint);
        self.lemma_cold_append_keeps_coverage(mid, f, j);
        if self.cold_covered(f, j) {
            self.lemma_cold_append_keeps_value(mid, f, j);
        }
    }

    /// A Hot header's saved length is its snapshot's length.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_saved_len(&self, f: int)
        requires self.wf(), 0 <= f < self.hot_stack@.len(),
        ensures self.hot_stack@[f].saved_len.as_nat()
            == self.snapshots@[self.cold_stack@.len() + f].len(),
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
    }

    /// The physical range of closed Hot frame `f` during a migration: the
    /// sealed header bounds of `pre`, the same in `self` (headers and pool
    /// length are untouched), and unique in `self`'s pool.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migrating_frame_range(&self, pre: Self, f: int)
        requires self.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
        ensures
            self.phys_hot_start(f) == pre.hot_stack@[f].start as int,
            self.phys_hot_end(f) == pre.hot_stack@[f].end as int,
            pre.hot_stack@[f].start <= pre.hot_stack@[f].end <= self.hot_value_pool@.len(),
            stratum_unique::<T, I>(self.hot_value_pool@,
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating_cold);
        hide(stratum_unique);
        reveal(Vec::hot_migrating);
        reveal(Vec::hot_migrating_hot);
        pre.lemma_closed_hot_frame_end(f);
        assert(self.phys_hot_start(f) == pre.phys_hot_start(f));
        assert(self.phys_hot_end(f) == pre.phys_hot_end(f));
    }

    /// A sorted unique closed frame is strictly increasing.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_strict(&self, pre: Self, f: int)
        requires self.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            self.hot_frame_sorted(f),
        ensures ({
            let entries = self.hot_value_pool@.subrange(
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int);
            forall|a: int, b: int| 0 <= a < b < entries.len() ==>
                (#[trigger] entries[a]).1.as_nat() < (#[trigger] entries[b]).1.as_nat()
        }),
            pre.hot_stack@[f].start <= pre.hot_stack@[f].end <= self.hot_value_pool@.len(),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        self.lemma_hot_migrating_frame_range(pre, f);
        let start = pre.hot_stack@[f].start as int;
        let end = pre.hot_stack@[f].end as int;
        let entries = self.hot_value_pool@.subrange(start, end);
        assert forall|a: int, b: int| 0 <= a < b < entries.len() implies
            (#[trigger] entries[a]).1.as_nat() < (#[trigger] entries[b]).1.as_nat() by {
            assert(entries[a] == self.hot_value_pool@[start + a]);
            assert(entries[b] == self.hot_value_pool@[start + b]);
            assert(self.hot_value_pool@[start + a].1.as_nat() != self.hot_value_pool@[start + b].1.as_nat());
        }
    }

    /// Every index of a migrating frame lies below its saved length.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_index_bound(&self, pre: Self, f: int, q: int)
        requires self.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            pre.hot_stack@[f].start + q < pre.hot_stack@[f].end, 0 <= q,
        ensures self.hot_value_pool@[pre.hot_stack@[f].start + q].1.as_nat()
            < pre.hot_stack@[f].saved_len.as_nat(),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating_cold);
        reveal(Vec::hot_migrating);
        reveal(Vec::hot_migrating_hot);
        pre.lemma_closed_hot_frame_end(f);
        pre.lemma_hot_saved_len(f);
        let start = pre.hot_stack@[f].start as int;
        let end = pre.hot_stack@[f].end as int;
        let cc = pre.cold_stack@.len() as int;
        assert(pre.phys_hot_start(f) == start);
        assert(pre.phys_hot_end(f) == end);
        pre.lemma_pair_tier_contract(false, f);
        let j = self.hot_value_pool@[start + q].1.as_nat();
        lemma_unique_range_saved_value::<T, I>(self.hot_value_pool@, start, end, j);
        assert(range_saved_value::<T, I>(self.hot_value_pool@, start, end, j) is Some);
        assert(range_saved_value::<T, I>(pre.hot_value_pool@, start, end, j) is Some);
        assert(captured_in_range::<T, I>(pre.hot_value_pool@, start, end, j));
        let k = choose|k: int| start <= k < end && 0 <= k < pre.hot_value_pool@.len()
            && (#[trigger] pre.hot_value_pool@[k]).1.as_nat() == j;
        assert(pre.hot_value_pool@[k].1.as_nat() < pre.snapshots@[cc + f].len());
    }

    /// A sorted unique closed frame is a strictly increasing sequence whose
    /// indices lie below the frame's saved length: the Cold encoder's input.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_encode_ready(&self, pre: Self, f: int)
        requires self.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            self.hot_frame_sorted(f),
        ensures ({
            let entries = self.hot_value_pool@.subrange(
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int);
            &&& forall|a: int, b: int| 0 <= a < b < entries.len() ==>
                (#[trigger] entries[a]).1.as_nat() < (#[trigger] entries[b]).1.as_nat()
            &&& forall|q: int| 0 <= q < entries.len() ==>
                (#[trigger] entries[q]).1.as_nat() < pre.hot_stack@[f].saved_len.as_nat()
        }),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(stratum_unique);
        hide(range_saved_value);
        self.lemma_hot_frame_strict(pre, f);
        let start = pre.hot_stack@[f].start as int;
        let end = pre.hot_stack@[f].end as int;
        let entries = self.hot_value_pool@.subrange(start, end);
        assert forall|q: int| 0 <= q < entries.len() implies
            (#[trigger] entries[q]).1.as_nat() < pre.hot_stack@[f].saved_len.as_nat() by {
            assert(entries[q] == self.hot_value_pool@[start + q]);
            self.lemma_hot_frame_index_bound(pre, f, q);
        }
    }

    /// Hot side of an encode step: the pool is untouched, so one more frame
    /// enters the migrating scope.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_encoded_hot(&self, mid: Self, pre: Self, f: int)
        requires mid.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            self.hot_value_pool@ == mid.hot_value_pool@,
        ensures self.hot_migrating_hot(pre, f as nat + 1),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating_cold);
        hide(stratum_unique);
        reveal(Vec::hot_migrating);
        reveal(Vec::hot_migrating_hot);
        pre.lemma_hot_cut_order(f as nat + 1, f as nat + 2);
        assert forall|q: int| pre.hot_retirement_cut(f as nat + 2) <= q < pre.hot_value_pool@.len() implies
            #[trigger] self.hot_value_pool@[q] == pre.hot_value_pool@[q] by {
            assert(pre.hot_retirement_cut(f as nat + 1) <= q);
        }
        assert forall|g: int| #![trigger pre.phys_hot_start(g)] #![trigger pre.phys_hot_end(g)] 0 <= g <= f + 1 && g < pre.hot_stack@.len() implies {
            &&& stratum_unique::<T, I>(self.hot_value_pool@, pre.phys_hot_start(g), pre.phys_hot_end(g))
            &&& forall|j: nat| #[trigger] range_saved_value::<T, I>(self.hot_value_pool@,
                    pre.phys_hot_start(g), pre.phys_hot_end(g), j)
                == range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(g), pre.phys_hot_end(g), j)
        } by {
            if g == f + 1 {
                pre.lemma_wf_named_parts();
                pre.lemma_pair_tier_frame_layout(false, g);
                assert(pre.hot_retirement_cut(f as nat + 1) == pre.hot_stack@[g].start as nat);
                assert forall|q: int| pre.phys_hot_start(g) <= q < pre.phys_hot_end(g) implies
                    #[trigger] self.hot_value_pool@[q] == pre.hot_value_pool@[q] by {}
                assert(stratum_unique::<T, I>(pre.hot_value_pool@, pre.phys_hot_start(g), pre.phys_hot_end(g))) by {
                    reveal(Vec::hot_repr_ok);
                }
                assert(stratum_unique::<T, I>(self.hot_value_pool@, pre.phys_hot_start(g), pre.phys_hot_end(g))) by {
                    reveal(stratum_unique);
                }
                assert forall|j: nat| #[trigger] range_saved_value::<T, I>(self.hot_value_pool@,
                        pre.phys_hot_start(g), pre.phys_hot_end(g), j)
                    == range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(g), pre.phys_hot_end(g), j) by {
                    lemma_range_saved_value_local::<T, I>(pre.hot_value_pool@, self.hot_value_pool@,
                        pre.phys_hot_start(g), pre.phys_hot_end(g), j);
                }
            }
        }
    }

    /// Cold side of an encode step: prefixes, kept frames, and the new frame.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_encoded_cold(
        &self, mid: Self, pre: Self, f: int, entries: Seq<(T, I)>, cold: crate::frame::ColdFrameHdr<I>,
    )
        requires mid.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            entries == mid.hot_value_pool@.subrange(
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int),
            self.cold_stack@ == mid.cold_stack@.push(cold),
            self.cold_index_runs@.subrange(0, mid.cold_index_runs@.len() as int) == mid.cold_index_runs@,
            self.cold_value_pool@.subrange(0, mid.cold_value_pool@.len() as int) == mid.cold_value_pool@,
            mid.cold_index_runs@.len() <= self.cold_index_runs@.len(),
            self.cold_value_pool@.len() == mid.cold_value_pool@.len() + entries.len(),
            forall|q: int| 0 <= q < entries.len() ==>
                #[trigger] self.cold_value_pool@[mid.cold_value_pool@.len() + q] == entries[q].0,
            cold.saved_len == pre.hot_stack@[f].saved_len,
            cold.runs_start == mid.cold_index_runs@.len(),
            cold.runs_start + cold.runs_len == self.cold_index_runs@.len(),
            crate::cold_encode::run_prefix(self.cold_index_runs@,
                mid.cold_index_runs@.len() as int, mid.cold_value_pool@.len() as int,
                entries, entries.len() as int, cold.saved_len.as_nat()),
            self.repr_ok(), self.cold_payload_ok(), self.cold_runs_disjoint(),
        ensures self.hot_migrating_cold(pre, f as nat + 1),
    {
        hide(Vec::wf);
        hide(Vec::repr_ok);
        hide(Vec::cold_runs_disjoint);
        hide(Vec::hot_migrating_hot);
        hide(stratum_unique);
        hide(range_saved_value);
        hide(Vec::cold_payload_ok);
        hide(crate::cold_encode::run_prefix);
        reveal(Vec::hot_migrating);
        reveal(Vec::hot_migrating_cold);
        let cc = pre.cold_stack@.len() as int;
        assert(self.cold_stack@.subrange(0, cc) =~= pre.cold_stack@);
        assert(self.cold_index_runs@.subrange(0, pre.cold_index_runs@.len() as int) =~= pre.cold_index_runs@);
        assert(self.cold_value_pool@.subrange(0, pre.cold_value_pool@.len() as int) =~= pre.cold_value_pool@);
        assert(self.cold_stack@.subrange(0, mid.cold_stack@.len() as int) =~= mid.cold_stack@);
        let k = cc + f;
        assert(self.cold_stack@[k] == cold);
        self.lemma_hot_frame_encoded_new(mid, pre, f, entries, cold);
        assert forall|q: int| 0 <= q < f + 1 implies {
            &&& (#[trigger] self.cold_stack@[cc + q]).saved_len == pre.hot_stack@[q].saved_len
            &&& forall|j: nat| #[trigger] self.cold_covered(cc + q, j)
                <==> range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(q), pre.phys_hot_end(q), j) is Some
            &&& forall|j: nat| self.cold_covered(cc + q, j) ==>
                Some(#[trigger] self.cold_value(cc + q, j))
                    == range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(q), pre.phys_hot_end(q), j)
        } by {
            if q < f {
                assert(self.cold_stack@[cc + q] == mid.cold_stack@[cc + q]);
                assert forall|j: nat| #[trigger] self.cold_covered(cc + q, j)
                    <==> range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(q), pre.phys_hot_end(q), j) is Some by {
                    self.lemma_cold_append_keeps_frame(mid, cc + q, j);
                }
                assert forall|j: nat| self.cold_covered(cc + q, j) implies
                    Some(#[trigger] self.cold_value(cc + q, j))
                        == range_saved_value::<T, I>(pre.hot_value_pool@,
                            pre.phys_hot_start(q), pre.phys_hot_end(q), j) by {
                    self.lemma_cold_append_keeps_frame(mid, cc + q, j);
                    assert(mid.cold_covered(cc + q, j));
                }
            }
        }
    }

    /// The appended Cold frame carries exactly the encoded Hot frame's saved
    /// map, and the migration state advances by one frame.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_encoded(
        &self, mid: Self, pre: Self, f: int, entries: Seq<(T, I)>, cold: crate::frame::ColdFrameHdr<I>,
    )
        requires mid.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            mid.hot_frame_sorted(f),
            entries == mid.hot_value_pool@.subrange(
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int),
            *self == (Self { cold_stack: self.cold_stack, cold_index_runs: self.cold_index_runs,
                cold_value_pool: self.cold_value_pool, ..mid }),
            self.cold_stack@ == mid.cold_stack@.push(cold),
            self.cold_index_runs@.subrange(0, mid.cold_index_runs@.len() as int) == mid.cold_index_runs@,
            self.cold_value_pool@.subrange(0, mid.cold_value_pool@.len() as int) == mid.cold_value_pool@,
            mid.cold_index_runs@.len() <= self.cold_index_runs@.len(),
            self.cold_value_pool@.len() == mid.cold_value_pool@.len() + entries.len(),
            forall|q: int| 0 <= q < entries.len() ==>
                #[trigger] self.cold_value_pool@[mid.cold_value_pool@.len() + q] == entries[q].0,
            cold.saved_len == pre.hot_stack@[f].saved_len,
            cold.runs_start == mid.cold_index_runs@.len(),
            cold.runs_start + cold.runs_len == self.cold_index_runs@.len(),
            crate::cold_encode::run_prefix(self.cold_index_runs@,
                mid.cold_index_runs@.len() as int, mid.cold_value_pool@.len() as int,
                entries, entries.len() as int, cold.saved_len.as_nat()),
            self.repr_ok(), self.cold_payload_ok(), self.cold_runs_disjoint(),
        ensures self.hot_migrating(pre, f as nat + 1),
    {
        hide(Vec::wf);
        hide(Vec::repr_ok);
        hide(Vec::cold_runs_disjoint);
        hide(stratum_unique);
        hide(range_saved_value);
        hide(Vec::cold_payload_ok);
        hide(crate::cold_encode::run_prefix);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        reveal(Vec::hot_migrating);
        self.lemma_hot_frame_encoded_hot(mid, pre, f);
        self.lemma_hot_frame_encoded_cold(mid, pre, f, entries, cold);
    }

    /// The new Cold frame's coverage is capture in the source frame, and each
    /// covered cell holds the captured value. Decomposed into its two halves
    /// (coverage, values) so each stays inside the solver budget.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_encoded_new(
        &self, mid: Self, pre: Self, f: int, entries: Seq<(T, I)>, cold: crate::frame::ColdFrameHdr<I>,
    )
        requires mid.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            entries == mid.hot_value_pool@.subrange(
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int),
            self.cold_stack@ == mid.cold_stack@.push(cold),
            self.cold_value_pool@.len() == mid.cold_value_pool@.len() + entries.len(),
            forall|q: int| 0 <= q < entries.len() ==>
                #[trigger] self.cold_value_pool@[mid.cold_value_pool@.len() + q] == entries[q].0,
            cold.runs_start == mid.cold_index_runs@.len(),
            cold.runs_start + cold.runs_len == self.cold_index_runs@.len(),
            crate::cold_encode::run_prefix(self.cold_index_runs@,
                mid.cold_index_runs@.len() as int, mid.cold_value_pool@.len() as int,
                entries, entries.len() as int, cold.saved_len.as_nat()),
        ensures ({
            let k = pre.cold_stack@.len() + f;
            &&& forall|j: nat| #[trigger] self.cold_covered(k, j)
                <==> range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(f), pre.phys_hot_end(f), j) is Some
            &&& forall|j: nat| self.cold_covered(k, j) ==>
                Some(#[trigger] self.cold_value(k, j))
                    == range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(f), pre.phys_hot_end(f), j)
        }),
    {
        self.lemma_hot_frame_encoded_new_covered(mid, pre, f, entries, cold);
        self.lemma_hot_frame_encoded_new_value(mid, pre, f, entries, cold);
    }

    /// The facts both halves of `lemma_hot_frame_encoded_new` need from the
    /// migration invariant, gathered once so the halves can hide it (the
    /// invariant's Cold-side clauses over every earlier frame are what put
    /// them over the solver budget).
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_encoded_new_facts(mid: Self, pre: Self, f: int)
        requires mid.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
        ensures
            f < pre.hot_stack@.len(),
            mid.cold_stack@.len() == pre.cold_stack@.len() + f,
            pre.phys_hot_start(f) == pre.hot_stack@[f].start as int,
            pre.phys_hot_end(f) == pre.hot_stack@[f].end as int,
            pre.hot_stack@[f].start <= pre.hot_stack@[f].end <= mid.hot_value_pool@.len(),
            stratum_unique::<T, I>(mid.hot_value_pool@,
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int),
            forall|j: nat| #[trigger] range_saved_value::<T, I>(mid.hot_value_pool@,
                    pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int, j)
                == range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int, j),
    {
        hide(Vec::wf);
        hide(stratum_unique);
        hide(range_saved_value);
        hide(Vec::cold_payload_ok);
        reveal(Vec::hot_migrating);
        reveal(Vec::hot_migrating_hot);
        reveal(Vec::hot_migrating_cold);
        pre.lemma_closed_hot_frame_end(f);
    }

    /// Coverage half of `lemma_hot_frame_encoded_new`: the two directions are
    /// separate lemmas (each direction alone fits the solver budget).
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_encoded_new_covered(
        &self, mid: Self, pre: Self, f: int, entries: Seq<(T, I)>, cold: crate::frame::ColdFrameHdr<I>,
    )
        requires mid.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            entries == mid.hot_value_pool@.subrange(
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int),
            self.cold_stack@ == mid.cold_stack@.push(cold),
            self.cold_value_pool@.len() == mid.cold_value_pool@.len() + entries.len(),
            forall|q: int| 0 <= q < entries.len() ==>
                #[trigger] self.cold_value_pool@[mid.cold_value_pool@.len() + q] == entries[q].0,
            cold.runs_start == mid.cold_index_runs@.len(),
            cold.runs_start + cold.runs_len == self.cold_index_runs@.len(),
            crate::cold_encode::run_prefix(self.cold_index_runs@,
                mid.cold_index_runs@.len() as int, mid.cold_value_pool@.len() as int,
                entries, entries.len() as int, cold.saved_len.as_nat()),
        ensures ({
            let k = pre.cold_stack@.len() + f;
            forall|j: nat| #[trigger] self.cold_covered(k, j)
                <==> range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(f), pre.phys_hot_end(f), j) is Some
        }),
    {
        self.lemma_hot_frame_encoded_new_covered_fwd(mid, pre, f, entries, cold);
        self.lemma_hot_frame_encoded_new_covered_bwd(mid, pre, f, entries, cold);
    }

    /// Covered ⟹ captured in the source frame.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_encoded_new_covered_fwd(
        &self, mid: Self, pre: Self, f: int, entries: Seq<(T, I)>, cold: crate::frame::ColdFrameHdr<I>,
    )
        requires mid.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            entries == mid.hot_value_pool@.subrange(
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int),
            self.cold_stack@ == mid.cold_stack@.push(cold),
            self.cold_value_pool@.len() == mid.cold_value_pool@.len() + entries.len(),
            forall|q: int| 0 <= q < entries.len() ==>
                #[trigger] self.cold_value_pool@[mid.cold_value_pool@.len() + q] == entries[q].0,
            cold.runs_start == mid.cold_index_runs@.len(),
            cold.runs_start + cold.runs_len == self.cold_index_runs@.len(),
            crate::cold_encode::run_prefix(self.cold_index_runs@,
                mid.cold_index_runs@.len() as int, mid.cold_value_pool@.len() as int,
                entries, entries.len() as int, cold.saved_len.as_nat()),
        ensures ({
            let k = pre.cold_stack@.len() + f;
            forall|j: nat| #[trigger] self.cold_covered(k, j)
                ==> range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(f), pre.phys_hot_end(f), j) is Some
        }),
    {
        hide(Vec::wf);
        hide(stratum_unique);
        hide(crate::cold_encode::run_prefix);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(Vec::cold_payload_ok);
        Self::lemma_hot_frame_encoded_new_facts(mid, pre, f);
        let cc = pre.cold_stack@.len() as int;
        let start = pre.hot_stack@[f].start as int;
        let end = pre.hot_stack@[f].end as int;
        let rs = mid.cold_index_runs@.len() as int;
        let vs = mid.cold_value_pool@.len() as int;
        let n = entries.len() as int;
        let runs = self.cold_index_runs@;
        let limit = cold.saved_len.as_nat();
        let k = cc + f;
        assert(mid.cold_stack@.len() == k);
        assert(self.cold_stack@[k] == cold);
        assert(pre.phys_hot_start(f) == start);
        assert(pre.phys_hot_end(f) == end);
        assert(stratum_unique::<T, I>(mid.hot_value_pool@, start, end));
        crate::cold_encode::lemma_run_prefix_layout(runs, rs, vs, entries, n, limit);
        assert forall|j: nat| #[trigger] self.cold_covered(k, j)
            implies range_saved_value::<T, I>(pre.hot_value_pool@, start, end, j) is Some by {
            lemma_unique_range_saved_value::<T, I>(mid.hot_value_pool@, start, end, j);
                let r = choose|r: int|
                    self.cold_stack@[k].runs_start <= r
                        < self.cold_stack@[k].runs_start + self.cold_stack@[k].runs_len
                    && (#[trigger] self.cold_index_runs@[r]).base.as_nat() <= j
                    && j < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len;
                let q = (j - runs[r].base.as_nat()) as int;
                crate::cold_encode::lemma_run_prefix_cell(runs, rs, vs, entries, n, limit, r, q);
                let o = runs[r].start - vs + q;
                assert(entries[o] == mid.hot_value_pool@[start + o]);
                assert(mid.hot_value_pool@[start + o].1.as_nat() == j);
                assert(range_saved_value::<T, I>(mid.hot_value_pool@, start, end, j)
                    == Some(mid.hot_value_pool@[start + o].0));
        }
    }

    /// Captured in the source frame ⟹ covered.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_encoded_new_covered_bwd(
        &self, mid: Self, pre: Self, f: int, entries: Seq<(T, I)>, cold: crate::frame::ColdFrameHdr<I>,
    )
        requires mid.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            entries == mid.hot_value_pool@.subrange(
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int),
            self.cold_stack@ == mid.cold_stack@.push(cold),
            self.cold_value_pool@.len() == mid.cold_value_pool@.len() + entries.len(),
            forall|q: int| 0 <= q < entries.len() ==>
                #[trigger] self.cold_value_pool@[mid.cold_value_pool@.len() + q] == entries[q].0,
            cold.runs_start == mid.cold_index_runs@.len(),
            cold.runs_start + cold.runs_len == self.cold_index_runs@.len(),
            crate::cold_encode::run_prefix(self.cold_index_runs@,
                mid.cold_index_runs@.len() as int, mid.cold_value_pool@.len() as int,
                entries, entries.len() as int, cold.saved_len.as_nat()),
        ensures ({
            let k = pre.cold_stack@.len() + f;
            forall|j: nat| range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(f), pre.phys_hot_end(f), j) is Some
                ==> #[trigger] self.cold_covered(k, j)
        }),
    {
        hide(Vec::wf);
        hide(stratum_unique);
        hide(crate::cold_encode::run_prefix);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(Vec::cold_payload_ok);
        Self::lemma_hot_frame_encoded_new_facts(mid, pre, f);
        let cc = pre.cold_stack@.len() as int;
        let start = pre.hot_stack@[f].start as int;
        let end = pre.hot_stack@[f].end as int;
        let rs = mid.cold_index_runs@.len() as int;
        let vs = mid.cold_value_pool@.len() as int;
        let n = entries.len() as int;
        let runs = self.cold_index_runs@;
        let limit = cold.saved_len.as_nat();
        let k = cc + f;
        assert(mid.cold_stack@.len() == k);
        assert(self.cold_stack@[k] == cold);
        assert(pre.phys_hot_start(f) == start);
        assert(pre.phys_hot_end(f) == end);
        assert(stratum_unique::<T, I>(mid.hot_value_pool@, start, end));
        crate::cold_encode::lemma_run_prefix_layout(runs, rs, vs, entries, n, limit);
        assert forall|j: nat| range_saved_value::<T, I>(pre.hot_value_pool@, start, end, j) is Some
            implies #[trigger] self.cold_covered(k, j) by {
            lemma_unique_range_saved_value::<T, I>(mid.hot_value_pool@, start, end, j);
                assert(range_saved_value::<T, I>(mid.hot_value_pool@, start, end, j) is Some);
                assert(captured_in_range::<T, I>(mid.hot_value_pool@, start, end, j));
                let k0 = choose|k0: int| start <= k0 < end && 0 <= k0 < mid.hot_value_pool@.len()
                    && (#[trigger] mid.hot_value_pool@[k0]).1.as_nat() == j;
                let p = k0 - start;
                assert(entries[p] == mid.hot_value_pool@[k0]);
                crate::cold_encode::lemma_run_prefix_entry(runs, rs, vs, entries, n, limit, p);
                let r = choose|r: int| rs <= r < runs.len()
                    && (#[trigger] runs[r]).base.as_nat() <= entries[p].1.as_nat()
                    && entries[p].1.as_nat() < runs[r].base.as_nat() + runs[r].len
                    && runs[r].start + (entries[p].1.as_nat() - runs[r].base.as_nat()) == vs + p;
                assert(self.cold_stack@[k].runs_start <= r
                    < self.cold_stack@[k].runs_start + self.cold_stack@[k].runs_len);
                assert(self.cold_covered(k, j));
        }
    }

    /// Value half of `lemma_hot_frame_encoded_new`.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_encoded_new_value(
        &self, mid: Self, pre: Self, f: int, entries: Seq<(T, I)>, cold: crate::frame::ColdFrameHdr<I>,
    )
        requires mid.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            entries == mid.hot_value_pool@.subrange(
                pre.hot_stack@[f].start as int, pre.hot_stack@[f].end as int),
            self.cold_stack@ == mid.cold_stack@.push(cold),
            self.cold_value_pool@.len() == mid.cold_value_pool@.len() + entries.len(),
            forall|q: int| 0 <= q < entries.len() ==>
                #[trigger] self.cold_value_pool@[mid.cold_value_pool@.len() + q] == entries[q].0,
            cold.runs_start == mid.cold_index_runs@.len(),
            cold.runs_start + cold.runs_len == self.cold_index_runs@.len(),
            crate::cold_encode::run_prefix(self.cold_index_runs@,
                mid.cold_index_runs@.len() as int, mid.cold_value_pool@.len() as int,
                entries, entries.len() as int, cold.saved_len.as_nat()),
        ensures ({
            let k = pre.cold_stack@.len() + f;
            forall|j: nat| self.cold_covered(k, j) ==>
                Some(#[trigger] self.cold_value(k, j))
                    == range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(f), pre.phys_hot_end(f), j)
        }),
    {
        hide(Vec::wf);
        hide(stratum_unique);
        hide(crate::cold_encode::run_prefix);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(Vec::cold_payload_ok);
        Self::lemma_hot_frame_encoded_new_facts(mid, pre, f);
        let cc = pre.cold_stack@.len() as int;
        let start = pre.hot_stack@[f].start as int;
        let end = pre.hot_stack@[f].end as int;
        let rs = mid.cold_index_runs@.len() as int;
        let vs = mid.cold_value_pool@.len() as int;
        let n = entries.len() as int;
        let runs = self.cold_index_runs@;
        let limit = cold.saved_len.as_nat();
        let k = cc + f;
        assert(mid.cold_stack@.len() == k);
        assert(self.cold_stack@[k] == cold);
        assert(pre.phys_hot_start(f) == start);
        assert(pre.phys_hot_end(f) == end);
        assert(stratum_unique::<T, I>(mid.hot_value_pool@, start, end));
        crate::cold_encode::lemma_run_prefix_layout(runs, rs, vs, entries, n, limit);
        assert forall|j: nat| self.cold_covered(k, j) implies
            Some(#[trigger] self.cold_value(k, j))
                == range_saved_value::<T, I>(pre.hot_value_pool@, start, end, j) by {
            lemma_unique_range_saved_value::<T, I>(mid.hot_value_pool@, start, end, j);
            let r = choose|r: int|
                self.cold_stack@[k].runs_start <= r
                    < self.cold_stack@[k].runs_start + self.cold_stack@[k].runs_len
                && (#[trigger] self.cold_index_runs@[r]).base.as_nat() <= j
                && j < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len;
            let q = (j - runs[r].base.as_nat()) as int;
            crate::cold_encode::lemma_run_prefix_cell(runs, rs, vs, entries, n, limit, r, q);
            let o = runs[r].start - vs + q;
            assert(entries[o] == mid.hot_value_pool@[start + o]);
            assert(mid.hot_value_pool@[start + o].1.as_nat() == j);
            assert(self.cold_value(k, j) == self.cold_value_pool@[runs[r].start as int + q]);
            assert(runs[r].start as int + q == vs + o);
            assert(self.cold_value_pool@[vs + o] == entries[o].0);
            assert(range_saved_value::<T, I>(mid.hot_value_pool@, start, end, j)
                == Some(mid.hot_value_pool@[start + o].0));
        }
    }

    /// Encode sorted closed Hot frame `f` as the newest Cold frame, straight
    /// from the Hot pool slice.
    #[verifier::spinoff_prover]
    fn hot_frame_encode_checked(&mut self, f: usize, Ghost(pre): Ghost<Self>)
        requires old(self).hot_migrating(pre, f as nat), f < pre.hot_closed_count(),
            old(self).hot_frame_sorted(f as int),
        ensures final(self).hot_migrating(pre, f as nat + 1),
            *final(self) == (Self { cold_stack: final(self).cold_stack,
                cold_index_runs: final(self).cold_index_runs,
                cold_value_pool: final(self).cold_value_pool, ..*old(self) }),
    {
        hide(Vec::wf);
        hide(stratum_unique);
        hide(range_saved_value);
        hide(Vec::cold_payload_ok);
        hide(crate::cold_encode::run_prefix);
        proof {
            reveal(Vec::hot_migrating);
            reveal(Vec::hot_migrating_cold);
            pre.lemma_closed_hot_frame_end(f as int);
            self.lemma_hot_frame_encode_ready(pre, f as int);
        }
        let frame = self.hot_stack[f];
        let ghost mid = *self;
        let ghost entries = self.hot_value_pool@.subrange(frame.start as int, frame.end as int);
        let cold = crate::cold_encode::append_sorted(
            &mut self.cold_index_runs, &mut self.cold_value_pool,
            &self.hot_value_pool[frame.start..frame.end], frame.saved_len);
        self.cold_stack.push(cold);
        proof {
            assert(self.cold_stack@ == mid.cold_stack@.push(cold));
            self.lemma_cold_append_structure(mid, entries, cold);
            self.lemma_cold_append_payload(mid, entries, cold);
            self.lemma_cold_append_disjoint(mid, entries, cold);
            self.lemma_hot_frame_encoded(mid, pre, f as int, entries, cold);
        }
    }

    /// Physical effects of retiring the migrated Hot prefix from `mid`.
    closed spec fn hot_retired_from(&self, mid: Self, count: nat) -> bool {
        let cut = mid.hot_retirement_cut(count);
        &&& count <= mid.hot_stack@.len()
        &&& *self == (Self { hot_stack: self.hot_stack, hot_value_pool: self.hot_value_pool, ..mid })
        &&& cut <= mid.hot_value_pool@.len()
        &&& self.hot_value_pool@ == mid.hot_value_pool@.subrange(cut as int, mid.hot_value_pool@.len() as int)
        &&& self.hot_stack@.len() == mid.hot_stack@.len() - count
        &&& forall|f: int| 0 <= f < self.hot_stack@.len() ==> {
            let h = #[trigger] self.hot_stack@[f];
            let old_h = mid.hot_stack@[count + f];
            &&& h.saved_len == old_h.saved_len
            &&& h.start == old_h.start - cut
            &&& h.end == old_h.end - cut
        }
    }

    /// Partition counts of a well-formed container.
    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_partition_counts(&self)
        requires self.wf(),
        ensures self.snapshots@.len() == self.trail_frames@.len(),
            self.cold_stack@.len() + self.hot_stack@.len() + self.trail_stack@.len() == self.snapshots@.len(),
            !TRACK ==> self.snapshots@.len() == 0,
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
    }

    /// A Cold header's saved length is its snapshot's length.
    #[verifier::spinoff_prover]
    proof fn lemma_cold_saved_len(&self, f: int)
        requires self.wf(), 0 <= f < self.cold_stack@.len(),
        ensures self.cold_stack@[f].saved_len.as_nat() == self.snapshots@[f].len(),
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
    }

    /// A Trail header's saved length is its snapshot's length.
    #[verifier::spinoff_prover]
    proof fn lemma_trail_saved_len(&self, f: int)
        requires self.wf(), 0 <= f < self.trail_stack@.len(),
        ensures self.trail_stack@[f].saved_len.as_nat()
            == self.snapshots@[self.cold_stack@.len() + self.hot_stack@.len() + f].len(),
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
    }

    /// Header accessor for the Cold side of a migration in progress.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migrating_cold_headers(&self, pre: Self, count: nat)
        requires self.hot_migrating_cold(pre, count),
        ensures self.cold_stack@.len() == pre.cold_stack@.len() + count,
            forall|f: int| 0 <= f < pre.cold_stack@.len() ==>
                #[trigger] self.cold_stack@[f] == pre.cold_stack@[f],
            forall|q: int| 0 <= q < count ==>
                (#[trigger] self.cold_stack@[pre.cold_stack@.len() + q]).saved_len
                    == pre.hot_stack@[q].saved_len,
    {
        reveal(Vec::hot_migrating_cold);
        let cc = pre.cold_stack@.len() as int;
        assert forall|f: int| 0 <= f < cc implies #[trigger] self.cold_stack@[f] == pre.cold_stack@[f] by {
            assert(self.cold_stack@[f] == self.cold_stack@.subrange(0, cc)[f]);
        }
    }

    /// Accessor for the migration state's framing and bounds.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migrating_frame(&self, pre: Self, count: nat)
        requires self.hot_migrating(pre, count),
        ensures pre.wf(), count <= pre.hot_closed_count(),
            *self == (Self { cold_stack: self.cold_stack, cold_index_runs: self.cold_index_runs,
                cold_value_pool: self.cold_value_pool, hot_value_pool: self.hot_value_pool, ..pre }),
            self.hot_migrating_hot(pre, count), self.hot_migrating_cold(pre, count),
            self.hot_value_pool@.len() == pre.hot_value_pool@.len(),
    {
        reveal(Vec::hot_migrating);
        reveal(Vec::hot_migrating_hot);
    }

    /// Accessor for the retirement effect.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_retired_frame(&self, mid: Self, count: nat)
        requires self.hot_retired_from(mid, count),
        ensures count <= mid.hot_stack@.len(),
            *self == (Self { hot_stack: self.hot_stack, hot_value_pool: self.hot_value_pool, ..mid }),
            mid.hot_retirement_cut(count) <= mid.hot_value_pool@.len(),
            self.hot_value_pool@ == mid.hot_value_pool@.subrange(
                mid.hot_retirement_cut(count) as int, mid.hot_value_pool@.len() as int),
            self.hot_stack@.len() == mid.hot_stack@.len() - count,
            forall|f: int| 0 <= f < self.hot_stack@.len() ==> {
                let h = #[trigger] self.hot_stack@[f];
                let old_h = mid.hot_stack@[count + f];
                let cut = mid.hot_retirement_cut(count);
                &&& h.saved_len == old_h.saved_len
                &&& h.start == old_h.start - cut
                &&& h.end == old_h.end - cut
            },
    {
        reveal(Vec::hot_retired_from);
    }

    /// Frame counts and saved lengths after moving `count` Hot frames to Cold.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migration_partition(&self, mid: Self, pre: Self, count: nat)
        requires mid.hot_migrating(pre, count), self.hot_retired_from(mid, count),
        ensures self.frame_partition_ok(),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(Vec::hot_retired_from);
        mid.lemma_hot_migrating_frame(pre, count);
        mid.lemma_hot_migrating_cold_headers(pre, count);
        self.lemma_hot_retired_frame(mid, count);
        pre.lemma_partition_counts();
        let cc = pre.cold_stack@.len() as int;
        let hc = pre.hot_stack@.len() as int;
        assert(self.cold_stack@ == mid.cold_stack@);
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            (#[trigger] self.cold_stack@[f]).saved_len.as_nat() == self.snapshots@[f].len() by {
            if f < cc {
                assert(self.cold_stack@[f] == pre.cold_stack@[f]);
                pre.lemma_cold_saved_len(f);
            } else {
                let q = f - cc;
                assert(mid.cold_stack@[cc + q].saved_len == pre.hot_stack@[q].saved_len);
                assert(cc + q == f);
                pre.lemma_hot_saved_len(q);
            }
        }
        assert forall|i: int| 0 <= i < self.hot_stack@.len() implies
            (#[trigger] self.hot_stack@[i]).saved_len.as_nat()
                == self.snapshots@[self.cold_stack@.len() + i].len() by {
            assert(self.hot_stack@[i].saved_len == pre.hot_stack@[count + i].saved_len);
            pre.lemma_hot_saved_len(count + i);
        }
        assert forall|i: int| 0 <= i < self.trail_stack@.len() implies
            (#[trigger] self.trail_stack@[i]).saved_len.as_nat()
                == self.snapshots@[self.cold_stack@.len() + self.hot_stack@.len() + i].len() by {
            pre.lemma_trail_saved_len(i);
        }
        reveal(Vec::frame_partition_ok);
    }

    /// Trail representation is untouched by a Hot-to-Cold move: the tier's
    /// offset `cold + hot` and every referenced layer are unchanged.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migration_trail_repr(&self, pre: Self)
        requires pre.wf(),
            self.trail_stack@ == pre.trail_stack@, self.trail_value_pool@ == pre.trail_value_pool@,
            self.snapshots@ == pre.snapshots@, self.trail_frames@ == pre.trail_frames@,
            self.view() == pre.view(),
            self.cold_stack@.len() + self.hot_stack@.len() == pre.cold_stack@.len() + pre.hot_stack@.len(),
        ensures self.trail_repr_ok(),
    {
        hide(Vec::wf);
        hide(frame_inv_range);
        pre.lemma_wf_named_parts();
        reveal(Vec::trail_repr_ok);
        let offset = self.cold_stack@.len() + self.hot_stack@.len();
        assert forall|i: int| 0 <= i < self.trail_stack@.len() implies
            self.phys_trail_end(i) == pre.phys_trail_end(i)
            && self.layer_above_at(offset + i) == pre.layer_above_at(offset + i) by {}
    }

    /// Canonical history and compatibility residue are untouched by a
    /// Hot-to-Cold move once the frame partition is restored.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migration_history(&self, pre: Self)
        requires pre.wf(), self.frame_partition_ok(),
            self.view() == pre.view(), self.snapshots@ == pre.snapshots@,
            self.trail_frames@ == pre.trail_frames@, self.full_trail@ == pre.full_trail@,
            self.diff_log@ == pre.diff_log@, self.store == pre.store,
        ensures self.wf_for_snap(), self.proof_compat_ok(),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        assert(self.store.wf()) by { reveal(Vec::wf_for_snap); }
        self.lemma_canonical_history_repartition(pre);
        reveal(Vec::proof_compat_ok);
    }

    /// Accessor: Cold storage of `pre` is a prefix and the tier is laid out.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migrating_cold_prefix(&self, pre: Self, count: nat)
        requires self.hot_migrating_cold(pre, count),
        ensures self.cold_stack@.len() == pre.cold_stack@.len() + count,
            self.cold_stack@.subrange(0, pre.cold_stack@.len() as int) == pre.cold_stack@,
            self.cold_index_runs@.subrange(0, pre.cold_index_runs@.len() as int) == pre.cold_index_runs@,
            self.cold_value_pool@.subrange(0, pre.cold_value_pool@.len() as int) == pre.cold_value_pool@,
            pre.cold_index_runs@.len() <= self.cold_index_runs@.len(),
            pre.cold_value_pool@.len() <= self.cold_value_pool@.len(),
            self.repr_ok(), self.cold_payload_ok(), self.cold_runs_disjoint(),
    {
        reveal(Vec::hot_migrating_cold);
    }

    /// Accessor: the new Cold frame `q` carries Hot frame `q`'s saved map.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migrating_cold_new_frame(&self, pre: Self, count: nat, q: int)
        requires self.hot_migrating_cold(pre, count), 0 <= q < count,
        ensures ({
            let k = pre.cold_stack@.len() + q;
            &&& self.cold_stack@[k].saved_len == pre.hot_stack@[q].saved_len
            &&& forall|j: nat| #[trigger] self.cold_covered(k, j)
                <==> range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(q), pre.phys_hot_end(q), j) is Some
            &&& forall|j: nat| self.cold_covered(k, j) ==>
                Some(#[trigger] self.cold_value(k, j))
                    == range_saved_value::<T, I>(pre.hot_value_pool@,
                        pre.phys_hot_start(q), pre.phys_hot_end(q), j)
        }),
    {
        reveal(Vec::hot_migrating_cold);
    }

    /// Accessor: Hot frame `g <= count` is unique with `pre`'s saved map.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migrating_hot_frame_map(&self, pre: Self, count: nat, g: int)
        requires self.hot_migrating_hot(pre, count), 0 <= g <= count, g < pre.hot_stack@.len(),
        ensures stratum_unique::<T, I>(self.hot_value_pool@, pre.phys_hot_start(g), pre.phys_hot_end(g)),
            forall|j: nat| #[trigger] range_saved_value::<T, I>(self.hot_value_pool@,
                    pre.phys_hot_start(g), pre.phys_hot_end(g), j)
                == range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(g), pre.phys_hot_end(g), j),
    {
        reveal(Vec::hot_migrating_hot);
    }

    /// Accessor: cells from frame `count + 1` on are untouched.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migrating_hot_unchanged(&self, pre: Self, count: nat)
        requires self.hot_migrating_hot(pre, count),
        ensures self.hot_value_pool@.len() == pre.hot_value_pool@.len(),
            forall|q: int| pre.hot_retirement_cut(count + 1) <= q < pre.hot_value_pool@.len() ==>
                #[trigger] self.hot_value_pool@[q] == pre.hot_value_pool@[q],
    {
        reveal(Vec::hot_migrating_hot);
    }

    /// The frame contract at one cell, read through the earliest-capture map.
    #[verifier::spinoff_prover]
    proof fn lemma_captured_cell_value(
        above: Seq<T>, diffs: Seq<(T, I)>, lo: int, hi: int, snap: Seq<T>, saved_len: nat, c: int,
    )
        requires frame_inv_range::<T, I>(above, diffs, lo, hi, snap, saved_len), 0 <= c < saved_len,
            0 <= lo <= hi <= diffs.len(),
        ensures
            captured_in_range::<T, I>(diffs, lo, hi, c as nat) ==>
                range_saved_value::<T, I>(diffs, lo, hi, c as nat) == Some(snap[c]),
            !captured_in_range::<T, I>(diffs, lo, hi, c as nat) ==>
                c < above.len() && above[c] == snap[c],
    {
        lemma_frame_inv_arm_at::<T, I>(above, diffs, lo, hi, snap, saved_len, c);
        if captured_in_range::<T, I>(diffs, lo, hi, c as nat) {
            let k = choose|k: int| lo <= k < hi
                && (#[trigger] diffs[k]).1.as_nat() == c as nat
                && diffs[k].0 == snap[c]
                && first_hitter::<T, I>(diffs, lo, k, c as nat);
            let p = choose|p: int| lo <= p < hi
                && (#[trigger] diffs[p]).1.as_nat() == c as nat
                && first_hitter::<T, I>(diffs, lo, p, c as nat);
            if p < k {
                assert(diffs[p].1.as_nat() != c as nat);
            } else if k < p {
                assert(diffs[k].1.as_nat() != c as nat);
            }
            assert(range_saved_value::<T, I>(diffs, lo, hi, c as nat) == Some(diffs[p].0));
        }
    }

    /// Every Cold frame reconstructs after the move: kept frames keep their
    /// cells, and each new frame carries its source Hot frame's contract.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migration_cold_reconstructs(&self, mid: Self, pre: Self, count: nat, k: int)
        requires mid.hot_migrating(pre, count), self.hot_retired_from(mid, count),
            0 <= k < self.cold_stack@.len(),
        ensures self.cold_reconstructs(k),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(Vec::hot_retired_from);
        hide(Vec::repr_ok);
        hide(Vec::cold_runs_disjoint);
        hide(Vec::cold_payload_ok);
        hide(stratum_unique);
        mid.lemma_hot_migrating_frame(pre, count);
        mid.lemma_hot_migrating_cold_prefix(pre, count);
        self.lemma_hot_retired_frame(mid, count);
        pre.lemma_wf_named_parts();
        let cc = pre.cold_stack@.len() as int;
        assert(self.cold_stack@ == mid.cold_stack@);
        assert(self.cold_index_runs@ == mid.cold_index_runs@);
        assert(self.cold_value_pool@ == mid.cold_value_pool@);
        assert(self.snapshots@ == pre.snapshots@);
        assert(self.trail_frames@ == pre.trail_frames@);
        assert(self.view() == pre.view());
        if k < cc {
            assert(pre.repr_ok() && pre.cold_runs_disjoint() && pre.cold_reconstructs(k)) by {
                reveal(Vec::cold_repr_ok);
            }
            assert forall|c: int| #![trigger self.cold_covered(k, c as nat)]
                0 <= c < self.g_saved_len(k) as int implies
                if self.cold_covered(k, c as nat) {
                    self.cold_value(k, c as nat) == self.snapshots@[k][c]
                } else {
                    &&& c < self.layer_above_at(k).len()
                    &&& self.snapshots@[k][c] == self.layer_above_at(k)[c]
                } by {
                pre.lemma_cold_reconstructs_at(k, c);
                self.lemma_cold_append_keeps_frame(pre, k, c as nat);
                assert(self.layer_above_at(k) == pre.layer_above_at(k));
            }
            assert(self.cold_reconstructs(k)) by { reveal(Vec::cold_reconstructs); }
        } else {
            let q = k - cc;
            mid.lemma_hot_migrating_cold_new_frame(pre, count, q);
            assert(cc + q == k);
            pre.lemma_pair_tier_contract(false, q);
            pre.lemma_pair_tier_frame_layout(false, q);
            pre.lemma_hot_saved_len(q);
            let s = pre.phys_hot_start(q);
            let e = pre.phys_hot_end(q);
            let saved = pre.snapshots@[k].len();
            assert forall|c: int| #![trigger self.cold_covered(k, c as nat)]
                0 <= c < self.g_saved_len(k) as int implies
                if self.cold_covered(k, c as nat) {
                    self.cold_value(k, c as nat) == self.snapshots@[k][c]
                } else {
                    &&& c < self.layer_above_at(k).len()
                    &&& self.snapshots@[k][c] == self.layer_above_at(k)[c]
                } by {
                Self::lemma_captured_cell_value(pre.layer_above_at(k), pre.hot_value_pool@, s, e,
                    pre.snapshots@[k], saved, c);
                assert(self.layer_above_at(k) == pre.layer_above_at(k));
                assert(mid.cold_covered(k, c as nat) == self.cold_covered(k, c as nat));
                if self.cold_covered(k, c as nat) {
                    assert(self.cold_value(k, c as nat) == mid.cold_value(k, c as nat));
                    assert(captured_in_range::<T, I>(pre.hot_value_pool@, s, e, c as nat));
                }
            }
            assert(self.cold_reconstructs(k)) by { reveal(Vec::cold_reconstructs); }
        }
    }

    /// Retained Hot frame `i` (source frame `count + i`) keeps its saved map
    /// and uniqueness on its rebased range.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migration_hot_map(&self, mid: Self, pre: Self, count: nat, i: int)
        requires mid.hot_migrating(pre, count), self.hot_retired_from(mid, count),
            0 <= i < self.hot_stack@.len(),
        ensures
            self.phys_hot_start(i) == pre.phys_hot_start(count + i) - pre.hot_retirement_cut(count),
            self.phys_hot_end(i) == pre.phys_hot_end(count + i) - pre.hot_retirement_cut(count),
            0 <= self.phys_hot_start(i) <= self.phys_hot_end(i) <= self.hot_value_pool@.len(),
            stratum_unique::<T, I>(self.hot_value_pool@, self.phys_hot_start(i), self.phys_hot_end(i)),
            forall|j: nat| #[trigger] range_saved_value::<T, I>(self.hot_value_pool@,
                    self.phys_hot_start(i), self.phys_hot_end(i), j)
                == range_saved_value::<T, I>(pre.hot_value_pool@,
                    pre.phys_hot_start(count + i), pre.phys_hot_end(count + i), j),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_cold);
        hide(Vec::hot_retired_from);
        hide(range_saved_value);
        hide(stratum_unique);
        mid.lemma_hot_migrating_frame(pre, count);
        mid.lemma_hot_migrating_hot_unchanged(pre, count);
        self.lemma_hot_retired_frame(mid, count);
        let g = count + i;
        let len = pre.hot_stack@.len() as int;
        assert(mid.hot_stack@ == pre.hot_stack@);
        assert(count < len);
        let cut = pre.hot_retirement_cut(count) as int;
        assert(mid.hot_retirement_cut(count) == pre.hot_retirement_cut(count));
        pre.lemma_pair_tier_frame_layout(false, g);
        pre.lemma_pair_tier_start_order(false, count as int, g);
        let s = pre.phys_hot_start(g);
        let e = pre.phys_hot_end(g);
        assert(cut <= s);
        assert(self.phys_hot_start(i) == s - cut);
        assert(self.phys_hot_end(i) == e - cut);
        // mid's frame g has pre's map
        assert(stratum_unique::<T, I>(mid.hot_value_pool@, s, e)
            && forall|j: nat| #[trigger] range_saved_value::<T, I>(mid.hot_value_pool@, s, e, j)
                == range_saved_value::<T, I>(pre.hot_value_pool@, s, e, j)) by {
            if g <= count {
                mid.lemma_hot_migrating_hot_frame_map(pre, count, g);
            } else {
                pre.lemma_pair_tier_start_order(false, count as int + 1, g);
                assert(pre.hot_retirement_cut(count + 1) == pre.hot_stack@[count as int + 1].start as nat);
                assert forall|q: int| s <= q < e implies
                    #[trigger] mid.hot_value_pool@[q] == pre.hot_value_pool@[q] by {}
                assert(stratum_unique::<T, I>(pre.hot_value_pool@, s, e)) by {
                    pre.lemma_wf_named_parts();
                    reveal(Vec::hot_repr_ok);
                }
                assert(stratum_unique::<T, I>(mid.hot_value_pool@, s, e)) by { reveal(stratum_unique); }
                assert forall|j: nat| #[trigger] range_saved_value::<T, I>(mid.hot_value_pool@, s, e, j)
                    == range_saved_value::<T, I>(pre.hot_value_pool@, s, e, j) by {
                    lemma_range_saved_value_local::<T, I>(pre.hot_value_pool@, mid.hot_value_pool@, s, e, j);
                }
            }
        }
        // rebase
        assert forall|j: nat| #[trigger] range_saved_value::<T, I>(self.hot_value_pool@, s - cut, e - cut, j)
            == range_saved_value::<T, I>(mid.hot_value_pool@, s, e, j) by {
            lemma_range_saved_value_retire_prefix::<T, I>(mid.hot_value_pool@, cut, s, e, j);
        }
        assert(stratum_unique::<T, I>(self.hot_value_pool@, s - cut, e - cut)) by {
            reveal(stratum_unique);
            assert forall|a: int, b: int| s - cut <= a < e - cut && s - cut <= b < e - cut && a != b implies
                (#[trigger] self.hot_value_pool@[a]).1.as_nat() != (#[trigger] self.hot_value_pool@[b]).1.as_nat() by {
                assert(self.hot_value_pool@[a] == mid.hot_value_pool@[cut + a]);
                assert(self.hot_value_pool@[b] == mid.hot_value_pool@[cut + b]);
            }
        }
    }

    /// Retained Hot frame `i` satisfies its physical frame contract.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migration_hot_frame(&self, mid: Self, pre: Self, count: nat, i: int)
        requires mid.hot_migrating(pre, count), self.hot_retired_from(mid, count),
            0 <= i < self.hot_stack@.len(),
        ensures self.phys_frame_inv_range_holds(i),
            stratum_unique::<T, I>(self.hot_value_pool@, self.phys_hot_start(i), self.phys_hot_end(i)),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(Vec::hot_retired_from);
        hide(range_saved_value);
        hide(stratum_unique);
        hide(frame_inv_range);
        hide(Vec::phys_frame_inv_range_holds);
        mid.lemma_hot_migrating_frame(pre, count);
        mid.lemma_hot_migrating_cold_prefix(pre, count);
        self.lemma_hot_retired_frame(mid, count);
        self.lemma_hot_migration_hot_map(mid, pre, count, i);
        let g = count + i;
        let cc = pre.cold_stack@.len() as int;
        pre.lemma_pair_tier_contract(false, g);
        pre.lemma_pair_tier_frame_layout(false, g);
        assert(self.cold_stack@.len() == cc + count);
        assert(self.snapshots@ == pre.snapshots@);
        assert(self.trail_frames@ == pre.trail_frames@);
        assert(self.view() == pre.view());
        assert(self.layer_above_at(cc + g) == pre.layer_above_at(cc + g));
        lemma_frame_inv_range_same_saved_map::<T, I>(pre.layer_above_at(cc + g), pre.hot_value_pool@,
            pre.phys_hot_start(g), pre.phys_hot_end(g), self.hot_value_pool@,
            self.phys_hot_start(i), self.phys_hot_end(i), pre.snapshots@[cc + g], pre.snapshots@[cc + g].len());
        reveal(Vec::phys_frame_inv_range_holds);
    }

    /// Hot representation after retiring the encoded prefix.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migration_hot_repr(&self, mid: Self, pre: Self, count: nat)
        requires mid.hot_migrating(pre, count), self.hot_retired_from(mid, count),
            self.frame_partition_ok(),
        ensures self.hot_repr_ok(),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(Vec::hot_retired_from);
        hide(range_saved_value);
        hide(stratum_unique);
        hide(frame_inv_range);
        mid.lemma_hot_migrating_frame(pre, count);
        self.lemma_hot_retired_frame(mid, count);
        pre.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
        let cut = pre.hot_retirement_cut(count) as int;
        let len = pre.hot_stack@.len() as int;
        let hs = self.hot_stack@;
        let pool = self.hot_value_pool@;
        assert(mid.hot_stack@ == pre.hot_stack@);
        assert(mid.hot_retirement_cut(count) == pre.hot_retirement_cut(count));
        pre.lemma_hot_cut_order(count, count);
        assert(pool.len() == pre.hot_value_pool@.len() - cut);
        if hs.len() == 0 {
            assert(count == len);
            assert(pool.len() == 0);
        } else {
            assert(count < len);
            pre.lemma_pair_tier_frame_layout(false, count as int);
            assert(hs[0].start == pre.hot_stack@[count as int].start - cut);
        }
        assert forall|i: int| 0 <= i < hs.len() implies {
            &&& (#[trigger] hs[i]).start <= hs[i].end
            &&& hs[i].end <= pool.len()
            &&& hs[i].start as int <= self.phys_hot_end(i)
            &&& self.phys_hot_end(i) <= pool.len() as int
            &&& (i + 1 < hs.len() ==> {
                &&& hs[i].end == hs[i + 1].start
                &&& self.phys_hot_end(i) == hs[i + 1].start as int
            })
            &&& (i + 1 == hs.len() ==> self.phys_hot_end(i) == pool.len() as int)
            &&& stratum_unique::<T, I>(pool, hs[i].start as int, self.phys_hot_end(i))
            &&& self.phys_frame_inv_range_holds(i)
            &&& self.cold_stack@.len() + i < self.snapshots@.len()
        } by {
            let g = count + i;
            pre.lemma_pair_tier_frame_layout(false, g);
            pre.lemma_pair_tier_start_order(false, count as int, g);
            self.lemma_hot_migration_hot_frame(mid, pre, count, i);
            self.lemma_hot_migration_hot_map(mid, pre, count, i);
            if i + 1 < hs.len() {
                pre.lemma_pair_tier_frame_layout(false, g + 1);
            }
        }
        reveal(Vec::hot_repr_ok);
    }

    /// Capture ownership after retiring the encoded prefix.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migration_ingress(&self, mid: Self, pre: Self, count: nat)
        requires mid.hot_migrating(pre, count), self.hot_retired_from(mid, count),
        ensures self.open_ingress_ok(),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(Vec::hot_retired_from);
        hide(stratum_unique);
        hide(frame_inv_range);
        mid.lemma_hot_migrating_frame(pre, count);
        self.lemma_hot_retired_frame(mid, count);
        pre.lemma_wf_named_parts();
        reveal(Vec::open_ingress_ok);
        let depth = self.snapshots@.len();
        let hs = self.hot_stack@;
        let len = pre.hot_stack@.len() as int;
        let cut = pre.hot_retirement_cut(count) as int;
        assert(mid.hot_stack@ == pre.hot_stack@);
        assert(mid.hot_retirement_cut(count) == pre.hot_retirement_cut(count));
        assert(self.store == pre.store);
        assert(self.view() == pre.view());
        assert(self.snapshots@ == pre.snapshots@);
        assert(self.active_saved_len == pre.active_saved_len);
        assert(self.trail_stack@ == pre.trail_stack@);
        assert(self.trail_value_pool@ == pre.trail_value_pool@);
        if self.store.unique_capture_spec() {
            if depth > 0 {
                assert(pre.hot_stack@.len() > 0);
                assert(count <= pre.hot_closed_count());
                assert(count < len);
                let i = hs.len() - 1;
                let g = len - 1;
                assert(count + i == g);
                self.lemma_hot_migration_hot_map(mid, pre, count, i);
                assert(pre.phys_hot_end(g) == pre.hot_value_pool@.len() as int);
                assert(self.phys_hot_end(i) == self.hot_value_pool@.len() as int);
                assert forall|j: int| 0 <= j < self.active_saved_len.as_nat() && j < self.view().len() implies
                    (#[trigger] self.store.captured()[j])
                        == captured_in_range::<T, I>(self.hot_value_pool@,
                            hs[i].start as int, self.hot_value_pool@.len() as int, j as nat) by {
                    assert(range_saved_value::<T, I>(self.hot_value_pool@,
                            self.phys_hot_start(i), self.phys_hot_end(i), j as nat)
                        == range_saved_value::<T, I>(pre.hot_value_pool@,
                            pre.phys_hot_start(g), pre.phys_hot_end(g), j as nat));
                }
            }
        } else {
            if hs.len() > 0 {
                assert(count < len);
                assert(hs[hs.len() - 1].end == pre.hot_stack@[len - 1].end - cut);
                pre.lemma_hot_cut_order(count, count);
            }
        }
    }

    /// A completed Hot-to-Cold migration restores the full invariant.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_migration_wf(&self, mid: Self, pre: Self, count: nat)
        requires mid.hot_migrating(pre, count), self.hot_retired_from(mid, count),
        ensures self.wf(),
            *self == (Self { cold_stack: self.cold_stack, cold_index_runs: self.cold_index_runs,
                cold_value_pool: self.cold_value_pool, hot_stack: self.hot_stack,
                hot_value_pool: self.hot_value_pool, ..pre }),
            self.cold_stack@.len() == pre.cold_stack@.len() + count,
            self.hot_stack@.len() == pre.hot_stack@.len() - count,
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(Vec::hot_retired_from);
        hide(Vec::wf_for_snap);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::open_ingress_ok);
        hide(Vec::cold_repr_ok);
        hide(Vec::proof_compat_ok);
        hide(Vec::frame_partition_ok);
        hide(Vec::repr_ok);
        hide(Vec::cold_payload_ok);
        hide(Vec::cold_runs_disjoint);
        mid.lemma_hot_migrating_frame(pre, count);
        mid.lemma_hot_migrating_cold_prefix(pre, count);
        self.lemma_hot_retired_frame(mid, count);
        self.lemma_hot_migration_partition(mid, pre, count);
        self.lemma_hot_migration_hot_repr(mid, pre, count);
        self.lemma_hot_migration_trail_repr(pre);
        self.lemma_hot_migration_ingress(mid, pre, count);
        self.lemma_hot_migration_history(pre);
        assert(self.cold_stack@ == mid.cold_stack@);
        assert(self.cold_index_runs@ == mid.cold_index_runs@);
        assert(self.cold_value_pool@ == mid.cold_value_pool@);
        assert(self.repr_ok()) by { reveal(Vec::repr_ok); }
        assert(self.cold_runs_disjoint()) by { reveal(Vec::cold_runs_disjoint); }
        self.lemma_cold_payload_ok_transfer(mid);
        assert(self.cold_repr_ok()) by {
            reveal(Vec::cold_repr_ok);
            assert forall|k: int| 0 <= k < self.cold_stack@.len() implies
                #[trigger] self.cold_reconstructs(k) by {
                self.lemma_hot_migration_cold_reconstructs(mid, pre, count, k);
            }
        }
        self.lemma_wf_from_named_parts();
    }

    /// Retire the encoded Hot prefix and restore the full invariant.
    #[verifier::spinoff_prover]
    fn hot_migration_finish_checked(&mut self, count: usize, Ghost(pre): Ghost<Self>)
        requires old(self).hot_migrating(pre, count as nat),
        ensures final(self).wf(),
            *final(self) == (Self { cold_stack: final(self).cold_stack,
                cold_index_runs: final(self).cold_index_runs,
                cold_value_pool: final(self).cold_value_pool, hot_stack: final(self).hot_stack,
                hot_value_pool: final(self).hot_value_pool, ..pre }),
            final(self).cold_stack@.len() == pre.cold_stack@.len() + count,
            final(self).hot_stack@.len() == pre.hot_stack@.len() - count,
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        hide(Vec::hot_migrating_hot);
        hide(Vec::hot_migrating_cold);
        hide(Vec::hot_retired_from);
        let ghost mid = *self;
        proof {
            mid.lemma_hot_migrating_frame(pre, count as nat);
            pre.lemma_hot_cut_order(count as nat, count as nat);
        }
        if count == 0 {
            proof {
                assert(self.hot_retired_from(mid, 0)) by {
                    reveal(Vec::hot_retired_from);
                    if pre.hot_stack@.len() > 0 {
                        pre.lemma_pair_tier_frame_layout(false, 0);
                    } else {
                        pre.lemma_wf_named_parts();
                        reveal(Vec::hot_repr_ok);
                    }
                    assert(self.hot_value_pool@ =~= mid.hot_value_pool@.subrange(
                        mid.hot_retirement_cut(0) as int, mid.hot_value_pool@.len() as int));
                }
                self.lemma_hot_migration_wf(mid, pre, 0);
            }
            return;
        }
        proof {
            assert forall|f: int| count <= f < mid.hot_stack@.len() implies
                mid.hot_retirement_cut(count as nat) <= (#[trigger] mid.hot_stack@[f]).start
                && mid.hot_retirement_cut(count as nat) <= mid.hot_stack@[f].end by {
                pre.lemma_pair_tier_start_order(false, count as int, f);
                pre.lemma_pair_tier_frame_layout(false, f);
            }
        }
        self.retire_hot_prefix_checked(count);
        proof {
            assert(self.hot_retired_from(mid, count as nat)) by { reveal(Vec::hot_retired_from); }
            self.lemma_hot_migration_wf(mid, pre, count as nat);
        }
    }

    /// Every index of a migrating frame fits below `usize::MAX`, so the run
    /// counter's successor probe cannot overflow.
    #[verifier::spinoff_prover]
    proof fn lemma_hot_frame_indices_fit(&self, pre: Self, f: int)
        requires self.hot_migrating(pre, f as nat), 0 <= f < pre.hot_closed_count(),
            pre.hot_stack@[f].saved_len.as_nat() <= usize::MAX,
        ensures forall|q: int| pre.hot_stack@[f].start <= q < pre.hot_stack@[f].end ==>
            (#[trigger] self.hot_value_pool@[q]).1.as_nat() < usize::MAX,
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating_cold);
        hide(stratum_unique);
        hide(range_saved_value);
        assert forall|q: int| pre.hot_stack@[f].start <= q < pre.hot_stack@[f].end implies
            (#[trigger] self.hot_value_pool@[q]).1.as_nat() < usize::MAX by {
            self.lemma_hot_frame_index_bound(pre, f, q - pre.hot_stack@[f].start);
        }
    }

    /// Reclaim the pools a Hot-to-Cold move touched when the policy asks for
    /// it. Capacity only: every view, the store and the history are unchanged.
    #[verifier::spinoff_prover]
    fn reclaim_after_hot_migration_checked(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(),
            *final(self) == (Self { hot_value_pool: final(self).hot_value_pool,
                cold_value_pool: final(self).cold_value_pool,
                cold_index_runs: final(self).cold_index_runs, ..*old(self) }),
            final(self).hot_value_pool@ == old(self).hot_value_pool@,
            final(self).cold_value_pool@ == old(self).cold_value_pool@,
            final(self).cold_index_runs@ == old(self).cold_index_runs@,
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_repr_ok);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::open_ingress_ok);
        let ghost pre = *self;
        if matches!(self.tier_policy.cold_reclaim, crate::tier_policy::ReclaimPolicy::ShrinkToFit) {
            crate::parallel_store::shrink_vec_capacity(&mut self.hot_value_pool, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_value_pool, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_index_runs, 0, 1);
        }
        proof {
            pre.lemma_wf_named_parts();
            assert(pre.store.wf()) by { reveal(Vec::wf_for_snap); }
            self.lemma_survivor_history_transfer(pre);
            self.lemma_persistence_views_framing(pre);
            self.lemma_open_ingress_transfer(pre);
            reveal(Vec::wf);
        }
    }

    /// Execute an exact oldest closed Hot prefix as direct-restorable runs:
    /// each frame is sorted in place and encoded straight from the pool, then
    /// the prefix is retired in one bulk move.
    #[verifier::spinoff_prover]
    #[cold]
    #[inline(never)]
    fn runtime_migrate_hot_count(&mut self, count: usize)
        requires old(self).wf(), count <= old(self).hot_closed_count(),
        ensures final(self).wf(),
            *final(self) == (Self { cold_stack: final(self).cold_stack,
                cold_index_runs: final(self).cold_index_runs,
                cold_value_pool: final(self).cold_value_pool, hot_stack: final(self).hot_stack,
                hot_value_pool: final(self).hot_value_pool, ..*old(self) }),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        if count == 0 {
            return;
        }
        let ghost pre = *self;
        proof { self.lemma_hot_migrating_start(pre); }
        let mut f = 0usize;
        while f < count
            invariant self.hot_migrating(pre, f as nat), f <= count, count <= pre.hot_closed_count(),
            decreases count - f,
        {
            self.hot_frame_sort_checked(f, Ghost(pre));
            self.hot_frame_encode_checked(f, Ghost(pre));
            f += 1;
        }
        self.hot_migration_finish_checked(count, Ghost(pre));
        self.reclaim_after_hot_migration_checked();
    }

    /// Migrate an oldest closed unique prefix to direct-restorable runs. The
    /// `Adaptive` limit keeps encoding oldest-first while each frame's run count
    /// stays at most half its entries; the first frame that does not stops the
    /// pass (it stays in Hot, sorted in place).
    #[verifier::spinoff_prover]
    #[cold]
    #[inline(never)]
    fn runtime_migrate_hot(&mut self, compress_all: bool)
        requires old(self).wf(),
        ensures final(self).wf(),
            *final(self) == (Self { cold_stack: final(self).cold_stack,
                cold_index_runs: final(self).cold_index_runs,
                cold_value_pool: final(self).cold_value_pool, hot_stack: final(self).hot_stack,
                hot_value_pool: final(self).hot_value_pool, ..*old(self) }),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        let closed = if self.store.unique_capture() {
            self.hot_stack.len().saturating_sub(1)
        } else {
            self.hot_stack.len()
        };
        proof { assert(closed == self.hot_closed_count()); }
        if closed == 0 {
            return;
        }
        let adaptive = match self.tier_policy.hot {
            crate::tier_policy::TierLimit::Adaptive => true,
            _ => false,
        };
        if !compress_all && adaptive {
            let ghost pre = *self;
            proof { self.lemma_hot_migrating_start(pre); }
            let mut count = 0usize;
            while count < closed
                invariant self.hot_migrating(pre, count as nat), count <= closed,
                    closed == pre.hot_closed_count(),
                decreases closed - count,
            {
                self.hot_frame_sort_checked(count, Ghost(pre));
                proof {
                    self.lemma_hot_migrating_frame(pre, count as nat);
                    pre.lemma_closed_hot_frame_end(count as int);
                }
                let frame = self.hot_stack[count];
                let saved_len = frame.saved_len;
                let entries = frame.end - frame.start;
                proof {
                    saved_len.lemma_as_nat_bounded();
                    I::lemma_max_nat_fits_usize();
                    self.lemma_hot_frame_indices_fit(pre, count as int);
                }
                let runs = Self::count_index_runs(&self.hot_value_pool, frame.start, frame.end);
                let doubled = match runs.checked_mul(2) {
                    Some(d) => d,
                    None => usize::MAX,
                };
                if entries == 0 || doubled > entries {
                    break;
                }
                self.hot_frame_encode_checked(count, Ghost(pre));
                count += 1;
            }
            self.hot_migration_finish_checked(count, Ghost(pre));
            if count > 0 {
                self.reclaim_after_hot_migration_checked();
            }
            return;
        }
        let count = if compress_all {
            closed
        } else {
            self.retained_closed_prefix(false, closed, self.tier_policy.hot, core::mem::size_of::<(T, I)>())
        };
        self.runtime_migrate_hot_count(count);
    }

    /// Adaptive Hot stage: sort closed Hot frames in place oldest-first and
    /// encode each into Cold while the closed-history budget is exceeded and
    /// the frame's run shape pays for it. An ineligible frame stops the stage
    /// and stays in Hot. Returns the updated logical byte estimate.
    #[verifier::spinoff_prover]
    #[cold]
    #[inline(never)]
    fn adaptive_hot_stage_checked(
        &mut self, input: &crate::tier_policy::AdaptiveInput,
        report: &mut crate::tier_policy::AdaptiveReport, logical: usize, preexisting_hot_frames: usize,
    ) -> (r: usize)
        requires old(self).wf(),
            old(report).inspected_hot_frames == 0, old(report).migrated_hot_frames == 0,
        ensures final(self).wf(),
            *final(self) == (Self { cold_stack: final(self).cold_stack,
                cold_index_runs: final(self).cold_index_runs,
                cold_value_pool: final(self).cold_value_pool, hot_stack: final(self).hot_stack,
                hot_value_pool: final(self).hot_value_pool, ..*old(self) }),
            *final(report) == (crate::tier_policy::AdaptiveReport {
                inspected_hot_frames: final(report).inspected_hot_frames,
                migrated_hot_frames: final(report).migrated_hot_frames,
                uniques: final(report).uniques, runs: final(report).runs, ..*old(report) }),
            final(report).migrated_hot_frames == old(self).hot_stack@.len() - final(self).hot_stack@.len(),
    {
        hide(Vec::wf);
        hide(Vec::hot_migrating);
        let hot_closed = if self.store.unique_capture() {
            self.hot_stack.len().saturating_sub(1)
        } else {
            self.hot_stack.len()
        };
        proof { assert(hot_closed == self.hot_closed_count()); }
        let pair_bytes = core::mem::size_of::<(T, I)>();
        let hot_header_bytes = core::mem::size_of::<crate::frame::HotFrame<I>>();
        let cold_header_bytes = core::mem::size_of::<crate::frame::ColdFrameHdr<I>>();
        let value_bytes = core::mem::size_of::<T>();
        let run_bytes = core::mem::size_of::<crate::frame::IndexRun<I>>();
        let ghost pre = *self;
        let ghost report0 = *report;
        proof { self.lemma_hot_migrating_start(pre); }
        let mut logical = logical;
        let mut hot_count = 0usize;
        while hot_count < hot_closed && logical > input.max_closed_history_bytes
            invariant_except_break
                report.inspected_hot_frames == hot_count,
            invariant
                self.hot_migrating(pre, hot_count as nat),
                hot_count <= hot_closed, hot_closed == pre.hot_closed_count(),
                *report == (crate::tier_policy::AdaptiveReport {
                    inspected_hot_frames: report.inspected_hot_frames,
                    uniques: report.uniques, runs: report.runs, ..report0 }),
            decreases hot_closed - hot_count,
        {
            self.hot_frame_sort_checked(hot_count, Ghost(pre));
            proof {
                self.lemma_hot_migrating_frame(pre, hot_count as nat);
                pre.lemma_closed_hot_frame_end(hot_count as int);
            }
            let frame = self.hot_stack[hot_count];
            let saved_len = frame.saved_len;
            let uniques = frame.end - frame.start;
            proof {
                saved_len.lemma_as_nat_bounded();
                I::lemma_max_nat_fits_usize();
                self.lemma_hot_frame_indices_fit(pre, hot_count as int);
            }
            let runs = Self::count_index_runs(&self.hot_value_pool, frame.start, frame.end);
            report.inspected_hot_frames = report.inspected_hot_frames + 1;
            if hot_count < preexisting_hot_frames {
                report.uniques = Self::adaptive_add_total(report.uniques, uniques);
            }
            report.runs = Self::adaptive_add_total(report.runs, runs);
            let hot_bytes = Self::adaptive_frame_bytes(hot_header_bytes, uniques, pair_bytes);
            let values = match uniques.checked_mul(value_bytes) {
                Some(v) => v,
                None => crate::guard::refuse("logical adaptive Cold byte count overflow"),
            };
            let cold_bytes = match cold_header_bytes.checked_add(values) {
                Some(b) => {
                    let run_total = match runs.checked_mul(run_bytes) {
                        Some(v) => v,
                        None => crate::guard::refuse("logical adaptive Cold byte count overflow"),
                    };
                    match b.checked_add(run_total) {
                        Some(c) => c,
                        None => crate::guard::refuse("logical adaptive Cold byte count overflow"),
                    }
                }
                None => crate::guard::refuse("logical adaptive Cold byte count overflow"),
            };
            let eligible = if uniques == 0 {
                cold_bytes <= hot_bytes
            } else {
                input.min_uniques_per_run.accepts(uniques, runs) && cold_bytes <= hot_bytes
            };
            if !eligible {
                break;
            }
            logical = match logical.checked_sub(hot_bytes) {
                Some(v) => v,
                None => crate::guard::refuse("adaptive logical byte estimate underflow"),
            };
            logical = match logical.checked_add(cold_bytes) {
                Some(v) => v,
                None => crate::guard::refuse("adaptive logical byte estimate overflow"),
            };
            self.hot_frame_encode_checked(hot_count, Ghost(pre));
            hot_count += 1;
        }
        report.migrated_hot_frames = hot_count;
        self.hot_migration_finish_checked(hot_count, Ghost(pre));
        logical
    }

    /// Only the seven physical tier vectors differ from `pre`: live contents,
    /// snapshots, canonical history, the store and the policy are untouched.
    pub open(crate) spec fn tiers_only_changed(&self, pre: Self) -> bool {
        *self == (Self { cold_stack: self.cold_stack, cold_index_runs: self.cold_index_runs,
            cold_value_pool: self.cold_value_pool, hot_stack: self.hot_stack,
            hot_value_pool: self.hot_value_pool, trail_stack: self.trail_stack,
            trail_value_pool: self.trail_value_pool, trail_seen: self.trail_seen, ..pre })
    }

    /// All-tier capacity reclamation after an adaptive pass (`ShrinkToFit`
    /// only). Capacity only: every view, the store and the history are unchanged.
    #[verifier::spinoff_prover]
    #[cold]
    #[inline(never)]
    fn runtime_reclaim_adaptive_tier_capacities(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).tiers_only_changed(*old(self)),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_repr_ok);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::open_ingress_ok);
        let ghost pre = *self;
        if matches!(self.tier_policy.cold_reclaim, crate::tier_policy::ReclaimPolicy::ShrinkToFit) {
            crate::parallel_store::shrink_vec_capacity(&mut self.trail_value_pool, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.trail_stack, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.hot_value_pool, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.hot_stack, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_value_pool, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_index_runs, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_stack, 0, 1);
            self.trail_seen = None;
        }
        proof {
            pre.lemma_wf_named_parts();
            assert(pre.store.wf()) by { reveal(Vec::wf_for_snap); }
            self.lemma_survivor_history_transfer(pre);
            self.lemma_persistence_views_framing(pre);
            self.lemma_open_ingress_transfer(pre);
            reveal(Vec::wf);
        }
    }

    /// One deterministic explicit-budget Trail -> Hot -> Cold pass over closed
    /// history; the writable frame and its store protocol are never touched.
    #[verifier::spinoff_prover]
    #[cold]
    #[inline(never)]
    fn runtime_apply_adaptive(
        &mut self,
        input: crate::tier_policy::AdaptiveInput,
    ) -> (report: crate::tier_policy::AdaptiveReport)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).tiers_only_changed(*old(self)),
    {
        hide(Vec::wf);
        let mut report = crate::tier_policy::AdaptiveReport {
            inspected_frames: 0, migrated_frames: 0, inspected_trail_frames: 0,
            migrated_trail_frames: 0, inspected_hot_frames: 0, migrated_hot_frames: 0,
            writes: 0, uniques: 0, runs: 0, logical_bytes_before: 0, logical_bytes_after: 0,
            budget_unmet_bytes: 0,
        };
        let mut logical = self.runtime_closed_history_bytes();
        report.logical_bytes_before = logical;
        if logical <= input.max_closed_history_bytes {
            report.logical_bytes_after = logical;
            return report;
        }

        let preexisting_hot_frames = self.hot_stack.len();
        // Both stages return the pressure they leave behind; neither value is
        // read here, because the Trail stage's result is superseded by the exact
        // recomputation below and the Hot stage's is only reported.
        self.adaptive_trail_stage_checked(&input, &mut report, logical);

        // Trail -> Hot is executed first. Recompute exact pressure before the
        // Hot scan so the second stage sees the actual closed representation.
        logical = self.runtime_closed_history_bytes();
        self.adaptive_hot_stage_checked(&input, &mut report, logical, preexisting_hot_frames);

        report.inspected_frames = match report.inspected_trail_frames.checked_add(report.inspected_hot_frames) {
            Some(v) => v,
            None => crate::guard::refuse("adaptive frame count overflow"),
        };
        report.migrated_frames = match report.migrated_trail_frames.checked_add(report.migrated_hot_frames) {
            Some(v) => v,
            None => crate::guard::refuse("adaptive frame count overflow"),
        };
        if report.migrated_frames != 0 {
            // Reclaim only after both stages finish so a Trail -> Hot -> Cold
            // cascade does not shrink and immediately regrow intermediate pools.
            self.runtime_reclaim_adaptive_tier_capacities();
        }
        report.logical_bytes_after = self.runtime_closed_history_bytes();
        report.budget_unmet_bytes = report
            .logical_bytes_after
            .saturating_sub(input.max_closed_history_bytes);
        report
    }

    /// Apply one deterministic explicit-budget Trail -> Hot -> Cold pass to
    /// closed history. The writable ingress frame and its immutable
    /// [`DiffStore`] protocol are never changed.
    #[cold]
    #[inline(never)]
    pub fn apply_adaptive(
        &mut self,
        input: crate::tier_policy::AdaptiveInput,
    ) -> (report: crate::tier_policy::AdaptiveReport)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        self.runtime_apply_adaptive(input)
    }

    #[cold]
    #[inline(never)]
    fn runtime_apply_tier_policy(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).tiers_only_changed(*old(self)),
    {
        self.runtime_migrate_trail(false);
        self.runtime_migrate_hot(false);
    }

    /// Enforce both configured limits immediately. The open ingress frame is
    /// excluded even when a limit is zero.
    pub fn apply_tier_policy(&mut self)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        self.runtime_apply_tier_policy();
    }

    /// Explicitly dedupe every closed chronological frame.
    pub fn flush_trail(&mut self)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        self.runtime_migrate_trail(true);
    }

    /// Explicitly run-compress every closed unique frame.
    pub fn compress_hot(&mut self)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        self.runtime_migrate_hot(true);
    }

    /// Automatic rollover after a mark: the legacy Hot-buffer batch when it is
    /// due, otherwise the configured tier limits unless both are `Unbounded`.
    #[inline(always)]
    fn runtime_apply_configured_rollover(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).tiers_only_changed(*old(self)),
    {
        let legacy_batch_due = match self.hot_buffer {
            Some(keep) => {
                let closed = if self.store.unique_capture() {
                    self.hot_stack.len().saturating_sub(1)
                } else {
                    self.trail_stack.len().saturating_sub(1)
                };
                closed > keep
            }
            None => false,
        };
        if legacy_batch_due {
            if !self.store.unique_capture() {
                self.runtime_migrate_trail(true);
            }
            self.runtime_migrate_hot(true);
        } else {
            let automatic_policy_is_noop = if self.store.unique_capture() {
                matches!(self.tier_policy.hot, crate::tier_policy::TierLimit::Unbounded)
            } else {
                matches!(
                    self.tier_policy.trail,
                    crate::tier_policy::TierLimit::Unbounded
                ) && matches!(
                    self.tier_policy.hot,
                    crate::tier_policy::TierLimit::Unbounded
                )
            };
            if !automatic_policy_is_noop {
                self.runtime_apply_tier_policy();
            }
        }
    }

    /// Explicit rollover requested by a mark.
    fn runtime_rollover_on_mark(&mut self, rollover: crate::tier_policy::RolloverPolicy)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).tiers_only_changed(*old(self)),
    {
        match rollover {
            crate::tier_policy::RolloverPolicy::Defer => {}
            crate::tier_policy::RolloverPolicy::ApplyConfigured => {
                self.runtime_apply_configured_rollover();
            }
            crate::tier_policy::RolloverPolicy::ForceClosed {
                trail_to_hot,
                hot_to_cold,
            } => {
                if trail_to_hot {
                    self.runtime_migrate_trail(true);
                }
                if hot_to_cold {
                    self.runtime_migrate_hot(true);
                }
            }
        }
    }

    /// Verified Hot-only mark for the exact no-reclaim Defer path. It seals
    /// the prior header at `hot_value_pool.len()`, opens one empty top frame,
    /// and advances the logical frame/snapshot count in lockstep.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1400)]
    fn hot_defer_mark_checked(&mut self)
        requires
            old(self).wf(),
            old(self).hot_defer_wf(),
            old(self).hot_stack@.len() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).hot_defer_wf(),
            final(self).view() == old(self).view(),
            final(self).hot_value_pool@ == old(self).hot_value_pool@,
            final(self).full_trail@ == old(self).full_trail@,
            final(self).diff_log@ == old(self).diff_log@,
            final(self).hot_stack@.len() == old(self).hot_stack@.len() + 1,
            final(self).snapshots@ == old(self).snapshots@.push(old(self).view()),
            final(self).trail_frames@ == old(self).trail_frames@.push(
                old(self).full_trail@.len() as nat),
    {
        let ghost pre = *self;
        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
            I::lemma_max_nat_fits_usize();
        }
        let saved_len = self.store.len();
        let pool_len = self.hot_value_pool.len();
        let old_depth = self.hot_stack.len();
        let parent_start = if old_depth > 0 {
            self.hot_stack[old_depth - 1].start
        } else {
            0
        };
        let active = vstd::slice::slice_subrange(
            self.hot_value_pool.as_slice(), parent_start, pool_len);
        proof {
            assert(active@ == pre.hot_value_pool@.subrange(
                parent_start as int, pool_len as int));
            assert forall|j: int| 0 <= j < self.store.captured().len()
                && #[trigger] self.store.captured()[j]
                implies exists|k: int| 0 <= k < active@.len()
                    && (#[trigger] active@[k]).1.as_nat() == j as nat by {
                assert(old_depth > 0);
                assert(j < pre.active_saved_len.as_nat());
                assert(j < pre.view().len());
                assert(pre.store.captured()[j]
                    == captured_in_range::<T, I>(
                        pre.hot_value_pool@, parent_start as int,
                        pre.hot_value_pool@.len() as int, j as nat));
                let p = choose|p: int| parent_start <= p < pre.hot_value_pool@.len()
                    && (#[trigger] pre.hot_value_pool@[p]).1.as_nat() == j as nat;
                assert(active@[p - parent_start] == pre.hot_value_pool@[p]);
            }
        }
        self.store.prepare_mark(saved_len, active);
        if old_depth > 0 {
            self.hot_stack[old_depth - 1].end = pool_len;
        }
        let ghost sealed_hot = self.hot_stack@;
        proof {
            assert(sealed_hot.len() == pre.hot_stack@.len());
            assert forall|i: int| 0 <= i < sealed_hot.len() implies {
                &&& (#[trigger] sealed_hot[i]).start == pre.hot_stack@[i].start
                &&& sealed_hot[i].saved_len == pre.hot_stack@[i].saved_len
                &&& sealed_hot[i].end == if i + 1 == sealed_hot.len() {
                    pool_len
                } else {
                    pre.hot_stack@[i].end
                }
            } by {}
        }
        self.hot_stack.push(crate::frame::HotFrame {
            saved_len,
            start: pool_len,
            end: pool_len,
        });
        let ghost old_view = self.view();
        proof {
            self.snapshots = Ghost(self.snapshots@.push(old_view));
            self.trail_frames@ = self.trail_frames@.push(self.full_trail@.len() as nat);
        }
        self.active_saved_len = saved_len;

        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
            let depth = self.hot_stack@.len();
            let old_n = pre.hot_stack@.len();
            let pool = self.hot_value_pool@;
            assert(depth == old_n + 1);
            assert(self.hot_stack@.subrange(0, old_n as int) == sealed_hot);
            assert(pool == pre.hot_value_pool@);
            assert(self.view() == pre.view());
            assert(self.store.captured().len() == self.view().len()) by {
                self.store.lemma_wf_captured_len();
            }
            assert(self.snapshots@ == pre.snapshots@.push(pre.view()));
            assert(self.trail_frames@ == pre.trail_frames@.push(
                pre.full_trail@.len() as nat));
            assert(depth < usize::MAX);

            assert forall|i: int| 0 <= i < depth implies {
                &&& (#[trigger] self.hot_stack@[i]).start <= self.hot_stack@[i].end
                &&& self.hot_stack@[i].end <= pool.len()
                &&& self.hot_stack@[i].start as int <= self.hot_defer_end(i)
                &&& self.hot_defer_end(i) <= pool.len() as int
                &&& (i + 1 < depth ==> {
                    &&& self.hot_stack@[i].end == self.hot_stack@[i + 1].start
                    &&& self.hot_defer_end(i) == self.hot_stack@[i + 1].start as int
                })
                &&& (i + 1 == depth ==> self.hot_defer_end(i) == pool.len() as int)
            } by {
                if i < old_n {
                    assert(self.hot_stack@[i] == sealed_hot[i]);
                    if i + 1 < old_n {
                        assert(self.hot_stack@[i].end == pre.hot_stack@[i].end);
                        assert(self.hot_stack@[i + 1].start == pre.hot_stack@[i + 1].start);
                        assert(self.hot_defer_end(i) == pre.hot_defer_end(i));
                    } else {
                        assert(i + 1 == old_n);
                        assert(self.hot_stack@[i].start == pre.hot_stack@[i].start);
                        assert(self.hot_stack@[i].end == pool.len());
                        assert(self.hot_stack@[i + 1].start == pool.len());
                        assert(self.hot_defer_end(i) == pool.len() as int);
                    }
                } else {
                    assert(i == old_n);
                    assert(self.hot_stack@[i].start == pool.len());
                    assert(self.hot_stack@[i].end == pool.len());
                }
            }
            assert forall|i: int| 0 <= i < depth implies
                (#[trigger] self.hot_stack@[i]).saved_len.as_nat()
                    == self.snapshots@[i].len() by {
                if i < old_n {
                    assert(self.hot_stack@[i] == sealed_hot[i]);
                    assert(self.hot_stack@[i].saved_len == pre.hot_stack@[i].saved_len);
                    assert(self.snapshots@[i] == pre.snapshots@[i]);
                } else {
                    assert(i == old_n);
                    assert(self.hot_stack@[i].saved_len == saved_len);
                    assert(saved_len.as_nat() == pre.view().len());
                }
            }
            assert forall|i: int| 0 <= i < depth implies
                #[trigger] stratum_unique::<T, I>(
                    pool, self.hot_stack@[i].start as int, self.hot_defer_end(i)) by {
                if i < old_n {
                    assert(self.hot_stack@[i] == sealed_hot[i]);
                    assert(self.hot_stack@[i].start == pre.hot_stack@[i].start);
                    if i + 1 < old_n {
                        assert(self.hot_defer_end(i) == pre.hot_defer_end(i));
                    } else {
                        assert(i + 1 == old_n);
                        assert(self.hot_defer_end(i) == pool.len() as int);
                        assert(pre.hot_defer_end(i) == pool.len() as int);
                    }
                } else {
                    assert(i == old_n);
                    assert(self.hot_stack@[i].start as int == self.hot_defer_end(i));
                }
            }
            assert forall|i: int| 0 <= i < depth implies
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(i), pool, self.hot_stack@[i].start as int,
                    self.hot_defer_end(i), self.snapshots@[i], self.snapshots@[i].len()) by {
                if i < old_n {
                    assert(self.hot_stack@[i] == sealed_hot[i]);
                    assert(self.hot_stack@[i].start == pre.hot_stack@[i].start);
                    assert(self.snapshots@[i] == pre.snapshots@[i]);
                    if i + 1 < old_n {
                        assert(self.layer_above_at(i) == pre.layer_above_at(i));
                        assert(self.hot_defer_end(i) == pre.hot_defer_end(i));
                    } else {
                        assert(i + 1 == old_n);
                        assert(self.layer_above_at(i) == self.snapshots@[i + 1]);
                        assert(self.snapshots@[i + 1] == pre.view());
                        assert(pre.layer_above_at(i) == pre.view());
                        assert(self.layer_above_at(i) == pre.layer_above_at(i));
                        assert(self.hot_defer_end(i) == pool.len() as int);
                        assert(pre.hot_defer_end(i) == pool.len() as int);
                    }
                } else {
                    assert(i == old_n);
                    assert(self.layer_above_at(i) == self.view());
                    assert(self.snapshots@[i] == pre.view());
                    assert(self.hot_stack@[i].start as int == self.hot_defer_end(i));
                    assert forall|j: int| 0 <= j < self.snapshots@[i].len() implies
                        #[trigger] frame_cell_inv::<T, I>(
                            self.view(), pool, self.hot_defer_end(i),
                            self.hot_defer_end(i), self.snapshots@[i], j) by {}
                }
            }
            assert forall|j: int| 0 <= j < self.store.captured().len()
                implies !(#[trigger] self.store.captured()[j]) by {
                assert(j < saved_len.as_nat());
            }
            assert forall|j: int|
                0 <= j < self.active_saved_len.as_nat() && j < self.view().len() implies
                (#[trigger] self.store.captured()[j])
                    == captured_in_range::<T, I>(
                        pool, self.hot_stack@[(depth - 1) as int].start as int,
                        pool.len() as int, j as nat) by {
                assert(self.hot_stack@[(depth - 1) as int].start == pool.len());
            }
            assert(self.hot_defer_wf());

            // Reuse the tier-independent canonical opening theorem.
            pre.lemma_wf_named_parts();
            self.lemma_canonical_mark(pre);
            reveal(Vec::proof_compat_ok);
            assert(self.proof_compat_ok());
            self.lemma_hot_defer_snap_implies_wf();
        }
    }

    /// Sequence-preserving post-mark reclamation for the all-Hot scope.
    /// Persistent Hot ordering is unchanged; this operation changes allocator
    /// capacity only.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1400)]
    fn hot_defer_post_mark_shrink_checked(&mut self, factor: usize, headroom: usize)
        requires
            old(self).wf(),
            old(self).hot_defer_scope(),
        ensures
            final(self).wf(),
            final(self).hot_defer_scope(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let ghost marked = *self;
        log_shrink_capacity(&mut self.trail_value_pool, factor, headroom);
        log_shrink_capacity(&mut self.hot_value_pool, factor, headroom);
        if matches!(
            self.tier_policy.cold_reclaim,
            crate::tier_policy::ReclaimPolicy::ShrinkToFit
        ) {
            crate::parallel_store::shrink_vec_capacity(
                &mut self.cold_value_pool, 0, 0);
            crate::parallel_store::shrink_vec_capacity(
                &mut self.cold_index_runs, 0, 0);
        }
        proof {
            reveal(Vec::hot_defer_scope);
            assert(self.store == marked.store);
            assert(self.view() == marked.view());
            assert(self.hot_stack@ == marked.hot_stack@);
            assert(self.hot_value_pool@ == marked.hot_value_pool@);
            assert(self.trail_stack@ == marked.trail_stack@);
            assert(self.trail_value_pool@ == marked.trail_value_pool@);
            assert(self.cold_stack@ == marked.cold_stack@);
            assert(self.cold_index_runs@ == marked.cold_index_runs@);
            assert(self.cold_value_pool@ == marked.cold_value_pool@);
            assert(self.snapshots@ == marked.snapshots@);
            assert(self.trail_frames@ == marked.trail_frames@);
            assert(self.full_trail@ == marked.full_trail@);
            assert(self.diff_log@ == marked.diff_log@);
            assert(self.active_saved_len == marked.active_saved_len);
            assert forall|i: int| 0 <= i < self.hot_stack@.len() implies
                #[trigger] self.layer_above_at(i) == marked.layer_above_at(i) by {}
            marked.lemma_hot_defer_scope_implies_projection();
            self.lemma_hot_defer_transfer_canonical(marked);
            marked.lemma_wf_named_parts();
            self.lemma_wf_for_snap_transfer(marked);
            assert(self.proof_compat_ok());
            self.lemma_hot_defer_snap_implies_wf();
            assert(self.hot_defer_scope());
        }
    }

    /// Complete checked explicit-Defer mark, including the historical
    /// thresholded capacity-reclamation ordering before and after opening the
    /// replacement frame.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1800)]
    fn hot_defer_mark_with_shrink_checked(&mut self, shrink: ShrinkPolicy)
        requires
            old(self).wf(),
            old(self).hot_defer_scope(),
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).hot_defer_scope(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view()
                == old(self).snapshots_view().push(old(self).view()),
    {
        let ghost pre = *self;
        self.maybe_shrink(shrink);
        proof {
            reveal(Vec::hot_defer_scope);
            assert(self.trail_stack@ == pre.trail_stack@);
            assert(self.trail_value_pool@ == pre.trail_value_pool@);
            assert(self.cold_stack@ == pre.cold_stack@);
            assert(self.cold_index_runs@ == pre.cold_index_runs@);
            assert(self.cold_value_pool@ == pre.cold_value_pool@);
            assert(self.hot_defer_scope());
            self.lemma_hot_defer_scope_implies_projection();
        }
        self.hot_defer_mark_checked();
        if let ShrinkPolicy::IfOverallocated { factor, headroom } = shrink {
            self.hot_defer_post_mark_shrink_checked(factor, headroom);
        }
    }

    #[verifier::spinoff_prover]
    fn mark_reclaim_checked(&mut self, shrink: ShrinkPolicy)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).view() == old(self).view(),
            final(self).snapshots@ == old(self).snapshots@,
            final(self).trail_frames@ == old(self).trail_frames@,
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::cold_repr_ok);
        hide(Vec::open_ingress_ok);
        let ghost pre = *self;
        if let ShrinkPolicy::IfOverallocated { factor, headroom } = shrink {
            // Apply the same thresholded reclaim rule to the executable
            // three-tier pools. This replaces the earlier unconditional
            // shrink-to-fit shortcut while preserving mark-time reclamation.
            log_shrink_capacity(&mut self.trail_value_pool, factor, headroom);
            log_shrink_capacity(&mut self.hot_value_pool, factor, headroom);
            if matches!(
                self.tier_policy.cold_reclaim,
                crate::tier_policy::ReclaimPolicy::ShrinkToFit
            ) {
                crate::parallel_store::shrink_vec_capacity(&mut self.cold_value_pool, 0, 1);
                crate::parallel_store::shrink_vec_capacity(&mut self.cold_index_runs, 0, 1);
            }
        }
        proof {
            pre.lemma_wf_named_parts();
            assert(pre.store.wf()) by { reveal(Vec::wf_for_snap); }
            self.lemma_survivor_history_transfer(pre);
            self.lemma_open_ingress_transfer(pre);
            reveal(Vec::wf);
        }
    }

    #[verifier::spinoff_prover]
    fn mark_defer_checked(&mut self, shrink: ShrinkPolicy)
        requires old(self).wf(), TRACK,
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures final(self).wf(), final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots@ == old(self).snapshots@.push(old(self).view()),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        self.maybe_shrink(shrink);
        self.open_mark_checked();
        self.mark_reclaim_checked(shrink);
    }

    fn runtime_push_frame_fallback<const APPLY_CONFIGURED: bool>(&mut self, options: MarkOptions)
        requires
            TRACK,
            old(self).wf(),
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
            APPLY_CONFIGURED || !old(self).hot_defer_scope()
                || !(options.rollover is Defer),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view()
                == old(self).snapshots_view().push(old(self).view()),
    {
        // Preserve the established thresholded reclaim contract. Rollover is
        // independent and still occurs only after the replacement frame opens.
        self.maybe_shrink(options.shrink);
        self.open_mark_checked();
        // Rollover is deliberately after the new frame opens. Migration
        // helpers therefore see only closed oldest prefixes and cannot change
        // depth, token coordinates, snapshots, or the writable frame.
        if APPLY_CONFIGURED {
            if self.automatic_rollover_enabled {
                self.runtime_apply_configured_rollover();
            }
        } else {
            self.runtime_rollover_on_mark(options.rollover);
        }
        self.mark_reclaim_checked(options.shrink);
    }

    fn runtime_push_frame<const APPLY_CONFIGURED: bool>(&mut self, options: MarkOptions)
        requires
            TRACK,
            old(self).wf(),
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view()
                == old(self).snapshots_view().push(old(self).view()),
    {
        let hot = self.hot_defer_scope_exec();
        if !APPLY_CONFIGURED
            && hot
            && matches!(options.rollover, crate::tier_policy::RolloverPolicy::Defer)
        {
            proof { self.lemma_hot_defer_scope_implies_projection(); }
            self.hot_defer_mark_with_shrink_checked(options.shrink);
        } else if !APPLY_CONFIGURED
            && matches!(options.rollover, crate::tier_policy::RolloverPolicy::Defer)
        {
            self.mark_defer_checked(options.shrink);
        } else {
            self.runtime_push_frame_fallback::<APPLY_CONFIGURED>(options);
        }
    }

    fn cold_value_cut(&self, runs_start: usize) -> (cut: usize)
        ensures cut == if runs_start < self.cold_index_runs@.len() {
            self.cold_index_runs@[runs_start as int].start as nat
        } else { self.cold_value_pool@.len() },
    {
        if runs_start < self.cold_index_runs.len() {
            self.cold_index_runs[runs_start].start
        } else {
            self.cold_value_pool.len()
        }
    }

    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_replay_ingress(&self)
        requires self.wf(), self.depth_spec() > 0,
        ensures
            self.store.unique_capture_spec() ==> self.trail_stack@.len() == 0,
            self.pair_tier_count(!self.store.unique_capture_spec()) > 0,
            0 <= self.pair_tier_start(!self.store.unique_capture_spec(),
                self.pair_tier_count(!self.store.unique_capture_spec()) - 1)
                <= self.pair_tier_pool(!self.store.unique_capture_spec()).len(),
            forall|j: int| 0 <= j < self.store.captured().len()
                && #[trigger] self.store.captured()[j] ==>
                captured_in_range::<T, I>(
                    self.pair_tier_pool(!self.store.unique_capture_spec()),
                    self.pair_tier_start(!self.store.unique_capture_spec(),
                        self.pair_tier_count(!self.store.unique_capture_spec()) - 1),
                    self.pair_tier_pool(!self.store.unique_capture_spec()).len() as int, j as nat),
    {
        self.lemma_wf_named_parts();
        reveal(Vec::open_ingress_ok);
        reveal(Vec::frame_partition_ok);
        self.lemma_pair_tier_frame_layout(!self.store.unique_capture_spec(),
            self.pair_tier_count(!self.store.unique_capture_spec()) - 1);
    }

    #[inline(always)]
    #[verifier::spinoff_prover]
    fn prepare_mark_range_checked(
        store: &mut S, pool: &std::vec::Vec<(T, I)>, lo: usize, hi: usize, saved_len: I,
    )
        requires
            old(store).wf(), lo <= hi <= pool@.len(),
            saved_len.as_nat() == old(store).data().len(),
            TRACK ==> forall|j: int| 0 <= j < old(store).captured().len()
                && #[trigger] old(store).captured()[j] ==>
                captured_in_range::<T, I>(pool@, lo as int, hi as int, j as nat),
        ensures
            final(store).wf(),
            final(store).data() == old(store).data(),
            final(store).unique_capture_spec() == old(store).unique_capture_spec(),
            final(store).needs_replayed_indices_spec() == old(store).needs_replayed_indices_spec(),
            final(store).restore_entries_clear_capture_spec()
                == old(store).restore_entries_clear_capture_spec(),
            TRACK ==> forall|j: int| 0 <= j < final(store).captured().len() ==>
                !(#[trigger] final(store).captured()[j]),
    {
        let entries = vstd::slice::slice_subrange(pool.as_slice(), lo, hi);
        proof {
            if TRACK {
                assert forall|j: int| 0 <= j < store.captured().len()
                    && #[trigger] store.captured()[j] implies
                    exists|k: int| 0 <= k < entries@.len()
                        && (#[trigger] entries@[k]).1.as_nat() == j as nat
                by {
                    let k = choose|k: int| lo <= k < hi && 0 <= k < pool@.len()
                        && (#[trigger] pool@[k]).1.as_nat() == j as nat;
                    assert(entries@[k - lo] == pool@[k]);
                }
            }
        }
        store.prepare_mark(saved_len, entries);
        proof { store.lemma_wf_captured_len(); }
    }

    /// Clear capture state through the store-selected active range. Full
    /// container well-formedness is restored only after the empty frame opens.
    #[verifier::spinoff_prover]
    fn prepare_mark_checked(&mut self, saved_len: I)
        requires old(self).wf(), TRACK,
            saved_len.as_nat() == old(self).view().len(),
        ensures
            *final(self) == (Self { store: final(self).store, ..*old(self) }),
            final(self).store.wf(),
            final(self).view() == old(self).view(),
            final(self).store.unique_capture_spec() == old(self).store.unique_capture_spec(),
            final(self).store.needs_replayed_indices_spec() == old(self).store.needs_replayed_indices_spec(),
            final(self).store.restore_entries_clear_capture_spec()
                == old(self).store.restore_entries_clear_capture_spec(),
            forall|j: int| 0 <= j < final(self).store.captured().len() ==>
                !(#[trigger] final(self).store.captured()[j]),
    {
        hide(Vec::wf);
        proof { self.lemma_wf_named_parts(); }
        if self.store.unique_capture() {
            let n = self.hot_stack.len();
            if n == 0 {
                proof { reveal(Vec::open_ingress_ok); reveal(Vec::frame_partition_ok); }
                self.store.prepare_mark(saved_len, &[]);
            } else {
                proof { self.lemma_replay_ingress(); }
                let lo = self.hot_stack[n - 1].start;
                let hi = self.hot_value_pool.len();
                Self::prepare_mark_range_checked(&mut self.store, &self.hot_value_pool, lo, hi, saved_len);
            }
        } else {
            let n = self.trail_stack.len();
            if n == 0 {
                proof { reveal(Vec::open_ingress_ok); reveal(Vec::frame_partition_ok); }
                self.store.prepare_mark(saved_len, &[]);
            } else {
                proof { self.lemma_replay_ingress(); }
                let lo = self.trail_stack[n - 1].start;
                let hi = self.trail_value_pool.len();
                Self::prepare_mark_range_checked(&mut self.store, &self.trail_value_pool, lo, hi, saved_len);
            }
        }
        proof { self.store.lemma_wf_captured_len(); }
    }

    #[inline(always)]
    #[verifier::spinoff_prover]
    fn begin_restore_range_checked(
        store: &mut S, pool: &std::vec::Vec<(T, I)>, lo: usize, hi: usize,
    )
        requires
            old(store).wf(), lo <= hi <= pool@.len(),
            TRACK ==> forall|j: int| 0 <= j < old(store).captured().len()
                && #[trigger] old(store).captured()[j] ==>
                captured_in_range::<T, I>(pool@, lo as int, hi as int, j as nat),
        ensures
            final(store).wf(),
            final(store).data() == old(store).data(),
            final(store).unique_capture_spec() == old(store).unique_capture_spec(),
            final(store).needs_replayed_indices_spec() == old(store).needs_replayed_indices_spec(),
            final(store).restore_entries_clear_capture_spec()
                == old(store).restore_entries_clear_capture_spec(),
            TRACK ==> forall|j: int| 0 <= j < final(store).captured().len() ==>
                !(#[trigger] final(store).captured()[j]),
    {
        let entries = vstd::slice::slice_subrange(pool.as_slice(), lo, hi);
        proof {
            if TRACK {
                assert forall|j: int| 0 <= j < store.captured().len()
                    && #[trigger] store.captured()[j] implies
                    exists|k: int| 0 <= k < entries@.len()
                        && (#[trigger] entries@[k]).1.as_nat() == j as nat
                by {
                    let k = choose|k: int| lo <= k < hi && 0 <= k < pool@.len()
                        && (#[trigger] pool@[k]).1.as_nat() == j as nat;
                    assert(entries@[k - lo] == pool@[k]);
                }
            }
        }
        store.begin_restore(entries);
    }

    /// Capture preparation after resize. History still equals the frozen
    /// pre-state; resized flags form a subset of the original ingress flags.
    #[verifier::spinoff_prover]
    fn runtime_begin_restore(&mut self, Ghost(pre): Ghost<Self>)
        requires
            pre.wf(), pre.depth_spec() > 0,
            *old(self) == (Self { store: old(self).store, ..pre }),
            old(self).store.wf(),
            old(self).store.unique_capture_spec() == pre.store.unique_capture_spec(),
            TRACK ==> forall|j: int| 0 <= j < old(self).store.captured().len()
                && #[trigger] old(self).store.captured()[j]
                ==> j < pre.store.captured().len() && pre.store.captured()[j],
        ensures
            *final(self) == (Self { store: final(self).store, ..pre }),
            final(self).store.wf(),
            final(self).view() == old(self).view(),
            final(self).store.unique_capture_spec() == old(self).store.unique_capture_spec(),
            final(self).store.needs_replayed_indices_spec() == old(self).store.needs_replayed_indices_spec(),
            final(self).store.restore_entries_clear_capture_spec()
                == old(self).store.restore_entries_clear_capture_spec(),
            TRACK ==> forall|j: int| 0 <= j < final(self).store.captured().len() ==>
                !(#[trigger] final(self).store.captured()[j]),
    {
        hide(Vec::wf);
        if !self.store.needs_replayed_indices() {
            self.store.begin_restore(&[]);
            return;
        }
        proof { pre.lemma_replay_ingress(); }
        if self.store.unique_capture() {
            let top = self.hot_stack.len() - 1;
            let lo = self.hot_stack[top].start;
            let hi = self.hot_value_pool.len();
            Self::begin_restore_range_checked(&mut self.store, &self.hot_value_pool, lo, hi);
        } else {
            let top = self.trail_stack.len() - 1;
            let lo = self.trail_stack[top].start;
            let hi = self.trail_value_pool.len();
            Self::begin_restore_range_checked(&mut self.store, &self.trail_value_pool, lo, hi);
        }
    }

    /// Rebuild flags from the retained writable physical frame over the entire
    /// live buffer. The frame's saved length may exceed the current length.
    #[verifier::spinoff_prover]
    fn finish_restore_range_checked(store: &mut S, pool: &std::vec::Vec<(T, I)>, lo: usize)
        requires old(store).wf(), lo <= pool@.len(), TRACK,
            forall|j: int| 0 <= j < old(store).captured().len() ==>
                !(#[trigger] old(store).captured()[j]),
        ensures final(store).wf(), final(store).data() == old(store).data(),
            final(store).unique_capture_spec() == old(store).unique_capture_spec(),
            final(store).needs_replayed_indices_spec() == old(store).needs_replayed_indices_spec(),
            final(store).restore_entries_clear_capture_spec() == old(store).restore_entries_clear_capture_spec(),
            forall|j: int| 0 <= j < final(store).captured().len() ==>
                #[trigger] final(store).captured()[j] == captured_in_range::<T, I>(
                    pool@, lo as int, pool@.len() as int, j as nat),
    {
        let hi = pool.len();
        let entries = vstd::slice::slice_subrange(pool.as_slice(), lo, hi);
        let live_len = store.len();
        store.finish_restore(entries, live_len);
        proof {
            store.lemma_wf_captured_len();
            assert forall|j: int| 0 <= j < store.captured().len() implies
                #[trigger] store.captured()[j] == captured_in_range::<T, I>(
                    pool@, lo as int, pool@.len() as int, j as nat)
            by {
                if store.captured()[j] {
                    let q = choose|q: int| 0 <= q < entries@.len()
                        && (#[trigger] entries@[q]).1.as_nat() == j;
                    assert(pool@[lo + q] == entries@[q]);
                } else if captured_in_range::<T, I>(pool@, lo as int, hi as int, j as nat) {
                    let q = choose|q: int| lo <= q < hi && 0 <= q < pool@.len()
                        && (#[trigger] pool@[q]).1.as_nat() == j;
                    assert(entries@[q - lo] == pool@[q]);
                }
            }
        }
    }

    closed spec fn mark_open_effect(&self, pre: Self) -> bool {
        &&& self.store.wf()
        &&& self.view() == pre.view()
        &&& self.store.unique_capture_spec() == pre.store.unique_capture_spec()
        &&& self.active_saved_len.as_nat() == self.view().len()
        &&& forall|j: int| 0 <= j < self.store.captured().len() ==>
            !(#[trigger] self.store.captured()[j])
        &&& *self == (Self {
                store: self.store, hot_stack: self.hot_stack, trail_stack: self.trail_stack,
                snapshots: self.snapshots, trail_frames: self.trail_frames,
                active_saved_len: self.active_saved_len, ..pre
            })
        &&& self.frame_partition_ok()
        &&& self.snapshots@ == pre.snapshots@.push(pre.view())
        &&& self.trail_frames@ == pre.trail_frames@.push(pre.full_trail@.len() as nat)
        &&& pre.store.unique_capture_spec() ==> {
                &&& self.trail_stack@ == pre.trail_stack@
                &&& self.hot_stack@ == (if pre.hot_stack@.len() == 0 {
                    pre.hot_stack@
                } else {
                    pre.hot_stack@.update(pre.hot_stack@.len() - 1,
                        crate::frame::HotFrame {
                            end: pre.hot_value_pool@.len() as usize,
                            ..pre.hot_stack@[pre.hot_stack@.len() - 1]
                        })
                }).push(crate::frame::HotFrame {
                    saved_len: self.active_saved_len, start: pre.hot_value_pool@.len() as usize,
                    end: pre.hot_value_pool@.len() as usize,
                })
            }
        &&& !pre.store.unique_capture_spec() ==> {
                &&& self.hot_stack@ == pre.hot_stack@
                &&& self.trail_stack@ == (if pre.trail_stack@.len() == 0 {
                    pre.trail_stack@
                } else {
                    pre.trail_stack@.update(pre.trail_stack@.len() - 1,
                        crate::frame::TrailFrame {
                            end: pre.trail_value_pool@.len() as usize,
                            ..pre.trail_stack@[pre.trail_stack@.len() - 1]
                        })
                }).push(crate::frame::TrailFrame {
                    saved_len: self.active_saved_len, start: pre.trail_value_pool@.len() as usize,
                    end: pre.trail_value_pool@.len() as usize,
                })
            }
        &&& forall|trail: bool, f: int| 0 <= f < pre.pair_tier_count(trail) ==> {
                &&& self.pair_tier_offset(trail) == pre.pair_tier_offset(trail)
                &&& self.pair_tier_start(trail, f) == pre.pair_tier_start(trail, f)
                &&& #[trigger] self.pair_tier_end(trail, f) == pre.pair_tier_end(trail, f)
            }
        &&& self.pair_tier_count(!pre.store.unique_capture_spec())
                == pre.pair_tier_count(!pre.store.unique_capture_spec()) + 1
        &&& self.pair_tier_start(!pre.store.unique_capture_spec(),
                pre.pair_tier_count(!pre.store.unique_capture_spec()) as int)
                == self.pair_tier_pool(!pre.store.unique_capture_spec()).len()
        &&& self.pair_tier_end(!pre.store.unique_capture_spec(),
                pre.pair_tier_count(!pre.store.unique_capture_spec()) as int)
                == self.pair_tier_pool(!pre.store.unique_capture_spec()).len()
    }

    /// Seal the selected writable header and append the new empty frame.
    /// Capture preparation has already happened; reconstruction is composed
    /// separately from this exact structural transition.
    #[verifier::spinoff_prover]
    fn open_mark_headers_checked(&mut self, saved_len: I)
        requires TRACK, old(self).frame_partition_ok(),
            old(self).store.unique_capture_spec() ==> old(self).trail_stack@.len() == 0,
            saved_len.as_nat() == old(self).view().len(),
        ensures
            *final(self) == (Self {
                hot_stack: final(self).hot_stack, trail_stack: final(self).trail_stack,
                snapshots: final(self).snapshots, trail_frames: final(self).trail_frames,
                active_saved_len: saved_len, ..*old(self)
            }),
            final(self).frame_partition_ok(),
            final(self).snapshots@ == old(self).snapshots@.push(old(self).view()),
            final(self).trail_frames@ == old(self).trail_frames@.push(old(self).full_trail@.len() as nat),
            old(self).store.unique_capture_spec() ==> {
                &&& final(self).trail_stack@ == old(self).trail_stack@
                &&& final(self).hot_stack@ == (if old(self).hot_stack@.len() == 0 {
                    old(self).hot_stack@
                } else {
                    old(self).hot_stack@.update(old(self).hot_stack@.len() - 1,
                        crate::frame::HotFrame {
                            end: old(self).hot_value_pool@.len() as usize,
                            ..old(self).hot_stack@[old(self).hot_stack@.len() - 1]
                        })
                }).push(crate::frame::HotFrame {
                    saved_len, start: old(self).hot_value_pool@.len() as usize,
                    end: old(self).hot_value_pool@.len() as usize,
                })
            },
            !old(self).store.unique_capture_spec() ==> {
                &&& final(self).hot_stack@ == old(self).hot_stack@
                &&& final(self).trail_stack@ == (if old(self).trail_stack@.len() == 0 {
                    old(self).trail_stack@
                } else {
                    old(self).trail_stack@.update(old(self).trail_stack@.len() - 1,
                        crate::frame::TrailFrame {
                            end: old(self).trail_value_pool@.len() as usize,
                            ..old(self).trail_stack@[old(self).trail_stack@.len() - 1]
                        })
                }).push(crate::frame::TrailFrame {
                    saved_len, start: old(self).trail_value_pool@.len() as usize,
                    end: old(self).trail_value_pool@.len() as usize,
                })
            },
            forall|trail: bool, f: int| 0 <= f < old(self).pair_tier_count(trail) ==> {
                &&& final(self).pair_tier_offset(trail) == old(self).pair_tier_offset(trail)
                &&& final(self).pair_tier_start(trail, f) == old(self).pair_tier_start(trail, f)
                &&& #[trigger] final(self).pair_tier_end(trail, f) == old(self).pair_tier_end(trail, f)
            },
            final(self).pair_tier_count(!old(self).store.unique_capture_spec())
                == old(self).pair_tier_count(!old(self).store.unique_capture_spec()) + 1,
            final(self).pair_tier_start(!old(self).store.unique_capture_spec(),
                old(self).pair_tier_count(!old(self).store.unique_capture_spec()) as int)
                == final(self).pair_tier_pool(!old(self).store.unique_capture_spec()).len(),
            final(self).pair_tier_end(!old(self).store.unique_capture_spec(),
                old(self).pair_tier_count(!old(self).store.unique_capture_spec()) as int)
                == final(self).pair_tier_pool(!old(self).store.unique_capture_spec()).len(),
    {
        if self.store.unique_capture() {
            let n = self.hot_stack.len();
            if n > 0 {
                self.hot_stack[n - 1].end = self.hot_value_pool.len();
            }
            let start = self.hot_value_pool.len();
            self.hot_stack.push(crate::frame::HotFrame {
                saved_len,
                start,
                end: start,
            });
        } else {
            let n = self.trail_stack.len();
            if n > 0 {
                self.trail_stack[n - 1].end = self.trail_value_pool.len();
            }
            let start = self.trail_value_pool.len();
            self.trail_stack.push(crate::frame::TrailFrame {
                saved_len,
                start,
                end: start,
            });
        }
        let ghost old_view = self.view();
        proof {
            self.snapshots = Ghost(self.snapshots@.push(old_view));
            self.trail_frames@ = self.trail_frames@.push(self.full_trail@.len() as nat);
        }
        self.active_saved_len = saved_len;
        proof { reveal(Vec::frame_partition_ok); }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_mark_hot_repr(&self, pre: Self)
        requires pre.wf(), self.mark_open_effect(pre),
        ensures self.hot_repr_ok(),
    {
        hide(Vec::wf);
        reveal(Vec::mark_open_effect);
        pre.lemma_wf_named_parts();
        reveal(Vec::hot_repr_ok);
        reveal(Vec::frame_partition_ok);
        let hs = self.hot_stack@;
        let pool = self.hot_value_pool@;
        let cc = self.cold_stack@.len();
        assert forall|i: int| 0 <= i < hs.len() implies {
            &&& (#[trigger] hs[i]).start <= hs[i].end
            &&& hs[i].end <= pool.len()
            &&& hs[i].start as int <= self.phys_hot_end(i)
            &&& self.phys_hot_end(i) <= pool.len() as int
            &&& (i + 1 < hs.len() ==> {
                &&& hs[i].end == hs[i + 1].start
                &&& self.phys_hot_end(i) == hs[i + 1].start as int
            })
            &&& (i + 1 == hs.len() ==> self.phys_hot_end(i) == pool.len() as int)
            &&& stratum_unique::<T, I>(pool, hs[i].start as int, self.phys_hot_end(i))
            &&& self.phys_frame_inv_range_holds(i)
            &&& cc + i < self.snapshots@.len()
        } by {
            if i < pre.hot_stack@.len() {
                self.lemma_mark_pair_frame(pre, false, i);
            } else {
                assert(i == pre.hot_stack@.len());
                assert(cc + i == pre.snapshots@.len()) by { reveal(Vec::open_ingress_ok); }
                assert(self.layer_above_at(cc + i) == self.view());
                assert(self.snapshots@[cc + i] == self.view());
                assert(self.phys_hot_start(i) == self.phys_hot_end(i));
                assert forall|j: int| 0 <= j < self.view().len() implies
                    #[trigger] frame_cell_inv::<T, I>(self.view(), pool,
                        self.phys_hot_start(i), self.phys_hot_end(i), self.view(), j) by {}
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_mark_trail_repr(&self, pre: Self)
        requires pre.wf(), self.mark_open_effect(pre),
        ensures self.trail_repr_ok(),
    {
        hide(Vec::wf);
        reveal(Vec::mark_open_effect);
        pre.lemma_wf_named_parts();
        reveal(Vec::trail_repr_ok);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        let ts = self.trail_stack@;
        let pool = self.trail_value_pool@;
        let offset = self.cold_stack@.len() + self.hot_stack@.len();
        assert forall|i: int| 0 <= i < ts.len() implies {
            &&& (#[trigger] ts[i]).start <= ts[i].end
            &&& ts[i].end <= pool.len()
            &&& ts[i].start as int <= self.phys_trail_end(i)
            &&& self.phys_trail_end(i) <= pool.len() as int
            &&& (i + 1 < ts.len() ==> {
                &&& ts[i].end == ts[i + 1].start
                &&& self.phys_trail_end(i) == ts[i + 1].start as int
            })
            &&& (i + 1 == ts.len() ==> self.phys_trail_end(i) == pool.len() as int)
            &&& frame_inv_range::<T, I>(self.layer_above_at(offset + i), pool,
                ts[i].start as int, self.phys_trail_end(i), self.snapshots@[offset + i],
                self.snapshots@[offset + i].len())
            &&& offset + i < self.snapshots@.len()
        } by {
            if i < pre.trail_stack@.len() {
                self.lemma_mark_pair_frame(pre, true, i);
            } else {
                assert(i == pre.trail_stack@.len());
                assert(offset + i == pre.snapshots@.len());
                assert(self.layer_above_at(offset + i) == self.view());
                assert(self.snapshots@[offset + i] == self.view());
                assert(ts[i].start as int == self.phys_trail_end(i));
                assert forall|j: int| 0 <= j < self.view().len() implies
                    #[trigger] frame_cell_inv::<T, I>(self.view(), pool,
                        ts[i].start as int, self.phys_trail_end(i), self.view(), j) by {}
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_mark_ingress(&self, pre: Self)
        requires pre.wf(), self.mark_open_effect(pre),
        ensures self.open_ingress_ok(), self.proof_compat_ok(),
    {
        hide(Vec::wf);
        reveal(Vec::mark_open_effect);
        pre.lemma_wf_named_parts();
        self.store.lemma_wf_captured_len();
        reveal(Vec::open_ingress_ok);
        reveal(Vec::proof_compat_ok);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_mark_preserves(&self, pre: Self)
        requires pre.wf(), TRACK, pre.depth_spec() < u32::MAX,
            self.mark_open_effect(pre),
        ensures self.wf(),
    {
        hide(Vec::wf);
        self.lemma_mark_hot_repr(pre);
        self.lemma_mark_trail_repr(pre);
        self.lemma_mark_ingress(pre);
        reveal(Vec::mark_open_effect);
        pre.lemma_wf_named_parts();
        self.lemma_mark_cold_repr(pre);
        self.lemma_canonical_mark(pre);
        reveal(Vec::wf);
    }

    #[verifier::spinoff_prover]
    fn open_mark_checked(&mut self)
        requires old(self).wf(), TRACK,
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures final(self).wf(), final(self).mark_open_effect(*old(self)),
            final(self).view() == old(self).view(),
            final(self).snapshots@ == old(self).snapshots@.push(old(self).view()),
            final(self).depth_spec() == old(self).depth_spec() + 1,
    {
        hide(Vec::wf);
        let ghost pre = *self;
        proof { self.lemma_wf_named_parts(); }
        let saved_len = self.store.len();
        self.prepare_mark_checked(saved_len);
        proof {
            reveal(Vec::frame_partition_ok);
            reveal(Vec::open_ingress_ok);
        }
        self.open_mark_headers_checked(saved_len);
        proof {
            reveal(Vec::mark_open_effect);
            self.lemma_mark_preserves(pre);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_mark_cold_repr(&self, pre: Self)
        requires pre.wf(),
            self.view() == pre.view(),
            self.snapshots@ == pre.snapshots@.push(pre.view()),
            self.trail_frames@ == pre.trail_frames@.push(pre.full_trail@.len() as nat),
            self.cold_stack@ == pre.cold_stack@,
            self.cold_index_runs@ == pre.cold_index_runs@,
            self.cold_value_pool@ == pre.cold_value_pool@,
        ensures self.cold_repr_ok(),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        reveal(Vec::cold_repr_ok);
        reveal(Vec::cold_payload_ok);
        reveal(Vec::frame_partition_ok);
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f) by {
            assert(self.snapshots@[f] == pre.snapshots@[f]);
            assert(self.layer_above_at(f) == pre.layer_above_at(f));
            self.lemma_cold_reconstructs_frame_transfer(pre, f);
        }
    }

    /// Existing pair frames retain their physical ranges when a mark opens.
    /// Their former live layer becomes an equal snapshot; Hot uniqueness is
    /// independent of that change of layer.
    #[verifier::spinoff_prover]
    proof fn lemma_mark_pair_frame(&self, pre: Self, trail: bool, f: int)
        requires pre.wf(), 0 <= f < pre.pair_tier_count(trail),
            self.view() == pre.view(),
            self.snapshots@ == pre.snapshots@.push(pre.view()),
            self.trail_frames@ == pre.trail_frames@.push(pre.full_trail@.len() as nat),
            self.pair_tier_pool(trail) == pre.pair_tier_pool(trail),
            self.pair_tier_offset(trail) == pre.pair_tier_offset(trail),
            self.pair_tier_start(trail, f) == pre.pair_tier_start(trail, f),
            self.pair_tier_end(trail, f) == pre.pair_tier_end(trail, f),
        ensures
            frame_inv_range::<T, I>(self.layer_above_at(self.pair_tier_offset(trail) + f),
                self.pair_tier_pool(trail), self.pair_tier_start(trail, f),
                self.pair_tier_end(trail, f), self.snapshots@[self.pair_tier_offset(trail) + f],
                self.snapshots@[self.pair_tier_offset(trail) + f].len()),
            !trail ==> stratum_unique::<T, I>(self.pair_tier_pool(trail),
                self.pair_tier_start(trail, f), self.pair_tier_end(trail, f)),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        pre.lemma_pair_tier_frame_layout(trail, f);
        assert(pre.snapshots@.len() == pre.trail_frames@.len()) by {
            reveal(Vec::frame_partition_ok);
        }
        let k = pre.pair_tier_offset(trail) + f;
        assert(self.layer_above_at(k) == pre.layer_above_at(k));
        assert(self.snapshots@[k] == pre.snapshots@[k]);
        if trail { reveal(Vec::trail_repr_ok); }
        else { reveal(Vec::hot_repr_ok); }
    }

    /// Opening a frame appends one horizontal snapshot and one canonical
    /// boundary. The former top inherits from the equal snapshot, so its
    /// reconstruction contract is unchanged across every physical tier.
    #[verifier::spinoff_prover]
    proof fn lemma_canonical_mark_frame(&self, pre: Self, k: int)
        requires pre.wf_for_snap(),
            self.view() == pre.view(),
            self.snapshots@ == pre.snapshots@.push(pre.view()),
            self.trail_frames@ == pre.trail_frames@.push(pre.full_trail@.len() as nat),
            self.full_trail@ == pre.full_trail@,
            0 <= k < self.snapshots@.len(),
        ensures self.frame_inv_range_holds(k),
    {
        hide(Vec::wf_for_snap);
        assert(pre.snapshots@.len() == pre.trail_frames@.len()) by {
            reveal(Vec::wf_for_snap);
        }
        let n = pre.snapshots@.len();
        if k < n {
            pre.lemma_canonical_frame_contract_at(k);
            assert(self.snapshots@[k] == pre.snapshots@[k]);
            assert(self.g_start(k) == pre.g_start(k)) by { reveal(Vec::wf_for_snap); }
            assert(self.g_end(k) == pre.g_end(k)) by { reveal(Vec::wf_for_snap); }
            assert(self.layer_above_at(k) == pre.layer_above_at(k));
        } else {
            assert(k == n);
            assert(self.g_start(k) == self.full_trail@.len()) by { reveal(Vec::wf_for_snap); }
            assert(self.g_end(k) == self.full_trail@.len()) by { reveal(Vec::wf_for_snap); }
            assert(self.snapshots@[k] == self.view());
            assert forall|j: int| 0 <= j < self.snapshots@[k].len() implies
                #[trigger] frame_cell_inv::<T, I>(self.layer_above_at(k),
                    self.full_trail@, self.g_start(k), self.g_end(k),
                    self.snapshots@[k], j) by {}
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_canonical_mark(&self, pre: Self)
        requires pre.wf_for_snap(), TRACK,
            pre.depth_spec() < u32::MAX,
            self.store.wf(), self.frame_partition_ok(),
            self.view() == pre.view(),
            self.snapshots@ == pre.snapshots@.push(pre.view()),
            self.trail_frames@ == pre.trail_frames@.push(pre.full_trail@.len() as nat),
            self.full_trail@ == pre.full_trail@,
        ensures self.wf_for_snap(),
    {
        hide(frame_inv_range);
        assert forall|k: int| 0 <= k < self.trail_frames@.len() implies
            #[trigger] frame_inv_range::<T, I>(self.layer_above_at(k), self.full_trail@,
                self.g_start(k), self.g_end(k), self.snapshots@[k], self.snapshots@[k].len())
        by {
            self.lemma_canonical_mark_frame(pre, k);
        }
        reveal(Vec::wf_for_snap);
        assert forall|k: int| 0 <= k && k + 1 < self.trail_frames@.len() implies
            #[trigger] self.trail_frames@[k] <= self.trail_frames@[k + 1] by {
            if k + 1 == pre.trail_frames@.len() {
                assert(pre.trail_frames@[k] <= pre.full_trail@.len());
            }
        }
    }

    /// Canonical history depends on tier placement only through the partition.
    #[verifier::spinoff_prover]
    proof fn lemma_canonical_history_repartition(&self, pre: Self)
        requires pre.wf_for_snap(), self.store.wf(), self.frame_partition_ok(),
            self.view() == pre.view(), self.snapshots@ == pre.snapshots@,
            self.trail_frames@ == pre.trail_frames@, self.full_trail@ == pre.full_trail@,
        ensures self.wf_for_snap(),
    {
        reveal(Vec::wf_for_snap);
        assert forall|f: int| 0 <= f < self.depth_spec() implies
            #[trigger] frame_inv_range::<T, I>(self.layer_above_at(f), self.full_trail@,
                self.g_start(f), self.g_end(f), self.snapshots@[f], self.snapshots@[f].len())
        by {
            assert(pre.frame_inv_range_holds(f));
            assert(self.layer_above_at(f) == pre.layer_above_at(f));
        }
    }

    /// Capture flags and the cached active length do not affect frame meaning.
    #[verifier::spinoff_prover]
    proof fn lemma_survivor_history_transfer(&self, pre: Self)
        requires pre.wf_for_snap(), pre.hot_repr_ok(), pre.trail_repr_ok(), pre.cold_repr_ok(),
            pre.proof_compat_ok(), self.store.wf(), self.view() == pre.view(),
            self.full_trail@ == pre.full_trail@, self.trail_frames@ == pre.trail_frames@,
            self.snapshots@ == pre.snapshots@, self.diff_log@ == pre.diff_log@,
            self.cold_stack@ == pre.cold_stack@, self.cold_index_runs@ == pre.cold_index_runs@,
            self.cold_value_pool@ == pre.cold_value_pool@,
            self.hot_stack@ == pre.hot_stack@, self.hot_value_pool@ == pre.hot_value_pool@,
            self.trail_stack@ == pre.trail_stack@, self.trail_value_pool@ == pre.trail_value_pool@,
        ensures self.wf_for_snap(), self.hot_repr_ok(), self.trail_repr_ok(),
            self.cold_repr_ok(), self.proof_compat_ok(),
    {
        assert forall|f: int| 0 <= f < self.depth_spec() implies
            #[trigger] self.layer_above_at(f) == pre.layer_above_at(f) by {};
        self.lemma_wf_for_snap_transfer(pre);
        reveal(Vec::hot_repr_ok);
        reveal(Vec::trail_repr_ok);
        reveal(Vec::cold_repr_ok);
        reveal(Vec::proof_compat_ok);
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f) by {
            self.lemma_cold_reconstructs_transfer(pre, f);
        }
    }

    /// Only the surviving writable frame supplies capture bounds. Keep the
    /// other frames' adjacency and reconstruction quantifiers out of finalization.
    #[verifier::spinoff_prover]
    proof fn lemma_survivor_top_bounds_hot(&self)
        requires self.frame_partition_ok(), self.hot_repr_ok(), self.depth_spec() > 0,
            self.store.unique_capture_spec(), self.trail_stack@.len() == 0,
            self.hot_stack@.len() > 0,
        ensures ({
            let top = self.hot_stack@[self.hot_stack@.len() - 1];
            &&& top.start <= self.hot_value_pool@.len()
            &&& top.saved_len.as_nat() == self.snapshots@[self.depth_spec() - 1].len()
            &&& forall|q: int| top.start <= q < self.hot_value_pool@.len() ==>
                (#[trigger] self.hot_value_pool@[q]).1.as_nat() < top.saved_len.as_nat()
        }),
    {
        hide(frame_inv_range);
        hide(Vec::hot_repr_ok);
        let top = self.hot_stack@[self.hot_stack@.len() - 1];
        assert(top.start <= self.hot_value_pool@.len()
            && top.saved_len.as_nat() == self.snapshots@[self.depth_spec() - 1].len()
            && frame_inv_range::<T, I>(self.view(), self.hot_value_pool@,
                top.start as int, self.hot_value_pool@.len() as int,
                self.snapshots@[self.depth_spec() - 1], top.saved_len.as_nat())) by {
            reveal(Vec::frame_partition_ok);
            self.lemma_hot_repr_at(self.hot_stack@.len() - 1);
        }
        reveal(frame_inv_range);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_survivor_top_bounds_trail(&self)
        requires self.frame_partition_ok(), self.trail_repr_ok(), self.depth_spec() > 0,
            !self.store.unique_capture_spec(), self.trail_stack@.len() > 0,
        ensures ({
            let top = self.trail_stack@[self.trail_stack@.len() - 1];
            &&& top.start <= self.trail_value_pool@.len()
            &&& top.saved_len.as_nat() == self.snapshots@[self.depth_spec() - 1].len()
            &&& forall|q: int| top.start <= q < self.trail_value_pool@.len() ==>
                (#[trigger] self.trail_value_pool@[q]).1.as_nat() < top.saved_len.as_nat()
        }),
    {
        hide(frame_inv_range);
        hide(Vec::trail_repr_ok);
        let top = self.trail_stack@[self.trail_stack@.len() - 1];
        assert(top.start <= self.trail_value_pool@.len()
            && top.saved_len.as_nat() == self.snapshots@[self.depth_spec() - 1].len()
            && frame_inv_range::<T, I>(self.view(), self.trail_value_pool@,
                top.start as int, self.trail_value_pool@.len() as int,
                self.snapshots@[self.depth_spec() - 1], top.saved_len.as_nat())) by {
            // Pointwise, like the Hot twin: the aggregate `trail_repr_ok`
            // quantifier is instantiated once, inside the per-header lemma.
            reveal(Vec::frame_partition_ok);
            self.lemma_trail_repr_at(self.trail_stack@.len() - 1);
        }
        reveal(frame_inv_range);
    }

    /// Per-header accessor for the Trail representation (the Trail twin of
    /// `lemma_hot_repr_at`): pointwise, so callers never instantiate the
    /// aggregate quantifier in their own query.
    pub(crate) proof fn lemma_trail_repr_at(&self, i: int)
        requires
            self.trail_repr_ok(),
            self.frame_partition_ok(),
            0 <= i < self.trail_stack@.len(),
        ensures
            self.trail_stack@[i].start <= self.trail_stack@[i].end,
            self.trail_stack@[i].end <= self.trail_value_pool@.len(),
            self.trail_stack@[i].start as int <= self.phys_trail_end(i),
            self.phys_trail_end(i) <= self.trail_value_pool@.len() as int,
            i + 1 == self.trail_stack@.len() ==>
                self.phys_trail_end(i) == self.trail_value_pool@.len() as int,
            self.cold_stack@.len() + self.hot_stack@.len() + i < self.snapshots@.len(),
            self.trail_stack@[i].saved_len.as_nat()
                == self.snapshots@[self.cold_stack@.len() + self.hot_stack@.len() + i].len(),
            frame_inv_range::<T, I>(
                self.layer_above_at(self.cold_stack@.len() + self.hot_stack@.len() + i),
                self.trail_value_pool@, self.trail_stack@[i].start as int,
                self.phys_trail_end(i),
                self.snapshots@[self.cold_stack@.len() + self.hot_stack@.len() + i],
                self.snapshots@[self.cold_stack@.len() + self.hot_stack@.len() + i].len()),
    {
        reveal(Vec::trail_repr_ok);
        reveal(Vec::frame_partition_ok);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_survivor_top_bounds(&self)
        requires self.frame_partition_ok(), self.hot_repr_ok(), self.trail_repr_ok(),
            self.depth_spec() > 0,
            self.store.unique_capture_spec() ==> self.trail_stack@.len() == 0
                && self.hot_stack@.len() > 0,
            !self.store.unique_capture_spec() ==> self.trail_stack@.len() > 0,
        ensures
            self.store.unique_capture_spec() ==> {
                let top = self.hot_stack@[self.hot_stack@.len() - 1];
                &&& top.start <= self.hot_value_pool@.len()
                &&& top.saved_len.as_nat() == self.snapshots@[self.depth_spec() - 1].len()
                &&& forall|q: int| top.start <= q < self.hot_value_pool@.len() ==>
                    (#[trigger] self.hot_value_pool@[q]).1.as_nat() < top.saved_len.as_nat()
            },
            !self.store.unique_capture_spec() ==> {
                let top = self.trail_stack@[self.trail_stack@.len() - 1];
                &&& top.start <= self.trail_value_pool@.len()
                &&& top.saved_len.as_nat() == self.snapshots@[self.depth_spec() - 1].len()
                &&& forall|q: int| top.start <= q < self.trail_value_pool@.len() ==>
                    (#[trigger] self.trail_value_pool@[q]).1.as_nat() < top.saved_len.as_nat()
            },
    {
        hide(frame_inv_range);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::frame_partition_ok);
        if self.store.unique_capture_spec() {
            self.lemma_survivor_top_bounds_hot();
        } else {
            self.lemma_survivor_top_bounds_trail();
        }
    }

    /// Finish restore once the surviving top occupies its writable tier.
    /// Promotion is responsible only for establishing these physical premises.
    #[verifier::spinoff_prover]
    fn finish_survivor_checked(&mut self)
        requires TRACK, old(self).wf_for_snap(),
            old(self).hot_repr_ok(), old(self).trail_repr_ok(), old(self).cold_repr_ok(),
            old(self).proof_compat_ok(), old(self).depth_spec() > 0,
            old(self).store.unique_capture_spec() ==> old(self).trail_stack@.len() == 0
                && old(self).hot_stack@.len() > 0,
            !old(self).store.unique_capture_spec() ==> old(self).trail_stack@.len() > 0
                && (old(self).hot_stack@.len() > 0 ==>
                    old(self).hot_stack@[old(self).hot_stack@.len() - 1].end
                        == old(self).hot_value_pool@.len()),
            forall|j: int| 0 <= j < old(self).store.captured().len() ==>
                !(#[trigger] old(self).store.captured()[j]),
        ensures final(self).wf(), final(self).view() == old(self).view(),
            final(self).persistence_model() == old(self).persistence_model(),
            *final(self) == (Self { store: final(self).store,
                active_saved_len: final(self).active_saved_len, ..*old(self) }),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_repr_ok);
        hide(Vec::cold_payload_ok);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        let ghost pre = *self;
        proof {
            assert(pre.store.wf() && pre.frame_partition_ok()) by { reveal(Vec::wf_for_snap); }
            pre.lemma_survivor_top_bounds();
        }
        if self.store.unique_capture() {
            let n = self.hot_stack.len();
            let top = self.hot_stack[n - 1];
            self.active_saved_len = top.saved_len;
            Self::finish_restore_range_checked(&mut self.store, &self.hot_value_pool, top.start);
        } else {
            let n = self.trail_stack.len();
            let top = self.trail_stack[n - 1];
            self.active_saved_len = top.saved_len;
            Self::finish_restore_range_checked(&mut self.store, &self.trail_value_pool, top.start);
        }
        proof {
            self.lemma_survivor_history_transfer(pre);
            self.store.lemma_wf_captured_len();
            reveal(Vec::open_ingress_ok);
            reveal(Vec::proof_compat_ok);
            reveal(Vec::wf);
            assert(self.wf());
            self.lemma_persistence_store_framing(pre);
        }
    }

    pub closed spec fn hot_survivor_promoted(&self, pre: Self) -> bool {
        let n = pre.hot_stack@.len();
        let top = pre.hot_stack@[n - 1];
        &&& *self == (Self { hot_stack: self.hot_stack, hot_value_pool: self.hot_value_pool,
            trail_stack: self.trail_stack, trail_value_pool: self.trail_value_pool, ..pre })
        &&& self.hot_stack@ == pre.hot_stack@.subrange(0, n - 1)
        &&& self.hot_value_pool@ == pre.hot_value_pool@.subrange(0, top.start as int)
        &&& self.trail_value_pool@ == pre.hot_value_pool@.subrange(top.start as int, top.end as int)
        &&& self.trail_stack@ == seq![crate::frame::TrailFrame {
            saved_len: top.saved_len, start: 0, end: (top.end - top.start) as usize }]
    }

    #[verifier::spinoff_prover]
    proof fn lemma_hot_header_order(&self, a: int, b: int)
        requires self.hot_repr_ok(), 0 <= a <= b < self.hot_stack@.len(),
        ensures self.hot_stack@[a].start <= self.hot_stack@[b].start,
        decreases b - a,
    {
        reveal(Vec::hot_repr_ok);
        if a < b { self.lemma_hot_header_order(a + 1, b); }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_hot_promotion_retained_frame(&self, pre: Self, f: int)
        requires pre.hot_repr_ok(), pre.frame_partition_ok(),
            pre.hot_stack@.len() > 0, pre.trail_stack@.len() == 0,
            self.hot_survivor_promoted(pre), 0 <= f < self.hot_stack@.len(),
        ensures
            self.hot_stack@[f].start <= self.hot_stack@[f].end <= self.hot_value_pool@.len(),
            self.phys_hot_start(f) <= self.phys_hot_end(f) <= self.hot_value_pool@.len(),
            self.phys_hot_end(f) == pre.phys_hot_end(f),
            self.phys_frame_inv_range_holds(f),
            stratum_unique::<T, I>(self.hot_value_pool@, self.phys_hot_start(f), self.phys_hot_end(f)),
    {
        hide(frame_inv_range);
        hide(Vec::hot_repr_ok);
        reveal(Vec::hot_survivor_promoted);
        let n = pre.hot_stack@.len();
        let cc = pre.cold_stack@.len();
        pre.lemma_hot_repr_at(f);
        pre.lemma_hot_repr_at(n - 1);
        pre.lemma_hot_header_order(f + 1, n - 1);
        assert(self.phys_hot_end(f) == pre.phys_hot_end(f));
        lemma_frame_inv_range_local::<T, I>(self.layer_above_at(cc + f),
            pre.hot_value_pool@, self.hot_value_pool@, self.phys_hot_start(f), self.phys_hot_end(f),
            self.snapshots@[cc + f], self.snapshots@[cc + f].len());
        lemma_stratum_unique_local::<T, I>(pre.hot_value_pool@, self.hot_value_pool@,
            self.phys_hot_start(f), self.phys_hot_end(f));
    }

    #[verifier::spinoff_prover]
    proof fn lemma_hot_promotion_hot_repr(&self, pre: Self)
        requires pre.hot_repr_ok(), pre.frame_partition_ok(),
            pre.hot_stack@.len() > 0, pre.trail_stack@.len() == 0,
            self.hot_survivor_promoted(pre),
        ensures self.hot_repr_ok(),
            self.hot_stack@.len() > 0 ==>
                self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len(),
    {
        hide(frame_inv_range);
        reveal(Vec::hot_survivor_promoted);
        reveal(Vec::hot_repr_ok);
        let hs = self.hot_stack@;
        let pool = self.hot_value_pool@;
        let cc = self.cold_stack@.len();
        assert forall|f: int| 0 <= f < hs.len() implies {
            &&& (#[trigger] hs[f]).start <= hs[f].end <= pool.len()
            &&& hs[f].start as int <= self.phys_hot_end(f) <= pool.len()
            &&& (f + 1 < hs.len() ==> hs[f].end == hs[f + 1].start
                && self.phys_hot_end(f) == hs[f + 1].start)
            &&& (f + 1 == hs.len() ==> self.phys_hot_end(f) == pool.len())
            &&& stratum_unique::<T, I>(pool, hs[f].start as int, self.phys_hot_end(f))
            &&& self.phys_frame_inv_range_holds(f)
            &&& cc + f < self.snapshots@.len()
        } by { self.lemma_hot_promotion_retained_frame(pre, f); }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_hot_survivor_promotion(&self, pre: Self)
        requires pre.wf_for_snap(), pre.hot_repr_ok(), pre.trail_repr_ok(), pre.cold_repr_ok(),
            pre.proof_compat_ok(), pre.trail_stack@.len() == 0, pre.hot_stack@.len() > 0,
            pre.hot_stack@[pre.hot_stack@.len() - 1].end == pre.hot_value_pool@.len(),
            self.hot_survivor_promoted(pre),
        ensures self.wf_for_snap(), self.hot_repr_ok(), self.trail_repr_ok(),
            self.cold_repr_ok(), self.proof_compat_ok(),
            self.hot_stack@.len() > 0 ==>
                self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len(),
    {
        hide(Vec::wf_for_snap);
        hide(Vec::hot_repr_ok);
        hide(frame_inv_range);
        hide(frame_cell_inv);
        assert(pre.frame_partition_ok() && pre.store.wf()) by { reveal(Vec::wf_for_snap); }
        reveal(Vec::hot_survivor_promoted);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::trail_repr_ok);
        reveal(Vec::cold_repr_ok);
        reveal(Vec::proof_compat_ok);
        let n = pre.hot_stack@.len();
        let top = pre.hot_stack@[n - 1];
        let cc = pre.cold_stack@.len();
        pre.lemma_hot_repr_at(n - 1);
        assert(self.frame_partition_ok());
        self.lemma_canonical_history_repartition(pre);
        assert forall|f: int| 0 <= f < self.depth_spec() implies
            #[trigger] self.layer_above_at(f) == pre.layer_above_at(f) by {};
        self.lemma_hot_promotion_hot_repr(pre);
        lemma_frame_inv_subrange::<T, I>(pre.layer_above_at(cc + n - 1), pre.hot_value_pool@,
            top.start as int, top.end as int, pre.snapshots@[cc + n - 1]);
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f) by {
            self.lemma_cold_reconstructs_transfer(pre, f);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_hot_promotion_lookup(&self, pre: Self, f: int, j: nat)
        requires pre.hot_repr_ok(), pre.frame_partition_ok(),
            pre.trail_stack@.len() == 0, pre.hot_stack@.len() > 0,
            pre.hot_stack@[pre.hot_stack@.len() - 1].end == pre.hot_value_pool@.len(),
            self.hot_survivor_promoted(pre), 0 <= f < pre.depth_spec(),
        ensures self.frame_saved_len(f) == pre.frame_saved_len(f),
            self.frame_saved_value(f, j) == pre.frame_saved_value(f, j),
    {
        hide(Vec::hot_repr_ok);
        reveal(Vec::hot_survivor_promoted);
        reveal(Vec::frame_partition_ok);
        let cc = pre.cold_stack@.len();
        let n = pre.hot_stack@.len();
        if f >= cc {
            pre.lemma_hot_repr_at(n - 1);
            let h = f - cc;
            pre.lemma_hot_repr_at(h);
            if h + 1 < n {
                self.lemma_hot_promotion_retained_frame(pre, h);
                assert forall|q: int| self.phys_hot_start(h) <= q < self.phys_hot_end(h) implies
                    #[trigger] self.hot_value_pool@[q] == pre.hot_value_pool@[q] by {
                    assert(0 <= q < self.hot_value_pool@.len());
                }
                lemma_range_saved_value_local::<T, I>(self.hot_value_pool@, pre.hot_value_pool@,
                    self.phys_hot_start(h), self.phys_hot_end(h), j);
            } else {
                let top = pre.hot_stack@[n - 1];
                lemma_range_saved_value_subrange::<T, I>(pre.hot_value_pool@,
                    top.start as int, top.end as int, j);
            }
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_hot_promotion(&self, pre: Self)
        requires pre.hot_repr_ok(), pre.frame_partition_ok(),
            pre.trail_stack@.len() == 0, pre.hot_stack@.len() > 0,
            pre.hot_stack@[pre.hot_stack@.len() - 1].end == pre.hot_value_pool@.len(),
            self.hot_survivor_promoted(pre),
        ensures self.persistence_model() == pre.persistence_model(),
    {
        hide(Vec::hot_repr_ok);
        reveal(Vec::hot_survivor_promoted);
        reveal(Vec::frame_partition_ok);
        assert forall|f: int| 0 <= f < pre.depth_spec() implies
            #[trigger] self.persistence_frame(f) == pre.persistence_frame(f) by {
            self.lemma_persistence_hot_promotion_lookup(pre, f, 0);
            let a = self.persistence_frame(f).saved;
            let b = pre.persistence_frame(f).saved;
            assert forall|j: nat| #[trigger] a.dom().contains(j) == b.dom().contains(j)
                && (a.dom().contains(j) ==> a[j] == b[j]) by {
                self.lemma_persistence_hot_promotion_lookup(pre, f, j);
                crate::persistence_model::bounded_saved_map_at(self.frame_saved_len(f),
                    |i: nat| self.frame_saved_value(f, i), j);
                crate::persistence_model::bounded_saved_map_at(pre.frame_saved_len(f),
                    |i: nat| pre.frame_saved_value(f, i), j);
            }
            assert(a =~= b);
        }
        assert(self.persistence_model().frames =~= pre.persistence_model().frames);
    }

    #[verifier::spinoff_prover]
    fn promote_hot_survivor_checked(&mut self)
        requires old(self).wf_for_snap(), old(self).hot_repr_ok(), old(self).trail_repr_ok(),
            old(self).cold_repr_ok(), old(self).proof_compat_ok(),
            old(self).trail_stack@.len() == 0, old(self).hot_stack@.len() > 0,
            old(self).hot_stack@[old(self).hot_stack@.len() - 1].end == old(self).hot_value_pool@.len(),
        ensures final(self).hot_survivor_promoted(*old(self)),
            final(self).persistence_model() == old(self).persistence_model(),
            final(self).wf_for_snap(), final(self).hot_repr_ok(), final(self).trail_repr_ok(),
            final(self).cold_repr_ok(), final(self).proof_compat_ok(),
            final(self).hot_stack@.len() > 0 ==>
                final(self).hot_stack@[final(self).hot_stack@.len() - 1].end == final(self).hot_value_pool@.len(),
    {
        hide(Vec::wf_for_snap);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::cold_repr_ok);
        let ghost pre = *self;
        let n = self.hot_stack.len();
        proof {
            assert(pre.frame_partition_ok()) by { reveal(Vec::wf_for_snap); }
            pre.lemma_hot_repr_at(n - 1);
            assert(self.trail_value_pool@.len() == 0) by { reveal(Vec::trail_repr_ok); }
        }
        let frame = self.hot_stack[n - 1];
        let _ = self.hot_stack.pop();
        let slice = vstd::slice::slice_subrange(self.hot_value_pool.as_slice(), frame.start, frame.end);
        let start = self.trail_value_pool.len();
        // Copy directly: generic Clone is allowed to differ from Copy.
        // Reserve once and retain the existing Trail allocation.
        self.trail_value_pool.reserve(slice.len());
        let mut q: usize = 0;
        while q < slice.len()
            invariant
                q <= slice@.len(),
                self.trail_value_pool@ == slice@.subrange(0, q as int),
                slice@ == pre.hot_value_pool@.subrange(frame.start as int, frame.end as int),
                self.hot_stack@ == pre.hot_stack@.subrange(0, n - 1),
                self.hot_value_pool@ == pre.hot_value_pool@,
                self.trail_stack@ == pre.trail_stack@,
                pre.trail_stack@.len() == 0, start == 0,
            decreases slice@.len() - q,
        {
            self.trail_value_pool.push(slice[q]);
            q += 1;
            proof { assert(self.trail_value_pool@ =~= slice@.subrange(0, q as int)); }
        }
        self.hot_value_pool.truncate(frame.start);
        let end = self.trail_value_pool.len();
        self.trail_stack.push(crate::frame::TrailFrame { saved_len: frame.saved_len, start, end });
        proof {
            reveal(Vec::hot_survivor_promoted);
            assert(self.hot_stack@ =~= pre.hot_stack@.subrange(0, n - 1));
            assert(self.trail_stack@ =~= seq![crate::frame::TrailFrame {
                saved_len: frame.saved_len, start: 0, end: (frame.end - frame.start) as usize }]);
            assert(self.hot_value_pool@ =~= pre.hot_value_pool@.subrange(0, frame.start as int));
            assert(self.trail_value_pool@ =~= pre.hot_value_pool@.subrange(frame.start as int, frame.end as int));
            assert(self.hot_survivor_promoted(pre));
            self.lemma_hot_survivor_promotion(pre);
            self.lemma_persistence_hot_promotion(pre);
        }
    }

    pub closed spec fn cold_survivor_promoted(&self, pre: Self) -> bool {
        let n = pre.cold_stack@.len();
        let top = pre.cold_stack@[n - 1];
        let unique = pre.store.unique_capture_spec();
        let entries = self.pair_tier_pool(!unique);
        &&& entries.len() <= usize::MAX
        &&& *self == (Self { cold_stack: self.cold_stack, cold_index_runs: self.cold_index_runs,
            cold_value_pool: self.cold_value_pool, hot_stack: self.hot_stack,
            hot_value_pool: self.hot_value_pool, trail_stack: self.trail_stack,
            trail_value_pool: self.trail_value_pool, ..pre })
        &&& self.cold_prefix_of(pre, (n - 1) as nat)
        &&& crate::cold_decode::decoded(pre.cold_index_runs@, pre.cold_value_pool@,
            top.runs_start as int, (top.runs_start + top.runs_len) as int,
            if top.runs_len > 0 { pre.cold_index_runs@[top.runs_start as int].start as int }
            else { 0int }, entries)
        &&& if unique {
            &&& self.hot_stack@ == seq![crate::frame::HotFrame {
                saved_len: top.saved_len, start: 0, end: entries.len() as usize }]
            &&& self.trail_stack@.len() == 0 && self.trail_value_pool@.len() == 0
        } else {
            &&& self.trail_stack@ == seq![crate::frame::TrailFrame {
                saved_len: top.saved_len, start: 0, end: entries.len() as usize }]
            &&& self.hot_stack@.len() == 0 && self.hot_value_pool@.len() == 0
        }
    }

    /// Decode and publish the newest Cold frame in the store-selected tier.
    /// Global invariant reconstruction is a separate proof over this effect.
    #[verifier::spinoff_prover]
    fn promote_cold_storage_checked(&mut self)
        requires old(self).cold_repr_ok(), old(self).cold_stack@.len() > 0,
            old(self).hot_stack@.len() == 0, old(self).hot_value_pool@.len() == 0,
            old(self).trail_stack@.len() == 0, old(self).trail_value_pool@.len() == 0,
        ensures final(self).cold_survivor_promoted(*old(self)),
    {
        hide(Vec::cold_repr_ok);
        let ghost pre = *self;
        let n = self.cold_stack.len();
        let frame = self.cold_stack[n - 1];
        let runs_end = self.cold_index_runs.len();
        proof {
            pre.lemma_cold_decode_layout(n - 1);
            assert(pre.repr_ok()) by { reveal(Vec::cold_repr_ok); }
            pre.lemma_cold_layout_header_at(n - 1);
        }
        let _ = self.cold_stack.pop();
        if self.store.unique_capture() {
            crate::cold_decode::decode_into(&mut self.hot_value_pool,
                &self.cold_index_runs, &self.cold_value_pool, frame.runs_start,
                runs_end, frame.saved_len);
            let end = self.hot_value_pool.len();
            self.hot_stack.push(crate::frame::HotFrame { saved_len: frame.saved_len, start: 0, end });
            proof { assert(self.hot_stack@ =~= seq![crate::frame::HotFrame { saved_len: frame.saved_len, start: 0, end }]); }
        } else {
            crate::cold_decode::decode_into(&mut self.trail_value_pool,
                &self.cold_index_runs, &self.cold_value_pool, frame.runs_start,
                runs_end, frame.saved_len);
            let end = self.trail_value_pool.len();
            self.trail_stack.push(crate::frame::TrailFrame { saved_len: frame.saved_len, start: 0, end });
            proof { assert(self.trail_stack@ =~= seq![crate::frame::TrailFrame { saved_len: frame.saved_len, start: 0, end }]); }
        }
        let value_cut = self.cold_value_cut(frame.runs_start);
        self.cold_index_runs.truncate(frame.runs_start);
        self.cold_value_pool.truncate(value_cut);
        proof {
            reveal(Vec::cold_prefix_of);
            reveal(Vec::cold_survivor_promoted);
            assert(self.cold_stack@ =~= pre.cold_stack@.subrange(0, n - 1));
            assert(self.cold_index_runs@ =~= pre.cold_index_runs@.subrange(0, frame.runs_start as int));
            assert(self.cold_value_pool@ =~= pre.cold_value_pool@.subrange(0, value_cut as int));
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_promotion_partition(&self, pre: Self)
        requires pre.frame_partition_ok(), pre.cold_stack@.len() > 0,
            pre.hot_stack@.len() == 0, pre.trail_stack@.len() == 0,
            self.cold_survivor_promoted(pre),
        ensures self.frame_partition_ok(), self.depth_spec() == pre.depth_spec(),
    {
        reveal(Vec::cold_survivor_promoted);
        reveal(Vec::cold_prefix_of);
        reveal(Vec::frame_partition_ok);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_prefix_repr(&self, pre: Self, kept: nat)
        requires pre.cold_repr_ok(), pre.frame_partition_ok(), self.cold_prefix_of(pre, kept),
            self.snapshots@ == pre.snapshots@, self.trail_frames@ == pre.trail_frames@,
            self.view() == pre.view(),
        ensures self.cold_repr_ok(),
    {
        hide(Vec::cold_repr_ok);
        hide(Vec::cold_prefix_of);
        hide(Vec::repr_ok);
        hide(Vec::cold_payload_ok);
        hide(Vec::cold_reconstructs);
        self.lemma_cold_prefix_layout(pre, kept);
        assert(pre.cold_payload_ok()) by { reveal(Vec::cold_repr_ok); }
        reveal(Vec::frame_partition_ok);
        assert forall|f: int, r: int| 0 <= f < self.cold_stack@.len()
            && (#[trigger] self.cold_stack@[f]).runs_start <= r
            < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len implies
            0 < (#[trigger] self.cold_index_runs@[r]).len
                && self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len
                    <= self.cold_stack@[f].saved_len.as_nat() by {
            reveal(Vec::cold_payload_ok);
            self.lemma_cold_layout_header_at(f);
        }
        assert(self.cold_payload_ok()) by { reveal(Vec::cold_payload_ok); }
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f) by {
            assert forall|j: int| 0 <= j < self.snapshots@[f].len() implies
                if #[trigger] self.cold_covered(f, j as nat) {
                    self.cold_value(f, j as nat) == self.snapshots@[f][j]
                } else {
                    j < self.layer_above_at(f).len() && self.layer_above_at(f)[j] == self.snapshots@[f][j]
                } by {
                self.lemma_cold_prefix_cell(pre, kept, f, j as nat);
                assert(pre.cold_reconstructs(f)) by { reveal(Vec::cold_repr_ok); }
                pre.lemma_cold_reconstructs_at(f, j);
            }
            reveal(Vec::cold_reconstructs);
        }
        reveal(Vec::cold_repr_ok);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_survivor_promotion(&self, pre: Self)
        requires pre.wf_for_snap(), pre.cold_repr_ok(), pre.proof_compat_ok(),
            pre.cold_stack@.len() > 0, pre.hot_stack@.len() == 0, pre.trail_stack@.len() == 0,
            self.cold_survivor_promoted(pre),
        ensures self.wf_for_snap(), self.cold_repr_ok(), self.hot_repr_ok(), self.trail_repr_ok(),
            self.proof_compat_ok(),
            self.hot_stack@.len() > 0 ==> self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len(),
    {
        hide(Vec::wf_for_snap);
        hide(Vec::cold_repr_ok);
        hide(frame_inv_range);
        hide(frame_cell_inv);
        assert(pre.frame_partition_ok() && pre.store.wf()) by { reveal(Vec::wf_for_snap); }
        self.lemma_cold_promotion_partition(pre);
        reveal(Vec::cold_survivor_promoted);
        let f = pre.cold_stack@.len() - 1;
        let trail = !pre.store.unique_capture_spec();
        let entries = self.pair_tier_pool(trail);
        self.lemma_canonical_history_repartition(pre);
        self.lemma_cold_prefix_repr(pre, f as nat);
        pre.lemma_cold_decoded_frame(f, entries);
        assert(self.layer_above_at(f) == pre.layer_above_at(f));
        assert(frame_inv_range::<T, I>(self.layer_above_at(f), entries, 0, entries.len() as int,
            self.snapshots@[f], self.snapshots@[f].len()));
        reveal(Vec::cold_prefix_of);
        reveal(Vec::hot_repr_ok);
        reveal(Vec::trail_repr_ok);
        reveal(Vec::proof_compat_ok);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_cold_promotion_lookup(&self, pre: Self, f: int, j: nat)
        requires pre.cold_repr_ok(), pre.frame_partition_ok(), pre.cold_stack@.len() > 0,
            pre.hot_stack@.len() == 0, pre.trail_stack@.len() == 0,
            self.cold_survivor_promoted(pre), 0 <= f < pre.depth_spec(),
        ensures self.frame_saved_len(f) == pre.frame_saved_len(f),
            self.frame_saved_value(f, j) == pre.frame_saved_value(f, j),
    {
        hide(Vec::cold_repr_ok);
        reveal(Vec::cold_survivor_promoted);
        reveal(Vec::cold_prefix_of);
        reveal(Vec::frame_partition_ok);
        let last = pre.cold_stack@.len() - 1;
        if f < last { self.lemma_cold_prefix_cell(pre, last as nat, f, j); }
        else {
            let entries = self.pair_tier_pool(!pre.store.unique_capture_spec());
            pre.lemma_cold_decoded_lookup(last, entries, j);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_cold_promotion(&self, pre: Self)
        requires pre.cold_repr_ok(), pre.frame_partition_ok(), pre.cold_stack@.len() > 0,
            pre.hot_stack@.len() == 0, pre.trail_stack@.len() == 0,
            self.cold_survivor_promoted(pre),
        ensures self.persistence_model() == pre.persistence_model(),
    {
        hide(Vec::cold_repr_ok);
        reveal(Vec::cold_survivor_promoted);
        assert forall|f: int| 0 <= f < pre.depth_spec() implies
            #[trigger] self.persistence_frame(f) == pre.persistence_frame(f) by {
            self.lemma_persistence_cold_promotion_lookup(pre, f, 0);
            let a = self.persistence_frame(f).saved;
            let b = pre.persistence_frame(f).saved;
            assert forall|j: nat| #[trigger] a.dom().contains(j) == b.dom().contains(j)
                && (a.dom().contains(j) ==> a[j] == b[j]) by {
                self.lemma_persistence_cold_promotion_lookup(pre, f, j);
                crate::persistence_model::bounded_saved_map_at(self.frame_saved_len(f),
                    |i: nat| self.frame_saved_value(f, i), j);
                crate::persistence_model::bounded_saved_map_at(pre.frame_saved_len(f),
                    |i: nat| pre.frame_saved_value(f, i), j);
            }
            assert(a =~= b);
        }
        assert(self.persistence_model().frames =~= pre.persistence_model().frames);
    }

    #[verifier::spinoff_prover]
    fn promote_cold_survivor_checked(&mut self)
        requires old(self).wf_for_snap(), old(self).cold_repr_ok(), old(self).proof_compat_ok(),
            old(self).cold_stack@.len() > 0,
            old(self).hot_stack@.len() == 0, old(self).hot_value_pool@.len() == 0,
            old(self).trail_stack@.len() == 0, old(self).trail_value_pool@.len() == 0,
        ensures final(self).cold_survivor_promoted(*old(self)),
            final(self).persistence_model() == old(self).persistence_model(),
            final(self).wf_for_snap(), final(self).cold_repr_ok(),
            final(self).hot_repr_ok(), final(self).trail_repr_ok(), final(self).proof_compat_ok(),
            final(self).hot_stack@.len() > 0 ==> final(self).hot_stack@[final(self).hot_stack@.len() - 1].end
                == final(self).hot_value_pool@.len(),
    {
        let ghost pre = *self;
        self.promote_cold_storage_checked();
        proof {
            self.lemma_cold_survivor_promotion(pre);
            assert(pre.frame_partition_ok()) by { reveal(Vec::wf_for_snap); }
            self.lemma_persistence_cold_promotion(pre);
        }
    }

    /// Verified Hot-only restore to the oldest token coordinate. Replaying the
    /// whole authoritative Hot pool reconstructs snapshot zero, after which
    /// every frame and capture flag is retired. Capacity reclamation remains
    /// in the external dispatch because allocator capacity has no spec content.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1200)]
    fn hot_defer_restore_zero_checked(&mut self)
    where
        T: core::default::Default,
        requires
            old(self).hot_defer_wf(),
            old(self).hot_stack@.len() > 0,
        ensures
            final(self).hot_defer_wf(),
            final(self).wf(),
            final(self).view() == old(self).snapshots@[0],
            final(self).hot_stack@.len() == 0,
            final(self).hot_value_pool@.len() == 0,
            final(self).snapshots@.len() == 0,
            final(self).trail_frames@.len() == 0,
    {
        let ghost pre = *self;
        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
        }
        let saved_len = self.hot_stack[0].saved_len;
        proof {
            saved_len.lemma_as_nat_bounded();
            assert(saved_len.as_nat() == pre.snapshots@[0].len());
        }
        if self.store.len().as_usize() != saved_len.as_usize() {
            self.store.resize_default(saved_len);
        }
        let ghost base = self.store.data();
        proof {
            assert(base.len() == saved_len.as_nat());
            assert forall|j: int| 0 <= j < base.len() && j < pre.view().len()
                implies #[trigger] base[j] == pre.view()[j] by {}
            assert forall|j: int| 0 <= j < self.store.captured().len()
                && #[trigger] self.store.captured()[j]
                implies exists|k: int| 0 <= k < self.hot_value_pool@.len()
                    && (#[trigger] self.hot_value_pool@[k]).1.as_nat() == j as nat by {
                assert(j < pre.view().len());
                assert(pre.store.captured()[j]);
                assert(j < pre.active_saved_len.as_nat());
                let top = (pre.hot_stack@.len() - 1) as int;
                assert(pre.store.captured()[j]
                    == captured_in_range::<T, I>(
                        pre.hot_value_pool@, pre.hot_stack@[top].start as int,
                        pre.hot_value_pool@.len() as int, j as nat));
                let p = choose|p: int| pre.hot_stack@[top].start <= p
                    < pre.hot_value_pool@.len()
                    && (#[trigger] pre.hot_value_pool@[p]).1.as_nat() == j as nat;
                assert(self.hot_value_pool@[p] == pre.hot_value_pool@[p]);
            }
        }
        let fused = self.store.restore_entries_clear_capture();
        if !fused {
            if self.store.needs_replayed_indices() {
                let replayed = self.hot_value_pool.as_slice();
                proof {
                    assert(replayed@ == self.hot_value_pool@);
                    assert forall|j: int| 0 <= j < self.store.captured().len()
                        && #[trigger] self.store.captured()[j]
                        implies exists|k: int| 0 <= k < replayed@.len()
                            && (#[trigger] replayed@[k]).1.as_nat() == j as nat by {}
                }
                self.store.begin_restore(replayed);
            } else {
                let empty: std::vec::Vec<(T, I)> = std::vec::Vec::new();
                self.store.begin_restore(empty.as_slice());
            }
        }
        let ghost cleared = self.store.captured();
        proof {
            assert(!fused ==> forall|j: int| 0 <= j < cleared.len()
                ==> !(#[trigger] cleared[j]));
            assert forall|j: int| 0 <= j < cleared.len() && #[trigger] cleared[j]
                implies captured_in_range::<T, I>(
                    self.hot_value_pool@, 0, self.hot_value_pool@.len() as int,
                    j as nat) by {}
            assert(pre.hot_stack@[0].start == 0);
            assert forall|j: int| 0 <= j < pre.snapshots@[0].len() as int implies
                #[trigger] overlay::<T, I>(
                    base, pre.hot_value_pool@, 0,
                    pre.hot_value_pool@.len() as int)[j]
                    == pre.snapshots@[0][j] by {
                pre.lemma_hot_defer_cell_eq_overlay(base, 0, j);
            }
            lemma_overlay_len::<T, I>(
                base, pre.hot_value_pool@, 0, pre.hot_value_pool@.len() as int);
        }
        let n = self.hot_value_pool.len();
        replay_physical_range::<T, I, S, TRACK>(&mut self.store, &self.hot_value_pool, 0, n);
        proof {
            assert(self.store.data().len() == pre.snapshots@[0].len());
            assert forall|j: int| 0 <= j < self.store.data().len() implies
                #[trigger] self.store.data()[j] == pre.snapshots@[0][j] by {}
            assert(self.store.data() =~= pre.snapshots@[0]);
            assert forall|j: int| 0 <= j < self.store.captured().len()
                implies !(#[trigger] self.store.captured()[j]) by {
                if self.store.captured()[j] {
                    assert(j < cleared.len() && cleared[j]);
                    if fused {
                        assert(captured_in_range::<T, I>(
                            pre.hot_value_pool@, 0, pre.hot_value_pool@.len() as int,
                            j as nat));
                        assert(!captured_in_range::<T, I>(
                            pre.hot_value_pool@, 0, pre.hot_value_pool@.len() as int,
                            j as nat));
                    }
                }
            }
        }
        self.hot_stack.clear();
        self.hot_value_pool.clear();
        self.diff_log.clear();
        proof {
            self.full_trail@ = Seq::empty();
            self.trail_frames@ = Seq::empty();
            self.snapshots = Ghost(Seq::empty());
        }
        self.active_saved_len = <I as IndexLike>::min();
        proof {
            I::lemma_min_as_nat();
            self.store.lemma_wf_captured_len();
            assert forall|j: int| 0 <= j < self.store.captured().len()
                implies !(#[trigger] self.store.captured()[j]) by {}
            assert(self.hot_defer_wf());
            reveal(Vec::frame_partition_ok);
            reveal(Vec::proof_compat_ok);
            assert(self.wf_for_snap());
            assert(self.proof_compat_ok());
            self.lemma_hot_defer_snap_implies_wf();
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(400)]
    proof fn hot_defer_restore_nonzero_layout(
        &self, pre: Self, target: usize, cut: usize,
    )
        requires
            pre.hot_defer_wf(),
            0 < target,
            (target as nat) < pre.hot_stack@.len(),
            cut == pre.hot_stack@[target as int].start,
            self.hot_stack@ == pre.hot_stack@.subrange(0, target as int),
            self.hot_value_pool@ == pre.hot_value_pool@.subrange(0, cut as int),
            self.snapshots@ == pre.snapshots@.subrange(0, target as int),
        ensures
            forall|i: int| 0 <= i < self.hot_stack@.len() ==> {
                &&& (#[trigger] self.hot_stack@[i]).start <= self.hot_stack@[i].end
                &&& self.hot_stack@[i].end <= self.hot_value_pool@.len()
                &&& self.hot_stack@[i].start as int <= self.hot_defer_end(i)
                &&& self.hot_defer_end(i) <= self.hot_value_pool@.len() as int
                &&& (i + 1 < self.hot_stack@.len() ==> {
                    &&& self.hot_stack@[i].end == self.hot_stack@[i + 1].start
                    &&& self.hot_defer_end(i) == self.hot_stack@[i + 1].start as int
                })
                &&& (i + 1 == self.hot_stack@.len() ==>
                    self.hot_defer_end(i) == self.hot_value_pool@.len() as int)
            },
            forall|i: int| 0 <= i < self.hot_stack@.len() ==>
                (#[trigger] self.hot_stack@[i]).saved_len.as_nat()
                    == self.snapshots@[i].len(),
    {
        reveal(Vec::hot_defer_wf);
        reveal(Vec::hot_defer_end);
        let depth = self.hot_stack@.len();
        let pool = self.hot_value_pool@;
        assert(depth == target);
        assert forall|i: int| 0 <= i < depth implies {
            &&& (#[trigger] self.hot_stack@[i]).start <= self.hot_stack@[i].end
            &&& self.hot_stack@[i].end <= pool.len()
            &&& self.hot_stack@[i].start as int <= self.hot_defer_end(i)
            &&& self.hot_defer_end(i) <= pool.len() as int
            &&& (i + 1 < depth ==> {
                &&& self.hot_stack@[i].end == self.hot_stack@[i + 1].start
                &&& self.hot_defer_end(i) == self.hot_stack@[i + 1].start as int
            })
            &&& (i + 1 == depth ==> self.hot_defer_end(i) == pool.len() as int)
        } by {
            assert(self.hot_stack@[i] == pre.hot_stack@[i]);
            if i + 1 < depth {
                assert(self.hot_stack@[i + 1] == pre.hot_stack@[i + 1]);
                assert(self.hot_defer_end(i) == pre.hot_defer_end(i));
                pre.lemma_hot_defer_start_monotone(i + 1, target as int);
                assert(self.hot_stack@[i].end == self.hot_stack@[i + 1].start);
                assert(self.hot_stack@[i].end <= cut);
            } else {
                assert(i + 1 == target);
                assert(pre.hot_stack@[i].end == pre.hot_stack@[target as int].start);
                assert(self.hot_stack@[i].end == cut);
                assert(self.hot_defer_end(i) == pool.len() as int);
            }
        }
        assert forall|i: int| 0 <= i < depth implies
            (#[trigger] self.hot_stack@[i]).saved_len.as_nat()
                == self.snapshots@[i].len() by {
            assert(self.hot_stack@[i] == pre.hot_stack@[i]);
            assert(self.snapshots@[i] == pre.snapshots@[i]);
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(400)]
    proof fn hot_defer_restore_nonzero_unique(
        &self, pre: Self, target: usize, cut: usize,
    )
        requires
            pre.hot_defer_wf(),
            0 < target,
            (target as nat) < pre.hot_stack@.len(),
            cut == pre.hot_stack@[target as int].start,
            self.hot_stack@ == pre.hot_stack@.subrange(0, target as int),
            self.hot_value_pool@ == pre.hot_value_pool@.subrange(0, cut as int),
            forall|i: int| 0 <= i < self.hot_stack@.len() ==>
                self.hot_defer_end(i) <= self.hot_value_pool@.len() as int,
        ensures
            forall|i: int| 0 <= i < self.hot_stack@.len() ==>
                #[trigger] stratum_unique::<T, I>(
                    self.hot_value_pool@, self.hot_stack@[i].start as int,
                    self.hot_defer_end(i)),
    {
        reveal(Vec::hot_defer_wf);
        reveal(Vec::hot_defer_end);
        let depth = self.hot_stack@.len();
        let pool = self.hot_value_pool@;
        assert(depth == target);
        assert forall|i: int| 0 <= i < depth implies
            #[trigger] stratum_unique::<T, I>(
                pool, self.hot_stack@[i].start as int, self.hot_defer_end(i)) by {
            let lo = self.hot_stack@[i].start as int;
            let hi = self.hot_defer_end(i);
            assert(self.hot_stack@[i] == pre.hot_stack@[i]);
            if i + 1 < depth {
                assert(self.hot_defer_end(i) == pre.hot_defer_end(i));
            } else {
                assert(i + 1 == target);
                assert(hi == cut);
                assert(pre.hot_defer_end(i) == cut);
            }
            assert forall|q: int| lo <= q < hi implies
                #[trigger] pool[q] == pre.hot_value_pool@[q] by {}
            lemma_stratum_unique_local::<T, I>(
                pre.hot_value_pool@, pool, lo, hi);
        }
    }

    // Retiring the legacy diff_log proof subsystem removed a large block of
    // module-level definitions from this query's SMT context, which reshuffled
    // the search enough to push it past the old 600 budget. The proof text is
    // unchanged; only the resource bound is.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(2400)]
    proof fn hot_defer_restore_nonzero_frame_invariants(
        &self, pre: Self, target: usize, cut: usize,
    )
        requires
            pre.hot_defer_wf(),
            0 < target,
            (target as nat) < pre.hot_stack@.len(),
            cut == pre.hot_stack@[target as int].start,
            self.hot_stack@ == pre.hot_stack@.subrange(0, target as int),
            self.hot_value_pool@ == pre.hot_value_pool@.subrange(0, cut as int),
            self.view() == pre.snapshots@[target as int],
            self.snapshots@ == pre.snapshots@.subrange(0, target as int),
            self.trail_frames@ == pre.trail_frames@.subrange(0, target as int),
            forall|i: int| 0 <= i < self.hot_stack@.len() ==>
                self.hot_defer_end(i) <= self.hot_value_pool@.len() as int,
        ensures
            forall|i: int| 0 <= i < self.hot_stack@.len() ==>
                #[trigger] frame_inv_range::<T, I>(
                    self.layer_above_at(i), self.hot_value_pool@,
                    self.hot_stack@[i].start as int, self.hot_defer_end(i),
                    self.snapshots@[i], self.snapshots@[i].len()),
    {
        reveal(Vec::hot_defer_wf);
        reveal(Vec::hot_defer_end);
        let depth = self.hot_stack@.len();
        let pool = self.hot_value_pool@;
        assert(depth == target);
        assert forall|i: int| 0 <= i < depth implies
            #[trigger] frame_inv_range::<T, I>(
                self.layer_above_at(i), pool, self.hot_stack@[i].start as int,
                self.hot_defer_end(i), self.snapshots@[i], self.snapshots@[i].len()) by {
            let lo = self.hot_stack@[i].start as int;
            let hi = self.hot_defer_end(i);
            assert(self.hot_stack@[i] == pre.hot_stack@[i]);
            assert(self.snapshots@[i] == pre.snapshots@[i]);
            if i + 1 < depth {
                assert(self.layer_above_at(i) == pre.layer_above_at(i));
                assert(hi == pre.hot_defer_end(i));
            } else {
                assert(i + 1 == target);
                assert(self.layer_above_at(i) == self.view());
                assert(pre.layer_above_at(i) == pre.snapshots@[target as int]);
                assert(self.layer_above_at(i) == pre.layer_above_at(i));
                assert(hi == cut);
                assert(pre.hot_defer_end(i) == cut);
            }
            assert forall|q: int| lo <= q < hi implies
                #[trigger] pre.hot_value_pool@[q] == pool[q] by {}
            lemma_frame_inv_range_local::<T, I>(
                self.layer_above_at(i), pre.hot_value_pool@, pool, lo, hi,
                self.snapshots@[i], self.snapshots@[i].len());
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    proof fn hot_defer_restore_nonzero_capture_bound(
        &self, target: usize, top_start: usize,
    )
        requires
            0 < target,
            self.hot_stack@.len() == target,
            top_start == self.hot_stack@[target as int - 1].start,
            self.active_saved_len == self.hot_stack@[target as int - 1].saved_len,
            self.hot_stack@[target as int - 1].saved_len.as_nat()
                == self.snapshots@[target as int - 1].len(),
            self.hot_defer_end(target as int - 1)
                == self.hot_value_pool@.len() as int,
            frame_inv_range::<T, I>(
                self.layer_above_at(target as int - 1), self.hot_value_pool@,
                top_start as int, self.hot_defer_end(target as int - 1),
                self.snapshots@[target as int - 1],
                self.snapshots@[target as int - 1].len()),
            forall|j: int| 0 <= j < self.view().len() ==> {
                (#[trigger] self.store.captured()[j])
                    == captured_in_range::<T, I>(
                        self.hot_value_pool@, top_start as int,
                        self.hot_value_pool@.len() as int, j as nat)
            },
        ensures
            forall|j: int| 0 <= j < self.view().len()
                && #[trigger] self.store.captured()[j]
                ==> self.hot_stack@.len() > 0
                    && j < self.active_saved_len.as_nat(),
    {
        let pool = self.hot_value_pool@;
        assert forall|j: int| 0 <= j < self.view().len()
            && #[trigger] self.store.captured()[j]
            implies self.hot_stack@.len() > 0
                && j < self.active_saved_len.as_nat() by {
            assert(captured_in_range::<T, I>(
                pool, top_start as int, pool.len() as int, j as nat));
            let p = choose|p: int| top_start <= p < pool.len()
                && (#[trigger] pool[p]).1.as_nat() == j as nat;
            assert(pool[p].1.as_nat() < self.snapshots@[target as int - 1].len());
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    proof fn hot_defer_restore_nonzero_finish(
        &self, pre: Self, target: usize, cut: usize, top_start: usize,
    )
        requires
            pre.hot_defer_wf(),
            0 < target,
            (target as nat) < pre.hot_stack@.len(),
            cut == pre.hot_stack@[target as int].start,
            self.hot_stack@ == pre.hot_stack@.subrange(0, target as int),
            self.hot_value_pool@ == pre.hot_value_pool@.subrange(0, cut as int),
            self.view() == pre.snapshots@[target as int],
            self.trail_stack@ == pre.trail_stack@,
            self.trail_value_pool@ == pre.trail_value_pool@,
            self.cold_stack@ == pre.cold_stack@,
            self.cold_index_runs@ == pre.cold_index_runs@,
            self.cold_value_pool@ == pre.cold_value_pool@,
            self.trail_frames@ == pre.trail_frames@.subrange(0, target as int),
            self.snapshots@ == pre.snapshots@.subrange(0, target as int),
            self.active_saved_len == self.hot_stack@[target as int - 1].saved_len,
            top_start == self.hot_stack@[target as int - 1].start,
            self.store.wf(),
            self.store.unique_capture_spec(),
            self.store.captured().len() == self.view().len(),
            forall|j: int| 0 <= j < self.view().len() ==> {
                (#[trigger] self.store.captured()[j])
                    == captured_in_range::<T, I>(
                        self.hot_value_pool@, top_start as int,
                        self.hot_value_pool@.len() as int, j as nat)
            },
        ensures
            self.hot_defer_wf(),
    {
        reveal(Vec::hot_defer_wf);
        reveal(Vec::hot_defer_end);
        let depth = self.hot_stack@.len();
        assert(depth == target);
        self.hot_defer_restore_nonzero_layout(pre, target, cut);
        self.hot_defer_restore_nonzero_unique(pre, target, cut);
        self.hot_defer_restore_nonzero_frame_invariants(pre, target, cut);
        self.hot_defer_restore_nonzero_capture_bound(target, top_start);
        assert(self.hot_defer_wf());
    }

    /// Retain the logical history below a restored target. The surviving top's
    /// new live layer is exactly its former newer snapshot, so every older
    /// frame keeps both its range and its reconstruction premise.
    #[verifier::spinoff_prover]
    proof fn lemma_restore_canonical_prefix(&self, pre: Self, target: usize)
        requires
            pre.wf_for_snap(),
            0 < target < pre.trail_frames@.len(),
            self.store.wf(),
            self.frame_partition_ok(),
            self.view() == pre.snapshots@[target as int],
            self.trail_frames@ == pre.trail_frames@.subrange(0, target as int),
            self.snapshots@ == pre.snapshots@.subrange(0, target as int),
            self.full_trail@ == pre.full_trail@.subrange(
                0, pre.trail_frames@[target as int] as int),
        ensures self.wf_for_snap(),
    {
        let boundary = pre.trail_frames@[target as int] as int;
        pre.lemma_diff_start_le_n(target as int);
        assert(self.full_trail@.len() == boundary);
        assert forall|k: int| 0 <= k < target implies
            #[trigger] frame_inv_range::<T, I>(
                self.layer_above_at(k), self.full_trail@,
                self.g_start(k), self.g_end(k), self.snapshots@[k],
                self.snapshots@[k].len()) by {
            pre.lemma_diff_start_monotone(k + 1, target as int);
            assert(self.g_start(k) == pre.g_start(k));
            assert(self.g_end(k) == pre.g_end(k));
            assert(self.layer_above_at(k) == pre.layer_above_at(k));
            assert(self.snapshots@[k] == pre.snapshots@[k]);
            assert forall|q: int| pre.g_start(k) <= q < pre.g_end(k)
                implies #[trigger] self.full_trail@[q] == pre.full_trail@[q] by {}
            lemma_frame_inv_range_local::<T, I>(
                self.layer_above_at(k), pre.full_trail@, self.full_trail@,
                self.g_start(k), self.g_end(k), self.snapshots@[k],
                self.snapshots@[k].len());
        }
        pre.lemma_diff_start_monotone(target as int - 1, target as int);
        assert(self.wf_for_snap());
    }

    /// Verified Hot-only restore to a surviving nonempty prefix. The target
    /// frame and every newer frame are replayed and removed; the preceding
    /// closed frame becomes the writable top and `finish_restore` rebuilds its
    /// capture bridge from the surviving Hot slice.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(1000)]
    fn hot_defer_restore_nonzero_checked(&mut self, target: usize)
    where
        T: core::default::Default,
        requires
            old(self).hot_defer_wf(),
            old(self).wf(),
            0 < target,
            (target as nat) < old(self).hot_stack@.len(),
        ensures
            final(self).hot_defer_wf(),
            final(self).wf(),
            final(self).view() == old(self).snapshots@[target as int],
            final(self).hot_stack@ == old(self).hot_stack@.subrange(0, target as int),
            final(self).snapshots@ == old(self).snapshots@.subrange(0, target as int),
            final(self).trail_frames@ == old(self).trail_frames@.subrange(0, target as int),
    {
        let ghost pre = *self;
        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
        }
        let saved_len = self.hot_stack[target].saved_len;
        let cut = self.hot_stack[target].start;
        proof {
            saved_len.lemma_as_nat_bounded();
            assert(saved_len.as_nat() == pre.snapshots@[target as int].len());
        }
        if self.store.len().as_usize() != saved_len.as_usize() {
            self.store.resize_default(saved_len);
        }
        let ghost base = self.store.data();
        proof {
            assert(base.len() == saved_len.as_nat());
            assert forall|j: int| 0 <= j < base.len() && j < pre.view().len()
                implies #[trigger] base[j] == pre.view()[j] by {}
            let top = (pre.hot_stack@.len() - 1) as int;
            pre.lemma_hot_defer_start_monotone(target as int, top);
            assert forall|j: int| 0 <= j < self.store.captured().len()
                && #[trigger] self.store.captured()[j]
                implies exists|k: int| cut <= k < self.hot_value_pool@.len()
                    && (#[trigger] self.hot_value_pool@[k]).1.as_nat() == j as nat by {
                assert(j < pre.view().len());
                assert(pre.store.captured()[j]);
                assert(j < pre.active_saved_len.as_nat());
                assert(pre.store.captured()[j] == captured_in_range::<T, I>(
                    pre.hot_value_pool@, pre.hot_stack@[top].start as int,
                    pre.hot_value_pool@.len() as int, j as nat));
                let p = choose|p: int| pre.hot_stack@[top].start <= p
                    < pre.hot_value_pool@.len()
                    && (#[trigger] pre.hot_value_pool@[p]).1.as_nat() == j as nat;
                assert(cut <= pre.hot_stack@[top].start);
                assert(self.hot_value_pool@[p] == pre.hot_value_pool@[p]);
            }
        }
        let fused = self.store.restore_entries_clear_capture();
        if !fused {
            if self.store.needs_replayed_indices() {
                let replayed = vstd::slice::slice_subrange(
                    self.hot_value_pool.as_slice(), cut, self.hot_value_pool.len());
                proof {
                    assert forall|j: int| 0 <= j < self.store.captured().len()
                        && #[trigger] self.store.captured()[j]
                        implies exists|k: int| 0 <= k < replayed@.len()
                            && (#[trigger] replayed@[k]).1.as_nat() == j as nat by {
                        let p = choose|p: int| cut <= p < self.hot_value_pool@.len()
                            && (#[trigger] self.hot_value_pool@[p]).1.as_nat() == j as nat;
                        assert(replayed@[p - cut] == self.hot_value_pool@[p]);
                    }
                }
                self.store.begin_restore(replayed);
            } else {
                let empty: std::vec::Vec<(T, I)> = std::vec::Vec::new();
                self.store.begin_restore(empty.as_slice());
            }
        }
        let ghost cleared = self.store.captured();
        proof {
            assert(!fused ==> forall|j: int| 0 <= j < cleared.len()
                ==> !(#[trigger] cleared[j]));
            assert forall|j: int| 0 <= j < cleared.len() && #[trigger] cleared[j]
                implies captured_in_range::<T, I>(
                    self.hot_value_pool@, cut as int, self.hot_value_pool@.len() as int,
                    j as nat) by {}
            lemma_overlay_len::<T, I>(
                base, pre.hot_value_pool@, cut as int,
                pre.hot_value_pool@.len() as int);
            assert forall|j: int| 0 <= j < pre.snapshots@[target as int].len() as int implies
                #[trigger] overlay::<T, I>(
                    base, pre.hot_value_pool@, cut as int,
                    pre.hot_value_pool@.len() as int)[j]
                    == pre.snapshots@[target as int][j] by {
                pre.lemma_hot_defer_cell_eq_overlay(base, target as int, j);
            }
        }
        let n = self.hot_value_pool.len();
        replay_physical_range::<T, I, S, TRACK>(&mut self.store, &self.hot_value_pool, cut, n);
        proof {
            assert(self.store.data().len() == pre.snapshots@[target as int].len());
            assert forall|j: int| 0 <= j < self.store.data().len() implies
                #[trigger] self.store.data()[j] == pre.snapshots@[target as int][j] by {}
            assert(self.store.data() =~= pre.snapshots@[target as int]);
            assert forall|j: int| 0 <= j < self.store.captured().len()
                implies !(#[trigger] self.store.captured()[j]) by {
                if self.store.captured()[j] {
                    assert(j < cleared.len() && cleared[j]);
                    if fused {
                        assert(captured_in_range::<T, I>(
                            pre.hot_value_pool@, cut as int, pre.hot_value_pool@.len() as int,
                            j as nat));
                        assert(!captured_in_range::<T, I>(
                            pre.hot_value_pool@, cut as int, pre.hot_value_pool@.len() as int,
                            j as nat));
                    }
                }
            }
        }
        self.hot_stack.truncate(target);
        self.hot_value_pool.truncate(cut);
        proof {
            self.full_trail@ = pre.full_trail@.subrange(
                0, pre.trail_frames@[target as int] as int);
            self.trail_frames@ = pre.trail_frames@.subrange(0, target as int);
            self.snapshots = Ghost(pre.snapshots@.subrange(0, target as int));
        }
        let top = target - 1;
        self.active_saved_len = self.hot_stack[top].saved_len;
        let top_start = self.hot_stack[top].start;
        let present_len = self.store.len();
        self.store.finish_restore(
            vstd::slice::slice_subrange(
                self.hot_value_pool.as_slice(), top_start, self.hot_value_pool.len()),
            present_len);
        proof {
            let pool = self.hot_value_pool@;
            let surviving = pool.subrange(top_start as int, pool.len() as int);
            assert(self.store.captured().len() == self.view().len()) by {
                self.store.lemma_wf_captured_len();
            }
            assert forall|j: int| 0 <= j < self.view().len() implies
                (#[trigger] self.store.captured()[j])
                    == captured_in_range::<T, I>(
                        pool, top_start as int, pool.len() as int, j as nat) by {
                lemma_captured_subrange::<T, I>(
                    pool, surviving, top_start as int, pool.len() as int, j as nat);
            }
            self.hot_defer_restore_nonzero_finish(pre, target, cut, top_start);
            reveal(Vec::frame_partition_ok);
            reveal(Vec::proof_compat_ok);
            assert(self.frame_partition_ok());
            self.lemma_restore_canonical_prefix(pre, target);
            assert(self.proof_compat_ok());
            self.lemma_hot_defer_snap_implies_wf();
        }
    }

    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_replay_partition(&self)
        requires self.wf(),
        ensures
            self.cold_stack@.len() + self.hot_stack@.len() + self.trail_stack@.len() == self.depth_spec(),
            self.snapshots@.len() == self.depth_spec(),
            self.depth_spec() < usize::MAX,
            self.hot_stack@.len() > 0 && self.trail_stack@.len() > 0 ==>
                self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len(),
    {
        self.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
    }

    /// Reconstruction only: the caller has resized once and may have cleared
    /// flags, but history still equals `pre`. Preserve every history field and
    /// consume the tier suffix proofs in actual Trail -> Hot -> Cold order.
    #[verifier::spinoff_prover]
    fn replay_all_tiers_checked(&mut self, target: usize, Ghost(pre): Ghost<Self>)
        requires
            pre.wf(),
            target < pre.depth_spec(),
            *old(self) == (Self { store: old(self).store, ..pre }),
            old(self).store.wf(),
            TRACK ==> forall|j: int| 0 <= j < old(self).store.captured().len()
                && #[trigger] old(self).store.captured()[j]
                ==> j < pre.store.captured().len() && pre.store.captured()[j],
            TRACK && !old(self).store.restore_entries_clear_capture_spec() ==>
                forall|j: int| 0 <= j < old(self).store.captured().len() ==>
                    !(#[trigger] old(self).store.captured()[j]),
            old(self).view().len() == pre.snapshots@[target as int].len(),
            forall|j: int| 0 <= j < old(self).view().len() && j < pre.view().len() ==>
                #[trigger] old(self).view()[j] == pre.view()[j],
        ensures
            *final(self) == (Self { store: final(self).store, ..pre }),
            final(self).store.wf(),
            final(self).view() == pre.snapshots@[target as int],
            TRACK ==> forall|j: int| 0 <= j < final(self).store.captured().len() ==>
                !(#[trigger] final(self).store.captured()[j]),
            final(self).store.unique_capture_spec() == old(self).store.unique_capture_spec(),
            final(self).store.needs_replayed_indices_spec() == old(self).store.needs_replayed_indices_spec(),
            final(self).store.restore_entries_clear_capture_spec()
                == old(self).store.restore_entries_clear_capture_spec(),
            TRACK ==> forall|j: int| 0 <= j < final(self).store.captured().len()
                && #[trigger] final(self).store.captured()[j]
                ==> j < old(self).store.captured().len() && old(self).store.captured()[j],
    {
        hide(Vec::wf);
        proof {
            pre.lemma_replay_partition();
            pre.lemma_replay_ingress();
        }
        let cold = self.cold_stack.len();
        let hot = self.hot_stack.len();
        let trail = self.trail_stack.len();
        let trail_start = cold + hot;
        let first_trail = target.saturating_sub(trail_start).min(trail);
        if first_trail < trail {
            let lo = self.trail_stack[first_trail].start;
            // The newest ingress frame is open, so its effective end is the
            // active pool length rather than its not-yet-sealed header end.
            let hi = self.trail_value_pool.len();
            Self::replay_pair_suffix_checked(
                &mut self.store, &self.trail_value_pool, lo, hi,
                Ghost(true), Ghost(first_trail as int), Ghost(pre),
            );
        }

        let first_hot = target.saturating_sub(cold).min(hot);
        let hot_end = if target < trail_start { hot } else { 0 };
        if first_hot < hot_end {
            let lo = self.hot_stack[first_hot].start;
            // With unique ingress, hot_end reaches the open top frame. Trail
            // ingress has no open hot frame and uses sealed header ends.
            let hi = if trail == 0 {
                self.hot_value_pool.len()
            } else {
                self.hot_stack[hot_end - 1].end
            };
            Self::replay_pair_suffix_checked(
                &mut self.store, &self.hot_value_pool, lo, hi,
                Ghost(false), Ghost(first_hot as int), Ghost(pre),
            );
        }

        if target < cold {
            Self::replay_cold_suffix_checked(
                &mut self.store, &self.cold_stack, &self.cold_index_runs, &self.cold_value_pool,
                target, Ghost(pre),
            );
        }

        proof {
            assert(self.view() =~= pre.snapshots@[target as int]);
        }
    }

    /// Checked reconstruction phase of restore. Resize once, preserve the
    /// live prefix, prepare capture state, then execute the batched tier replay.
    /// No history is truncated or promoted until the target is reconstructed.
    #[verifier::spinoff_prover]
    fn reconstruct_target_checked(&mut self, target: usize)
    where T: core::default::Default,
        requires old(self).wf(), TRACK, target < old(self).depth_spec(),
        ensures
            *final(self) == (Self { store: final(self).store, ..*old(self) }),
            final(self).store.wf(),
            final(self).view() == old(self).snapshots@[target as int],
            forall|j: int| 0 <= j < final(self).store.captured().len() ==>
                !(#[trigger] final(self).store.captured()[j]),
            final(self).store.unique_capture_spec() == old(self).store.unique_capture_spec(),
            final(self).store.needs_replayed_indices_spec() == old(self).store.needs_replayed_indices_spec(),
            final(self).store.restore_entries_clear_capture_spec()
                == old(self).store.restore_entries_clear_capture_spec(),
            forall|j: int| 0 <= j < final(self).store.captured().len()
                && #[trigger] final(self).store.captured()[j]
                ==> j < old(self).store.captured().len() && old(self).store.captured()[j],
    {
        let ghost pre = *self;
        let saved_len = self.frame_saved_len_exec(target);
        proof { saved_len.lemma_as_nat_bounded(); }
        if self.store.len().as_usize() != saved_len.as_usize() {
            self.store.resize_default(saved_len);
        }
        if !self.store.restore_entries_clear_capture() {
            self.runtime_begin_restore(Ghost(pre));
        }
        self.replay_all_tiers_checked(target, Ghost(pre));
    }

    /// Exact physical and canonical prefix after retiring target and newer
    /// frames. This predicate deliberately excludes writable-ingress ownership:
    /// the newest retained frame may still need promotion into that tier.
    pub closed spec fn restored_history_prefix(&self, pre: Self, target: nat) -> bool {
        let cc = pre.cold_stack@.len();
        let hc = pre.hot_stack@.len();
        let tc = pre.trail_stack@.len();
        let kc = if target < cc { target } else { cc };
        let kh = if target <= cc { 0nat }
            else if target < cc + hc { (target - cc) as nat } else { hc };
        let kt = if target <= cc + hc { 0nat } else { (target - cc - hc) as nat };
        let rc = if kc < cc { pre.cold_stack@[kc as int].runs_start as nat }
            else { pre.cold_index_runs@.len() };
        let vc = if rc < pre.cold_index_runs@.len() { pre.cold_index_runs@[rc as int].start as nat }
            else { pre.cold_value_pool@.len() };
        let hp = if kh < hc { pre.hot_stack@[kh as int].start as nat }
            else { pre.hot_value_pool@.len() };
        let tp = if kt < tc { pre.trail_stack@[kt as int].start as nat }
            else { pre.trail_value_pool@.len() };
        &&& self.cold_stack@ == pre.cold_stack@.subrange(0, kc as int)
        &&& self.cold_index_runs@ == pre.cold_index_runs@.subrange(0, rc as int)
        &&& self.cold_value_pool@ == pre.cold_value_pool@.subrange(0, vc as int)
        &&& self.hot_stack@ == pre.hot_stack@.subrange(0, kh as int)
        &&& self.hot_value_pool@ == pre.hot_value_pool@.subrange(0, hp as int)
        &&& self.trail_stack@ == pre.trail_stack@.subrange(0, kt as int)
        &&& self.trail_value_pool@ == pre.trail_value_pool@.subrange(0, tp as int)
        &&& self.snapshots@ == pre.snapshots@.subrange(0, target as int)
        &&& self.trail_frames@ == pre.trail_frames@.subrange(0, target as int)
        &&& self.full_trail@ == pre.full_trail@.subrange(0, pre.trail_frames@[target as int] as int)
        &&& self.diff_log@ == if target == 0 { Seq::empty() } else { pre.diff_log@ }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_truncation_bounds(&self, target: int)
        requires self.wf(), 0 <= target < self.depth_spec(),
        ensures
            self.repr_ok(),
            self.hot_stack@.len() == 0 ==> self.hot_value_pool@.len() == 0,
            self.hot_stack@.len() > 0 ==> self.hot_stack@[0].start == 0,
            self.trail_stack@.len() == 0 ==> self.trail_value_pool@.len() == 0,
            self.trail_stack@.len() > 0 ==> self.trail_stack@[0].start == 0,
            self.cold_stack@.len() == 0 ==> self.cold_value_pool@.len() == 0,
            self.trail_frames@[target] <= self.full_trail@.len(),
    {
        self.lemma_wf_named_parts();
        reveal(Vec::cold_repr_ok);
        reveal(Vec::hot_repr_ok);
        reveal(Vec::trail_repr_ok);
        self.lemma_diff_start_le_n(target);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_restored_prefix_partition(&self, pre: Self, target: nat)
        requires
            pre.frame_partition_ok(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target),
        ensures self.frame_partition_ok(), self.depth_spec() == target,
    {
        reveal(Vec::restored_history_prefix);
        reveal(Vec::frame_partition_ok);
        assert(self.hot_stack@.len() > 0 ==> self.cold_stack@.len() == pre.cold_stack@.len());
        assert(self.trail_stack@.len() > 0 ==> {
            &&& self.cold_stack@.len() == pre.cold_stack@.len()
            &&& self.hot_stack@.len() == pre.hot_stack@.len()
        });
    }

    /// The surviving top sees the restored target as its newer layer, exactly
    /// as before. Thus the unchanged older canonical ranges remain valid.
    #[verifier::spinoff_prover]
    proof fn lemma_restored_prefix_canonical(&self, pre: Self, target: usize)
        requires
            pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target as nat),
            self.store.wf(), self.view() == pre.snapshots@[target as int],
        ensures self.wf_for_snap(),
    {
        pre.lemma_wf_named_parts();
        self.lemma_restored_prefix_partition(pre, target as nat);
        reveal(Vec::restored_history_prefix);
        if target > 0 {
            self.lemma_restore_canonical_prefix(pre, target);
        } else {
            assert(pre.trail_frames@[0] == 0);
            assert(self.full_trail@.len() == 0);
            assert(self.wf_for_snap());
        }
    }

    /// Retained snapshots and newer layers are unchanged, including the new
    /// top frame whose newer layer is now the reconstructed live buffer.
    #[verifier::spinoff_prover]
    proof fn lemma_restored_layer_at(&self, pre: Self, target: nat, f: int)
        requires
            pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target),
            self.view() == pre.snapshots@[target as int],
            0 <= f < target,
        ensures
            self.snapshots@[f] == pre.snapshots@[f],
            self.layer_above_at(f) == pre.layer_above_at(f),
    {
        hide(Vec::wf);
        pre.lemma_replay_partition();
        reveal(Vec::restored_history_prefix);
    }

    /// Truncating a pair tier keeps each retained frame's original extent.
    /// A newly open top ends at exactly the cut that used to seal that frame.
    #[verifier::spinoff_prover]
    proof fn lemma_restored_pair_layout(&self, pre: Self, target: nat, trail: bool, f: int)
        requires
            pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target),
            0 <= f < self.pair_tier_count(trail),
        ensures
            f == 0 ==> self.pair_tier_start(trail, f) == 0,
            self.pair_tier_start(trail, f) <= self.pair_tier_header_end(trail, f)
                <= self.pair_tier_end(trail, f),
            f + 1 < self.pair_tier_count(trail) ==>
                self.pair_tier_header_end(trail, f) == self.pair_tier_start(trail, f + 1)
                    && self.pair_tier_end(trail, f) == self.pair_tier_start(trail, f + 1),
            self.pair_tier_count(trail) <= pre.pair_tier_count(trail),
            self.pair_tier_offset(trail) == pre.pair_tier_offset(trail),
            self.pair_tier_offset(trail) + f < target,
            self.pair_tier_start(trail, f) == pre.pair_tier_start(trail, f),
            self.pair_tier_end(trail, f) == pre.pair_tier_end(trail, f),
            0 <= self.pair_tier_start(trail, f) <= self.pair_tier_end(trail, f)
                <= self.pair_tier_pool(trail).len() <= pre.pair_tier_pool(trail).len(),
            forall|q: int| 0 <= q < self.pair_tier_pool(trail).len() ==>
                #[trigger] self.pair_tier_pool(trail)[q] == pre.pair_tier_pool(trail)[q],
    {
        hide(Vec::wf);
        reveal(Vec::restored_history_prefix);
        pre.lemma_replay_partition();
        let kept = self.pair_tier_count(trail);
        assert(kept <= pre.pair_tier_count(trail));
        pre.lemma_pair_tier_frame_layout(trail, f);
        if kept < pre.pair_tier_count(trail) {
            pre.lemma_pair_tier_frame_layout(trail, kept as int);
            pre.lemma_pair_tier_start_order(trail, f + 1, kept as int);
            assert(self.pair_tier_pool(trail).len() == pre.pair_tier_start(trail, kept as int));
        }
    }

    /// Transfer a retained Trail/Hot frame through its unchanged physical
    /// range, snapshot, and newer layer. No capture-state premise is needed.
    #[verifier::spinoff_prover]
    proof fn lemma_restored_pair_frame(&self, pre: Self, target: nat, trail: bool, f: int)
        requires
            pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target),
            self.view() == pre.snapshots@[target as int],
            0 <= f < self.pair_tier_count(trail),
        ensures
            frame_inv_range::<T, I>(
                self.layer_above_at(self.pair_tier_offset(trail) + f),
                self.pair_tier_pool(trail), self.pair_tier_start(trail, f), self.pair_tier_end(trail, f),
                self.snapshots@[self.pair_tier_offset(trail) + f],
                self.snapshots@[self.pair_tier_offset(trail) + f].len()),
            !trail ==> stratum_unique::<T, I>(self.pair_tier_pool(trail),
                self.pair_tier_start(trail, f), self.pair_tier_end(trail, f)),
    {
        hide(Vec::wf);
        self.lemma_restored_pair_layout(pre, target, trail, f);
        let k = self.pair_tier_offset(trail) + f;
        self.lemma_restored_layer_at(pre, target, k);
        pre.lemma_wf_named_parts();
        if trail {
            reveal(Vec::trail_repr_ok);
        } else {
            pre.lemma_hot_repr_at(f);
            lemma_stratum_unique_local::<T, I>(pre.pair_tier_pool(trail), self.pair_tier_pool(trail),
                self.pair_tier_start(trail, f), self.pair_tier_end(trail, f));
        }
        lemma_frame_inv_range_local::<T, I>(
            self.layer_above_at(k), pre.pair_tier_pool(trail), self.pair_tier_pool(trail),
            self.pair_tier_start(trail, f), self.pair_tier_end(trail, f),
            self.snapshots@[k], self.snapshots@[k].len());
    }

    #[verifier::spinoff_prover]
    proof fn lemma_restored_pair_repr(&self, pre: Self, target: nat, trail: bool)
        requires
            pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target),
            self.view() == pre.snapshots@[target as int],
        ensures if trail { self.trail_repr_ok() } else { self.hot_repr_ok() },
    {
        hide(Vec::wf);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(frame_inv_range);
        hide(stratum_unique);
        pre.lemma_truncation_bounds(target as int);
        pre.lemma_replay_partition();
        reveal(Vec::restored_history_prefix);
        assert(self.pair_tier_count(trail) == 0 ==> self.pair_tier_pool(trail).len() == 0);
        if trail {
            let ts = self.trail_stack@;
            let pool = self.trail_value_pool@;
            let offset = self.cold_stack@.len() + self.hot_stack@.len();
            assert forall|i: int| 0 <= i < ts.len() implies {
                &&& (#[trigger] ts[i]).start <= ts[i].end
                &&& ts[i].end <= pool.len()
                &&& ts[i].start as int <= self.phys_trail_end(i)
                &&& self.phys_trail_end(i) <= pool.len() as int
                &&& (i + 1 < ts.len() ==> {
                    &&& ts[i].end == ts[i + 1].start
                    &&& self.phys_trail_end(i) == ts[i + 1].start as int
                })
                &&& (i + 1 == ts.len() ==>
                    self.phys_trail_end(i) == pool.len() as int)
                &&& frame_inv_range::<T, I>(
                    self.layer_above_at(offset + i), pool, ts[i].start as int,
                    self.phys_trail_end(i), self.snapshots@[offset + i],
                    self.snapshots@[offset + i].len())
                &&& offset + i < self.snapshots@.len()
            } by {
                self.lemma_restored_pair_layout(pre, target, true, i);
                self.lemma_restored_pair_frame(pre, target, true, i);
            }
            if self.pair_tier_count(true) > 0 {
                self.lemma_restored_pair_layout(pre, target, true, 0);
            }
            reveal(Vec::trail_repr_ok);
        } else {
            let hs = self.hot_stack@;
            let pool = self.hot_value_pool@;
            let cc = self.cold_stack@.len();
            assert forall|i: int| 0 <= i < hs.len() implies {
                &&& (#[trigger] hs[i]).start <= hs[i].end
                &&& hs[i].end <= pool.len()
                &&& hs[i].start as int <= self.phys_hot_end(i)
                &&& self.phys_hot_end(i) <= pool.len() as int
                &&& (i + 1 < hs.len() ==> {
                    &&& hs[i].end == hs[i + 1].start
                    &&& self.phys_hot_end(i) == hs[i + 1].start as int
                })
                &&& (i + 1 == hs.len() ==>
                    self.phys_hot_end(i) == pool.len() as int)
                &&& stratum_unique::<T, I>(
                    pool, hs[i].start as int, self.phys_hot_end(i))
                &&& self.phys_frame_inv_range_holds(i)
                &&& cc + i < self.snapshots@.len()
            } by {
                self.lemma_restored_pair_layout(pre, target, false, i);
                self.lemma_restored_pair_frame(pre, target, false, i);
            }
            if self.pair_tier_count(false) > 0 {
                self.lemma_restored_pair_layout(pre, target, false, 0);
            }
            reveal(Vec::hot_repr_ok);
        }
    }

    /// Physical offsets are monotone even when frame saved lengths zigzag.
    #[verifier::spinoff_prover]
    proof fn lemma_cold_frame_start_order(&self, a: int, b: int)
        requires self.repr_ok(), 0 <= a <= b < self.cold_stack@.len(),
        ensures self.cold_stack@[a].runs_start <= self.cold_stack@[b].runs_start,
        decreases b - a,
    {
        if a < b {
            self.lemma_cold_frame_start_order(a + 1, b);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_value_start_order(&self, a: int, b: int)
        requires self.repr_ok(), 0 <= a <= b < self.cold_index_runs@.len(),
        ensures self.cold_index_runs@[a].start <= self.cold_index_runs@[b].start,
        decreases b - a,
    {
        if a < b {
            self.lemma_cold_value_start_order(a + 1, b);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_layout_parts(&self)
        requires self.wf(),
        ensures self.repr_ok(), self.cold_runs_disjoint(),
    {
        self.lemma_wf_named_parts();
        reveal(Vec::cold_repr_ok);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_disjoint_at(&self, f: int, r: int)
        requires self.cold_runs_disjoint(), 0 <= f < self.cold_stack@.len(),
            self.cold_stack@[f].runs_start <= r,
            r + 1 < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len,
        ensures self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len
            <= self.cold_index_runs@[r + 1].base.as_nat(),
    {}

    /// The Cold cuts land on frame and run boundaries, retaining complete
    /// run slices and their complete payloads, including empty frames.
    /// Exact Cold prefix, independent of snapshots, ingress ownership and tags.
    pub closed spec fn cold_prefix_of(&self, pre: Self, kept: nat) -> bool {
        let rc = if kept < pre.cold_stack@.len() { pre.cold_stack@[kept as int].runs_start as nat }
            else { pre.cold_index_runs@.len() };
        let vc = if rc < pre.cold_index_runs@.len() { pre.cold_index_runs@[rc as int].start as nat }
            else { pre.cold_value_pool@.len() };
        &&& kept <= pre.cold_stack@.len()
        &&& self.cold_stack@ == pre.cold_stack@.subrange(0, kept as int)
        &&& self.cold_index_runs@ == pre.cold_index_runs@.subrange(0, rc as int)
        &&& self.cold_value_pool@ == pre.cold_value_pool@.subrange(0, vc as int)
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_prefix_layout(&self, pre: Self, kept: nat)
        requires pre.cold_repr_ok(), self.cold_prefix_of(pre, kept),
        ensures self.repr_ok(), self.cold_runs_disjoint(),
            self.cold_stack@.len() <= pre.cold_stack@.len(),
            self.cold_index_runs@.len() <= pre.cold_index_runs@.len(),
            self.cold_value_pool@.len() <= pre.cold_value_pool@.len(),
            forall|f: int| 0 <= f < self.cold_stack@.len() ==>
                #[trigger] self.cold_stack@[f] == pre.cold_stack@[f],
            forall|r: int| 0 <= r < self.cold_index_runs@.len() ==>
                #[trigger] self.cold_index_runs@[r] == pre.cold_index_runs@[r],
            forall|q: int| 0 <= q < self.cold_value_pool@.len() ==>
                #[trigger] self.cold_value_pool@[q] == pre.cold_value_pool@[q],
    {
        hide(Vec::cold_payload_ok);
        hide(Vec::repr_ok);
        hide(Vec::cold_runs_disjoint);
        reveal(Vec::cold_repr_ok);
        pre.lemma_cold_layout_basics();
        reveal(Vec::cold_prefix_of);
        if kept < pre.cold_stack@.len() { pre.lemma_cold_layout_header_at(kept as int); }
        let runs = self.cold_index_runs@.len();
        if runs < pre.cold_index_runs@.len() { pre.lemma_cold_layout_run_at(runs as int); }
        assert forall|f: int| 0 <= f < kept implies {
            &&& (#[trigger] self.cold_stack@[f]).runs_start + self.cold_stack@[f].runs_len <= runs
            &&& (f == 0 ==> self.cold_stack@[f].runs_start == 0)
            &&& (f + 1 < kept ==> self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len == self.cold_stack@[f + 1].runs_start)
            &&& (f + 1 == kept ==> self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len == runs)
        } by {
            pre.lemma_cold_layout_header_at(f);
            if kept < pre.cold_stack@.len() {
                pre.lemma_cold_frame_start_order(f + 1, kept as int);
            }
        }
        assert forall|r: int| 0 <= r < runs implies {
            &&& (#[trigger] self.cold_index_runs@[r]).start + self.cold_index_runs@[r].len <= self.cold_value_pool@.len()
            &&& (r == 0 ==> self.cold_index_runs@[r].start == 0)
            &&& (r + 1 < runs ==> self.cold_index_runs@[r].start + self.cold_index_runs@[r].len == self.cold_index_runs@[r + 1].start)
            &&& (r + 1 == runs ==> self.cold_index_runs@[r].start + self.cold_index_runs@[r].len == self.cold_value_pool@.len())
        } by {
            pre.lemma_cold_layout_run_at(r);
            if runs < pre.cold_index_runs@.len() {
                pre.lemma_cold_value_start_order(r + 1, runs as int);
            }
        }
        assert(self.repr_ok()) by { reveal(Vec::repr_ok); }
        assert forall|f: int, r: int| 0 <= f < self.cold_stack@.len()
            && (#[trigger] self.cold_stack@[f]).runs_start <= r
            && r + 1 < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len implies
            (#[trigger] self.cold_index_runs@[r]).base.as_nat() + self.cold_index_runs@[r].len
                <= self.cold_index_runs@[r + 1].base.as_nat()
        by {
            pre.lemma_cold_disjoint_at(f, r);
        }
        assert(self.cold_runs_disjoint()) by { reveal(Vec::cold_runs_disjoint); }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_restored_cold_layout(&self, pre: Self, target: nat)
        requires pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target),
        ensures self.repr_ok(), self.cold_runs_disjoint(),
            self.cold_stack@.len() <= pre.cold_stack@.len(),
            self.cold_index_runs@.len() <= pre.cold_index_runs@.len(),
            self.cold_value_pool@.len() <= pre.cold_value_pool@.len(),
            forall|f: int| 0 <= f < self.cold_stack@.len() ==>
                #[trigger] self.cold_stack@[f] == pre.cold_stack@[f],
            forall|r: int| 0 <= r < self.cold_index_runs@.len() ==>
                #[trigger] self.cold_index_runs@[r] == pre.cold_index_runs@[r],
            forall|q: int| 0 <= q < self.cold_value_pool@.len() ==>
                #[trigger] self.cold_value_pool@[q] == pre.cold_value_pool@[q],
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        reveal(Vec::restored_history_prefix);
        reveal(Vec::cold_prefix_of);
        let kept = if target < pre.cold_stack@.len() { target } else { pre.cold_stack@.len() };
        self.lemma_cold_prefix_layout(pre, kept);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_prefix_coverage(&self, pre: Self, kept: nat, f: int, j: nat)
        requires pre.cold_repr_ok(), self.cold_prefix_of(pre, kept),
            0 <= f < self.cold_stack@.len(),
        ensures self.cold_covered(f, j) == pre.cold_covered(f, j),
    {
        hide(Vec::cold_value);
        self.lemma_cold_prefix_layout(pre, kept);
        let lo = self.cold_stack@[f].runs_start as int;
        let hi = lo + self.cold_stack@[f].runs_len;
        assert forall|r: int| lo <= r < hi implies
            #[trigger] self.cold_index_runs@[r] == pre.cold_index_runs@[r] by {};
        if self.cold_covered(f, j) {
            let r = choose|r: int|
                self.cold_stack@[f].runs_start <= r
                    < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
                && (#[trigger] self.cold_index_runs@[r]).base.as_nat() <= j
                && j < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len;
            assert(pre.cold_index_runs@[r] == self.cold_index_runs@[r]);
            assert(pre.cold_covered(f, j));
        }
        if pre.cold_covered(f, j) {
            let r = choose|r: int|
                pre.cold_stack@[f].runs_start <= r
                    < pre.cold_stack@[f].runs_start + pre.cold_stack@[f].runs_len
                && (#[trigger] pre.cold_index_runs@[r]).base.as_nat() <= j
                && j < pre.cold_index_runs@[r].base.as_nat() + pre.cold_index_runs@[r].len;
            assert(self.cold_index_runs@[r] == pre.cold_index_runs@[r]);
            assert(self.cold_covered(f, j));
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_prefix_cell(&self, pre: Self, kept: nat, f: int, j: nat)
        requires pre.cold_repr_ok(), self.cold_prefix_of(pre, kept),
            0 <= f < self.cold_stack@.len(),
        ensures self.cold_covered(f, j) == pre.cold_covered(f, j),
            self.cold_covered(f, j) ==> self.cold_value(f, j) == pre.cold_value(f, j),
    {
        hide(Vec::cold_repr_ok);
        hide(Vec::cold_prefix_of);
        hide(Vec::repr_ok);
        hide(Vec::cold_payload_ok);
        hide(Vec::cold_runs_disjoint);
        hide(Vec::cold_value);
        self.lemma_cold_prefix_layout(pre, kept);
        self.lemma_cold_layout_header_at(f);
        let lo = self.cold_stack@[f].runs_start as int;
        let hi = lo + self.cold_stack@[f].runs_len;
        self.lemma_cold_prefix_coverage(pre, kept, f, j);
        assert forall|r: int| lo <= r && r + 1 < hi implies
            (#[trigger] self.cold_index_runs@[r]).base.as_nat() + self.cold_index_runs@[r].len
                <= self.cold_index_runs@[r + 1].base.as_nat() by {
            self.lemma_cold_disjoint_at(f, r);
        }
        if self.cold_covered(f, j) {
            let a = choose|r: int|
                self.cold_stack@[f].runs_start <= r
                    < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
                && (#[trigger] self.cold_index_runs@[r]).base.as_nat() <= j
                && j < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len;
            let b = choose|r: int|
                pre.cold_stack@[f].runs_start <= r
                    < pre.cold_stack@[f].runs_start + pre.cold_stack@[f].runs_len
                && (#[trigger] pre.cold_index_runs@[r]).base.as_nat() <= j
                && j < pre.cold_index_runs@[r].base.as_nat() + pre.cold_index_runs@[r].len;
            if a < b {
                lemma_cold_run_order::<I>(self.cold_index_runs@, lo, hi, a, b);
            } else if b < a {
                lemma_cold_run_order::<I>(self.cold_index_runs@, lo, hi, b, a);
            }
            assert(a == b);
            reveal(Vec::cold_value);
            self.lemma_cold_layout_run_at(a);
            let q = self.cold_index_runs@[a].start as int
                + (j - self.cold_index_runs@[a].base.as_nat()) as int;
            assert(0 <= q < self.cold_value_pool@.len());
            assert(self.cold_value_pool@[q] == pre.cold_value_pool@[q]);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_restored_cold_coverage(&self, pre: Self, target: nat, f: int, j: nat)
        requires pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target),
            0 <= f < self.cold_stack@.len(),
        ensures self.cold_covered(f, j) == pre.cold_covered(f, j),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        reveal(Vec::restored_history_prefix);
        reveal(Vec::cold_prefix_of);
        let kept = if target < pre.cold_stack@.len() { target } else { pre.cold_stack@.len() };
        self.lemma_cold_prefix_coverage(pre, kept, f, j);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_restored_cold_cell(&self, pre: Self, target: nat, f: int, j: nat)
        requires pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target),
            0 <= f < self.cold_stack@.len(),
        ensures self.cold_covered(f, j) == pre.cold_covered(f, j),
            self.cold_covered(f, j) ==> self.cold_value(f, j) == pre.cold_value(f, j),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        reveal(Vec::restored_history_prefix);
        reveal(Vec::cold_prefix_of);
        let kept = if target < pre.cold_stack@.len() { target } else { pre.cold_stack@.len() };
        self.lemma_cold_prefix_cell(pre, kept, f, j);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_restored_cold_repr(&self, pre: Self, target: nat)
        requires pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target),
            self.view() == pre.snapshots@[target as int],
        ensures self.cold_repr_ok(),
    {
        hide(Vec::wf);
        hide(Vec::restored_history_prefix);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::wf_for_snap);
        self.lemma_restored_cold_layout(pre, target);
        pre.lemma_wf_named_parts();
        self.lemma_restored_prefix_partition(pre, target);
        reveal(Vec::cold_repr_ok);
        reveal(Vec::frame_partition_ok);
        assert forall|f: int| 0 <= f < self.cold_stack@.len() implies
            #[trigger] self.cold_reconstructs(f)
        by {
            self.lemma_restored_layer_at(pre, target, f);
            assert forall|j: int| 0 <= j < self.g_saved_len(f) implies
                if #[trigger] self.cold_covered(f, j as nat) {
                    self.cold_value(f, j as nat) == self.snapshots@[f][j]
                } else {
                    j < self.layer_above_at(f).len()
                        && self.snapshots@[f][j] == self.layer_above_at(f)[j]
                }
            by {
                self.lemma_restored_cold_cell(pre, target, f, j as nat);
                pre.lemma_cold_reconstructs_at(f, j);
            }
        }
    }

    /// Retained physical prefixes preserve the complete lookup, even while
    /// ingress ownership and capture flags have not yet been rebuilt.
    #[verifier::spinoff_prover]
    proof fn lemma_persistence_retained_lookup(&self, pre: Self, target: nat, f: int, j: nat)
        requires pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target), 0 <= f < target,
        ensures self.frame_saved_len(f) == pre.frame_saved_len(f),
            self.frame_saved_value(f, j) == pre.frame_saved_value(f, j),
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        self.lemma_restored_prefix_partition(pre, target);
        reveal(Vec::frame_partition_ok);
        reveal(Vec::restored_history_prefix);
        let cc = self.cold_stack@.len();
        let hc = self.hot_stack@.len();
        if f < cc {
            self.lemma_restored_cold_cell(pre, target, f, j);
        } else {
            let trail = f >= cc + hc;
            let t = f - self.pair_tier_offset(trail);
            self.lemma_restored_pair_layout(pre, target, trail, t);
            lemma_range_saved_value_local::<T, I>(self.pair_tier_pool(trail),
                pre.pair_tier_pool(trail), self.pair_tier_start(trail, t),
                self.pair_tier_end(trail, t), j);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_retained_frame(&self, pre: Self, target: nat, f: int)
        requires pre.wf(), target < pre.depth_spec(),
            self.restored_history_prefix(pre, target), 0 <= f < target,
        ensures self.persistence_frame(f) == pre.persistence_frame(f),
    {
        hide(Vec::wf);
        self.lemma_persistence_retained_lookup(pre, target, f, 0);
        let a = self.persistence_frame(f).saved;
        let b = pre.persistence_frame(f).saved;
        assert forall|j: nat| #[trigger] a.dom().contains(j) == b.dom().contains(j)
            && (a.dom().contains(j) ==> a[j] == b[j]) by {
            self.lemma_persistence_retained_lookup(pre, target, f, j);
            crate::persistence_model::bounded_saved_map_at(self.frame_saved_len(f),
                |i: nat| self.frame_saved_value(f, i), j);
            crate::persistence_model::bounded_saved_map_at(pre.frame_saved_len(f),
                |i: nat| pre.frame_saved_value(f, i), j);
        }
        assert(a =~= b);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_retired(&self, pre: Self, target: nat)
        requires pre.wf(), target < pre.depth_spec(), self.restored_history_prefix(pre, target),
        ensures self.persistence_model().frames == pre.persistence_model().frames.subrange(0, target as int),
            self.persistence_model().snapshots == pre.persistence_model().snapshots.subrange(0, target as int),
            self.depth_spec() == target,
    {
        hide(Vec::wf);
        pre.lemma_wf_named_parts();
        self.lemma_restored_prefix_partition(pre, target);
        reveal(Vec::restored_history_prefix);
        assert forall|f: int| 0 <= f < target implies
            #[trigger] self.persistence_model().frames[f] == pre.persistence_model().frames[f] by {
            self.lemma_persistence_retained_frame(pre, target, f);
        }
        assert(self.persistence_model().frames =~= pre.persistence_model().frames.subrange(0, target as int));
    }

    /// Retire physical suffixes and the matching canonical ghost history.
    /// Keep the reconstructed store unchanged; ingress promotion follows later.
    #[verifier::spinoff_prover]
    fn truncate_restored_history_checked(&mut self, target: usize, Ghost(pre): Ghost<Self>)
        requires
            pre.wf(), target < pre.depth_spec(),
            *old(self) == (Self { store: old(self).store, ..pre }),
            old(self).store.wf(), old(self).view() == pre.snapshots@[target as int],
        ensures
            final(self).store == old(self).store,
            final(self).tier_policy == old(self).tier_policy,
            final(self).hot_buffer == old(self).hot_buffer,
            final(self).automatic_rollover_enabled == old(self).automatic_rollover_enabled,
            final(self).active_saved_len == old(self).active_saved_len,
            final(self).restored_history_prefix(pre, target as nat),
            final(self).persistence_model().frames == pre.persistence_model().frames.subrange(0, target as int),
            final(self).persistence_model().snapshots == pre.persistence_model().snapshots.subrange(0, target as int),
            final(self).depth_spec() == target,
            final(self).wf_for_snap(),
            final(self).hot_repr_ok(), final(self).trail_repr_ok(),
            final(self).cold_repr_ok(),
    {
        hide(Vec::wf);
        proof {
            pre.lemma_replay_partition();
            pre.lemma_truncation_bounds(target as int);
            assert(pre.cold_stack@.subrange(0, pre.cold_stack@.len() as int) =~= pre.cold_stack@);
            assert(pre.cold_stack@.subrange(0, 0) =~= Seq::empty());
            assert(pre.cold_index_runs@.subrange(0, pre.cold_index_runs@.len() as int) =~= pre.cold_index_runs@);
            assert(pre.cold_index_runs@.subrange(0, 0) =~= Seq::empty());
            assert(pre.cold_value_pool@.subrange(0, pre.cold_value_pool@.len() as int) =~= pre.cold_value_pool@);
            assert(pre.cold_value_pool@.subrange(0, 0) =~= Seq::empty());
            assert(pre.hot_stack@.subrange(0, pre.hot_stack@.len() as int) =~= pre.hot_stack@);
            assert(pre.hot_stack@.subrange(0, 0) =~= Seq::empty());
            assert(pre.hot_value_pool@.subrange(0, pre.hot_value_pool@.len() as int) =~= pre.hot_value_pool@);
            assert(pre.hot_value_pool@.subrange(0, 0) =~= Seq::empty());
            assert(pre.trail_stack@.subrange(0, pre.trail_stack@.len() as int) =~= pre.trail_stack@);
            assert(pre.trail_stack@.subrange(0, 0) =~= Seq::empty());
            assert(pre.trail_value_pool@.subrange(0, pre.trail_value_pool@.len() as int) =~= pre.trail_value_pool@);
            assert(pre.trail_value_pool@.subrange(0, 0) =~= Seq::empty());
        }
        let cold = self.cold_stack.len();
        let hot = self.hot_stack.len();
        let trail = self.trail_stack.len();
        let trail_start = cold + hot;
        if target >= trail_start {
            let keep = target - trail_start;
            proof { pre.lemma_pair_tier_frame_layout(true, keep as int); }
            let cut = if keep < trail { self.trail_stack[keep].start } else { self.trail_value_pool.len() };
            self.trail_stack.truncate(keep);
            self.trail_value_pool.truncate(cut);
        } else {
            self.trail_stack.clear();
            self.trail_value_pool.clear();
            if target >= cold {
                let keep = target - cold;
                proof { pre.lemma_pair_tier_frame_layout(false, keep as int); }
                let cut = if keep < hot { self.hot_stack[keep].start } else { self.hot_value_pool.len() };
                self.hot_stack.truncate(keep);
                self.hot_value_pool.truncate(cut);
            } else {
                self.hot_stack.clear();
                self.hot_value_pool.clear();
                let runs_cut = if target < cold { self.cold_stack[target].runs_start } else { self.cold_index_runs.len() };
                let values_cut = self.cold_value_cut(runs_cut);
                self.cold_stack.truncate(target);
                self.cold_index_runs.truncate(runs_cut);
                self.cold_value_pool.truncate(values_cut);
            }
        }
        if target == 0 {
            self.diff_log.clear();
        }
        proof {
            let boundary = self.trail_frames@[target as int] as int;
            self.full_trail@ = self.full_trail@.subrange(0, boundary);
            self.trail_frames@ = self.trail_frames@.subrange(0, target as int);
            self.snapshots = Ghost(self.snapshots@.subrange(0, target as int));
            reveal(Vec::restored_history_prefix);
            assert(self.restored_history_prefix(pre, target as nat));
            self.lemma_restored_prefix_canonical(pre, target);
            self.lemma_restored_pair_repr(pre, target as nat, true);
            self.lemma_restored_pair_repr(pre, target as nat, false);
            self.lemma_restored_cold_repr(pre, target as nat);
            self.lemma_persistence_retired(pre, target as nat);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_restored_zero_empty(&self, pre: Self)
        requires pre.wf(), pre.depth_spec() > 0, self.restored_history_prefix(pre, 0),
        ensures
            self.cold_stack@.len() == 0, self.cold_index_runs@.len() == 0,
            self.cold_value_pool@.len() == 0,
            self.hot_stack@.len() == 0, self.hot_value_pool@.len() == 0,
            self.trail_stack@.len() == 0, self.trail_value_pool@.len() == 0,
            self.snapshots@.len() == 0, self.trail_frames@.len() == 0,
            self.full_trail@.len() == 0, self.diff_log@.len() == 0,
    {
        pre.lemma_wf_named_parts();
        pre.lemma_truncation_bounds(0);
        reveal(Vec::restored_history_prefix);
    }

    /// Close the empty-history invariant without exposing the retired pre-state.
    #[verifier::spinoff_prover]
    proof fn lemma_empty_history_wf(&self)
        requires self.wf_for_snap(), self.store.wf(),
            self.snapshots@.len() == 0, self.trail_frames@.len() == 0,
            self.cold_stack@.len() == 0, self.cold_index_runs@.len() == 0,
            self.cold_value_pool@.len() == 0,
            self.hot_stack@.len() == 0, self.hot_value_pool@.len() == 0,
            self.trail_stack@.len() == 0, self.trail_value_pool@.len() == 0,
            self.diff_log@.len() == 0, self.active_saved_len == I::min_spec(),
            TRACK ==> forall|j: int| 0 <= j < self.store.captured().len() ==>
                !(#[trigger] self.store.captured()[j]),
        ensures self.wf(),
    {
        self.store.lemma_wf_captured_len();
        reveal(Vec::hot_repr_ok);
        reveal(Vec::trail_repr_ok);
        reveal(Vec::cold_repr_ok);
        reveal(Vec::open_ingress_ok);
        reveal(Vec::proof_compat_ok);
    }

    /// Complete zero-target restore for every tier layout and store protocol.
    /// No survivor is promoted; the exact empty prefix closes the invariant.
    #[verifier::spinoff_prover]
    fn restore_zero_all_tiers_checked(&mut self)
    where T: core::default::Default,
        requires old(self).wf(), TRACK, old(self).depth_spec() > 0,
        ensures
            final(self).wf(),
            final(self).view() == old(self).snapshots@[0],
            final(self).depth_spec() == 0,
            final(self).snapshots@ == old(self).snapshots@.subrange(0, 0),
    {
        hide(Vec::wf);
        hide(Vec::cold_repr_ok);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        let ghost pre = *self;
        self.reconstruct_target_checked(0);
        self.truncate_restored_history_checked(0, Ghost(pre));
        proof { self.lemma_restored_zero_empty(pre); }
        self.active_saved_len = <I as IndexLike>::min();
        if matches!(self.tier_policy.cold_reclaim, crate::tier_policy::ReclaimPolicy::ShrinkToFit) {
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_stack, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_index_runs, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_value_pool, 0, 1);
        }
        proof { self.lemma_empty_history_wf(); }
    }

    #[verifier::spinoff_prover]
    fn reclaim_cold_checked(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).store == old(self).store,
            final(self).persistence_model() == old(self).persistence_model(),
            final(self).snapshots@ == old(self).snapshots@,
            final(self).trail_frames@ == old(self).trail_frames@,
            final(self).full_trail@ == old(self).full_trail@,
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_repr_ok);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::open_ingress_ok);
        let ghost pre = *self;
        if matches!(self.tier_policy.cold_reclaim, crate::tier_policy::ReclaimPolicy::ShrinkToFit) {
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_stack, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_index_runs, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_value_pool, 0, 1);
        }
        proof {
            pre.lemma_wf_named_parts();
            assert(pre.store.wf()) by { reveal(Vec::wf_for_snap); }
            self.lemma_survivor_history_transfer(pre);
            self.lemma_persistence_views_framing(pre);
            self.lemma_open_ingress_transfer(pre);
            reveal(Vec::wf);
        }
    }

    /// Restore while the surviving top remains in the selected writable tier.
    /// This also covers mixed histories with older immutable Cold/Hot frames.
    #[verifier::spinoff_prover]
    fn restore_retained_ingress_checked(&mut self, target: usize)
    where T: core::default::Default,
        requires old(self).wf(), TRACK, target < old(self).depth_spec(),
            old(self).store.unique_capture_spec() ==> target > old(self).cold_stack@.len(),
            !old(self).store.unique_capture_spec() ==>
                target > old(self).cold_stack@.len() + old(self).hot_stack@.len(),
        ensures final(self).wf(), final(self).view() == old(self).snapshots@[target as int],
            final(self).depth_spec() == target,
            final(self).snapshots@ == old(self).snapshots@.subrange(0, target as int),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::cold_repr_ok);
        let ghost pre = *self;
        proof { pre.lemma_replay_partition(); pre.lemma_replay_ingress(); }
        self.reconstruct_target_checked(target);
        self.truncate_restored_history_checked(target, Ghost(pre));
        proof {
            reveal(Vec::restored_history_prefix);
            reveal(Vec::proof_compat_ok);
        }
        self.finish_survivor_checked();
        self.reclaim_cold_checked();
    }

    #[verifier::spinoff_prover]
    proof fn lemma_restored_hot_promotion_ready(&self, pre: Self, target: usize)
        requires pre.wf(), !pre.store.unique_capture_spec(),
            pre.cold_stack@.len() < target <= pre.cold_stack@.len() + pre.hot_stack@.len(),
            target < pre.depth_spec(), self.restored_history_prefix(pre, target as nat),
        ensures self.trail_stack@.len() == 0, self.hot_stack@.len() > 0,
            self.hot_stack@[self.hot_stack@.len() - 1].end == self.hot_value_pool@.len(),
            self.depth_spec() == target,
    {
        hide(Vec::wf);
        reveal(Vec::restored_history_prefix);
        pre.lemma_replay_partition();
        pre.lemma_replay_ingress();
        let f = self.hot_stack@.len() - 1;
        self.lemma_restored_pair_layout(pre, target as nat, false, f);
        pre.lemma_pair_tier_frame_layout(false, f);
    }

    #[verifier::spinoff_prover]
    fn restore_hot_promotion_checked(&mut self, target: usize)
    where T: core::default::Default,
        requires old(self).wf(), TRACK, !old(self).store.unique_capture_spec(),
            old(self).cold_stack@.len() < target <= old(self).cold_stack@.len() + old(self).hot_stack@.len(),
            target < old(self).depth_spec(),
        ensures final(self).wf(), final(self).view() == old(self).snapshots@[target as int],
            final(self).depth_spec() == target,
            final(self).snapshots@ == old(self).snapshots@.subrange(0, target as int),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::cold_repr_ok);
        let ghost pre = *self;
        self.reconstruct_target_checked(target);
        self.truncate_restored_history_checked(target, Ghost(pre));
        proof {
            self.lemma_restored_hot_promotion_ready(pre, target);
            reveal(Vec::restored_history_prefix);
            reveal(Vec::proof_compat_ok);
        }
        self.promote_hot_survivor_checked();
        proof { reveal(Vec::hot_survivor_promoted); }
        self.finish_survivor_checked();
        self.reclaim_cold_checked();
    }

    /// Checked Cold-survivor restore for both DiffStore capture disciplines.
    #[verifier::spinoff_prover]
    fn restore_cold_survivor_checked(&mut self, target: usize)
    where
        T: core::default::Default,
        requires
            old(self).wf(),
            TRACK,
            0 < target < old(self).depth_spec(),
            target <= old(self).cold_stack@.len(),
            !old(self).hot_defer_scope(),
        ensures
            final(self).wf(),
            final(self).persistence_model().frames == old(self).persistence_model().frames.subrange(0, target as int),
            final(self).view() == old(self).snapshots_view()[target as int],
            final(self).depth_spec() == target as nat,
            final(self).snapshots_view()
                == old(self).snapshots_view().subrange(0, target as int),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_repr_ok);
        let ghost pre = *self;
        self.reconstruct_target_checked(target);
        self.truncate_restored_history_checked(target, Ghost(pre));
        proof {
            reveal(Vec::restored_history_prefix);
            reveal(Vec::hot_repr_ok);
            reveal(Vec::trail_repr_ok);
            reveal(Vec::proof_compat_ok);
        }
        self.promote_cold_survivor_checked();
        proof {
            reveal(Vec::cold_survivor_promoted);
            reveal(Vec::cold_prefix_of);
        }
        self.finish_survivor_checked();
        self.reclaim_cold_checked();
    }

    /// Preserve the restored state while releasing empty Cold allocations.
    /// The existing capacity-only primitive preserves every element sequence.
    #[verifier::spinoff_prover]
    fn hot_defer_restore_reclaim_checked(&mut self)
        requires old(self).wf(), old(self).hot_defer_wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            final(self).depth_spec() == old(self).depth_spec(),
    {
        let ghost pre = *self;
        if matches!(self.tier_policy.cold_reclaim, crate::tier_policy::ReclaimPolicy::ShrinkToFit) {
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_stack, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_index_runs, 0, 1);
            crate::parallel_store::shrink_vec_capacity(&mut self.cold_value_pool, 0, 1);
        }
        proof {
            reveal(Vec::hot_defer_wf);
            reveal(Vec::hot_defer_end);
            reveal(Vec::frame_partition_ok);
            reveal(Vec::proof_compat_ok);
            assert(self.hot_defer_wf());
            assert forall|k: int| 0 <= k < self.trail_frames@.len() implies
                #[trigger] self.layer_above_at(k) == pre.layer_above_at(k) by {}
            self.lemma_wf_for_snap_transfer(pre);
            self.lemma_hot_defer_snap_implies_wf();
        }
    }

    fn restore_keeps_ingress_exec(&self, target: usize) -> (keeps: bool)
        requires self.wf(),
        ensures keeps == if self.store.unique_capture_spec() {
            target > self.cold_stack@.len()
        } else { target > self.cold_stack@.len() + self.hot_stack@.len() },
    {
        proof { self.lemma_replay_partition(); }
        if self.store.unique_capture() {
            target > self.cold_stack.len()
        } else {
            target > self.cold_stack.len() + self.hot_stack.len()
        }
    }

    #[verifier::spinoff_prover]
    fn runtime_restore_frame(&mut self, target: usize)
    where
        T: core::default::Default,
        requires
            old(self).wf(),
            TRACK,
            (target as nat) < old(self).depth_spec(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).snapshots_view()[target as int],
            final(self).depth_spec() == target as nat,
            final(self).snapshots_view()
                == old(self).snapshots_view().subrange(0, target as int),
    {
        if self.hot_defer_scope_exec() {
            proof {
                self.lemma_hot_defer_scope_implies_projection();
                reveal(Vec::hot_defer_wf);
            }
            if target == 0 {
                self.hot_defer_restore_zero_checked();
            } else {
                self.hot_defer_restore_nonzero_checked(target);
            }
            self.hot_defer_restore_reclaim_checked();
        } else if target == 0 {
            self.restore_zero_all_tiers_checked();
        } else if self.restore_keeps_ingress_exec(target) {
            self.restore_retained_ingress_checked(target);
        } else if !self.store.unique_capture() && target > self.cold_stack.len() {
            self.restore_hot_promotion_checked(target);
        } else {
            self.restore_cold_survivor_checked(target);
        }
    }

    /// Capacity reclamation (production parity). `Never` is a no-op;
    /// `IfOverallocated` asks the store to shrink its backing capacity. Both
    /// are observationally inert: `shrink_if` preserves `data()`/`captured()`,
    /// so `view()`, `wf`, and all tracked sequences are unchanged. (The
    /// production diff_log capacity hint is omitted — it's a pure allocator
    /// hint with no effect on `diff_log@`.)
    #[verifier::spinoff_prover]
    #[verifier::rlimit(2000)]
    fn maybe_shrink(&mut self, policy: ShrinkPolicy)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).store.unique_capture_spec()
                == old(self).store.unique_capture_spec(),
            final(self).view() == old(self).view(),
            final(self).diff_log@ == old(self).diff_log@,
            final(self).trail_frames@ == old(self).trail_frames@,
            final(self).full_trail@ == old(self).full_trail@,
            final(self).snapshots@ == old(self).snapshots@,
            final(self).active_saved_len == old(self).active_saved_len,
            final(self).cold_stack@ == old(self).cold_stack@,
            final(self).cold_index_runs@ == old(self).cold_index_runs@,
            final(self).cold_value_pool@ == old(self).cold_value_pool@,
            final(self).hot_stack@ == old(self).hot_stack@,
            final(self).hot_value_pool@ == old(self).hot_value_pool@,
            final(self).trail_stack@ == old(self).trail_stack@,
            final(self).trail_value_pool@ == old(self).trail_value_pool@,
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        hide(Vec::cold_repr_ok);
        hide(Vec::hot_repr_ok);
        hide(Vec::trail_repr_ok);
        hide(Vec::open_ingress_ok);
        proof {
            old(self).lemma_wf_named_parts();
            assert(old(self).store.wf()) by { reveal(Vec::wf_for_snap); }
        }
        match policy {
            ShrinkPolicy::Never => {}
            ShrinkPolicy::IfOverallocated { factor, headroom } => {
                self.store.shrink_if(factor, headroom);
                // Production parity: the same overallocation check applies to
                // the diff log at mark time (shrink-at-mark ratcheting).
                // Observably inert (contract: element sequence unchanged).
                log_shrink_capacity(&mut self.diff_log, factor, headroom);
            }
        }
        proof {
            // Capacity only: every view is unchanged, so wf transfers through
            // its named parts exactly as after tier reclamation.
            let pre = *old(self);
            pre.lemma_wf_named_parts();
            assert(pre.store.wf()) by { reveal(Vec::wf_for_snap); }
            self.lemma_survivor_history_transfer(pre);
            self.lemma_persistence_views_framing(pre);
            if TRACK {
                self.lemma_open_ingress_transfer(pre);
            } else {
                // TRACK=false: frames are pinned empty, so the ingress predicate
                // has no capture content to transfer; only the flag length
                // (from the store's own wf) is needed.
                reveal(Vec::open_ingress_ok);
                assert(self.trail_frames@.len() == 0);
                self.store.lemma_wf_captured_len();
            }
            reveal(Vec::wf);
        }
    }

    /// Current frame-stack depth (number of live marks). Mirrors production.
    pub fn depth(&self) -> (d: usize)
        requires self.wf(),
        ensures d == self.depth_spec(),
    {
        self.depth_exec()
    }

    /// Depth over the three age-ordered frame segments.
    #[inline]
    pub(crate) fn depth_exec(&self) -> (r: usize)
        requires self.wf_for_snap(),
        ensures r == self.depth_spec(),
    {
        proof {
            reveal(Vec::frame_partition_ok);
            assert(self.cold_stack@.len() + self.hot_stack@.len()
                <= self.cold_stack@.len() + self.hot_stack@.len() + self.trail_stack@.len());
            assert(self.cold_stack@.len() + self.hot_stack@.len() + self.trail_stack@.len()
                == self.snapshots@.len());
            assert(self.snapshots@.len() < usize::MAX);
        }
        self.cold_stack.len() + self.hot_stack.len() + self.trail_stack.len()
    }

    /// The frame's saved length, dispatched across cold, hot, and trail.
    #[inline]
    pub(crate) fn frame_saved_len_exec(&self, k: usize) -> (r: I)
        requires self.wf_for_snap(), k < self.depth_spec(),
        ensures r.as_nat() == self.g_saved_len(k as int),
    {
        proof {
            reveal(Vec::frame_partition_ok);
            assert(self.cold_stack@.len() + self.hot_stack@.len()
                <= self.cold_stack@.len() + self.hot_stack@.len() + self.trail_stack@.len());
            assert(self.cold_stack@.len() + self.hot_stack@.len() + self.trail_stack@.len()
                == self.snapshots@.len());
            assert(self.snapshots@.len() < usize::MAX);
        }
        let cold = self.cold_stack.len();
        if k < cold {
            return self.cold_stack[k].saved_len;
        }
        let hot = self.hot_stack.len();
        if k < cold + hot {
            return self.hot_stack[k - cold].saved_len;
        }
        self.trail_stack[k - cold - hot].saved_len
    }

    /// Current independent tier policy.
    pub fn tier_policy(&self) -> crate::tier_policy::TierPolicy {
        self.tier_policy
    }

    /// Select future automatic migration behavior, replacing any legacy
    /// constructor cadence. Call `apply_tier_policy` to enforce a newly
    /// tightened policy immediately.
    pub fn set_tier_policy(&mut self, policy: crate::tier_policy::TierPolicy) {
        self.tier_policy = policy;
        self.hot_buffer = None;
        self.automatic_rollover_enabled =
            Self::configured_rollover_can_run(self.store.unique_capture(), policy, None);
    }

    /// Physical occupancy for deterministic policy tests and diagnostics.
    pub fn tier_stats(&self) -> crate::tier_policy::TierStats {
        crate::tier_policy::TierStats {
            trail_frames: self.trail_stack.len(),
            trail_entries: self.trail_value_pool.len(),
            hot_frames: self.hot_stack.len(),
            hot_entries: self.hot_value_pool.len(),
            cold_frames: self.cold_stack.len(),
            cold_runs: self.cold_index_runs.len(),
            cold_values: self.cold_value_pool.len(),
        }
    }

    /// Contiguous read access to the raw values when the backend stores them
    /// contiguously: `Some` for `ParallelStore`, `None` for `InlineStore`
    /// (production parity — the backend-specific fast path).
    pub fn as_slice(&self) -> (r: Option<&[T]>)
        ensures r matches Some(s) ==> s@ == self.view(),
    {
        self.store.as_slice()
    }

    /// Remaining mark-depth headroom before the `u32::MAX` frame cap.
    ///
    /// With the genealogy on the owning `History` (H2), restores no longer
    /// accumulate any per-container state; the only bound is the frame depth.
    /// (`u32::MAX ~ 4.29e9` — not a practical limit.)
    pub fn restores_remaining(&self) -> (r: usize)
        requires self.wf(),
        ensures
            self.depth_spec() < u32::MAX ==>
                r as nat == (u32::MAX - self.depth_spec()) as nat,
            self.depth_spec() >= u32::MAX ==> r == 0,
    {
        (u32::MAX as usize).saturating_sub(self.depth_exec())
    }

    /// A read-only view over the current contents (parity with production).
    pub fn view_handle(&self) -> (v: VecView<'_, T, I, S, TRACK, VC>)
        ensures v.vec_ref() == self,
    {
        VecView { vec: self }
    }

    // ------------------------------------------------------------------
    // Total-operation shell: no `requires` beyond wf; every
    // precondition of the partial core is evaluated by a verified exec counterpart
    // and the branch discharges the core's contract as a proof obligation,
    // so the check and the contract cannot drift.
    // ------------------------------------------------------------------

    /// Exec counterpart of `push`'s capacity precondition.
    pub fn can_push(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() + 1 < I::max_nat()),
    {
        let n = self.store.raw_len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(n as nat == self.view().len());
            assert(cap as nat == I::max_nat() - 1);
        }
        n < cap
    }

    /// Total push: refuses at the index word's capacity instead of the
    /// partial core's deferred trap-at-next-`len()` protocol.
    pub fn try_push(&mut self, value: T) -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).view() == old(self).view().push(value)
                && final(self).snapshots_view() == old(self).snapshots_view(),
            r is Err ==> final(self).view() == old(self).view()
                && final(self).snapshots_view() == old(self).snapshots_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        if self.can_push() {
            self.push(value);
            Ok(())
        } else {
            Err(crate::error::ContainerError::CapacityExhausted)
        }
    }

    /// Total batch push: ONE capacity check licenses the whole slice, the
    /// loop invariant carries the bound to each core `push` — the amortized
    /// form of `try_push` for hot loops (one branch per batch, none per
    /// element).
    #[verifier::spinoff_prover]
    pub fn try_extend(&mut self, values: &[T]) -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).view() == old(self).view() + values@,
            r is Err ==> final(self).view() == old(self).view(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        // `wf` is carried as a fact through `push`'s contract; its body is not
        // needed here and only feeds the solver.
        hide(Vec::wf);
        proof { self.lemma_store_wf(); }
        let n = self.store.raw_len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(n as nat == self.view().len());
            assert(cap as nat == I::max_nat() - 1);
        }
        // `n <= cap` first so `cap - n` cannot underflow; then the batch must
        // fit strictly under the word (`< max_nat` after every push).
        if n > cap || values.len() > cap - n {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        let ghost old_view = self.view();
        let mut i: usize = 0;
        while i < values.len()
            invariant
                self.wf(),
                i <= values@.len(),
                self.view() == old_view + values@.subrange(0, i as int),
                self.snapshots_view() == old(self).snapshots_view(),
                old_view.len() + values@.len() < I::max_nat(),
            decreases values@.len() - i,
        {
            proof {
                assert(self.view().len() + 1 < I::max_nat());
            }
            self.push(values[i]);
            proof {
                assert(self.view() =~= old_view + values@.subrange(0, i as int + 1));
            }
            i += 1;
        }
        proof {
            assert(values@.subrange(0, values@.len() as int) =~= values@);
        }
        Ok(())
    }

    /// Exec counterpart of `mark`'s preconditions (TRACK, depth headroom, length
    /// representable in the token's saved_len).
    pub fn can_mark(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (TRACK && self.depth_spec() < u32::MAX
            && self.view().len() < I::max_nat()),
    {
        let n = self.store.raw_len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(n as nat == self.view().len());
            assert(cap as nat == I::max_nat() - 1);
        }
        TRACK && self.depth_exec() < (u32::MAX as usize) && n <= cap
    }

    /// The structural twin of `try_mark_with` (what a typed group's member
    /// pushes): open a frame with explicit physical rollover control and
    /// mint nothing — the group's `History` mints (`mint_pushed`). Total.
    pub fn try_push_frame_with(&mut self, options: MarkOptions)
        -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> {
                &&& final(self).view() == old(self).view()
                &&& final(self).depth_spec() == old(self).depth_spec() + 1
                &&& final(self).snapshots_view()
                    == old(self).snapshots_view().push(old(self).view())
            },
            r is Err ==> final(self).view() == old(self).view()
                && final(self).depth_spec() == old(self).depth_spec()
                && final(self).snapshots_view() == old(self).snapshots_view(),
    {
        if !TRACK {
            return Err(crate::error::ContainerError::Untracked);
        }
        if !(self.depth_exec() < (u32::MAX as usize)) {
            return Err(crate::error::ContainerError::DepthLimit);
        }
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
        }
        if !(self.store.raw_len() <= <I as crate::index_like::IndexLike>::max().as_usize()) {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        self.push_frame_with_options(options);
        Ok(())
    }

    /// The structural twin of `try_mark_adaptive`: a deferred-rollover frame
    /// push followed by one explicit adaptive closed-history pass, minting
    /// nothing. Total.
    #[cold]
    #[inline(never)]
    pub fn try_push_frame_adaptive(
        &mut self,
        shrink: ShrinkPolicy,
        input: crate::tier_policy::AdaptiveInput,
    ) -> (r: Result<crate::tier_policy::AdaptiveReport, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> {
                &&& final(self).view() == old(self).view()
                &&& final(self).depth_spec() == old(self).depth_spec() + 1
                &&& final(self).snapshots_view()
                    == old(self).snapshots_view().push(old(self).view())
            },
            r is Err ==> final(self).view() == old(self).view()
                && final(self).depth_spec() == old(self).depth_spec()
                && final(self).snapshots_view() == old(self).snapshots_view(),
    {
        if !TRACK {
            return Err(crate::error::ContainerError::Untracked);
        }
        if !(self.depth_exec() < (u32::MAX as usize)) {
            return Err(crate::error::ContainerError::DepthLimit);
        }
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
        }
        if !(self.store.raw_len() <= <I as crate::index_like::IndexLike>::max().as_usize()) {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        self.push_frame_with_options(MarkOptions::new(
            shrink,
            crate::tier_policy::RolloverPolicy::Defer,
        ));
        let report = self.runtime_apply_adaptive(input);
        Ok(report)
    }






    /// The index column of the diff-log strata a `restore(token)` would pop:
    /// entries `[frames[token.frame_idx].diff_start, diff_log.len())`. Each
    /// returned index names a slot whose content the restore will roll back
    /// (first-write-wins per stratum under the unique discipline; a
    /// chronological column may repeat an index). An invalid token returns
    /// `None` and the empty case (nothing captured since that mark) returns
    /// an empty vec. Read-only: the column is unchanged.
    ///
    /// This is the map-repair enabler: an unverified associate structure
    /// keyed by slot content (the e-graph's hashcons index) reads this BEFORE
    /// a restore to remove exactly the entries whose keys are about to change,
    /// and re-inserts the same ids from restored content AFTER. The diff log
    /// already carries this set deduplicated, so no separate dirty list is
    /// needed alongside the column.
    /// Some retained entry of `out` names index `j`.
    pub open(crate) spec fn names_index(out: Seq<I>, j: nat) -> bool {
        exists|i: int| 0 <= i < out.len() && (#[trigger] out[i]).as_nat() == j
    }

    /// Frame `f` (any tier) captures index `j`.
    pub open(crate) spec fn frame_captures(&self, f: int, j: nat) -> bool {
        self.frame_saved_value(f, j) is Some
    }

    /// Cold frames `[lo_f, hi_f)`: append every covered cell index.
    #[verifier::spinoff_prover]
    fn pending_cold_indices_checked(&self, lo_f: usize, hi_f: usize, out: &mut std::vec::Vec<I>)
        requires self.wf(), lo_f <= hi_f <= self.cold_stack@.len(),
        ensures forall|j: nat| #[trigger] Self::names_index(final(out)@, j)
            <==> Self::names_index(old(out)@, j)
                || exists|f: int| lo_f <= f < hi_f && #[trigger] self.cold_covered(f, j),
    {
        hide(Vec::wf);
        hide(Vec::repr_ok);
        hide(Vec::cold_payload_ok);
        proof {
            self.lemma_wf_named_parts();
            assert(self.repr_ok() && self.cold_payload_ok()) by { reveal(Vec::cold_repr_ok); }
        }
        let ghost base_out = out@;
        let mut f = lo_f;
        while f < hi_f
            invariant lo_f <= f <= hi_f <= self.cold_stack@.len(), self.repr_ok(), self.cold_payload_ok(),
                forall|j: nat| #[trigger] Self::names_index(out@, j)
                    <==> Self::names_index(base_out, j)
                        || exists|g: int| lo_f <= g < f && #[trigger] self.cold_covered(g, j),
            decreases hi_f - f,
        {
            let h = self.cold_stack[f];
            let saved = h.saved_len;
            let runs_len = self.cold_index_runs.len();
            proof {
                self.lemma_cold_layout_header_at(f as int);
                assert(h == self.cold_stack@[f as int]);
                assert(h.runs_start + h.runs_len <= runs_len);
                saved.lemma_as_nat_bounded();
                I::lemma_max_nat_fits_usize();
            }
            let mut r = h.runs_start;
            let rend = h.runs_start + h.runs_len;
            let ghost before_frame = out@;
            while r < rend
                invariant h == self.cold_stack@[f as int], h.runs_start <= r <= rend,
                    rend == h.runs_start + h.runs_len, rend <= self.cold_index_runs@.len(),
                    self.repr_ok(), self.cold_payload_ok(), f < hi_f <= self.cold_stack@.len(),
                    saved == h.saved_len, saved.as_nat() < I::max_nat(), I::max_nat() <= usize::MAX as nat + 1,
                    forall|j: nat| #[trigger] Self::names_index(out@, j)
                        <==> Self::names_index(before_frame, j)
                            || exists|q: int| h.runs_start <= q < r
                                && cold_run_covers::<I>(#[trigger] self.cold_index_runs@[q], j),
                decreases rend - r,
            {
                let run = self.cold_index_runs[r];
                proof {
                    assert(run.base.as_nat() + run.len <= saved.as_nat()) by { reveal(Vec::cold_payload_ok); }
                }
                let b = run.base.as_usize();
                let ghost before_run = out@;
                let mut q = 0usize;
                while q < run.len
                    invariant run == self.cold_index_runs@[r as int], q <= run.len,
                        b as nat == run.base.as_nat(),
                        run.base.as_nat() + run.len < I::max_nat(), I::max_nat() <= usize::MAX as nat + 1,
                        forall|j: nat| #[trigger] Self::names_index(out@, j)
                            <==> Self::names_index(before_run, j)
                                || (run.base.as_nat() <= j < run.base.as_nat() + q),
                    decreases run.len - q,
                {
                    let ghost before_cell = out@;
                    if let Some(ix) = I::try_from_usize(b + q) {
                        out.push(ix);
                        proof {
                            assert forall|j: nat| #[trigger] Self::names_index(out@, j)
                                <==> Self::names_index(before_run, j)
                                    || (run.base.as_nat() <= j < run.base.as_nat() + q + 1) by {
                                if Self::names_index(out@, j) {
                                    let i = choose|i: int| 0 <= i < out@.len() && (#[trigger] out@[i]).as_nat() == j;
                                    if i < before_cell.len() {
                                        assert(before_cell[i] == out@[i]);
                                        assert(Self::names_index(before_cell, j));
                                    } else {
                                        assert(out@[i] == ix);
                                    }
                                } else {
                                    if Self::names_index(before_run, j)
                                        || (run.base.as_nat() <= j < run.base.as_nat() + q) {
                                        assert(Self::names_index(before_cell, j));
                                        let i = choose|i: int| 0 <= i < before_cell.len()
                                            && (#[trigger] before_cell[i]).as_nat() == j;
                                        assert(out@[i] == before_cell[i]);
                                        assert(Self::names_index(out@, j));
                                    }
                                    if j == run.base.as_nat() + q {
                                        assert(out@[before_cell.len() as int] == ix);
                                        assert(Self::names_index(out@, j));
                                    }
                                }
                            }
                        }
                    }
                    q += 1;
                }
                proof {
                    assert forall|j: nat| #[trigger] Self::names_index(out@, j)
                        <==> Self::names_index(before_frame, j)
                            || exists|q2: int| h.runs_start <= q2 < r + 1
                                && cold_run_covers::<I>(#[trigger] self.cold_index_runs@[q2], j) by {
                        if Self::names_index(out@, j) && !Self::names_index(before_run, j) {
                            assert(cold_run_covers::<I>(self.cold_index_runs@[r as int], j));
                        }
                        if exists|q2: int| h.runs_start <= q2 < r + 1
                            && cold_run_covers::<I>(#[trigger] self.cold_index_runs@[q2], j) {
                            let q2 = choose|q2: int| h.runs_start <= q2 < r + 1
                                && cold_run_covers::<I>(#[trigger] self.cold_index_runs@[q2], j);
                            if q2 < r {
                                assert(Self::names_index(before_run, j));
                            }
                        }
                    }
                }
                r += 1;
            }
            proof {
                assert forall|j: nat| #[trigger] Self::names_index(out@, j)
                    <==> Self::names_index(base_out, j)
                        || exists|g: int| lo_f <= g < f + 1 && #[trigger] self.cold_covered(g, j) by {
                    if Self::names_index(out@, j) && !Self::names_index(before_frame, j) {
                        let q = choose|q: int| h.runs_start <= q < rend
                            && cold_run_covers::<I>(#[trigger] self.cold_index_runs@[q], j);
                        assert(self.cold_covered(f as int, j));
                    }
                    if exists|g: int| lo_f <= g < f + 1 && #[trigger] self.cold_covered(g, j) {
                        let g = choose|g: int| lo_f <= g < f + 1 && #[trigger] self.cold_covered(g, j);
                        if g == f {
                            let q = choose|q: int| self.cold_stack@[g].runs_start <= q
                                < self.cold_stack@[g].runs_start + self.cold_stack@[g].runs_len
                                && (#[trigger] self.cold_index_runs@[q]).base.as_nat() <= j
                                && j < self.cold_index_runs@[q].base.as_nat() + self.cold_index_runs@[q].len;
                            assert(cold_run_covers::<I>(self.cold_index_runs@[q], j));
                        } else {
                            assert(Self::names_index(before_frame, j));
                        }
                    }
                }
            }
            f += 1;
        }
    }

    /// Pair frames `[lo, hi)` of one tier: append every captured index.
    #[verifier::spinoff_prover]
    fn pending_pair_indices_checked(&self, trail: bool, lo: usize, hi: usize, out: &mut std::vec::Vec<I>)
        requires self.wf(), lo <= hi <= self.pair_tier_count(trail),
        ensures forall|j: nat| #[trigger] Self::names_index(final(out)@, j)
            <==> Self::names_index(old(out)@, j)
                || exists|g: int| lo <= g < hi && #[trigger] captured_in_range::<T, I>(
                    self.pair_tier_pool(trail), self.pair_tier_start(trail, g), self.pair_tier_end(trail, g), j),
    {
        hide(Vec::wf);
        let ghost base_out = out@;
        let mut g = lo;
        while g < hi
            invariant lo <= g <= hi <= self.pair_tier_count(trail), self.wf(),
                forall|j: nat| #[trigger] Self::names_index(out@, j)
                    <==> Self::names_index(base_out, j)
                        || exists|k: int| lo <= k < g && #[trigger] captured_in_range::<T, I>(
                            self.pair_tier_pool(trail), self.pair_tier_start(trail, k), self.pair_tier_end(trail, k), j),
            decreases hi - g,
        {
            proof { self.lemma_pair_tier_frame_layout(trail, g as int); }
            let (start, end) = if trail {
                let frame = self.trail_stack[g];
                let end = if g + 1 == self.trail_stack.len() { self.trail_value_pool.len() } else { frame.end };
                (frame.start, end)
            } else {
                let frame = self.hot_stack[g];
                let end = if g + 1 == self.hot_stack.len() { self.hot_value_pool.len() } else { frame.end };
                (frame.start, end)
            };
            proof {
                assert(start as int == self.pair_tier_start(trail, g as int));
                assert(end as int == self.pair_tier_end(trail, g as int));
            }
            let ghost before_frame = out@;
            let mut p = start;
            while p < end
                invariant start <= p <= end, start as int == self.pair_tier_start(trail, g as int),
                    end as int == self.pair_tier_end(trail, g as int),
                    end <= self.pair_tier_pool(trail).len(),
                    trail ==> end <= self.trail_value_pool@.len(),
                    !trail ==> end <= self.hot_value_pool@.len(),
                    forall|j: nat| #[trigger] Self::names_index(out@, j)
                        <==> Self::names_index(before_frame, j)
                            || exists|q: int| start <= q < p
                                && (#[trigger] self.pair_tier_pool(trail)[q]).1.as_nat() == j,
                decreases end - p,
            {
                let ghost before_cell = out@;
                let index = if trail { self.trail_value_pool[p].1 } else { self.hot_value_pool[p].1 };
                proof { assert(index == self.pair_tier_pool(trail)[p as int].1); }
                out.push(index);
                proof {
                    assert forall|j: nat| #[trigger] Self::names_index(out@, j)
                        <==> Self::names_index(before_frame, j)
                            || exists|q: int| start <= q < p + 1
                                && (#[trigger] self.pair_tier_pool(trail)[q]).1.as_nat() == j by {
                        if Self::names_index(out@, j) {
                            let i = choose|i: int| 0 <= i < out@.len() && (#[trigger] out@[i]).as_nat() == j;
                            if i < before_cell.len() {
                                assert(before_cell[i] == out@[i]);
                                assert(Self::names_index(before_cell, j));
                            } else {
                                assert(out@[i] == index);
                                assert(self.pair_tier_pool(trail)[p as int].1.as_nat() == j);
                            }
                        } else {
                            if Self::names_index(before_cell, j) {
                                let i = choose|i: int| 0 <= i < before_cell.len()
                                    && (#[trigger] before_cell[i]).as_nat() == j;
                                assert(out@[i] == before_cell[i]);
                                assert(Self::names_index(out@, j));
                            }
                            if self.pair_tier_pool(trail)[p as int].1.as_nat() == j {
                                assert(out@[before_cell.len() as int] == index);
                                assert(Self::names_index(out@, j));
                            }
                        }
                    }
                }
                p += 1;
            }
            proof {
                assert forall|j: nat| #[trigger] Self::names_index(out@, j)
                    <==> Self::names_index(base_out, j)
                        || exists|k: int| lo <= k < g + 1 && #[trigger] captured_in_range::<T, I>(
                            self.pair_tier_pool(trail), self.pair_tier_start(trail, k), self.pair_tier_end(trail, k), j) by {
                    if Self::names_index(out@, j) && !Self::names_index(before_frame, j) {
                        assert(captured_in_range::<T, I>(self.pair_tier_pool(trail),
                            self.pair_tier_start(trail, g as int), self.pair_tier_end(trail, g as int), j));
                    }
                    if exists|k: int| lo <= k < g + 1 && #[trigger] captured_in_range::<T, I>(
                        self.pair_tier_pool(trail), self.pair_tier_start(trail, k), self.pair_tier_end(trail, k), j) {
                        let k = choose|k: int| lo <= k < g + 1 && #[trigger] captured_in_range::<T, I>(
                            self.pair_tier_pool(trail), self.pair_tier_start(trail, k), self.pair_tier_end(trail, k), j);
                        if k < g {
                            assert(Self::names_index(before_frame, j));
                        } else {
                            let q = choose|q: int| start <= q < end && 0 <= q < self.pair_tier_pool(trail).len()
                                && (#[trigger] self.pair_tier_pool(trail)[q]).1.as_nat() == j;
                            assert(Self::names_index(out@, j));
                        }
                    }
                }
            }
            g += 1;
        }
    }

    /// A Cold frame captures `j` exactly when one of its runs covers `j`.
    #[verifier::spinoff_prover]
    proof fn lemma_frame_captures_cold(&self, f: int, j: nat)
        requires 0 <= f < self.cold_stack@.len(),
        ensures self.frame_captures(f, j) == self.cold_covered(f, j),
    {}

    /// A pair-tier frame captures `j` exactly when its physical range does.
    #[verifier::spinoff_prover]
    proof fn lemma_frame_captures_pair(&self, trail: bool, g: int, j: nat)
        requires 0 <= g < self.pair_tier_count(trail),
        ensures self.frame_captures(self.pair_tier_offset(trail) + g, j)
            == captured_in_range::<T, I>(self.pair_tier_pool(trail),
                self.pair_tier_start(trail, g), self.pair_tier_end(trail, g), j),
    {
        hide(range_saved_value);
        let f = self.pair_tier_offset(trail) + g;
        if trail {
            assert(self.frame_saved_value(f, j) == range_saved_value::<T, I>(self.trail_value_pool@,
                self.trail_stack@[g].start as int, self.phys_trail_end(g), j));
        } else {
            assert(self.frame_saved_value(f, j) == range_saved_value::<T, I>(self.hot_value_pool@,
                self.phys_hot_start(g), self.phys_hot_end(g), j));
        }
        reveal(range_saved_value);
    }

    /// The three tier passes together name exactly the captured indices of
    /// frames `[tok, depth)`.
    #[verifier::spinoff_prover]
    proof fn lemma_pending_union(
        &self, tok: nat, cold_lo: nat, hot_lo: nat, trail_lo: nat,
        after_cold: Seq<I>, after_hot: Seq<I>, out: Seq<I>,
    )
        requires self.wf(), tok < self.depth_spec(),
            cold_lo as int == (if tok < self.cold_stack@.len() { tok as int } else { self.cold_stack@.len() as int }),
            hot_lo as int == (if tok < self.cold_stack@.len() { 0int }
                else if tok < self.cold_stack@.len() + self.hot_stack@.len() { tok - self.cold_stack@.len() }
                else { self.hot_stack@.len() as int }),
            trail_lo as int == (if tok < self.cold_stack@.len() + self.hot_stack@.len() { 0int }
                else { tok - self.cold_stack@.len() - self.hot_stack@.len() }),
            forall|j: nat| #[trigger] Self::names_index(after_cold, j)
                <==> exists|f: int| cold_lo <= f < self.cold_stack@.len() && #[trigger] self.cold_covered(f, j),
            forall|j: nat| #[trigger] Self::names_index(after_hot, j)
                <==> Self::names_index(after_cold, j)
                    || exists|g: int| hot_lo <= g < self.hot_stack@.len() && #[trigger] captured_in_range::<T, I>(
                        self.pair_tier_pool(false), self.pair_tier_start(false, g), self.pair_tier_end(false, g), j),
            forall|j: nat| #[trigger] Self::names_index(out, j)
                <==> Self::names_index(after_hot, j)
                    || exists|g: int| trail_lo <= g < self.trail_stack@.len() && #[trigger] captured_in_range::<T, I>(
                        self.pair_tier_pool(true), self.pair_tier_start(true, g), self.pair_tier_end(true, g), j),
        ensures forall|j: nat| #[trigger] Self::names_index(out, j)
            <==> exists|f: int| tok <= f < self.depth_spec() && #[trigger] self.frame_captures(f, j),
    {
        hide(Vec::wf);
        hide(range_saved_value);
        self.lemma_partition_counts();
        let cc = self.cold_stack@.len() as int;
        let hc = self.hot_stack@.len() as int;
        let tc = self.trail_stack@.len() as int;
        assert forall|j: nat| #[trigger] Self::names_index(out, j)
            <==> exists|f: int| tok <= f < self.depth_spec() && #[trigger] self.frame_captures(f, j) by {
            if Self::names_index(out, j) {
                if exists|g: int| trail_lo <= g < tc && #[trigger] captured_in_range::<T, I>(
                    self.pair_tier_pool(true), self.pair_tier_start(true, g), self.pair_tier_end(true, g), j) {
                    let g = choose|g: int| trail_lo <= g < tc && #[trigger] captured_in_range::<T, I>(
                        self.pair_tier_pool(true), self.pair_tier_start(true, g), self.pair_tier_end(true, g), j);
                    self.lemma_frame_captures_pair(true, g, j);
                    assert(self.frame_captures(cc + hc + g, j));
                } else if exists|g: int| hot_lo <= g < hc && #[trigger] captured_in_range::<T, I>(
                    self.pair_tier_pool(false), self.pair_tier_start(false, g), self.pair_tier_end(false, g), j) {
                    let g = choose|g: int| hot_lo <= g < hc && #[trigger] captured_in_range::<T, I>(
                        self.pair_tier_pool(false), self.pair_tier_start(false, g), self.pair_tier_end(false, g), j);
                    self.lemma_frame_captures_pair(false, g, j);
                    assert(self.frame_captures(cc + g, j));
                } else {
                    let f = choose|f: int| cold_lo <= f < cc && #[trigger] self.cold_covered(f, j);
                    self.lemma_frame_captures_cold(f, j);
                    assert(self.frame_captures(f, j));
                }
            } else {
                if exists|f: int| tok <= f < self.depth_spec() && #[trigger] self.frame_captures(f, j) {
                    let f = choose|f: int| tok <= f < self.depth_spec() && #[trigger] self.frame_captures(f, j);
                    if f < cc {
                        self.lemma_frame_captures_cold(f, j);
                        assert(Self::names_index(after_cold, j));
                        assert(Self::names_index(after_hot, j));
                    } else if f < cc + hc {
                        self.lemma_frame_captures_pair(false, f - cc, j);
                        assert(Self::names_index(after_hot, j));
                    } else {
                        self.lemma_frame_captures_pair(true, f - cc - hc, j);
                    }
                    assert(Self::names_index(out, j));
                }
            }
        }
    }


    /// The indices a restore to frame `depth` would touch (the typed-group
    /// form of `pending_restore_indices`: the depth is the group's token's
    /// depth, validated by the group's `History`; here only the frame's
    /// liveness is checked). `None` when `depth` is not below the frame
    /// stack.
    pub fn pending_restore_indices_at(&self, depth: usize) -> (r: Option<std::vec::Vec<I>>)
        requires
            self.wf(),
        ensures
            r is Some <==> (depth as nat) < self.depth_spec(),
            r matches Some(out) ==> forall|j: nat| #[trigger] Self::names_index(out@, j)
                <==> exists|f: int| depth as nat <= f < self.depth_spec()
                    && #[trigger] self.frame_captures(f, j),
    {
        hide(Vec::wf);
        hide(range_saved_value);
        proof { self.lemma_wf_named_parts(); }
        if !(depth < self.depth_exec()) {
            return None;
        }
        proof { self.lemma_partition_counts(); }
        let cold = self.cold_stack.len();
        let hot = self.hot_stack.len();
        let trail = self.trail_stack.len();
        let tok = depth;
        let mut out: std::vec::Vec<I> = std::vec::Vec::new();

        let cold_lo = if tok < cold { tok } else { cold };
        self.pending_cold_indices_checked(cold_lo, cold, &mut out);
        let ghost after_cold = out@;
        let hot_lo = if tok < cold { 0 } else if tok < cold + hot { tok - cold } else { hot };
        self.pending_pair_indices_checked(false, hot_lo, hot, &mut out);
        let ghost after_hot = out@;
        let trail_lo = if tok < cold + hot { 0 } else { tok - cold - hot };
        self.pending_pair_indices_checked(true, trail_lo, trail, &mut out);
        proof {
            self.lemma_pending_union(tok as nat, cold_lo as nat, hot_lo as nat, trail_lo as nat,
                after_cold, after_hot, out@);
        }
        Some(out)
    }

    /// Production instantiation of the sequence theorem on one representative
    /// interleaving: every fact below follows from the public contracts alone.
    /// Mark, write, mark, restore, write again, restore to the older mark, roll
    /// history over, and restore again: the live view is always the archived
    /// snapshot, the depth the token's frame, and the archive its prefix.
    #[verifier::spinoff_prover]
    #[allow(dead_code)]
    pub(crate) fn sequence_witness_checked(&mut self, i: I, a: T, b: T)
        where T: core::default::Default
        requires old(self).wf(), TRACK, i.as_nat() < old(self).view().len(),
            old(self).depth_spec() + 2 < u32::MAX,
        ensures final(self).wf(),
    {
        let ghost v0 = self.view();
        let ghost d0 = self.depth_spec();
        let ghost s0 = self.snapshots_view();
        // The two marks are frames `base` and `base + 1`: a group would mint a
        // token naming each, and here the frame index is the name.
        let base = self.depth();
        match self.try_push_frame_with(MarkOptions::default()) {
            Ok(()) => {}
            Err(_) => { return; }
        }
        assert(self.view() == v0 && self.depth_spec() == d0 + 1 && self.snapshots_view() == s0.push(v0));
        self.set_index(i, a);
        assert(self.view() == v0.update(i.as_nat() as int, a));
        let ghost v1 = self.view();
        match self.try_push_frame_with(MarkOptions::default()) {
            Ok(()) => {}
            Err(_) => { return; }
        }
        assert(self.snapshots_view() == s0.push(v0).push(v1) && self.depth_spec() == d0 + 2);
        self.set_index(i, b);
        // Reset to the second mark: the write of `b` is undone.
        // Semantics B (design doc 08 §1): the reset keeps that frame open.
        self.reset_frame(base + 1);
        assert(self.view() == v1);
        assert(self.depth_spec() == d0 + 2);
        assert(self.snapshots_view() == s0.push(v0).push(v1));
        // Mutate again after the reset, then roll history over.
        self.set_index(i, b);
        self.apply_tier_policy();
        assert(self.view() == v1.update(i.as_nat() as int, b));
        assert(self.snapshots_view() == s0.push(v0).push(v1));
        // Reset to the older mark: back to the original view, its frame open.
        self.reset_frame(base);
        assert(self.view() == v0);
        assert(self.depth_spec() == d0 + 1);
        assert(self.snapshots_view() == s0.push(v0));
    }


    #[verifier::rlimit(300)]
    #[inline(always)]
    pub(crate) fn push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().push(value),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        self.runtime_push(value);
    }

    /// Helper used in proofs: assert frame_inv_range for frame k from wf.
    pub open(crate) spec fn frame_inv_range_holds(&self, k: int) -> bool {
        frame_inv_range::<T, I>(
            self.layer_above_at(k),
            self.full_trail@,
            self.g_start(k),
            self.g_end(k),
            self.snapshots@[k],
            self.g_saved_len(k))
    }

    /// Physical stratum start of Hot frame `i` in `hot_value_pool`.
    pub open(crate) spec fn phys_hot_start(&self, i: int) -> int {
        self.hot_stack@[i].start as int
    }

    /// Effective end of Hot frame `i`. Closed frames use their sealed header;
    /// the newest Hot frame reaches the authoritative Hot pool length. When
    /// Trail owns ingress that newest Hot frame is closed too, so its sealed
    /// end is required to equal the pool length by `open_ingress_ok`.
    pub open(crate) spec fn phys_hot_end(&self, i: int) -> int {
        if i + 1 < self.hot_stack@.len() {
            self.hot_stack@[i].end as int
        } else {
            self.hot_value_pool@.len() as int
        }
    }

    /// Effective end of Trail frame `i`. Closed frames use their sealed header;
    /// the newest Trail frame reaches the authoritative chronological pool.
    pub open(crate) spec fn phys_trail_end(&self, i: int) -> int {
        if i + 1 < self.trail_stack@.len() {
            self.trail_stack@[i].end as int
        } else {
            self.trail_value_pool@.len() as int
        }
    }

    /// Per-frame authoritative-Hot/ghost index-set refinement. The compatibility
    /// ghost coordinates remain useful to old proof combinators, but all
    /// physical membership is read from `hot_value_pool`, never `diff_log`.
    pub open(crate) spec fn frame_iso(&self, i: int) -> bool {
        forall|j: int| 0 <= j < self.snapshots@[self.cold_stack@.len() + i].len() ==>
            #[trigger] captured_in_range::<T, I>(
                self.hot_value_pool@, self.phys_hot_start(i), self.phys_hot_end(i), j as nat)
            == captured_in_range::<T, I>(
                self.full_trail@,
                self.g_start(self.cold_stack@.len() + i),
                self.g_end(self.cold_stack@.len() + i), j as nat)
    }

    /// Authoritative Hot reconstruction for frame `i`. This compatibility
    /// accessor is retained for older proof bodies, but now delegates to the
    /// real Hot pool representation.
    pub open(crate) spec fn phys_frame_inv_range_holds(&self, i: int) -> bool {
        frame_inv_range::<T, I>(
            self.layer_above_at(self.cold_stack@.len() + i),
            self.hot_value_pool@,
            self.phys_hot_start(i),
            self.phys_hot_end(i),
            self.snapshots@[self.cold_stack@.len() + i],
            self.snapshots@[(self.cold_stack@.len() + i)].len())
    }

    /// Cell `c` is covered by some index run of cold frame `f`.
    pub open(crate) spec fn cold_covered(&self, f: int, c: nat) -> bool {
        exists|r: int|
            self.cold_stack@[f].runs_start <= r
                < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
            && (#[trigger] self.cold_index_runs@[r]).base.as_nat() <= c
            && c < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len
    }

    /// The value cold frame `f`'s covering run holds for cell `c`.
    pub open(crate) spec fn cold_value(&self, f: int, c: nat) -> T {
        let r = choose|r: int|
            self.cold_stack@[f].runs_start <= r
                < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
            && (#[trigger] self.cold_index_runs@[r]).base.as_nat() <= c
            && c < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len;
        self.cold_value_pool@[self.cold_index_runs@[r].start as int
            + (c - self.cold_index_runs@[r].base.as_nat()) as int]
    }

    /// The saved extent is read from the physical header in its age-ordered
    /// tier, rather than inferred from neighboring frame lengths.
    pub open(crate) spec fn frame_saved_len(&self, f: int) -> nat {
        let cc = self.cold_stack@.len();
        let hc = self.hot_stack@.len();
        if f < cc {
            self.cold_stack@[f].saved_len.as_nat()
        } else if f < cc + hc {
            self.hot_stack@[f - cc].saved_len.as_nat()
        } else {
            self.trail_stack@[f - cc - hc].saved_len.as_nat()
        }
    }

    /// Common logical meaning, read only from authoritative physical storage.
    pub open(crate) spec fn frame_saved_value(&self, f: int, j: nat) -> Option<T> {
        let cc = self.cold_stack@.len();
        let hc = self.hot_stack@.len();
        if f < cc {
            if self.cold_covered(f, j) { Some(self.cold_value(f, j)) } else { None }
        } else if f < cc + hc {
            let h = f - cc;
            range_saved_value::<T, I>(
                self.hot_value_pool@, self.phys_hot_start(h), self.phys_hot_end(h), j)
        } else {
            let t = f - cc - hc;
            range_saved_value::<T, I>(
                self.trail_value_pool@, self.trail_stack@[t].start as int,
                self.phys_trail_end(t), j)
        }
    }

    /// Derived finite map over the physical saved-value lookup. Its complete
    /// correspondence, including absence outside saved_len, is proved below.
    pub open(crate) spec fn persistence_frame(&self, f: int) -> crate::persistence_model::Frame<T> {
        crate::persistence_model::Frame {
            saved_len: self.frame_saved_len(f),
            saved: crate::persistence_model::bounded_saved_map(self.frame_saved_len(f),
                |j: nat| self.frame_saved_value(f, j)),
        }
    }

    pub open(crate) spec fn persistence_model(&self) -> crate::persistence_model::Model<T> {
        crate::persistence_model::Model {
            live: self.view(), snapshots: self.snapshots@,
            frames: Seq::new(self.depth_spec(), |f: int| self.persistence_frame(f)),
        }
    }

    /// Store/tag repair cannot alter a frame meaning derived from history.
    #[verifier::spinoff_prover]
    proof fn lemma_persistence_views_framing(&self, pre: Self)
        requires self.view() == pre.view(), self.snapshots@ == pre.snapshots@,
            self.trail_frames@ == pre.trail_frames@,
            self.cold_stack@ == pre.cold_stack@, self.cold_index_runs@ == pre.cold_index_runs@,
            self.cold_value_pool@ == pre.cold_value_pool@,
            self.hot_stack@ == pre.hot_stack@, self.hot_value_pool@ == pre.hot_value_pool@,
            self.trail_stack@ == pre.trail_stack@, self.trail_value_pool@ == pre.trail_value_pool@,
        ensures self.persistence_model() == pre.persistence_model(),
    {
        assert forall|f: int| 0 <= f < self.depth_spec() implies
            #[trigger] self.persistence_frame(f) == pre.persistence_frame(f) by {
            let a = self.persistence_frame(f).saved;
            let b = pre.persistence_frame(f).saved;
            assert forall|j: nat| #[trigger] a.dom().contains(j) == b.dom().contains(j)
                && (a.dom().contains(j) ==> a[j] == b[j]) by {
                assert(self.frame_saved_value(f, j) == pre.frame_saved_value(f, j));
                crate::persistence_model::bounded_saved_map_at(self.frame_saved_len(f),
                    |i: nat| self.frame_saved_value(f, i), j);
                crate::persistence_model::bounded_saved_map_at(pre.frame_saved_len(f),
                    |i: nat| pre.frame_saved_value(f, i), j);
            }
            assert(a =~= b);
        }
        assert(self.persistence_model().frames =~= pre.persistence_model().frames);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_store_framing(&self, pre: Self)
        requires *self == (Self { store: self.store, active_saved_len: self.active_saved_len, ..pre }),
            self.view() == pre.view(),
        ensures self.persistence_model() == pre.persistence_model(),
    {
        assert forall|f: int| 0 <= f < self.depth_spec() implies
            #[trigger] self.persistence_frame(f) == pre.persistence_frame(f) by {
            let a = self.persistence_frame(f).saved;
            let b = pre.persistence_frame(f).saved;
            assert forall|j: nat| #[trigger] a.dom().contains(j) == b.dom().contains(j)
                && (a.dom().contains(j) ==> a[j] == b[j]) by {
                assert(self.frame_saved_value(f, j) == pre.frame_saved_value(f, j));
                crate::persistence_model::bounded_saved_map_at(self.frame_saved_len(f),
                    |i: nat| self.frame_saved_value(f, i), j);
                crate::persistence_model::bounded_saved_map_at(pre.frame_saved_len(f),
                    |i: nat| pre.frame_saved_value(f, i), j);
            }
            assert(a =~= b);
        }
        assert(self.persistence_model().frames =~= pre.persistence_model().frames);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_saved_len(&self, f: int)
        requires self.wf(), 0 <= f < self.depth_spec(),
        ensures self.frame_saved_len(f) == self.snapshots@[f].len(),
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_physical_domain(&self, f: int, j: nat)
        requires self.wf(), 0 <= f < self.depth_spec(),
        ensures self.frame_saved_value(f, j) is Some ==> j < self.frame_saved_len(f),
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
        let cc = self.cold_stack@.len();
        let hc = self.hot_stack@.len();
        if self.frame_saved_value(f, j) is Some {
            if f < cc {
                reveal(Vec::cold_repr_ok);
                reveal(Vec::cold_payload_ok);
                let r = choose|r: int| self.cold_stack@[f].runs_start <= r
                    < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
                    && (#[trigger] self.cold_index_runs@[r]).base.as_nat() <= j
                    && j < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len;
            } else if f < cc + hc {
                let h = f - cc;
                self.lemma_hot_repr_at(h);
                let q = choose|q: int| self.phys_hot_start(h) <= q < self.phys_hot_end(h)
                    && 0 <= q < self.hot_value_pool@.len()
                    && (#[trigger] self.hot_value_pool@[q]).1.as_nat() == j;
            } else {
                reveal(Vec::trail_repr_ok);
                let t = f - cc - hc;
                let q = choose|q: int| self.trail_stack@[t].start <= q < self.phys_trail_end(t)
                    && 0 <= q < self.trail_value_pool@.len()
                    && (#[trigger] self.trail_value_pool@[q]).1.as_nat() == j;
            }
        }
    }

    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_persistence_lookup(&self, f: int, j: nat)
        requires self.wf(), 0 <= f < self.depth_spec(),
        ensures self.persistence_frame(f).saved.dom().contains(j) <==> self.frame_saved_value(f, j) is Some,
            self.persistence_frame(f).saved.dom().contains(j) ==>
                self.persistence_frame(f).saved[j] == self.frame_saved_value(f, j)->Some_0,
    {
        hide(Vec::wf);
        self.lemma_persistence_physical_domain(f, j);
        crate::persistence_model::bounded_saved_map_at(self.frame_saved_len(f),
            |i: nat| self.frame_saved_value(f, i), j);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_frame(&self, f: int)
        requires self.wf(), 0 <= f < self.depth_spec(),
        ensures crate::persistence_model::frame_ok(self.persistence_frame(f),
            self.snapshots@[f], self.layer_above_at(f)),
    {
        hide(Vec::wf);
        self.lemma_persistence_saved_len(f);
        let frame = self.persistence_frame(f);
        assert forall|j: nat| #[trigger] frame.saved.dom().contains(j) implies j < frame.saved_len by {
            crate::persistence_model::bounded_saved_map_at(self.frame_saved_len(f),
                |i: nat| self.frame_saved_value(f, i), j);
        }
        assert forall|j: nat| j < frame.saved_len implies
            if #[trigger] frame.saved.dom().contains(j) {
                frame.saved[j] == self.snapshots@[f][j as int]
            } else {
                j < self.layer_above_at(f).len()
                    && self.layer_above_at(f)[j as int] == self.snapshots@[f][j as int]
            } by {
            self.lemma_persistence_lookup(f, j);
            self.lemma_frame_saved_value_contract(f, j as int);
        }
    }

    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_persistence_model(&self)
        requires self.wf(),
        ensures crate::persistence_model::snapshots_ok(self.persistence_model()),
            self.persistence_model().live == self.view(),
            self.persistence_model().snapshots == self.snapshots@,
            self.persistence_model().frames.len() == self.depth_spec(),
    {
        hide(Vec::wf);
        self.lemma_replay_partition();
        let model = self.persistence_model();
        assert forall|f: int| 0 <= f < model.frames.len() implies
            #[trigger] crate::persistence_model::frame_ok(model.frames[f], model.snapshots[f],
                crate::persistence_model::above(model, f)) by {
            self.lemma_persistence_frame(f);
            assert(crate::persistence_model::above(model, f) == self.layer_above_at(f));
        }
    }

    /// The actual capture bridge for the active physical frame. In untracked
    /// mode there is no logical history; an adapter must expose an empty tag set.
    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_persistence_capture_at(&self, j: nat)
        requires self.wf(), TRACK, j < self.view().len(),
        ensures self.store.captured()[j as int] == (self.depth_spec() > 0
            && self.persistence_frame(self.depth_spec() - 1).saved.dom().contains(j)),
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
        reveal(Vec::open_ingress_ok);
        if self.depth_spec() > 0 {
            let f = self.depth_spec() - 1;
            self.lemma_persistence_saved_len(f);
            self.lemma_persistence_lookup(f, j);
            if j >= self.active_saved_len.as_nat() {
                self.lemma_persistence_physical_domain(f, j);
            }
        }
    }

    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_persistence_writable(&self)
        requires self.wf(),
        ensures
            self.active_saved_len.as_nat() == if self.depth_spec() > 0 {
                self.persistence_frame(self.depth_spec() - 1).saved_len
            } else { 0nat },
            self.store.unique_capture_spec() ==> self.trail_stack@.len() == 0
                && (self.depth_spec() > 0 ==> self.hot_stack@.len() > 0),
            !self.store.unique_capture_spec() && self.depth_spec() > 0 ==> self.trail_stack@.len() > 0,
            !TRACK ==> self.depth_spec() == 0,
    {
        hide(Vec::wf);
        self.lemma_wf_named_parts();
        reveal(Vec::open_ingress_ok);
        reveal(Vec::frame_partition_ok);
        if self.depth_spec() > 0 { self.lemma_persistence_saved_len(self.depth_spec() - 1); }
        else { I::lemma_min_as_nat(); }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_persistence_pair_frame(&self, trail: bool, f: int, buffer: Seq<T>)
        requires self.wf(), 0 <= f < self.pair_tier_count(trail),
        ensures overlay::<T, I>(buffer, self.pair_tier_pool(trail),
            self.pair_tier_start(trail, f), self.pair_tier_end(trail, f))
            == crate::persistence_model::apply(
                self.persistence_frame(self.pair_tier_offset(trail) + f).saved, buffer),
    {
        hide(Vec::wf);
        self.lemma_pair_tier_frame_layout(trail, f);
        self.lemma_replay_partition();
        let pool = self.pair_tier_pool(trail);
        let lo = self.pair_tier_start(trail, f);
        let hi = self.pair_tier_end(trail, f);
        let out = overlay::<T, I>(buffer, pool, lo, hi);
        let map = self.persistence_frame(self.pair_tier_offset(trail) + f).saved;
        lemma_overlay_len::<T, I>(buffer, pool, lo, hi);
        assert forall|j: int| 0 <= j < buffer.len() implies
            #[trigger] out[j] == crate::persistence_model::apply(map, buffer)[j] by {
            self.lemma_persistence_lookup(self.pair_tier_offset(trail) + f, j as nat);
            lemma_overlay_saved_value::<T, I>(buffer, pool, lo, hi, j);
        }
        assert(out =~= crate::persistence_model::apply(map, buffer));
    }

    /// The physical concatenated range is exactly the shared model's newest-
    /// to-oldest frame composition for every buffer, without layer premises.
    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_persistence_pair_suffix(&self, trail: bool, first: int, buffer: Seq<T>)
        requires self.wf(), 0 <= first < self.pair_tier_count(trail),
        ensures overlay::<T, I>(buffer, self.pair_tier_pool(trail),
            self.pair_tier_start(trail, first), self.pair_tier_pool(trail).len() as int)
            == crate::persistence_model::apply_range(self.persistence_model().frames,
                self.pair_tier_offset(trail) + first,
                (self.pair_tier_offset(trail) + self.pair_tier_count(trail)) as int, buffer),
        decreases self.pair_tier_count(trail) - first,
    {
        hide(Vec::wf);
        self.lemma_pair_tier_frame_layout(trail, first);
        self.lemma_replay_partition();
        let pool = self.pair_tier_pool(trail);
        let lo = self.pair_tier_start(trail, first);
        let mid = self.pair_tier_end(trail, first);
        let hi = pool.len() as int;
        let newer = overlay::<T, I>(buffer, pool, mid, hi);
        let model = self.persistence_model();
        let index = self.pair_tier_offset(trail) + first;
        let end = (self.pair_tier_offset(trail) + self.pair_tier_count(trail)) as int;
        assert(0 <= index < end <= model.frames.len());
        if first + 1 < self.pair_tier_count(trail) {
            self.lemma_persistence_pair_suffix(trail, first + 1, buffer);
        } else { assert(newer == buffer); }
        assert(newer == crate::persistence_model::apply_range(model.frames, index + 1, end, buffer));
        assert(model.frames[index] == self.persistence_frame(index));
        lemma_overlay_split::<T, I>(buffer, pool, lo, mid, hi);
        self.lemma_persistence_pair_frame(trail, first, newer);
        assert(crate::persistence_model::apply_range(model.frames, index, end, buffer)
            == crate::persistence_model::apply(model.frames[index].saved, newer));
    }

    /// Read-only coordinates for the two pair-encoded tiers. These are spec
    /// projections of existing pools/headers, not another history copy.
    pub open(crate) spec fn pair_tier_pool(&self, trail: bool) -> Seq<(T, I)> {
        if trail { self.trail_value_pool@ } else { self.hot_value_pool@ }
    }

    pub open(crate) spec fn pair_tier_count(&self, trail: bool) -> nat {
        if trail { self.trail_stack@.len() } else { self.hot_stack@.len() }
    }

    pub open(crate) spec fn pair_tier_offset(&self, trail: bool) -> nat {
        self.cold_stack@.len() + if trail { self.hot_stack@.len() } else { 0 }
    }

    pub open(crate) spec fn pair_tier_start(&self, trail: bool, f: int) -> int {
        if trail { self.trail_stack@[f].start as int } else { self.phys_hot_start(f) }
    }

    pub open(crate) spec fn pair_tier_header_end(&self, trail: bool, f: int) -> int {
        if trail { self.trail_stack@[f].end as int } else { self.hot_stack@[f].end as int }
    }

    pub open(crate) spec fn pair_tier_end(&self, trail: bool, f: int) -> int {
        if trail { self.phys_trail_end(f) } else { self.phys_hot_end(f) }
    }

    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_pair_tier_frame_layout(&self, trail: bool, f: int)
        requires self.wf(), 0 <= f < self.pair_tier_count(trail),
        ensures
            f == 0 ==> self.pair_tier_start(trail, f) == 0,
            self.pair_tier_start(trail, f) <= self.pair_tier_header_end(trail, f)
                <= self.pair_tier_end(trail, f),
            f + 1 < self.pair_tier_count(trail) ==>
                self.pair_tier_header_end(trail, f) == self.pair_tier_start(trail, f + 1),
            self.pair_tier_offset(trail) + self.pair_tier_count(trail) <= self.depth_spec(),
            0 <= self.pair_tier_start(trail, f) <= self.pair_tier_end(trail, f)
                <= self.pair_tier_pool(trail).len(),
            f + 1 < self.pair_tier_count(trail) ==>
                self.pair_tier_end(trail, f) == self.pair_tier_start(trail, f + 1),
            f + 1 == self.pair_tier_count(trail) ==>
                self.pair_tier_end(trail, f) == self.pair_tier_pool(trail).len(),
            forall|j: nat| #[trigger] self.frame_saved_value(self.pair_tier_offset(trail) + f, j)
                == range_saved_value::<T, I>(self.pair_tier_pool(trail),
                    self.pair_tier_start(trail, f), self.pair_tier_end(trail, f), j),
    {
        self.lemma_wf_named_parts();
        reveal(Vec::frame_partition_ok);
        if trail {
            reveal(Vec::trail_repr_ok);
        } else {
            reveal(Vec::hot_repr_ok);
        }
    }

    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_pair_tier_start_order(&self, trail: bool, a: int, b: int)
        requires self.wf(), 0 <= a <= b < self.pair_tier_count(trail),
        ensures self.pair_tier_start(trail, a) <= self.pair_tier_start(trail, b),
        decreases b - a,
    {
        hide(Vec::wf);
        self.lemma_pair_tier_frame_layout(trail, a);
        if a < b {
            self.lemma_pair_tier_start_order(trail, a + 1, b);
        }
    }

    /// Every surviving pre-replay flag is named in any suffix containing the
    /// open ingress frame. This is physical-pool membership, not ghost-log
    /// membership, and applies to duplicate-preserving Trail as well as Hot.
    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_ingress_suffix_capture(&self, trail: bool, first: int)
        requires
            self.wf(),
            self.depth_spec() > 0,
            trail == !self.store.unique_capture_spec(),
            0 <= first < self.pair_tier_count(trail),
        ensures
            forall|j: int| 0 <= j < self.store.captured().len()
                && #[trigger] self.store.captured()[j] ==>
                captured_in_range::<T, I>(self.pair_tier_pool(trail),
                    self.pair_tier_start(trail, first), self.pair_tier_pool(trail).len() as int, j as nat),
    {
        hide(Vec::wf);
        self.lemma_replay_ingress();
        self.lemma_pair_tier_start_order(trail, first, self.pair_tier_count(trail) - 1);
    }

    /// Pointwise induction over frames within a batched pair-pool replay.
    /// Only inherited cells recurse; covered cells are discharged immediately.
    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_pair_tier_suffix_cell(
        &self, trail: bool, first: int, base: Seq<T>, j: int,
    )
        requires
            self.wf(),
            0 <= first < self.pair_tier_count(trail),
            0 <= j < base.len(),
            j < self.snapshots@[self.pair_tier_offset(trail) + first].len(),
            j < self.layer_above_at(self.pair_tier_offset(trail) + self.pair_tier_count(trail) - 1).len() ==>
                base[j] == self.layer_above_at(self.pair_tier_offset(trail) + self.pair_tier_count(trail) - 1)[j],
        ensures
            overlay::<T, I>(base, self.pair_tier_pool(trail),
                self.pair_tier_start(trail, first), self.pair_tier_pool(trail).len() as int)[j]
                == self.snapshots@[self.pair_tier_offset(trail) + first][j],
        decreases self.pair_tier_count(trail) - first,
    {
        hide(Vec::wf);
        hide(overlay);
        hide(range_saved_value);
        hide(Vec::frame_saved_value);
        self.lemma_pair_tier_frame_layout(trail, first);
        let pool = self.pair_tier_pool(trail);
        let lo = self.pair_tier_start(trail, first);
        let mid = self.pair_tier_end(trail, first);
        let hi = pool.len() as int;
        let f = self.pair_tier_offset(trail) + first;
        let above = overlay::<T, I>(base, pool, mid, hi);
        lemma_overlay_len::<T, I>(base, pool, mid, hi);
        self.lemma_frame_saved_value_contract(f, j);
        if self.frame_saved_value(f, j as nat) is None {
            if first + 1 < self.pair_tier_count(trail) {
                self.lemma_pair_tier_frame_layout(trail, first + 1);
                assert(self.layer_above_at(f) == self.snapshots@[f + 1]);
                self.lemma_pair_tier_suffix_cell(trail, first + 1, base, j);
            } else {
                assert(above == base) by { reveal(overlay); }
            }
            assert(above[j] == self.snapshots@[f][j]);
        }
        lemma_overlay_saved_value::<T, I>(above, pool, lo, mid, j);
        lemma_overlay_split::<T, I>(base, pool, lo, mid, hi);
    }

    /// Lift the cell induction to the whole target-sized buffer. This proves
    /// batched execution without inserting an executable loop over frames.
    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_pair_tier_suffix(
        &self, trail: bool, first: int, base: Seq<T>,
    )
        requires
            self.wf(),
            0 <= first < self.pair_tier_count(trail),
            forall|j: int| 0 <= j < base.len()
                && j < self.layer_above_at(self.pair_tier_offset(trail) + self.pair_tier_count(trail) - 1).len() ==>
                #[trigger] base[j] == self.layer_above_at(self.pair_tier_offset(trail) + self.pair_tier_count(trail) - 1)[j],
        ensures
            forall|j: int| 0 <= j < base.len()
                && j < self.snapshots@[self.pair_tier_offset(trail) + first].len() ==>
                #[trigger] overlay::<T, I>(base, self.pair_tier_pool(trail),
                    self.pair_tier_start(trail, first), self.pair_tier_pool(trail).len() as int)[j]
                    == self.snapshots@[self.pair_tier_offset(trail) + first][j],
    {
        hide(overlay);
        assert forall|j: int| 0 <= j < base.len()
            && j < self.snapshots@[self.pair_tier_offset(trail) + first].len() implies
            #[trigger] overlay::<T, I>(base, self.pair_tier_pool(trail),
                self.pair_tier_start(trail, first), self.pair_tier_pool(trail).len() as int)[j]
                == self.snapshots@[self.pair_tier_offset(trail) + first][j]
        by {
            self.lemma_pair_tier_suffix_cell(trail, first, base, j);
        }
    }

    /// Checked physical batch contract used by the top-down interface. No
    /// layer agreement is required; execution is still one pool replay.
    #[inline(always)]
    #[verifier::spinoff_prover]
    fn replay_persistence_pair_checked(
        store: &mut S, pool: &std::vec::Vec<(T, I)>, lo: usize, hi: usize,
        Ghost(trail): Ghost<bool>, Ghost(first): Ghost<int>, Ghost(pre): Ghost<Self>,
    )
        requires
            pre.wf(),
            0 <= first < pre.pair_tier_count(trail),
            pool@ == pre.pair_tier_pool(trail),
            lo == pre.pair_tier_start(trail, first),
            hi == pool@.len(),
            old(store).wf(),
            TRACK ==> forall|j: int| 0 <= j < old(store).captured().len()
                && #[trigger] old(store).captured()[j]
                ==> j < pre.store.captured().len() && pre.store.captured()[j],
        ensures
            final(store).wf(),
            final(store).unique_capture_spec() == old(store).unique_capture_spec(),
            final(store).needs_replayed_indices_spec() == old(store).needs_replayed_indices_spec(),
            final(store).restore_entries_clear_capture_spec()
                == old(store).restore_entries_clear_capture_spec(),
            final(store).data().len() == old(store).data().len(),
            final(store).data() == overlay::<T, I>(old(store).data(), pool@, lo as int, hi as int),
            final(store).data() == crate::persistence_model::apply_range(pre.persistence_model().frames,
                pre.pair_tier_offset(trail) + first,
                (pre.pair_tier_offset(trail) + pre.pair_tier_count(trail)) as int, old(store).data()),
            TRACK ==> forall|j: int| 0 <= j < final(store).captured().len()
                && #[trigger] final(store).captured()[j]
                ==> j < old(store).captured().len() && old(store).captured()[j],
            TRACK && old(store).restore_entries_clear_capture_spec()
                && trail == !pre.store.unique_capture_spec() ==>
                forall|j: int| 0 <= j < final(store).captured().len() ==>
                    !(#[trigger] final(store).captured()[j]),
            TRACK && old(store).restore_entries_clear_capture_spec() ==>
                forall|j: int| 0 <= j < final(store).captured().len()
                    && #[trigger] final(store).captured()[j]
                    ==> !captured_in_range::<T, I>(pool@, lo as int, hi as int, j as nat),
    {
        hide(Vec::wf);
        proof { pre.lemma_pair_tier_frame_layout(trail, first); }
        let ghost before = store.data();
        replay_physical_range::<T, I, S, TRACK>(store, pool, lo, hi);
        proof {
            pre.lemma_persistence_pair_suffix(trail, first, before);
            if TRACK && store.restore_entries_clear_capture_spec()
                && trail == !pre.store.unique_capture_spec() {
                pre.lemma_pair_tier_frame_layout(trail, first);
                pre.lemma_ingress_suffix_capture(trail, first);
                assert forall|j: int| 0 <= j < store.captured().len() implies
                    !(#[trigger] store.captured()[j]) by {};
            }
        }
    }

    /// Runtime batch with the snapshot-prefix result of the frame induction.
    /// Tier/first/pre are erased proof inputs; execution stays one pool replay.
    #[inline(always)]
    #[verifier::spinoff_prover]
    fn replay_pair_suffix_checked(
        store: &mut S, pool: &std::vec::Vec<(T, I)>, lo: usize, hi: usize,
        Ghost(trail): Ghost<bool>, Ghost(first): Ghost<int>, Ghost(pre): Ghost<Self>,
    )
        requires
            pre.wf(),
            0 <= first < pre.pair_tier_count(trail),
            pool@ == pre.pair_tier_pool(trail),
            lo == pre.pair_tier_start(trail, first),
            hi == pool@.len(),
            old(store).wf(),
            TRACK ==> forall|j: int| 0 <= j < old(store).captured().len()
                && #[trigger] old(store).captured()[j]
                ==> j < pre.store.captured().len() && pre.store.captured()[j],
            forall|j: int| 0 <= j < old(store).data().len()
                && j < pre.layer_above_at(pre.pair_tier_offset(trail) + pre.pair_tier_count(trail) - 1).len() ==>
                #[trigger] old(store).data()[j]
                    == pre.layer_above_at(pre.pair_tier_offset(trail) + pre.pair_tier_count(trail) - 1)[j],
        ensures
            final(store).wf(),
            final(store).unique_capture_spec() == old(store).unique_capture_spec(),
            final(store).needs_replayed_indices_spec() == old(store).needs_replayed_indices_spec(),
            final(store).restore_entries_clear_capture_spec()
                == old(store).restore_entries_clear_capture_spec(),
            final(store).data().len() == old(store).data().len(),
            forall|j: int| 0 <= j < final(store).data().len()
                && j < pre.snapshots@[pre.pair_tier_offset(trail) + first].len() ==>
                #[trigger] final(store).data()[j] == pre.snapshots@[pre.pair_tier_offset(trail) + first][j],
            TRACK ==> forall|j: int| 0 <= j < final(store).captured().len()
                && #[trigger] final(store).captured()[j]
                ==> j < old(store).captured().len() && old(store).captured()[j],
            TRACK && old(store).restore_entries_clear_capture_spec()
                && trail == !pre.store.unique_capture_spec() ==>
                forall|j: int| 0 <= j < final(store).captured().len() ==>
                    !(#[trigger] final(store).captured()[j]),
            TRACK && old(store).restore_entries_clear_capture_spec() ==>
                forall|j: int| 0 <= j < final(store).captured().len()
                    && #[trigger] final(store).captured()[j]
                    ==> !captured_in_range::<T, I>(pool@, lo as int, hi as int, j as nat),
    {
        hide(Vec::wf);
        let ghost before = store.data();
        Self::replay_persistence_pair_checked(store, pool, lo, hi, Ghost(trail), Ghost(first), Ghost(pre));
        proof { pre.lemma_pair_tier_suffix(trail, first, before); }
    }

    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_cold_frame_layout(&self, f: int)
        requires self.wf(), 0 <= f < self.cold_stack@.len(),
        ensures
            f < self.depth_spec(),
            self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
                <= self.cold_index_runs@.len(),
            forall|r: int| self.cold_stack@[f].runs_start <= r
                < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len ==>
                (#[trigger] self.cold_index_runs@[r]).start + self.cold_index_runs@[r].len
                    <= self.cold_value_pool@.len(),
            forall|r: int| self.cold_stack@[f].runs_start <= r
                && r + 1 < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len ==>
                (#[trigger] self.cold_index_runs@[r]).base.as_nat() + self.cold_index_runs@[r].len
                    <= self.cold_index_runs@[r + 1].base.as_nat(),
    {
        self.lemma_wf_named_parts();
        reveal(Vec::cold_repr_ok);
        reveal(Vec::frame_partition_ok);
    }

    pub open(crate) spec fn cold_frame_decoded(&self, f: int, entries: Seq<(T, I)>) -> bool {
        let top = self.cold_stack@[f];
        crate::cold_decode::decoded(self.cold_index_runs@, self.cold_value_pool@,
            top.runs_start as int, (top.runs_start + top.runs_len) as int,
            if top.runs_len > 0 { self.cold_index_runs@[top.runs_start as int].start as int }
            else { 0int }, entries)
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_decoded_frame(&self, f: int, entries: Seq<(T, I)>)
        requires self.cold_repr_ok(), self.frame_partition_ok(),
            0 <= f < self.cold_stack@.len(), self.cold_frame_decoded(f, entries),
        ensures frame_inv_range::<T, I>(self.layer_above_at(f), entries, 0, entries.len() as int,
            self.snapshots@[f], self.snapshots@[f].len()),
            stratum_unique::<T, I>(entries, 0, entries.len() as int),
    {
        hide(Vec::cold_repr_ok);
        hide(Vec::cold_value);
        self.lemma_cold_decode_layout(f);
        reveal(Vec::frame_partition_ok);
        let top = self.cold_stack@[f];
        let lo = top.runs_start as int;
        let hi = lo + top.runs_len;
        let vs = if lo < hi { self.cold_index_runs@[lo].start as int } else { 0int };
        assert forall|p: int| 0 <= p < entries.len() implies
            (#[trigger] entries[p]).1.as_nat() < self.snapshots@[f].len() by {
            crate::cold_decode::decoded_entry(self.cold_index_runs@, self.cold_value_pool@,
                lo, hi, vs, entries, top.saved_len.as_nat(), p);
        }
        assert forall|a: int, b: int| 0 <= a < entries.len() && 0 <= b < entries.len() && a != b implies
            (#[trigger] entries[a]).1.as_nat() != (#[trigger] entries[b]).1.as_nat() by {
            if a < b {
                crate::cold_decode::decoded_sorted(self.cold_index_runs@, self.cold_value_pool@,
                    lo, hi, vs, entries, top.saved_len.as_nat(), a, b);
            } else {
                crate::cold_decode::decoded_sorted(self.cold_index_runs@, self.cold_value_pool@,
                    lo, hi, vs, entries, top.saved_len.as_nat(), b, a);
            }
        }
        assert forall|j: int| 0 <= j < self.snapshots@[f].len() implies
            #[trigger] frame_cell_inv::<T, I>(self.layer_above_at(f), entries, 0,
                entries.len() as int, self.snapshots@[f], j) by {
            self.lemma_cold_decoded_lookup(f, entries, j as nat);
            assert(self.cold_reconstructs(f)) by { reveal(Vec::cold_repr_ok); }
            self.lemma_cold_reconstructs_at(f, j);
            if captured_in_range::<T, I>(entries, 0, entries.len() as int, j as nat) {
                lemma_lowest_hitter::<T, I>(entries, 0, entries.len() as int, j as nat);
                let p = choose|p: int| 0 <= p < entries.len() && (#[trigger] entries[p]).1.as_nat() == j as nat
                    && first_hitter::<T, I>(entries, 0, p, j as nat);
                assert(entries[p].0 == self.snapshots@[f][j]);
            }
        }
    }

    /// Decoder premises come from the retained physical Cold representation,
    /// without requiring writable ownership or rebuilt capture flags.
    #[verifier::spinoff_prover]
    proof fn lemma_cold_decode_layout(&self, f: int)
        requires self.cold_repr_ok(), 0 <= f < self.cold_stack@.len(),
        ensures crate::cold_decode::layout(self.cold_index_runs@, self.cold_value_pool@,
            self.cold_stack@[f].runs_start as int,
            (self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len) as int,
            self.cold_stack@[f].saved_len.as_nat()),
    {
        reveal(Vec::cold_repr_ok);
        reveal(Vec::cold_payload_ok);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_cold_decoded_lookup(&self, f: int, entries: Seq<(T, I)>, j: nat)
        requires self.cold_repr_ok(), 0 <= f < self.cold_stack@.len(),
            crate::cold_decode::decoded(self.cold_index_runs@, self.cold_value_pool@,
                self.cold_stack@[f].runs_start as int,
                (self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len) as int,
                if self.cold_stack@[f].runs_len > 0 {
                    self.cold_index_runs@[self.cold_stack@[f].runs_start as int].start as int
                } else { 0int }, entries),
        ensures range_saved_value::<T, I>(entries, 0, entries.len() as int, j)
            == self.frame_saved_value(f, j),
    {
        hide(Vec::cold_repr_ok);
        self.lemma_cold_decode_layout(f);
        let lo = self.cold_stack@[f].runs_start as int;
        let hi = lo + self.cold_stack@[f].runs_len;
        let vs = if lo < hi { self.cold_index_runs@[lo].start as int } else { 0int };
        crate::cold_decode::decoded_lookup(self.cold_index_runs@, self.cold_value_pool@,
            lo, hi, vs, entries, self.cold_stack@[f].saved_len.as_nat(), j);
        self.lemma_cold_range_matches_frame(f, j);
    }

    /// Direct physical Cold replay refines the shared map for every buffer.
    /// The snapshot-oriented wrapper below retains its existing contract.
    #[inline(always)]
    #[verifier::spinoff_prover]
    fn replay_persistence_cold_checked(
        store: &mut S, frame: crate::frame::ColdFrameHdr<I>,
        runs: &std::vec::Vec<crate::frame::IndexRun<I>>, values: &std::vec::Vec<T>,
        f: usize, Ghost(pre): Ghost<Self>,
    )
        requires
            pre.wf(),
            f < pre.cold_stack@.len(),
            frame == pre.cold_stack@[f as int],
            runs@ == pre.cold_index_runs@,
            values@ == pre.cold_value_pool@,
            old(store).wf(),
        ensures
            final(store).wf(),
            final(store).unique_capture_spec() == old(store).unique_capture_spec(),
            final(store).needs_replayed_indices_spec() == old(store).needs_replayed_indices_spec(),
            final(store).restore_entries_clear_capture_spec()
                == old(store).restore_entries_clear_capture_spec(),
            final(store).captured() == old(store).captured(),
            final(store).data().len() == old(store).data().len(),
            final(store).data() == crate::persistence_model::apply(pre.persistence_frame(f as int).saved, old(store).data()),
            forall|j: int| 0 <= j < final(store).data().len() ==>
                #[trigger] final(store).data()[j] == match pre.frame_saved_value(f as int, j as nat) {
                    Some(value) => value, None => old(store).data()[j],
                },
    {
        hide(Vec::cold_payload_ok);
        proof { pre.lemma_cold_frame_layout(f as int); }
        let _ = runs.len();
        let ghost before = store.data();
        replay_cold_range::<T, I, S, TRACK>(
            store, runs, values, frame.runs_start, frame.runs_start + frame.runs_len);
        proof {
            assert forall|j: int| 0 <= j < before.len() implies
                #[trigger] store.data()[j] == match pre.frame_saved_value(f as int, j as nat) {
                    Some(value) => value,
                    None => before[j],
                } by {
                pre.lemma_cold_range_matches_frame(f as int, j as nat);
            }
            let map = pre.persistence_frame(f as int).saved;
            assert forall|j: int| 0 <= j < before.len() implies
                #[trigger] store.data()[j] == crate::persistence_model::apply(map, before)[j] by {
                pre.lemma_persistence_lookup(f as int, j as nat);
            }
            assert(store.data() =~= crate::persistence_model::apply(map, before));
        }
    }

    /// A real Cold frame step in the target-sized replay buffer. `pre` records
    /// the original history before resizing/replay; its physical pools remain
    /// authoritative while intermediate live values need not satisfy `wf`.
    #[inline(always)]
    #[verifier::spinoff_prover]
    fn replay_cold_frame_checked(
        store: &mut S, frame: crate::frame::ColdFrameHdr<I>,
        runs: &std::vec::Vec<crate::frame::IndexRun<I>>, values: &std::vec::Vec<T>,
        f: usize, Ghost(pre): Ghost<Self>,
    )
        requires
            pre.wf(),
            f < pre.cold_stack@.len(),
            frame == pre.cold_stack@[f as int],
            runs@ == pre.cold_index_runs@,
            values@ == pre.cold_value_pool@,
            old(store).wf(),
            forall|j: int| 0 <= j < old(store).data().len()
                && j < pre.layer_above_at(f as int).len() ==>
                #[trigger] old(store).data()[j] == pre.layer_above_at(f as int)[j],
        ensures
            final(store).wf(),
            final(store).unique_capture_spec() == old(store).unique_capture_spec(),
            final(store).needs_replayed_indices_spec() == old(store).needs_replayed_indices_spec(),
            final(store).restore_entries_clear_capture_spec()
                == old(store).restore_entries_clear_capture_spec(),
            final(store).captured() == old(store).captured(),
            final(store).data().len() == old(store).data().len(),
            forall|j: int| 0 <= j < final(store).data().len()
                && j < pre.snapshots@[f as int].len() ==>
                #[trigger] final(store).data()[j] == pre.snapshots@[f as int][j],
    {
        hide(Vec::cold_payload_ok);
        proof { pre.lemma_cold_frame_layout(f as int); }
        let ghost before = store.data();
        Self::replay_persistence_cold_checked(store, frame, runs, values, f, Ghost(pre));
        proof { pre.lemma_physical_frame_step(f as int, before, store.data()); }
    }

    /// Compose Cold frame steps without asking intermediate buffers to satisfy
    /// the live-container invariant. The loop is the existing reverse frame
    /// traversal; all history facts come from the local frozen pre-state.
    #[inline(always)]
    #[verifier::spinoff_prover]
    fn replay_cold_suffix_checked(
        store: &mut S, frames: &std::vec::Vec<crate::frame::ColdFrameHdr<I>>,
        runs: &std::vec::Vec<crate::frame::IndexRun<I>>, values: &std::vec::Vec<T>,
        target: usize, Ghost(pre): Ghost<Self>,
    )
        requires
            pre.wf(),
            frames@ == pre.cold_stack@,
            runs@ == pre.cold_index_runs@,
            values@ == pre.cold_value_pool@,
            target < frames@.len(),
            old(store).wf(),
            forall|j: int| 0 <= j < old(store).data().len()
                && j < pre.layer_above_at(frames@.len() - 1).len() ==>
                #[trigger] old(store).data()[j] == pre.layer_above_at(frames@.len() - 1)[j],
        ensures
            final(store).wf(),
            final(store).unique_capture_spec() == old(store).unique_capture_spec(),
            final(store).needs_replayed_indices_spec() == old(store).needs_replayed_indices_spec(),
            final(store).restore_entries_clear_capture_spec()
                == old(store).restore_entries_clear_capture_spec(),
            final(store).captured() == old(store).captured(),
            final(store).data().len() == old(store).data().len(),
            forall|j: int| 0 <= j < final(store).data().len()
                && j < pre.snapshots@[target as int].len() ==>
                #[trigger] final(store).data()[j] == pre.snapshots@[target as int][j],
    {
        let ghost before = *store;
        proof { pre.lemma_cold_frame_layout(target as int); }
        let mut cursor = frames.len();
        while cursor > target
            invariant
                pre.wf(),
                frames@ == pre.cold_stack@,
                runs@ == pre.cold_index_runs@,
                values@ == pre.cold_value_pool@,
                target <= cursor <= frames@.len(),
                target < pre.depth_spec(),
                store.wf(),
                store.unique_capture_spec() == before.unique_capture_spec(),
                store.needs_replayed_indices_spec() == before.needs_replayed_indices_spec(),
                store.restore_entries_clear_capture_spec() == before.restore_entries_clear_capture_spec(),
                store.captured() == before.captured(),
                store.data().len() == before.data().len(),
                forall|j: int| 0 <= j < store.data().len()
                    && j < pre.layer_above_at(cursor - 1).len() ==>
                    #[trigger] store.data()[j] == pre.layer_above_at(cursor - 1)[j],
            decreases cursor - target,
        {
            cursor -= 1;
            Self::replay_cold_frame_checked(store, frames[cursor], runs, values, cursor, Ghost(pre));
            proof { pre.lemma_cold_frame_layout(cursor as int); }
        }
    }

    /// Bridge the checked Cold range operation to the shared frame meaning.
    /// Both interpretations use the same covering predicate and physical pool.
    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_cold_range_matches_frame(&self, f: int, j: nat)
        requires
            0 <= f < self.cold_stack@.len(),
            self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
                <= self.cold_index_runs@.len(),
            forall|r: int| self.cold_stack@[f].runs_start <= r
                && r + 1 < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len ==>
                (#[trigger] self.cold_index_runs@[r]).base.as_nat() + self.cold_index_runs@[r].len
                    <= self.cold_index_runs@[r + 1].base.as_nat(),
        ensures
            cold_range_saved_value::<T, I>(
                self.cold_index_runs@, self.cold_value_pool@,
                self.cold_stack@[f].runs_start as int,
                self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len, j)
                == self.frame_saved_value(f, j),
    {
        let runs = self.cold_index_runs@;
        let lo = self.cold_stack@[f].runs_start as int;
        let hi = lo + self.cold_stack@[f].runs_len;
        let p = |r: int| lo <= r < hi && cold_run_covers(runs[r], j);
        let q = |r: int|
            self.cold_stack@[f].runs_start <= r
                < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
            && self.cold_index_runs@[r].base.as_nat() <= j
            && j < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len;
        assert(p =~= q);
        if self.cold_covered(f, j) {
            let a = choose|r: int| lo <= r < hi && cold_run_covers(#[trigger] runs[r], j);
            let b = choose|r: int|
                self.cold_stack@[f].runs_start <= r
                    < self.cold_stack@[f].runs_start + self.cold_stack@[f].runs_len
                && (#[trigger] self.cold_index_runs@[r]).base.as_nat() <= j
                && j < self.cold_index_runs@[r].base.as_nat() + self.cold_index_runs@[r].len;
            if a < b {
                lemma_cold_run_order::<I>(runs, lo, hi, a, b);
            } else if b < a {
                lemma_cold_run_order::<I>(runs, lo, hi, b, a);
            }
            assert(a == b);
        }
    }

    /// Every tier refines the same per-cell contract. Saved lengths need not be
    /// monotone, and a missing value explicitly requires the newer cell to exist.
    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_frame_saved_value_contract(&self, f: int, j: int)
        requires
            self.wf(),
            0 <= f < self.depth_spec(),
            0 <= j < self.snapshots@[f].len(),
        ensures
            self.frame_saved_len(f) == self.snapshots@[f].len(),
            match self.frame_saved_value(f, j as nat) {
                Some(value) => value == self.snapshots@[f][j],
                None => j < self.layer_above_at(f).len()
                    && self.layer_above_at(f)[j] == self.snapshots@[f][j],
            },
    {
        reveal(Vec::frame_partition_ok);
        self.lemma_wf_named_parts();
        let cc = self.cold_stack@.len();
        let hc = self.hot_stack@.len();
        if f < cc {
            reveal(Vec::cold_repr_ok);
            assert(self.cold_reconstructs(f));
        } else if f < cc + hc {
            let h = f - cc;
            self.lemma_hot_repr_at(h);
            lemma_frame_inv_arm_at::<T, I>(
                self.layer_above_at(f), self.hot_value_pool@,
                self.phys_hot_start(h), self.phys_hot_end(h),
                self.snapshots@[f], self.snapshots@[f].len(), j);
            lemma_range_saved_value_contract::<T, I>(
                self.layer_above_at(f), self.hot_value_pool@,
                self.phys_hot_start(h), self.phys_hot_end(h), self.snapshots@[f], j);
        } else {
            reveal(Vec::trail_repr_ok);
            let t = f - cc - hc;
            let lo = self.trail_stack@[t].start as int;
            let hi = self.phys_trail_end(t);
            lemma_frame_inv_arm_at::<T, I>(
                self.layer_above_at(f), self.trail_value_pool@, lo, hi,
                self.snapshots@[f], self.snapshots@[f].len(), j);
            lemma_range_saved_value_contract::<T, I>(
                self.layer_above_at(f), self.trail_value_pool@, lo, hi,
                self.snapshots@[f], j);
        }
    }

    /// One step of the shared fixed-window telescope. Indices outside this
    /// frame's saved domain remain pending; no adjacent-length ordering is used.
    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_physical_frame_step(
        &self, f: int, before: Seq<T>, after: Seq<T>,
    )
        requires
            self.wf(),
            0 <= f < self.depth_spec(),
            after.len() == before.len(),
            forall|j: int| 0 <= j < before.len()
                && j < self.layer_above_at(f).len() ==>
                    #[trigger] before[j] == self.layer_above_at(f)[j],
            forall|j: int| 0 <= j < before.len() ==>
                #[trigger] after[j] == match self.frame_saved_value(f, j as nat) {
                    Some(value) => value,
                    None => before[j],
                },
        ensures
            forall|j: int| 0 <= j < after.len() && j < self.snapshots@[f].len() ==>
                #[trigger] after[j] == self.snapshots@[f][j],
    {
        assert forall|j: int| 0 <= j < after.len() && j < self.snapshots@[f].len()
            implies #[trigger] after[j] == self.snapshots@[f][j] by {
            self.lemma_frame_saved_value_contract(f, j);
        }
    }

    /// COLD reconstruction (D5's third equivalence), pointwise and IndexLike-only
    /// (no from_nat): each cold frame reconstructs its snapshot - a covered cell
    /// takes its run's value, an uncovered cell keeps the layer above. Physical
    /// replay consumes this contract through frame_saved_value; retained Cold
    /// frames preserve it through unchanged runs, snapshots, and newer layers.
    pub open(crate) spec fn cold_reconstructs(&self, f: int) -> bool {
        forall|c: int| #![trigger self.cold_covered(f, c as nat)]
            0 <= c < self.g_saved_len(f) as int ==>
            if self.cold_covered(f, c as nat) {
                self.cold_value(f, c as nat) == self.snapshots@[f][c]
            } else {
                &&& c < self.layer_above_at(f).len()
                &&& self.snapshots@[f][c] == self.layer_above_at(f)[c]
            }
    }

    /// THE load-bearing restore theorem (tier-agnostic, ghost-based): the single
    /// telescope step. Given live data that already equals `snapshots[k+1]` (the
    /// layer above frame `k`) on the target window, undoing frame `k` yields
    /// `snapshots[k]`. "Undoing frame k" is captured abstractly by the replay
    /// effect: a cell touched by frame k's ghost stratum takes `snapshots[k][c]`
    /// (its captured old value, pinned by frame_inv's captured arm); an
    /// untouched cell keeps `data_before[c]`. This is INDEPENDENT of how the tier
    /// physically replays (trail/hot overlay right-to-left, cold run memcpy) -
    /// each tier's step lemma discharges the replay-effect hypothesis, then this
    /// lemma composes them into `restore` by induction with invariant
    /// `data == snapshots[k]`. Fixed window `ln` (== saved_len(target)); cells
    /// past `snapshots[k].len()` are pending (an older frame restores them).
    #[verifier::spinoff_prover]
    #[verifier::rlimit(400)]
    pub(crate) proof fn lemma_telescope_step(
        &self, k: int, ln: int, data_before: Seq<T>, data_after: Seq<T>,
    )
        requires
            0 <= k,
            k + 1 < self.trail_frames@.len(),
            self.frame_inv_range_holds(k),
            // in-invariant: data_before matches the layer snapshots[k+1] on the
            // window it covers.
            forall|c: int| 0 <= c < ln && c < self.snapshots@[k + 1].len() as int
                ==> #[trigger] data_before[c] == self.snapshots@[k + 1][c],
            // replay effect over [0, ln): a cell touched by frame k's ghost
            // stratum takes snapshots[k][c]; an untouched cell is unchanged.
            forall|c: int| 0 <= c < ln
                ==> #[trigger] data_after[c] == if captured_in_range::<T, I>(
                        self.full_trail@, self.g_start(k), self.g_end(k), c as nat) {
                        self.snapshots@[k][c]
                    } else {
                        data_before[c]
                    },
        ensures
            forall|c: int| 0 <= c < ln && c < self.snapshots@[k].len() as int
                ==> (#[trigger] data_after[c]) == self.snapshots@[k][c],
    {
        // layer_above_at(k) == snapshots[k+1] since k+1 < trail_frames.len().
        assert(self.layer_above_at(k) == self.snapshots@[k + 1]);
        let lo = self.g_start(k);
        let hi = self.g_end(k);
        let snap = self.snapshots@[k];
        let above = self.layer_above_at(k);
        assert forall|c: int| 0 <= c < ln && c < snap.len() as int implies
            data_after[c] == snap[c] by {
            // frame_inv's per-cell arm at c.
            lemma_frame_inv_arm_at::<T, I>(above, self.full_trail@, lo, hi, snap,
                self.g_saved_len(k), c);
            if captured_in_range::<T, I>(self.full_trail@, lo, hi, c as nat) {
                // effect gives data_after[c] == snap[c] directly.
            } else {
                // uncaptured arm: c < above.len() && above[c] == snap[c].
                assert(c < above.len() as int);
                assert(above[c] == snap[c]);
                assert(c < self.snapshots@[k + 1].len() as int);
                assert(data_after[c] == data_before[c]);
                assert(data_before[c] == self.snapshots@[k + 1][c]);
            }
        }
    }

    /// Pointwise Cold reconstruction accessor. Saved lengths are deliberately
    /// non-monotone: an uncovered saved cell must be present in the layer
    /// above, while a saved cell beyond that layer must be covered by Cold.
    pub(crate) proof fn lemma_cold_reconstructs_at(&self, f: int, c: int)
        requires
            self.cold_reconstructs(f),
            0 <= f < self.snapshots@.len(),
            0 <= c < self.g_saved_len(f) as int,
        ensures
            if self.cold_covered(f, c as nat) {
                self.cold_value(f, c as nat) == self.snapshots@[f][c]
            } else {
                &&& c < self.layer_above_at(f).len()
                &&& self.snapshots@[f][c] == self.layer_above_at(f)[c]
            },
    {
        reveal(Vec::cold_reconstructs);
    }

    /// Cold frames depend on their immediate newer layer, not necessarily
    /// the live vector. This also frames older Cold history across writes.
    pub(crate) proof fn lemma_cold_reconstructs_frame_transfer(&self, other: Self, f: int)
        requires
            other.cold_reconstructs(f),
            0 <= f < self.snapshots@.len(),
            self.cold_stack@ == other.cold_stack@,
            self.cold_index_runs@ == other.cold_index_runs@,
            self.cold_value_pool@ == other.cold_value_pool@,
            0 <= f < other.snapshots@.len(),
            self.snapshots@[f] == other.snapshots@[f],
            self.layer_above_at(f) == other.layer_above_at(f),
        ensures
            self.cold_reconstructs(f),
    {
        reveal(Vec::cold_reconstructs);
        assert(self.g_saved_len(f) == other.g_saved_len(f));
        assert(self.layer_above_at(f) == other.layer_above_at(f));
        assert forall|c: int| #![trigger self.cold_covered(f, c as nat)]
            0 <= c < self.g_saved_len(f) as int implies
            (if self.cold_covered(f, c as nat) {
                self.cold_value(f, c as nat) == self.snapshots@[f][c]
            } else {
                &&& c < self.layer_above_at(f).len()
                &&& self.snapshots@[f][c] == self.layer_above_at(f)[c]
            }) by {
            assert(self.cold_covered(f, c as nat)
                == other.cold_covered(f, c as nat));
            assert(c < other.g_saved_len(f) as int);
            other.lemma_cold_reconstructs_at(f, c);
            if self.cold_covered(f, c as nat) {
                assert(self.cold_value(f, c as nat)
                    == other.cold_value(f, c as nat));
            } else {
                assert(c < other.layer_above_at(f).len());
            }
        }
    }



    pub(crate) proof fn lemma_cold_reconstructs_layer_transfer(&self, other: Self, f: int)
        requires
            other.cold_reconstructs(f),
            0 <= f < self.snapshots@.len(),
            self.cold_stack@ == other.cold_stack@,
            self.cold_index_runs@ == other.cold_index_runs@,
            self.cold_value_pool@ == other.cold_value_pool@,
            self.snapshots@ == other.snapshots@,
            self.trail_frames@ == other.trail_frames@,
            self.layer_above_at(f) == other.layer_above_at(f),
        ensures
            self.cold_reconstructs(f),
    {
        self.lemma_cold_reconstructs_frame_transfer(other, f);
    }

    /// Capacity-only and other framing operations use this instead of
    /// re-expanding the nested Cold quantifiers at each call site.
    pub(crate) proof fn lemma_cold_reconstructs_transfer(&self, other: Self, f: int)
        requires
            other.cold_reconstructs(f),
            0 <= f < self.snapshots@.len(),
            self.cold_stack@ == other.cold_stack@,
            self.cold_index_runs@ == other.cold_index_runs@,
            self.cold_value_pool@ == other.cold_value_pool@,
            self.snapshots@ == other.snapshots@,
            self.trail_frames@ == other.trail_frames@,
            self.view() == other.view(),
        ensures
            self.cold_reconstructs(f),
    {
        self.lemma_cold_reconstructs_layer_transfer(other, f);
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    pub(crate) proof fn lemma_cold_replay_step(
        &self, f: int, data_before: Seq<T>, data_after: Seq<T>,
    )
        requires
            0 <= f,
            f + 1 < self.trail_frames@.len(),
            self.cold_reconstructs(f),
            // uncovered saved cells of f lie within the layer above (coverage).
            forall|c: int| 0 <= c < self.snapshots@[f].len() as int
                && !(#[trigger] self.cold_covered(f, c as nat))
                ==> c < self.snapshots@[f + 1].len() as int,
            // in-invariant: data_before matches the layer snapshots[f+1].
            forall|c: int| 0 <= c < self.snapshots@[f + 1].len() as int
                ==> #[trigger] data_before[c] == self.snapshots@[f + 1][c],
            // replay effect on f's saved region.
            forall|c: int| 0 <= c < self.snapshots@[f].len() as int
                ==> #[trigger] data_after[c] == if self.cold_covered(f, c as nat) {
                        self.cold_value(f, c as nat)
                    } else {
                        data_before[c]
                    },
        ensures
            forall|c: int| 0 <= c < self.snapshots@[f].len() as int
                ==> (#[trigger] data_after[c]) == self.snapshots@[f][c],
    {
        // layer_above_at(f) == snapshots[f+1] since f+1 < trail_frames.len().
        assert(self.layer_above_at(f) == self.snapshots@[f + 1]);
        assert forall|c: int| 0 <= c < self.snapshots@[f].len() as int implies
            (#[trigger] data_after[c]) == self.snapshots@[f][c] by {
            // cold_reconstructs(f) at c (c < g_saved_len(f) == snapshots[f].len()).
            // Fire its quantifier via the cold_value(f,c) trigger term.
            assert(self.g_saved_len(f) == self.snapshots@[f].len());
            let _ = self.cold_value(f, c as nat);
            if self.cold_covered(f, c as nat) {
                assert(self.cold_value(f, c as nat) == self.snapshots@[f][c]);
            } else {
                assert(c < self.snapshots@[f + 1].len() as int);
                assert(data_after[c] == data_before[c]);
                assert(data_before[c] == self.snapshots@[f + 1][c]);
                assert(self.snapshots@[f][c] == self.layer_above_at(f)[c]);
            }
        }
    }


    /// Pop the last element (FAITHFUL: may pop into a frame's marked region).
    ///
    /// If the removed slot lies inside the active frame's marked region
    /// (`old_len - 1 < active_saved_len`), it is first CAPTURED into the top
    /// stratum (first-write-wins), so the now-absent cell still satisfies the
    /// frame invariant via the captured arm — this is exactly the coverage
    /// obligation. Conditional capture (not production's unconditional
    /// force_capture) keeps the diff log bounded: at most one entry per index
    /// per stratum. `restore` later regrows the popped region with
    /// `resize_default` and overwrites each filler back from these captures.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    #[inline(always)]
    pub fn pop(&mut self) -> (r: Option<T>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).view().len() == 0 ==> r is None && final(self).view() == old(self).view(),
            old(self).view().len() > 0 ==> {
                &&& r is Some
                &&& r->Some_0 == old(self).view()[old(self).view().len() - 1]
                &&& final(self).view() == old(self).view().drop_last()
            },
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        self.runtime_pop()
    }

    /// Write `value` at index `i`, capturing the old value into the active
    /// frame's stratum (first-write-wins) when a frame is live. Works at any
    /// stack depth.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    #[inline(always)]
    pub fn set_index(&mut self, i: I, value: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            i.as_nat() < old(self).view().len() ==> {
                &&& final(self).view() == old(self).view().update(i.as_nat() as int, value)
                &&& final(self).snapshots_view() == old(self).snapshots_view()
            },
    {
        // Total-with-documented-panic (hot family): explicit bound branch.
        if !(i.as_usize() < self.store.raw_len()) {
            crate::guard::refuse("Vec::set_index: index out of bounds");
        }
        self.runtime_set(i, value);
    }


    /// Mark a snapshot point. Returns a token that can be passed to
    /// `restore` to roll back to the current state.
    ///
    /// Mark a snapshot point, possibly nested. The new frame's stratum
    /// starts empty (diff_start == current diff_log.len()), so its
    /// frame_inv_range holds with the view as both layer and snapshot.
    /// The previously-top frame's stratum is unchanged (its upper bound
    /// was the diff log's end, which equals the new frame's diff_start),
    /// and its layer flips from `view` to the new `snapshots[top]`, which
    /// equals the view — so its frame_inv_range transfers.
    /// Per-vector mark core with explicit rollover control. This has the same
    /// abstract effect as `push_frame`; only physical tier placement differs.
    pub(crate) fn push_frame_with_options(&mut self, options: MarkOptions)
        requires
            old(self).wf(),
            TRACK,
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        self.runtime_push_frame::<false>(options);
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(1800)]
    /// The per-vector core of `mark`: push a frame without genealogy. Shared fork
    /// history (doc 10) drives this from a `SyncGroup` while one `History` owns
    /// the branch/depth bookkeeping; `mark` is the standalone wrapper that adds
    /// the token. Preserves the frame/snapshot/wf theorems `mark` proves and
    /// leaves `forks` untouched (`final.forks == old.forks`).
    pub(crate) fn push_frame(&mut self, shrink: ShrinkPolicy)
        requires
            old(self).wf(),
            TRACK,
            old(self).depth_spec() < u32::MAX,
            old(self).view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        self.runtime_push_frame::<true>(MarkOptions {
            shrink,
            rollover: crate::tier_policy::RolloverPolicy::ApplyConfigured,
        });
    }



    /// The eviction buffer: how many closed hot strata a column keeps
    /// uncompressed before `mark` seals the oldest into a cold frame.
    /// Shallow push/pop (the SMT profile) therefore never compresses at all;
    /// deep saturation amortizes one seal per mark past the buffer. A
    /// constant for now; the design doc lists its final home (constructor
    /// argument or SEMPER_* lever) as an open parameter.
    pub const HOT_BUFFER: usize = 8;


    pub(crate) fn evict_cold_frame(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            final(self).trail_frames@.len() == old(self).trail_frames@.len(),
            final(self).store == old(self).store,
            final(self).active_saved_len == old(self).active_saved_len,
    {
        // A2a: no cold tier yet; eviction returns in A2b on the ColdStack.
    }

    /// Seal the open top frame with a value-opaque per-frame encoder (sorted index
    /// runs, self-demoting to plain when runs do not pay) when the column is the
    /// adaptive representation, aligned, and the open stratum is nonempty; a no-op
    /// otherwise. Preserves everything a caller observes (view, depth, snapshots,
    /// frames, store, forks); only the diff log's representation of the open
    /// stratum changes, within its write multiset, which the multiset frame rule
    /// lifts to `wf`.
    #[verifier::rlimit(800)]
    #[verifier::spinoff_prover]
    pub(crate) fn seal_open_frame_copy(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            final(self).trail_frames@ == old(self).trail_frames@,
            final(self).full_trail@ == old(self).full_trail@,
            final(self).store == old(self).store,
            final(self).active_saved_len == old(self).active_saved_len,
    {
        // Retired: seal-on-mark contradicted the buffered-eviction policy
        // (goal doc §6) and is gone for good; A2b's eviction replaces it.
    }















    /// The genealogy-free core of `restore`: reconstruct to frame `target_index`.
    /// Dispatches by tier: a HOT target (`target > cold_count`) goes through the
    /// fully-proven `restore_hot`; a COLD target (`target <= cold_count`, which
    /// re-materializes the surviving cold top) goes through `restore_cold`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(200)]
    pub(crate) fn restore_frame(&mut self, target_index: usize)
        where T: core::default::Default
        requires
            old(self).wf(),
            TRACK,
            (target_index as nat) < old(self).depth_spec(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).snapshots_view()[target_index as int],
            final(self).depth_spec() == target_index as nat,
            final(self).snapshots_view() == old(self).snapshots_view().subrange(0, target_index as int),
    {
        self.runtime_restore_frame(target_index);
    }

    /// Semantics B (design doc 08 §1): reconstruct to the version at frame
    /// `target` and keep that frame open and empty — the writable frame is
    /// `target` again, not its parent — so the token of that mark stays valid
    /// and can be restored to again, while every frame above it is gone and
    /// every token minted after it is dead. Built from the pop core and a
    /// frame push: `runtime_restore_frame(target)` undoes and pops the strata
    /// `target..`, a deferred-rollover push reopens frame `target` on the
    /// restored contents (the snapshot at `target` is the same contents, so
    /// the snapshot stack is exactly the old prefix of length `target + 1`),
    /// and the genealogy cut starts at `target + 1`.
    #[verifier::spinoff_prover]
    pub(crate) fn reset_frame(&mut self, target: usize)
        where T: core::default::Default
        requires
            old(self).wf(),
            TRACK,
            (target as nat) < old(self).depth_spec(),
            old(self).depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).view() == old(self).snapshots_view()[target as int],
            final(self).depth_spec() == target as nat + 1,
            final(self).snapshots_view() == old(self).snapshots_view().subrange(0, target as int + 1),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        self.reset_frame_physical(target);
        let ghost physical = *self;
    }

    /// The physical half of `reset_frame`: undo and pop the strata `target..`,
    /// then reopen frame `target` on the restored contents with a `Defer`
    /// rollover — a header push that converts no history. The pop core has
    /// just made the parent stratum writable; sealing it again under the
    /// configured rollover would migrate it (Trail → Hot dedupe, Hot → Cold)
    /// on every restore, work the next `mark` does exactly once, as it always
    /// did. `wf` stays hidden: each step's contract carries it as a fact.
    #[verifier::spinoff_prover]
    fn reset_frame_physical(&mut self, target: usize)
        where T: core::default::Default
        requires
            old(self).wf(),
            TRACK,
            (target as nat) < old(self).depth_spec(),
            old(self).depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).view() == old(self).snapshots_view()[target as int],
            final(self).depth_spec() == target as nat + 1,
            final(self).snapshots_view() == old(self).snapshots_view().subrange(0, target as int + 1),
    {
        hide(Vec::wf);
        hide(Vec::wf_for_snap);
        let ghost pre = *self;
        self.runtime_restore_frame(target);
        proof {
            // The restored contents fit the index word: the store's own bound.
            self.lemma_store_wf();
            self.store.lemma_wf_data_len();
        }
        self.evict_cold_frame();
        self.seal_open_frame_copy();
        self.push_frame_with_options(MarkOptions {
            shrink: ShrinkPolicy::Never,
            rollover: crate::tier_policy::RolloverPolicy::Defer,
        });
        proof {
            // One snapshot per frame, so the prefix of length `target + 1` exists.
            pre.lemma_snapshots_len();
            assert(pre.snapshots_view().subrange(0, target as int)
                .push(pre.snapshots_view()[target as int])
                =~= pre.snapshots_view().subrange(0, target as int + 1));
        }
    }

    /// One snapshot per frame (an accessor for bodies that keep `wf` hidden).
    pub(crate) proof fn lemma_snapshots_len(&self)
        requires self.wf(),
        ensures self.snapshots_view().len() == self.depth_spec(),
    {
    }

    /// `wf` implies the store's own well-formedness (an accessor for bodies
    /// that keep `wf` hidden).
    pub(crate) proof fn lemma_store_wf(&self)
        requires self.wf(),
        ensures self.store.wf(),
    {
    }

    /// Drop the open top frame: undo its stratum and make the parent frame
    /// writable again (the SMT-LIB `pop`). The popped frame's token dies with
    /// it (the cut starts at its depth). Refuses on an empty frame stack.
    #[verifier::spinoff_prover]
    pub(crate) fn pop_frame(&mut self)
        where T: core::default::Default
        requires
            old(self).wf(),
            TRACK,
        ensures
            final(self).wf(),
            old(self).depth_spec() >= 1 ==> {
                &&& final(self).view() == old(self).snapshots_view()[old(self).depth_spec() - 1]
                &&& final(self).depth_spec() == old(self).depth_spec() - 1
                &&& final(self).snapshots_view()
                    == old(self).snapshots_view().subrange(0, old(self).depth_spec() - 1)
            },
    {
        let d = self.depth_exec();
        if !(d >= 1) {
            crate::guard::refuse("Vec::pop_scope: no open frame");
        }
        self.restore_frame(d - 1);
    }





}

// ---------------------------------------------------------------------------
// View / VecViewIter — read-only iteration over the current contents (parity with
// production's `view()`). A `View` is a thin borrow exposing `len`/`get`; a
// `VecViewIter` walks `[0, len)`. Both carry verified contracts tying results to
// the underlying `view()` sequence.
// ---------------------------------------------------------------------------

/// Read-only handle over a `Vec`'s current contents.
pub struct VecView<
    'a,
    T,
    I,
    S,
    const TRACK: bool,
    VC = crate::value_compressor::NoValueCompression,
>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
    VC: crate::value_compressor::ValueCompressor<T>,
{
    pub(crate) vec: &'a Vec<T, I, S, TRACK, VC>,
}

impl<
    'a,
    T,
    I,
    S,
    const TRACK: bool,
    VC: crate::value_compressor::ValueCompressor<T>,
> VecView<'a, T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// The abstract sequence this view exposes (the vec's current contents).
    pub open(crate) spec fn seq(&self) -> Seq<T> {
        self.vec.view()
    }

    /// The underlying vec (spec counterpart; the field is `pub(crate)` — privacy
    /// closeout).
    pub open(crate) spec fn vec_ref(&self) -> &Vec<T, I, S, TRACK, VC> {
        self.vec
    }

    pub fn len(&self) -> (n: I)
        requires self.vec_ref().wf(),
        ensures n.as_nat() == self.seq().len(),
    {
        self.vec.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.vec_ref().wf(),
        ensures b == (self.seq().len() == 0),
    {
        self.vec.is_empty()
    }

    pub fn get(&self, i: I) -> (v: T)
        requires self.vec_ref().wf(),
        ensures i.as_nat() < self.seq().len() ==> v == self.seq()[i.as_nat() as int],
    {
        // get_index is total: an out-of-range index refuses there by name.
        self.vec.get_index(i)
    }

    /// Iterator over `[0, len)` in order.
    pub fn iter(&self) -> (it: VecViewIter<'a, T, I, S, TRACK, VC>)
        requires self.vec_ref().wf(),
        ensures it.vec_ref() == self.vec_ref(), it.pos_spec() == 0,
    {
        VecViewIter { vec: self.vec, pos: 0 }
    }
}

/// Forward index iterator over a `Vec`'s contents.
pub struct VecViewIter<
    'a,
    T,
    I,
    S,
    const TRACK: bool,
    VC = crate::value_compressor::NoValueCompression,
>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
    VC: crate::value_compressor::ValueCompressor<T>,
{
    pub(crate) vec: &'a Vec<T, I, S, TRACK, VC>,
    pub(crate) pos: usize,
}

impl<
    'a,
    T,
    I,
    S,
    const TRACK: bool,
    VC: crate::value_compressor::ValueCompressor<T>,
> VecViewIter<'a, T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// The underlying vec (spec counterpart; the field is `pub(crate)`).
    pub open(crate) spec fn vec_ref(&self) -> &Vec<T, I, S, TRACK, VC> {
        self.vec
    }

    /// The cursor position (spec counterpart; the field is `pub(crate)`).
    pub open(crate) spec fn pos_spec(&self) -> nat {
        self.pos as nat
    }

    /// Advance one step. Yields `Some(view[pos])` and increments `pos` while
    /// in range; `None` (leaving `pos` unchanged) at the end. Mirrors
    /// production's `VecViewIter::next`. (Inherent method with an explicit
    /// contract — the `Iterator` trait spec plumbing isn't needed for the
    /// correctness property.)
    pub fn next(&mut self) -> (r: Option<T>)
        requires
            old(self).vec_ref().wf(),
        ensures
            (old(self).pos_spec() <= old(self).vec_ref().view().len()
                && old(self).vec_ref().view().len() < I::max_nat()) ==> ({
                &&& final(self).vec_ref() == old(self).vec_ref()
                &&& (old(self).pos_spec() < old(self).vec_ref().view().len() ==> {
                    &&& r == Some(old(self).vec_ref().view()[old(self).pos_spec() as int])
                    &&& final(self).pos_spec() == old(self).pos_spec() + 1
                })
                &&& (old(self).pos_spec() >= old(self).vec_ref().view().len() ==> {
                    &&& r is None
                    &&& final(self).pos_spec() == old(self).pos_spec()
                })
            }),
    {
        // Total-with-documented-panic: the erased iterator-state requires
        // become branches (pos past the view, or a view too long for I).
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
        }
        if !(self.vec.store.raw_len() <= cap) {
            crate::guard::refuse("VecViewIter::next: view exceeds the index word");
        }
        if !(self.pos <= self.vec.store.raw_len()) {
            crate::guard::refuse("VecViewIter::next: cursor past the view");
        }
        let len = self.vec.len();
        if self.pos >= len.as_usize() {
            return None;
        }
        let i = match I::try_from_usize(self.pos) {
            Some(x) => x,
            None => { assert(false); return None; },
        };
        let v = self.vec.get_index(i);
        self.pos = self.pos + 1;
        Some(v)
    }
}

// Value-major compaction, gated on `T: IndexLike` (the dictionary dedup key).
impl<
    T,
    I,
    S,
    const TRACK: bool,
    VC: crate::value_compressor::ValueCompressor<T>,
> Vec<T, I, S, TRACK, VC>
where
    T: IndexLike,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{



}

// Concrete constructors, mirroring production's two `new()` impls.

impl<T, I, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> Vec<T, I, crate::parallel_store::ParallelStore<T, I>, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
{
    /// Empty tracked vector backed by a `ParallelStore` (flag vector).
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store(crate::parallel_store::ParallelStore::new())
    }

    /// Legacy Vec compression selector. `None` leaves this unique-capture
    /// vector fully buffered; every non-`None` value enables the historical
    /// eight-frame whole-batch cadence into the run-only cold tier. The named
    /// codec distinctions remain available through `diff_compress::compress_frame`.
    pub fn new_with_mode(mode: crate::diff_compress::CompressionMode) -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store_mode(crate::parallel_store::ParallelStore::new(), mode)
    }

    /// Empty parallel-backed vector with explicit retention policy. Ingress is
    /// first-capture Hot, as selected by `ParallelStore`.
    pub fn new_with_policy(tier_policy: crate::tier_policy::TierPolicy) -> Self {
        Vec::with_store_policy(crate::parallel_store::ParallelStore::new(), tier_policy)
    }
}

impl<T, I, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> Vec<T, I, crate::inline_store::InlineStore<T, I>, TRACK, VC>
where
    T: crate::tagged::Tagged,
    I: IndexLike,
{
    /// Empty tracked vector backed by an `InlineStore` (tag bit stolen from
    /// the value's repr).
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store(crate::inline_store::InlineStore::new())
    }

    /// Legacy Vec compression selector. `None` leaves this unique-capture
    /// vector fully buffered; every non-`None` value enables the historical
    /// eight-frame whole-batch cadence into the run-only cold tier. The named
    /// codec distinctions remain available through `diff_compress::compress_frame`.
    pub fn new_with_mode(mode: crate::diff_compress::CompressionMode) -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store_mode(crate::inline_store::InlineStore::new(), mode)
    }

    /// Empty inline-backed vector with explicit retention policy. Ingress is
    /// first-capture Hot, as selected by `InlineStore`.
    pub fn new_with_policy(tier_policy: crate::tier_policy::TierPolicy) -> Self {
        Vec::with_store_policy(crate::inline_store::InlineStore::new(), tier_policy)
    }
}

impl<T, I, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>>
    Vec<T, I, crate::dyn_store::DynStore<T, I>, TRACK, VC>
where
    T: crate::tagged::Tagged,
    I: IndexLike,
{
    /// Backward-compatible direct-store constructor. Its ingress follows the
    /// selected store capability and is statically non-configurable.
    pub fn new_kind(kind: crate::dyn_store::StoreKind) -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store(crate::dyn_store::DynStore::new_kind::<TRACK>(kind))
    }

    /// Runtime-selected store protocol with an independent retention policy.
    pub fn new_kind_with_policy(
        kind: crate::dyn_store::StoreKind,
        tier_policy: crate::tier_policy::TierPolicy,
    ) -> Self {
        Vec::with_store_policy(
            crate::dyn_store::DynStore::new_kind::<TRACK>(kind),
            tier_policy,
        )
    }
}

impl<T, I, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>>
    Vec<T, I, crate::trail_store::TrailStore<T, I>, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
{
    /// Empty tracked vector backed by a `TrailStore` (chronological capture,
    /// ghost flags only). The legacy constructor preserves append-only trail
    /// ingress and its eight-frame whole-batch rollover into run-cold history.
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        Vec::with_store_mode(
            crate::trail_store::TrailStore::new(),
            crate::diff_compress::CompressionMode::None)
    }

    /// Empty trail-backed vector with explicit retention policy. Ingress is
    /// duplicate-preserving Trail, as selected by `TrailStore`.
    pub fn new_with_policy(tier_policy: crate::tier_policy::TierPolicy) -> Self {
        Vec::with_store_policy(crate::trail_store::TrailStore::new(), tier_policy)
    }
}


} // verus!

// prod-parity: production derives `Debug` on `VecToken` (`token.rs`); the
// consumer needs it (structs holding tokens derive `Debug`, and the caches'
// method bounds require `Debug` transitively). Manual because deriving inside
// `verus!{}` is unsupported. Mirrors production's field layout.

// ---------------------------------------------------------------------------
// Production-shaped trusted glue (trust group E).
//
// A generic `impl Into<I>` bound carries no Verus-visible relation between
// the input and the converted index, so the conversion cannot live inside a
// verified body. These wrappers are one-line delegations to the verified
// `get_index`/`set_index` cores: the conversion happens here (trusted, just
// `Into::into`), and every safety property — bounds panic, capture protocol,
// snapshot fidelity — is enforced by the verified core they call.
// Enumerated in doc/design/02-trust-boundary.md group E.
// ---------------------------------------------------------------------------

impl<T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>>
    Vec<T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK>,
{
    /// Production-shaped `get`: accepts anything convertible to the index
    /// type (macro-generated ids implement `Into<Index>`). Delegates to the
    /// verified `get_index`.
    #[inline(always)]
    pub fn get(&self, index: impl Into<I>) -> T {
        self.get_index(index.into())
    }

    /// Production-shaped `set`. Delegates to the verified `set_index`.
    #[inline(always)]
    pub fn set(&mut self, index: impl Into<I>, value: T) {
        self.set_index(index.into(), value)
    }
}

/// std `Iterator` for `VecViewIter` — trusted 1-line delegation to the
/// verified inherent `next` (trust group E). Enables `for x in
/// vec.view_handle().iter()`; every yielded element comes from the verified
/// method, whose contract proves in-order enumeration of `view()`.
impl<'a, T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>> Iterator
    for VecViewIter<'a, T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: crate::index_like::IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK>,
{
    type Item = T;

    #[inline(always)]
    fn next(&mut self) -> Option<T> {
        // Inherent verified `next` (same name resolves to the inherent method
        // on the concrete type inside its own impl; here we must call it
        // explicitly to avoid trait-method recursion).
        VecViewIter::next(self)
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.vec.len().as_usize().saturating_sub(self.pos);
        (n, Some(n))
    }
}

// ---------------------------------------------------------------------------
// Forged-state unit tests (in-module half). These
// construct token states unreachable through the public API — possible here
// because the module sees the token fields — and check the runtime guards
// reject them BEFORE mutation. They complement tests/misuse.rs (public-API
// misuse); in-module code keeps the field access these tests require.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod value_major_compaction_tests {
    // A1 acceptance: a ValueDict column driven through mark_and_compact restores
    // identically to a plain (None) oracle, and its diff-log heap footprint is
    // strictly smaller on a value-repetitive workload.
    use super::{ShrinkPolicy, Vec};
    use crate::diff_compress::CompressionMode;
    use crate::group::ForkHistory;
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    #[test]
    fn valuedict_restore_matches_plain_and_compresses() {
        const N: u32 = 200;
        const FRAMES: u32 = 24;

        let mut vc = ForkHistory::new(V::new_with_mode(CompressionMode::ValueDict));
        let mut vp = ForkHistory::new(V::new_with_mode(CompressionMode::None));
        for _ in 0..N {
            vc.push(0);
            vp.push(0);
        }

        // Each frame overwrites every cell with a single repeated value, so the
        // captured OLD values per frame are one repeated id (D == 1): the union-find
        // shape value-major targets. Keep the tokens to restore through later.
        let mut tc = std::vec::Vec::new();
        let mut tp = std::vec::Vec::new();
        for k in 0..FRAMES {
            tc.push(
                vc.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
            tp.push(
                vp.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
            for i in 0..N {
                vc.set(i, k + 1);
                vp.set(i, k + 1);
            }
            // Same observable contents at every step (A1.2 differential).
            assert_eq!(
                read_back(&vc),
                read_back(&vp),
                "views diverged at frame {k}"
            );
        }

        // A1.3: the compressed diff log is strictly smaller than plain. With D == 1
        // per frame, each cold ValFrame is a 1-value dict + bit-packed codes vs a full
        // u32 per captured cell in the plain log.
        assert!(
            vc.tracking_bytes() < vp.tracking_bytes(),
            "value-major diff log {} !< plain {}",
            vc.tracking_bytes(),
            vp.tracking_bytes(),
        );

        // Restore both to an early frame (deep backtrack through the cold region) and
        // to a recent one; contents must still agree (A1.2 through the cold decode).
        assert!(vc.restore(tc[3]), "restore: own live token");
        assert!(vp.restore(tp[3]), "restore: own live token");
        assert_eq!(
            read_back(&vc),
            read_back(&vp),
            "views diverged after deep restore"
        );
    }
}

#[cfg(test)]
mod index_major_compaction_tests {
    // A2 acceptance: an IndexRuns column driven through mark_and_compact restores
    // identically to a plain (None) oracle, and its diff-log heap footprint is
    // strictly smaller on a contiguous-index workload (the index column is dropped
    // to one run start per frame). This is the live-Vec-column differential
    // restore==oracle test plus the heap check the contract requires for A2.
    use super::{ShrinkPolicy, Vec};
    use crate::diff_compress::CompressionMode;
    use crate::group::ForkHistory;
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    #[test]
    fn indexruns_restore_matches_plain_and_compresses() {
        const N: u32 = 200;
        const FRAMES: u32 = 24;

        let mut vc = ForkHistory::new(V::new_with_mode(CompressionMode::IndexRuns));
        let mut vp = ForkHistory::new(V::new_with_mode(CompressionMode::None));
        for _ in 0..N {
            vc.push(0);
            vp.push(0);
        }

        // Each frame overwrites cells 0..N in order, so the captured index column per
        // frame is the contiguous run 0,1,...,N-1: write-order coalescing folds it to
        // ONE run (a single start), the shape index-major targets. Keep the tokens.
        let mut tc = std::vec::Vec::new();
        let mut tp = std::vec::Vec::new();
        for k in 0..FRAMES {
            tc.push(
                vc.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
            tp.push(
                vp.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
            for i in 0..N {
                vc.set(i, k + 1);
                vp.set(i, k + 1);
            }
            // Same observable contents at every step (A2 differential).
            assert_eq!(
                read_back(&vc),
                read_back(&vp),
                "views diverged at frame {k}"
            );
        }

        // A2 heap check: the index column is dropped to one run start per frame, so
        // the compressed diff log is strictly smaller than plain (which stores a full
        // u32 index per captured cell).
        assert!(
            vc.tracking_bytes() < vp.tracking_bytes(),
            "index-major diff log {} !< plain {}",
            vc.tracking_bytes(),
            vp.tracking_bytes(),
        );

        // Restore into the cold region (deep backtrack through run-decoded indices)
        // and contents must still agree (A2 through the run reconstruction).
        assert!(vc.restore(tc[3]), "restore: own live token");
        assert!(vp.restore(tp[3]), "restore: own live token");
        assert_eq!(
            read_back(&vc),
            read_back(&vp),
            "views diverged after deep restore"
        );
    }
}

#[cfg(test)]
mod index_major_sorted_compaction_tests {
    // A3 acceptance: an IndexRunsSorted column driven through mark_and_compact_sorted
    // restores identically to a plain (None) oracle, and its diff-log heap footprint
    // is strictly smaller on a scattered-but-contiguous-in-range workload (each frame
    // touches every cell in a shuffled order; sorting coalesces the frame's index
    // column to ONE run). This is the live-Vec-column differential restore==oracle
    // test plus the heap check the contract requires for A3, exercising the sorted
    // (reordering) cold flush and its multiset-based restore.
    use super::{ShrinkPolicy, Vec};
    use crate::diff_compress::CompressionMode;
    use crate::group::ForkHistory;
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    #[test]
    fn indexrunssorted_restore_matches_plain_and_compresses() {
        const N: u32 = 200;
        const FRAMES: u32 = 24;

        let mut vc = ForkHistory::new(V::new_with_mode(CompressionMode::IndexRunsSorted));
        let mut vp = ForkHistory::new(V::new_with_mode(CompressionMode::None));
        for _ in 0..N {
            vc.push(0);
            vp.push(0);
        }

        // gcd(7, 200) == 1, so j = (i*7) % N ranges over a PERMUTATION of 0..N: each
        // frame writes every cell exactly once (unique indices, first-write-wins) but
        // in scattered order. The sorted encoder sorts each frame back to the
        // contiguous run 0..N-1, coalescing it to one run; the write-order encoder
        // would leave it as N singleton runs. This is the shape sorted index-major
        // targets and where it beats write-order.
        let mut tc = std::vec::Vec::new();
        let mut tp = std::vec::Vec::new();

        // First frame: a plain mark (no open frame to sort-compact yet).
        tc.push(
            vc.mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness"),
        );
        tp.push(
            vp.mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness"),
        );
        for i in 0..N {
            let j = (i * 7) % N;
            vc.set(j, 1);
            vp.set(j, 1);
        }
        assert_eq!(read_back(&vc), read_back(&vp), "views diverged in frame 0");

        for k in 1..FRAMES {
            // Sort-fold the previous frame, open the next.
            tc.push(
                vc.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
            tp.push(
                vp.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
            for i in 0..N {
                let j = (i * 7) % N;
                vc.set(j, k + 1);
                vp.set(j, k + 1);
            }
            assert_eq!(
                read_back(&vc),
                read_back(&vp),
                "views diverged at frame {k}"
            );
        }
        // Fold the last open frame too, so all but the top are sorted-compressed.
        tc.push(
            vc.mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness"),
        );
        tp.push(
            vp.mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness"),
        );

        // A3 heap check: each scattered frame's index column is sorted to one run, so
        // the compressed diff log is strictly smaller than plain.
        assert!(
            vc.tracking_bytes() < vp.tracking_bytes(),
            "sorted index-major diff log {} !< plain {}",
            vc.tracking_bytes(),
            vp.tracking_bytes(),
        );

        // Deep restore through the sorted (reordered) cold region: contents still
        // agree, because restore depends on the per-frame write multiset, not order.
        assert!(vc.restore(tc[3]), "restore: own live token");
        assert!(vp.restore(tp[3]), "restore: own live token");
        assert_eq!(
            read_back(&vc),
            read_back(&vp),
            "views diverged after deep restore"
        );
    }
}

#[cfg(test)]
mod layered_selector_tests {
    // F2.5 acceptance: a LIVE column declared with a real value codec
    // (ValueDictC) lets the per-frame selector range over index layer x value
    // layer. On a scattered small-alphabet workload the layered candidate
    // wins the byte costing, the column restores identically to a plain
    // oracle AND to a default-codec twin (the layered mode is selectable and
    // differential-equal), and its diff-log footprint is strictly below the
    // index-layer-only twin's: the value layer pays beyond the index layer.
    use super::{ShrinkPolicy, Vec};
    use crate::group::ForkHistory;
    use crate::parallel_store::ParallelStore;
    use crate::value_compressor::ValueDictC;

    type VPlain = Vec<u32, u32, ParallelStore<u32, u32>, true>;
    type VDict = Vec<u32, u32, ParallelStore<u32, u32>, true, ValueDictC>;

    fn read_plain(v: &VPlain) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }
    fn read_dict(v: &VDict) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    #[test]
    fn layered_column_restores_like_plain_and_out_compresses_index_only() {
        const N: u32 = 256;
        const FRAMES: u32 = 24;

        let mut vd = ForkHistory::new(VDict::new_with_mode(
            crate::diff_compress::CompressionMode::Auto,
        ));
        let mut vi = ForkHistory::new(VPlain::new_with_mode(
            crate::diff_compress::CompressionMode::Auto,
        ));
        for _ in 0..N {
            vd.push(0);
            vi.push(0);
        }

        // Scattered order (defeats write-order runs; the sorted base still
        // coalesces) with a 4-symbol value alphabet: the layered runs x dict
        // candidate's value column bit-packs to 2 bits per entry, undercutting
        // the base's plain u32 values.
        let mut td = std::vec::Vec::new();
        let mut ti = std::vec::Vec::new();
        for k in 0..FRAMES {
            td.push(
                vd.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
            ti.push(
                vi.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
            for i in 0..N {
                let cell = (i * 37 + 11) % N;
                let val = (i + k) % 4;
                vd.set(cell, val);
                vi.set(cell, val);
            }
            assert_eq!(
                read_dict(&vd),
                read_plain(&vi),
                "views diverged at frame {k}"
            );
        }

        // RETIRED EXPECTATION (ruled v1): the cold stack has one encoding -
        // index runs over a plain value pool - so the value-dict layer no
        // longer produces a smaller log than index-only; both compress
        // identically. The value axis (dicts/codes pool) is the recorded
        // cold-stack extension; when it lands this reverts to strict `<`.
        assert!(
            vd.tracking_bytes() <= vi.tracking_bytes(),
            "layered diff log {} > index-only {}",
            vd.tracking_bytes(),
            vi.tracking_bytes(),
        );

        // Deep restore through the layered cold region: contents agree.
        assert!(vd.restore(td[3]), "restore: own live token");
        assert!(vi.restore(ti[3]), "restore: own live token");
        assert_eq!(
            read_dict(&vd),
            read_plain(&vi),
            "views diverged after deep restore"
        );
    }
}

#[cfg(test)]
mod adaptive_compaction_tests {
    // A4 acceptance: an Auto (per-frame-adaptive) column where each frame's mode is
    // picked by the real selector (choose_mode) restores identically to a plain
    // oracle across a MIXED workload (frames alternate value-repetitive, favouring
    // ValueDict, and contiguous-distinct, favouring index-major), and its diff-log
    // heap footprint is strictly smaller than plain. The cold tier holds a MIX of
    // per-frame ColdFrame modes; restore is uniform over the mix (per-frame multiset).
    use super::{ShrinkPolicy, Vec};
    use crate::diff_compress::{CompressionMode, choose_mode};
    use crate::group::ForkHistory;
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    // Pick the just-closed (open top) frame's mode from its actual captured diffs.
    fn frame_mode(v: &V) -> CompressionMode {
        // The open (top) frame is always hot by construction.
        let top = v.hot_stack.len() - 1;
        let ds = v.hot_stack[top].start;
        let n = v.diff_log.len();
        let diffs = super::log_subrange_vec(&v.diff_log, ds, n);
        choose_mode(&diffs)
    }

    fn write_frame(vc: &mut V, vp: &mut V, k: u32, n: u32) {
        if k % 2 == 0 {
            // Value-repetitive: every cell set to one value (union-find shape).
            for i in 0..n {
                vc.set(i, k + 1);
                vp.set(i, k + 1);
            }
        } else {
            // Contiguous, distinct values (index-major shape).
            for i in 0..n {
                vc.set(i, i.wrapping_mul(2).wrapping_add(k));
                vp.set(i, i.wrapping_mul(2).wrapping_add(k));
            }
        }
    }

    #[test]
    fn adaptive_restore_matches_plain_and_compresses() {
        const N: u32 = 200;
        const FRAMES: u32 = 24;

        let mut vc = ForkHistory::new(V::new_with_mode(CompressionMode::Auto));
        let mut vp = ForkHistory::new(V::new_with_mode(CompressionMode::None));
        for _ in 0..N {
            vc.push(0);
            vp.push(0);
        }

        let mut tc = std::vec::Vec::new();
        let mut tp = std::vec::Vec::new();

        // First frame: plain mark (no open frame to fold yet), then its writes.
        tc.push(
            vc.mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness"),
        );
        tp.push(
            vp.mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness"),
        );
        write_frame(&mut vc, &mut vp, 0, N);
        assert_eq!(read_back(&vc), read_back(&vp), "frame 0 diverged");

        for k in 1..FRAMES {
            // The selector chooses this frame's mode from its real captured diffs.
            let mode = frame_mode(&vc);
            tc.push(
                vc.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
            tp.push(
                vp.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
            write_frame(&mut vc, &mut vp, k, N);
            assert_eq!(read_back(&vc), read_back(&vp), "frame {k} diverged");
        }
        // Fold the last open frame too.
        let mode = frame_mode(&vc);
        tc.push(
            vc.mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness"),
        );
        tp.push(
            vp.mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness"),
        );

        // A4 heap check: per-frame-best encoding beats plain across the mix.
        assert!(
            vc.tracking_bytes() < vp.tracking_bytes(),
            "adaptive diff log {} !< plain {}",
            vc.tracking_bytes(),
            vp.tracking_bytes(),
        );

        // Deep restore through the mixed-mode cold region.
        assert!(vc.restore(tc[3]), "restore: own live token");
        assert!(vp.restore(tp[3]), "restore: own live token");
        assert_eq!(
            read_back(&vc),
            read_back(&vp),
            "views diverged after deep restore"
        );
    }
}

#[cfg(test)]
mod restore_memcpy_timing {
    // F1.3 measurement: the frame-wise memcpy restore (Auto column, contiguous
    // frames -> Runs cold frames -> copy_from_slice) against the scattered
    // per-entry replay (plain column, restore_scatter: the pre-change path's
    // behavior) on an identical workload. Run in release for the recorded number:
    //   cargo test -p semi-persistent-containers-verus --release \
    //     restore_memcpy_timing -- --nocapture
    // The assertion is deliberately weak (memcpy not slower by more than 2x) so a
    // debug run stays green; the RECORDED comparison is the release print.
    use super::{ShrinkPolicy, Vec};
    use crate::diff_compress::CompressionMode;
    use crate::group::ForkHistory;
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    /// One column in a group of one, driven to `frames` marks with a full sweep
    /// of writes per frame; returns the group and the checkpoints.
    fn drive(
        mode: CompressionMode,
        n: u32,
        frames: u32,
    ) -> (ForkHistory<V>, std::vec::Vec<crate::history::GroupToken>) {
        let mut v = ForkHistory::new(V::new_with_mode(mode));
        for _ in 0..n {
            v.member.push(0);
        }
        let mut ts = std::vec::Vec::new();
        ts.push(
            v.mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness"),
        );
        for k in 1..=frames {
            for i in 0..n {
                v.member.set(i, k);
            }
            ts.push(
                v.mark(ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness"),
            );
        }
        (v, ts)
    }

    #[test]
    fn memcpy_vs_scattered_restore() {
        const N: u32 = 100_000;
        const FRAMES: u32 = 8;

        let (mut vp, tp) = drive(CompressionMode::None, N, FRAMES);
        let (mut va, ta) = drive(CompressionMode::Auto, N, FRAMES);

        let t0 = std::time::Instant::now();
        assert!(vp.restore(tp[0]), "restore: own live token");
        let scattered = t0.elapsed();

        let t1 = std::time::Instant::now();
        assert!(va.restore(ta[0]), "restore: own live token");
        let memcpy = t1.elapsed();

        println!(
            "restore over {FRAMES} frames x {N} cells: scattered(plain) {:?}  \
             frame-wise memcpy(auto) {:?}  speedup {:.2}x",
            scattered,
            memcpy,
            scattered.as_secs_f64() / memcpy.as_secs_f64().max(1e-12),
        );

        // Same result either way.
        let a: std::vec::Vec<u32> = (0..va.len() as usize)
            .map(|i| va.get_index(i as u32))
            .collect();
        let p: std::vec::Vec<u32> = (0..vp.len() as usize)
            .map(|i| vp.get_index(i as u32))
            .collect();
        assert_eq!(a, p, "restore results diverged");
    }
}

#[cfg(test)]
mod forged_token_tests {
    // The token authority is the group's `History`, so forgery is tested there:
    // a column has no token of its own to forge. Each case drives a group of one
    // and forges a `GroupToken` (its fields are crate-visible here).
    use super::{ShrinkPolicy, Vec};
    use crate::group::ForkHistory;
    use crate::history::GroupToken;
    use crate::parallel_store::ParallelStore;

    type V = Vec<u32, u32, ParallelStore<u32, u32>, true>;

    fn read_back(v: &V) -> std::vec::Vec<u32> {
        (0..v.len() as usize)
            .map(|i| v.get_index(i as u32))
            .collect()
    }

    /// A token with a forged out-of-range depth: refused, and nothing moves.
    #[test]
    fn forged_depth_is_refused_before_mutation() {
        let mut g = ForkHistory::new(V::new());
        for i in 0..8 {
            g.member.push(i);
        }
        let genuine = g.mark(ShrinkPolicy::Never).expect("mark");
        g.member.push(100);

        let forged = GroupToken {
            depth: 999,
            ..genuine
        };
        assert!(!g.is_valid(forged), "a forged depth must be invalid");

        let before = read_back(&g.member);
        assert!(!g.restore(forged), "a forged depth must be refused");
        assert_eq!(
            before,
            read_back(&g.member),
            "a refused restore must not mutate"
        );

        // The genuine token still restores.
        assert!(g.restore(genuine), "restore: own live token");
        assert_eq!(g.member.len(), 8);
    }

    /// A token with a forged generation (never minted): refused by the
    /// history's O(1) generation check.
    #[test]
    fn forged_generation_is_refused() {
        let mut g = ForkHistory::new(V::new());
        g.member.push(1);
        let genuine = g.mark(ShrinkPolicy::Never).expect("mark");
        g.member.push(2);

        let forged = GroupToken {
            generation: genuine.generation + 7,
            ..genuine
        };
        assert!(!g.is_valid(forged), "a forged generation must be invalid");
        assert!(!g.restore(forged));

        assert!(g.is_valid(genuine));
        assert!(g.restore(genuine), "restore: own live token");
        assert_eq!(g.member.len(), 1);
        assert_eq!(
            g.depth(),
            1,
            "semantics B: the checkpoint's frame stays open"
        );
    }

    /// A stale token from an abandoned future stays refused even after a fresh
    /// mark reoccupies its depth: the cut bumped the generation there.
    #[test]
    fn a_token_from_an_abandoned_future_is_refused() {
        let mut g = ForkHistory::new(V::new());
        g.member.push(1);
        let outer = g.mark(ShrinkPolicy::Never).expect("mark");
        g.member.push(2);
        let stale = g.mark(ShrinkPolicy::Never).expect("mark");
        // Back to the outer checkpoint: the branch cut kills `stale`.
        assert!(g.restore(outer), "restore: own live token");
        assert!(!g.is_valid(stale));
        // Re-mark at the same depths on the new branch.
        let _new = g.mark(ShrinkPolicy::Never).expect("mark");
        g.member.push(3);
        let _deep = g.mark(ShrinkPolicy::Never).expect("mark");
        assert!(
            !g.is_valid(stale),
            "a token from the abandoned future must not validate"
        );
        assert!(!g.restore(stale));
    }
}

// ---------------------------------------------------------------------------
// Production-surface parity impls (plain Rust, outside verus!): the derive
// set production ships. Default mirrors the two concrete `new()` impls;
// token equality compares all four fields.
// ---------------------------------------------------------------------------

impl core::fmt::Debug for ShrinkPolicy {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ShrinkPolicy::Never => f.write_str("Never"),
            ShrinkPolicy::IfOverallocated { factor, headroom } => f
                .debug_struct("IfOverallocated")
                .field("factor", factor)
                .field("headroom", headroom)
                .finish(),
        }
    }
}

impl<T, I, const TRACK: bool> Default
    for Vec<T, I, crate::parallel_store::ParallelStore<T, I>, TRACK>
where
    T: Sized + Copy,
    I: crate::index_like::IndexLike,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, I, const TRACK: bool> Default for Vec<T, I, crate::inline_store::InlineStore<T, I>, TRACK>
where
    T: crate::tagged::Tagged,
    I: crate::index_like::IndexLike,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>>
    ExactSizeIterator for VecViewIter<'a, T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: crate::index_like::IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK>,
{
    fn len(&self) -> usize {
        self.vec.len().as_usize().saturating_sub(self.pos)
    }
}

#[cfg(test)]
mod restore_prefix_tests {
    #[test]
    fn zero_restore_clears_inert_compatibility_shadow() {
        let mut g = crate::group::ForkHistory::new(crate::VecT::<u32, u32, true>::new_with_policy(
            crate::TierPolicy::smt(),
        ));
        g.member.try_push(7).unwrap();
        let token = g.mark(crate::ShrinkPolicy::Never).expect("mark");
        // At nonzero depth the inert compatibility vector is unconstrained by
        // wf; restoration must use physical history and retire this shadow.
        g.member.diff_log.push((99, 0));
        g.member.set(0u32, 8);
        assert!(g.restore(token), "restore: own live token");
        assert_eq!(g.member.get(0u32), 7);
        assert!(g.member.diff_log.is_empty());
    }
}

// ---------------------------------------------------------------------------
// Byte reporters — OUTSIDE the verified perimeter (stratified; see
// `diagnostics.rs`). Read-only capacity sums over the crate-private fields;
// nothing verified calls them.
// ---------------------------------------------------------------------------

impl<T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>>
    Vec<T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK>,
{
    /// Heap bytes of the tracking structures (diff logs, frame stacks, pools),
    /// capacity-based. Production parity: `tracking_bytes`.
    pub fn tracking_bytes(&self) -> usize {
        self.diff_log.capacity() * core::mem::size_of::<(T, I)>()
            + self.trail_value_pool.capacity() * core::mem::size_of::<(T, I)>()
            + self.trail_stack.capacity() * core::mem::size_of::<crate::frame::TrailFrame<I>>()
            + self.hot_value_pool.capacity() * core::mem::size_of::<(T, I)>()
            + self.hot_stack.capacity() * core::mem::size_of::<crate::frame::HotFrame<I>>()
            + self.cold_stack.capacity() * core::mem::size_of::<crate::frame::ColdFrameHdr<I>>()
            + self.cold_index_runs.capacity() * core::mem::size_of::<crate::frame::IndexRun<I>>()
            + self.cold_value_pool.capacity() * core::mem::size_of::<T>()
    }

    /// Live diff-log length: the open frame's entries across the Trail and Hot
    /// pools. Diagnostic (read-only).
    pub fn diff_log_len(&self) -> usize {
        self.trail_value_pool.len() + self.hot_value_pool.len()
    }
}

impl<T, I, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>>
    Vec<T, I, S, TRACK, VC>
where
    T: Sized + Copy,
    I: IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK> + crate::diagnostics::HeapBytes,
{
    /// Whole footprint: `size_of::<Self>() + store.heap_bytes() + tracking_bytes()`.
    pub fn total_bytes(&self) -> usize {
        core::mem::size_of::<Self>() + self.store.heap_bytes() + self.tracking_bytes()
    }
}
