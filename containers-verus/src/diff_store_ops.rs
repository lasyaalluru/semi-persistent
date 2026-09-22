// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `DiffStoreOps`: the crate-private half of the store contract — the capture
//! protocol `Vec` drives under its own proven invariants (see the module docs
//! of `diff_store` for the protocol). Sealed by construction: this module is
//! `pub(crate)`, so nothing outside the crate can name, call or implement
//! these operations, while the public `DiffStore` (whose supertrait this is)
//! stays the bound consumers write. Every operation here is partial for a
//! reason the public surface cannot check at runtime: `prepare_mark`,
//! `begin_restore` and `finish_restore` take ghost facts about the capture
//! flags, and the others take index/length bounds the vector has already
//! established once — re-checking them per element on the hottest path would
//! only duplicate `Vec`'s own guard.

use vstd::prelude::*;

use crate::index_like::IndexLike;

verus! {

/// The store's ghost views and the capture-protocol operations. Crate-private
/// supertrait of [`crate::diff_store::DiffStore`].
pub trait DiffStoreOps<T, I, const TRACK: bool>: Sized
where
    T: Sized + Copy,
    I: IndexLike,
{
    // -- ghost views ---------------------------------------------------------

    /// The abstract sequence of stored values. Tag-bit edits in concrete impls
    /// project out: `data()` is invariant under `set_tag`/`clear_tag` on the
    /// underlying repr.
    spec fn data(&self) -> Seq<T>;

    /// Per-slot capture flag for the active frame. Length matches `data()`.
    spec fn captured(&self) -> Seq<bool>;

    /// Backend-specific well-formedness. Concrete impls strengthen this; the
    /// universal part is `captured().len() == data().len()`.
    spec fn wf(&self) -> bool;

    fn get(&self, i: I) -> (v: T)
        requires
            self.wf(),
            i.as_nat() < self.data().len(),
        ensures v == self.data()[i.as_nat() as int];

    fn push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).data().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data() == old(self).data().push(value),
            // Flag maintenance is TRACK-conditional: an untracked store may
            // skip it wholesale (production parity — its flags are dead).
            TRACK ==> final(self).captured() == old(self).captured().push(false);

    fn set_raw(&mut self, i: I, value: T)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data() == old(self).data().update(i.as_nat() as int, value),
            // TRACK-conditional for the same reason as `push`/`pop` above, and
            // it is a performance contract, not just a modelling nicety.
            // Preserving an inline store's flag across a write costs a read and
            // a branch (read the old repr's tag, re-set it on the new one);
            // production spends that only when tracking is on
            // (`containers/src/diff_store.rs:263`, `let was_captured = TRACK &&
            // T::tag(...)`). Stating the clause unconditionally forces Verus's
            // `InlineStore` to pay that work on untracked writes too. Untracked
            // flags are dead: nothing reads `captured()` when `!TRACK`. The
            // current machine effect is a Criterion question.
            TRACK ==> final(self).captured() == old(self).captured();

    fn truncate(&mut self, len: I)
        requires
            old(self).wf(),
            len.as_nat() <= old(self).data().len(),
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data() == old(self).data().subrange(0, len.as_nat() as int),
            TRACK ==> final(self).captured() == old(self).captured().subrange(0, len.as_nat() as int);

    /// Mark slot `i` as captured without logging or changing `data`. Used by
    /// `Vec::push` when a previously-popped marked index is re-added: the
    /// pop already captured `snap[i]`, so the fresh slot must inherit the
    /// captured flag to keep first-write-wins (and bound the diff log).
    fn mark_captured(&mut self, i: I)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data() == old(self).data(),
            TRACK ==> final(self).captured()
                == old(self).captured().update(i.as_nat() as int, true);

    /// Resize `data` to `len`: truncate if longer, or extend with
    /// `T::default()` fillers if shorter. Used by `restore` to regrow the
    /// popped region before the overwrite-only replay. The filler values are
    /// arbitrary — they are always overwritten by the replay, which is why
    /// no constraint is placed on `T::default()`. New slots are uncaptured.
    fn resize_default(&mut self, len: I)
        where T: core::default::Default
        requires
            old(self).wf(),
            len.as_nat() < I::max_nat(),
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data().len() == len.as_nat(),
            // existing prefix preserved
            forall|j: int| 0 <= j < len.as_nat() && j < old(self).data().len()
                ==> #[trigger] final(self).data()[j] == old(self).data()[j],
            final(self).captured().len() == len.as_nat(),  // definitional (padded view at data len)
            // Flags: shared prefix preserved, grown region clear (both
            // stores: truncate retires, growth extends with clear tags).
            TRACK ==> forall|j: int| 0 <= j < len.as_nat()
                ==> #[trigger] final(self).captured()[j]
                    == (j < old(self).captured().len() && old(self).captured()[j]);

    // -- capture protocol ----------------------------------------------------

    /// Begin a new frame. Clears the capture flag for all slots in
    /// `[0, saved_len)`. The `prev_diffs` slice is the diff log of the
    /// outer (parent) frame, used by `InlineStore` to know which inline
    /// tags need clearing; `ParallelStore` ignores it.
    fn prepare_mark(&mut self, saved_len: I, prev_diffs: &[(T, I)])
        requires
            old(self).wf(),
            saved_len.as_nat() <= old(self).data().len(),
            // Sparse-clear soundness (production's O(diffs) protocol): every
            // set capture flag is indexed by some entry of `prev_diffs`, so
            // clearing exactly those slots clears ALL flags. The caller
            // (`Vec::mark`) holds this from its wf capture-flag bridge —
            // a flag is only ever set by capture/force_capture, which push
            // the slot into the diff log in the same step.
            TRACK ==> forall|j: int| 0 <= j < old(self).captured().len()
                && #[trigger] old(self).captured()[j]
                ==> exists|k: int| 0 <= k < prev_diffs@.len()
                        && (#[trigger] prev_diffs@[k]).1.as_nat() == j as nat,
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data() == old(self).data(),
            TRACK ==> forall|i: int| 0 <= i < saved_len.as_nat() ==>
                #[trigger] final(self).captured()[i] == false;

    /// Capture discipline: `true` means first-write-wins (one diff entry per
    /// cell per frame, enforced by runtime capture flags); `false` means
    /// chronological (every in-frame write appends, duplicates allowed, no
    /// runtime flags — the trail discipline). The reconstruction model
    /// (`overlay`, first-entry-wins) is correct for both; only the sealing
    /// and reordering paths require the unique discipline.
    spec fn unique_capture_spec(&self) -> bool;

    /// First-write-wins capture (unique discipline) or unconditional append
    /// (chronological discipline). If the slot is in-frame and not yet
    /// captured, log `(old.data()[i], i)` and flip `captured[i]`; a
    /// chronological store also appends when the slot is already captured.
    fn capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data() == old(self).data(),
            // First-write-wins (all TRACK-conditional; an untracked store's
            // flags are dead and its capture is a no-op — production parity):
            (TRACK && i.as_nat() < saved_len.as_nat()
                && !old(self).captured()[i.as_nat() as int])
                ==> {
                    &&& final(diff_log)@ == old(diff_log)@.push(
                            (old(self).data()[i.as_nat() as int], i))
                    &&& final(self).captured()[i.as_nat() as int] == true
                    &&& forall|j: int| 0 <= j < final(self).captured().len() && j != i.as_nat()
                            ==> #[trigger] final(self).captured()[j] == old(self).captured()[j]
                },
            // Out of frame or untracked: no-op for every discipline.
            !(TRACK && i.as_nat() < saved_len.as_nat())
                ==> {
                    &&& final(diff_log)@ == old(diff_log)@
                    &&& (TRACK ==> final(self).captured() == old(self).captured())
                },
            // In-frame but already captured: a unique-discipline store
            // no-ops; a chronological store appends the duplicate (the
            // reconstruction model is first-entry-wins, so the duplicate is
            // inert at restore).
            (TRACK && i.as_nat() < saved_len.as_nat()
                && old(self).captured()[i.as_nat() as int])
                ==> {
                    &&& old(self).unique_capture_spec()
                            ==> final(diff_log)@ == old(diff_log)@
                    &&& !old(self).unique_capture_spec()
                            ==> final(diff_log)@ == old(diff_log)@.push(
                                    (old(self).data()[i.as_nat() as int], i))
                    &&& final(self).captured() == old(self).captured()
                };

    /// Retained unconditional-capture operation. Within-frame: log + set
    /// captured. Out-of-frame: no-op. `Vec` has no call site; marked pops use
    /// conditional `capture` to preserve the one-entry-per-index bound.
    fn force_capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data() == old(self).data(),
            (TRACK && i.as_nat() < saved_len.as_nat()) ==> {
                &&& final(diff_log)@ == old(diff_log)@.push(
                        (old(self).data()[i.as_nat() as int], i))
                &&& final(self).captured()[i.as_nat() as int] == true
                &&& forall|j: int| 0 <= j < final(self).captured().len() && j != i.as_nat()
                        ==> #[trigger] final(self).captured()[j] == old(self).captured()[j]
            },
            !(TRACK && i.as_nat() < saved_len.as_nat()) ==> {
                &&& final(diff_log)@ == old(diff_log)@
                &&& (TRACK ==> final(self).captured() == old(self).captured())
            };

    /// Pre-replay flag reset: clear EVERY capture flag, given that each set
    /// flag is named by some entry of the about-to-be-replayed slice (the
    /// caller's wf bridge fact). ParallelStore: one in-place bitmap memset
    /// (production pays the identical zero inside its finish_restore;
    /// hoisting it lets `restore_entry` do NO per-entry bit work — measured
    /// 1.6µs/2048-entry replay). InlineStore: sparse tag-clear over the
    /// named slots, O(replayed) — the same protocol as its `prepare_mark`.
    /// Whether `begin_restore` actually READS the replayed-indices slice. A store
    /// that clears flags wholesale (ParallelStore's bitmap memset) never touches it,
    /// so its caller can skip materializing the index column entirely: on a
    /// compressed log that materialization is a full per-entry decode, and it was
    /// measured DOMINATING the frame-wise memcpy restore before this flag existed.
    /// A store that clears sparsely by name (InlineStore) returns true and gets the
    /// real slice.
    spec fn needs_replayed_indices_spec(&self) -> bool;

    /// Whether replaying every active entry clears that entry's capture state.
    /// Runtime restore may skip a separate pre-clear pass when this is true;
    /// the replayed open frame necessarily names every currently captured slot.
    spec fn restore_entries_clear_capture_spec(&self) -> bool;

    fn begin_restore(&mut self, replayed_diffs: &[(T, I)])
        requires
            old(self).wf(),
            // The named-slots justification is only owed when the store reads the
            // slice; a wholesale-clearing store establishes all-clear without it.
            (TRACK && old(self).needs_replayed_indices_spec())
                ==> forall|j: int| 0 <= j < old(self).captured().len()
                    && #[trigger] old(self).captured()[j]
                    ==> exists|k: int| 0 <= k < replayed_diffs@.len()
                            && (#[trigger] replayed_diffs@[k]).1.as_nat() == j as nat,
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data() == old(self).data(),
            TRACK ==> forall|j: int| 0 <= j < final(self).captured().len()
                ==> !(#[trigger] final(self).captured()[j]);

    /// Apply the diff-log range `[lo, hi)` BACKWARD onto the live data in one call
    /// (pure overwrite; an index at or beyond `data().len()` is dropped), replacing
    /// the per-entry `restore_entry` replay loop. The point of the batching: the
    /// store applies a whole frame at once, so a representation whose frame is
    /// contiguous can use a sliced memcpy instead of scattered per-entry writes.
    /// Capture flags only decrease (a replay write never sets one), so an all-clear
    /// state stays all-clear through the call.
    fn restore_overlay(
        &mut self,
        diff_log: &Vec<(T, I)>,
        lo: usize,
        hi: usize,
    )
        requires
            old(self).wf(),
            lo <= hi <= diff_log@.len(),
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data() == crate::vec::overlay::<T, I>(
                old(self).data(), diff_log@, lo as int, hi as int),
            TRACK ==> forall|j: int| 0 <= j < final(self).captured().len()
                && #[trigger] final(self).captured()[j]
                ==> j < old(self).captured().len() && old(self).captured()[j],
            TRACK && old(self).restore_entries_clear_capture_spec() ==>
                forall|j: int| 0 <= j < final(self).captured().len()
                    && #[trigger] final(self).captured()[j]
                    ==> !crate::vec::captured_in_range::<T, I>(
                        diff_log@, lo as int, hi as int, j as nat);

    /// Rewind a single slot to `old_value`. Within `[0, target_saved_len)`,
    /// either overwrites the existing slot (`index < data.len()`) or pushes
    /// (`index == data.len()`); above `target_saved_len`, no-op.
    ///
    /// The push case handles the pop+restore cycle: when restore truncates
    /// then replays diffs, popped slots reappear via `restore_entry`.
    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I)
        requires
            old(self).wf(),
            index.as_nat() < target_saved_len.as_nat() ==>
                index.as_nat() <= old(self).data().len(),
            // If we'd push, the new length must still fit in I.
            (index.as_nat() < target_saved_len.as_nat()
                && index.as_nat() == old(self).data().len())
                ==> old(self).data().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            // In-frame, in-bounds: overwrite.
            (index.as_nat() < target_saved_len.as_nat()
                && index.as_nat() < old(self).data().len())
                ==> final(self).data() ==
                    old(self).data().update(index.as_nat() as int, *old_value),
            // In-frame, at end: push.
            (index.as_nat() < target_saved_len.as_nat()
                && index.as_nat() == old(self).data().len())
                ==> final(self).data() == old(self).data().push(*old_value),
            // Out-of-frame: no-op on data.
            (index.as_nat() >= target_saved_len.as_nat())
                ==> final(self).data() == old(self).data(),
            // Flags decrease-only: a replay write never SETS a flag
            // (InlineStore writes tag-clear reprs; ParallelStore leaves its
            // pre-zeroed bitmap untouched). From `begin_restore`'s all-clear
            // start this keeps every flag clear through the replay — the
            // sparse set-only `finish_restore` needs exactly that.
            TRACK ==> forall|j: int| 0 <= j < final(self).captured().len()
                && #[trigger] final(self).captured()[j]
                ==> j < old(self).captured().len() && old(self).captured()[j];

    /// Rebuild `captured` from the surviving diff suffix. After restore, a
    /// slot is captured iff it appears in the parent frame's diff log.
    /// The all-clear requires (established by the replay loop via
    /// `restore_entry`'s flag-clearing ensures) is what makes an O(diffs)
    /// set-only implementation sound — production's protocol.
    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], saved_len: I)
        requires
            old(self).wf(),
            saved_len.as_nat() <= old(self).data().len(),
            // ALL flags clear (begin_restore + flag-free replay establish
            // this over the full flag range, not just [0, saved_len)).
            TRACK ==> forall|j: int| 0 <= j < old(self).captured().len()
                ==> !(#[trigger] old(self).captured()[j]),
        ensures
            final(self).wf(),
            // Discipline constancy: a store's capture discipline and replay
            // protocol are chosen at construction and immutable, so every
            // mutation preserves both. This is what lets the discipline be
            // an INSTANCE property (runtime-selectable via `DynStore`) while
            // `Vec`'s proofs still carry discipline facts across calls.
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).data() == old(self).data(),
            // Within `[0, saved_len)`, captured iff some surviving diff entry
            // points at this index. Above `saved_len`, unspecified (those
            // slots are about to be truncated by `Vec::restore`).
            TRACK ==> forall|i: int| 0 <= i < saved_len.as_nat() ==>
                #[trigger] final(self).captured()[i] == exists|k: int|
                    0 <= k < current_frame_diffs@.len()
                        && (#[trigger] current_frame_diffs@[k]).1.as_nat() == i;
}

} // verus!
