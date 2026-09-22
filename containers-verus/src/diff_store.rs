// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `DiffStore`: the capture-protocol contract.
//!
//! A storage backend exposes two ghost views:
//!   - `data: Seq<T>`     — the abstract sequence of stored values
//!   - `captured: Seq<bool>` — per-slot "has been logged this frame" flag
//!
//! Plus a well-formedness predicate `wf()` that ties the two together
//! (e.g. equal lengths, plus any backend-specific invariants).
//!
//! The capture protocol — first-write-wins:
//!
//!   - `prepare_mark(saved_len, prev_diffs)` clears `captured[0..saved_len]`.
//!   - `set_raw(i, v)` overwrites `data[i]`; `captured` unchanged.
//!   - `capture(i, saved_len, log)` — if `i < saved_len && !captured[i]`,
//!       appends `(data[i], i)` to `log` and sets `captured[i] = true`;
//!       otherwise no-op.
//!   - `force_capture(i, saved_len, log)` — retained trait surface for
//!       unconditional capture within `i < saved_len`; the vector does not
//!       call it, because `pop` uses bounded first-write-wins `capture`.
//!   - `restore_entry(i, old, target_saved_len)` rewinds `data[i] := old` for
//!     `i < target_saved_len` (and `i <= data.len()` because of the pre-pad
//!     pushed by previous `restore_entry` calls in the same loop).
//!   - `finish_restore(diffs, saved_len)` rebuilds `captured` from the
//!     surviving diff suffix.
//!
//! `Vec`'s proof talks only to this contract, so it's parametric in storage.

use vstd::prelude::*;

use crate::index_like::IndexLike;

verus! {

/// Storage backend for the semi-persistent vector — the PUBLIC half of the
/// store contract: total queries and maintenance operations. The capture
/// protocol itself (`push`/`get`/`set_raw`/`truncate`, `prepare_mark`,
/// `capture`, `begin_restore`/`restore_entry`/`restore_overlay`/
/// `finish_restore`, …) lives on the crate-private supertrait
/// [`crate::diff_store_ops::DiffStoreOps`]: those operations carry
/// preconditions that only `Vec`'s own proven invariants can discharge (some
/// are ghost — "every set flag is named by a diff entry"), so they are sealed
/// away from the public surface rather than guarded at runtime. Every store
/// implements both; `DiffStore` stays the one bound consumers name.
///
/// Diff entries are `(T, I)` pairs (old value, index). Methods take exec
/// slices/`Vec`s; their `@` views are the spec-level `Seq` we reason about.
pub trait DiffStore<T, I, const TRACK: bool>: crate::diff_store_ops::DiffStoreOps<T, I, TRACK> + Sized
where
    T: Sized + Copy,
    I: IndexLike,
{

    /// Universal consequence of `wf`: the capture-flag sequence is exactly
    /// as long as the data sequence. Both backends discharge this trivially.
    proof fn lemma_wf_captured_len(&self)
        requires self.wf(),
        ensures self.captured().len() == self.data().len();

    /// Universal consequence of `wf`: the element count fits the index word,
    /// so every position is representable in `I`. Each backend's `wf` pins
    /// it; a composite over an abstract store reaches it through this lemma
    /// (the frame-pushing `Vec` entry points require it).
    proof fn lemma_wf_data_len(&self)
        requires self.wf(),
        ensures self.data().len() < I::max_nat();

    // -- raw read / write API ------------------------------------------------

    fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.data().len() == 0);

    fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.data().len();

    /// Untrapped element count for total-operation headroom queries: `len()`
    /// deliberately traps past the index
    /// word (the deferred overflow protocol), so a capacity check needs the
    /// usize truth without a trap.
    fn raw_len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.data().len();

    fn pop(&mut self) -> (r: Option<T>)
        requires old(self).wf(),
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
            old(self).data().len() == 0 ==> {
                &&& r is None
                &&& final(self).data() == old(self).data()
                &&& TRACK ==> final(self).captured() == old(self).captured()
            },
            old(self).data().len() > 0 ==> {
                &&& r is Some
                &&& r->Some_0 == old(self).data()[old(self).data().len() - 1]
                &&& final(self).data() == old(self).data().drop_last()
                &&& TRACK ==> final(self).captured() == old(self).captured().drop_last()
            };

    /// Exec twin of `unique_capture_spec`: the sealing and reordering paths
    /// gate on it at runtime (a chronological column never seals).
    fn unique_capture(&self) -> (b: bool)
        ensures b == self.unique_capture_spec();

    fn needs_replayed_indices(&self) -> (b: bool)
        ensures b == self.needs_replayed_indices_spec();

    fn restore_entries_clear_capture(&self) -> (b: bool)
        ensures b == self.restore_entries_clear_capture_spec();

    // -- maintenance ---------------------------------------------------------


    /// Restore one cold run: write `values` into the live column starting at
    /// `base`, clamped to the current length. Overwrite-only: the window
    /// `[base, base+values.len())` (intersected with `[0, data.len())`) takes
    /// the run values, every other cell is untouched, and the length and
    /// capture flags are unchanged (a raw data write; the bitmap is inert).
    /// Each backend proves this operation: tag-inline re-encodes each cell,
    /// while raw stores use a checked copy_from_slice.
    fn restore_run(&mut self, base: I, values: &[T])
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).unique_capture_spec() == old(self).unique_capture_spec(),
            final(self).needs_replayed_indices_spec()
                == old(self).needs_replayed_indices_spec(),
            final(self).restore_entries_clear_capture_spec()
                == old(self).restore_entries_clear_capture_spec(),
            final(self).captured() == old(self).captured(),
            final(self).data().len() == old(self).data().len(),
            forall|i: int| 0 <= i < final(self).data().len() ==>
                #[trigger] final(self).data()[i] ==
                    if base.as_nat() <= i && (i as nat) < base.as_nat() + values@.len() {
                        values@[i - base.as_nat()]
                    } else {
                        old(self).data()[i]
                    };

    fn shrink_if(&mut self, factor: usize, headroom: usize)
        requires old(self).wf(),
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
            TRACK ==> final(self).captured() == old(self).captured();

    /// Contiguous read access to the raw values, when the backend stores them
    /// contiguously (production parity: `Some` for `ParallelStore`, `None`
    /// for `InlineStore`, whose cells are tag-carrying reprs, not `T`s).
    fn as_slice(&self) -> (r: Option<&[T]>)
        ensures r matches Some(s) ==> s@ == self.data(),
    {
        None
    }
}

/// Definitional broadcasts for the three base stores' constant discipline
/// answers. The trait's constancy ensures mention `unique_capture_spec` /
/// `needs_replayed_indices_spec` applications whose open bodies the solver
/// only unfolds when an occurrence triggers; these pin the constants at every
/// occurrence. They live here (not in the store modules) so each store module
/// can `broadcast use` its lemma without a definitional cycle.
pub broadcast proof fn lemma_inline_discipline<T, I, const TRACK: bool>(
    s: &crate::inline_store::InlineStore<T, I>,
)
where
    T: crate::tagged::Tagged,
    I: crate::index_like::IndexLike,
    ensures
        #[trigger] <crate::inline_store::InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>
            ::unique_capture_spec(s) == true,
        #[trigger] <crate::inline_store::InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>
            ::needs_replayed_indices_spec(s) == true,
        #[trigger] <crate::inline_store::InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>
            ::restore_entries_clear_capture_spec(s) == true,
{
}

pub broadcast proof fn lemma_parallel_discipline<T, I, const TRACK: bool>(
    s: &crate::parallel_store::ParallelStore<T, I>,
)
where
    T: Sized + Copy,
    I: crate::index_like::IndexLike,
    ensures
        #[trigger] <crate::parallel_store::ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>
            ::unique_capture_spec(s) == true,
        #[trigger] <crate::parallel_store::ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>
            ::needs_replayed_indices_spec(s) == false,
        #[trigger] <crate::parallel_store::ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>
            ::restore_entries_clear_capture_spec(s) == false,
{
}

pub broadcast proof fn lemma_trail_discipline<T, I, const TRACK: bool>(
    s: &crate::trail_store::TrailStore<T, I>,
)
where
    T: Sized + Copy,
    I: crate::index_like::IndexLike,
    ensures
        #[trigger] <crate::trail_store::TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>
            ::unique_capture_spec(s) == false,
        #[trigger] <crate::trail_store::TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>
            ::needs_replayed_indices_spec(s) == false,
        #[trigger] <crate::trail_store::TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>
            ::restore_entries_clear_capture_spec(s) == false,
{
}

/// Definitional broadcast for `DynStore`'s delegated spec views: pins each
/// view to its variant's, so a caller-supplied fact phrased over the enum
/// reaches the inner store's precondition (and back) in every proof context
/// that mentions the application. Lives here for the same no-cycle reason as
/// the discipline lemmas above.
pub broadcast proof fn lemma_dyn_views<T, I, const TRACK: bool>(
    s: &crate::dyn_store::DynStore<T, I>,
)
where
    T: crate::tagged::Tagged,
    I: crate::index_like::IndexLike,
    ensures
        (#[trigger] <crate::dyn_store::DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(s))
            == match s {
                crate::dyn_store::DynStore::Inline(inner) =>
                    <crate::inline_store::InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(inner),
                crate::dyn_store::DynStore::Parallel(inner) =>
                    <crate::parallel_store::ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(inner),
                crate::dyn_store::DynStore::Trail(inner) =>
                    <crate::trail_store::TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(inner),
            },
        (#[trigger] <crate::dyn_store::DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(s))
            == match s {
                crate::dyn_store::DynStore::Inline(inner) =>
                    <crate::inline_store::InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(inner),
                crate::dyn_store::DynStore::Parallel(inner) =>
                    <crate::parallel_store::ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(inner),
                crate::dyn_store::DynStore::Trail(inner) =>
                    <crate::trail_store::TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(inner),
            },
        (#[trigger] <crate::dyn_store::DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(s))
            == match s {
                crate::dyn_store::DynStore::Inline(inner) =>
                    <crate::inline_store::InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(inner),
                crate::dyn_store::DynStore::Parallel(inner) =>
                    <crate::parallel_store::ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(inner),
                crate::dyn_store::DynStore::Trail(inner) =>
                    <crate::trail_store::TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(inner),
            },
{
}

} // verus!
