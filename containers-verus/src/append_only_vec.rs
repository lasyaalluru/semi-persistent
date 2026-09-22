// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Push-only semi-persistent vector (verified).
//!
//! `mark` saves the current length; `restore` truncates back to it. There is
//! NO diff log — data is never overwritten, only appended. So the snapshot a
//! frame names is literally a length-prefix of the current data:
//! `snapshots[k] == data[0 .. frames[k]]`, and restore just truncates `data`
//! to `frames[target]`, reproducing `snapshots[target]` exactly.
//!
//! Reuses the verified `ForkHistory` (branch-cut safety) and `ContainerId`
//! (cross-container rejection) unchanged — `restore` requires the same
//! `is_token_valid_spec` validity precondition as `Vec::restore`, and records
//! the cut via `forks.fork(...)`.

use vstd::prelude::*;

verus! {

use crate::index_like::IndexLike;
use crate::vec::{ShrinkPolicy, VecToken};

/// Push-only vec with semi-persistent mark/restore.
///
/// `I` is the index word: it names a position and thereby bounds the collection
/// (`wf` pins `data.len() < I::max_nat()`, so the last storable element sits at
/// `I::max_spec()` and no position ever wraps). Saved frame lengths are positions
/// too, hence `frames: Vec<I>` rather than `Vec<usize>` — at a 31-bit index that
/// halves the frame stack. `usize` is the default because a container cannot know
/// its own population; a caller who knows it opts into the narrow word.
pub struct AppendOnlyVec<T, I: IndexLike = usize, const TRACK: bool = true> {
    pub(crate) data: std::vec::Vec<T>,
    pub(crate) frames: std::vec::Vec<I>,
    /// Ghost snapshot stack: `snapshots[k]` is `data@` as of frame `k`'s mark,
    /// i.e. the length-`frames[k]` prefix. Parallel to `frames`.
    pub(crate) snapshots: Ghost<Seq<Seq<T>>>,
}

impl<T, I: IndexLike, const TRACK: bool> AppendOnlyVec<T, I, TRACK> {
    /// The abstract contents: the data sequence.
    pub open(crate) spec fn view(&self) -> Seq<T> {
        self.data@
    }

    pub open(crate) spec fn snapshots_view(&self) -> Seq<Seq<T>> {
        self.snapshots@
    }

    /// Frame-stack depth (spec counterpart of `depth()`; fields are `pub(crate)` —
    /// privacy closeout — so public contracts phrase frame counts through this).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.frames@.len()
    }


    /// Well-formedness:
    ///  - the element count fits the index word, so every position — the index
    ///    `push` returns, the length `len` reports, the frame lengths `mark`
    ///    saves — is representable in `I` and the checked conversions below are
    ///    infallible rather than merely guarded;
    ///  - snapshots and frames are parallel stacks;
    ///  - every saved length is within the current data and monotone
    ///    non-decreasing (append-only: a frame's prefix never shrinks while
    ///    live, and marks record ever-larger lengths);
    ///  - each snapshot IS the corresponding data prefix;
    ///  - the fork history is well-formed.
    pub open(crate) spec fn wf(&self) -> bool {
        let data = self.data@;
        let frames = self.frames@;
        let snaps = self.snapshots@;
        &&& data.len() < I::max_nat()
        &&& snaps.len() == frames.len()
        &&& (forall|k: int| 0 <= k < frames.len() ==>
                #[trigger] frames[k].as_nat() <= data.len())
        &&& (forall|k: int| 0 <= k && k + 1 < frames.len() ==>
                (#[trigger] frames[k]).as_nat() <= (#[trigger] frames[k + 1]).as_nat())
        &&& (forall|k: int| 0 <= k < frames.len() ==>
                #[trigger] snaps[k] == data.subrange(0, frames[k].as_nat() as int))
        &&& true
    }



    /// The mark-depth quantity the depth-headroom contracts are phrased over.
    /// Post-H2 the container tracks no genealogy, so this is the live frame
    /// depth (the stamp-array length it used to be lived on `GenStamps`).
    pub open(crate) spec fn fork_count_spec(&self) -> nat {
        self.frames@.len()
    }


    /// Empty append-only vec.
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        proof { I::lemma_max_nat_positive(); }  // 0 < I::max_nat(), so empty is wf
        AppendOnlyVec {
            data: std::vec::Vec::new(),
            frames: std::vec::Vec::new(),
            snapshots: Ghost(Seq::empty()),
        }
    }

    /// Element count, as a position in `I`.
    ///
    /// The `expect` is discharged by `wf`'s `data.len() < I::max_nat()` clause, so
    /// this cannot fail for a well-formed vec — the same protocol as
    /// `InlineStore::len` (`inline_store.rs`), and the reason `push` guards the
    /// *new* length rather than the returned index.
    #[inline(always)]
    pub fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.view().len(),
    {
        I::try_from_usize(self.data.len()).expect("len overflow")
    }

    pub fn is_empty(&self) -> (b: bool)
        ensures b == (self.view().len() == 0),
    {
        self.data.len() == 0
    }

    pub fn get(&self, idx: I) -> (v: &T)
        ensures idx.as_nat() < self.view().len() ==> *v == self.view()[idx.as_nat() as int],
    {
        // Total-with-documented-panic: explicit bound branch.
        if !(idx.as_usize() < self.data.len()) {
            crate::guard::refuse("AppendOnlyVec::get: index out of bounds");
        }
        &self.data[idx.as_usize()]
    }

    /// Contiguous read access to all elements (production parity; also the
    /// safe replacement for egraph's `from_raw_parts` contiguity assumption).
    /// The backing store IS a `std::vec::Vec`, so the slice is the view.
    #[inline(always)]
    pub fn as_slice(&self) -> (r: &[T])
        ensures r@ == self.view(),
    {
        self.data.as_slice()
    }

    /// Append a value; returns its index. Existing data and every snapshot
    /// prefix are preserved (append-only), so `wf` is maintained.
    ///
    /// The capacity precondition is on the length *after* the append, not on the
    /// returned index: `wf` has to hold on exit, and it is what makes `len` and
    /// `mark` infallible. Requiring only `view().len() < I::max_nat()` would admit
    /// a final push whose successor length falls outside `I`.
    #[inline(always)]
    pub(crate) fn push(&mut self, val: T) -> (idx: I)
        requires
            old(self).wf(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            idx.as_nat() == old(self).view().len(),
            final(self).view() == old(self).view().push(val),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let idx = I::try_from_usize(self.data.len()).expect(
            "append-only vec is full for its index word",
        );
        self.data.push(val);
        proof {
            let data = self.data@;
            let old_data = old(self).data@;
            assert(data == old_data.push(val));
            // Each old frame length <= old_data.len() <= data.len(), and the
            // prefix [0, frames[k]) is unchanged by the append.
            assert forall|k: int| 0 <= k < self.frames@.len() implies
                #[trigger] self.snapshots@[k] == data.subrange(0, self.frames@[k].as_nat() as int)
            by {
                assert(old(self).snapshots@[k]
                    == old_data.subrange(0, self.frames@[k].as_nat() as int));
                assert(self.frames@[k].as_nat() <= old_data.len());
                assert(data.subrange(0, self.frames@[k].as_nat() as int)
                    =~= old_data.subrange(0, self.frames@[k].as_nat() as int));
            }
        }
        idx
    }

    /// Current depth (number of live marks).
    pub fn depth(&self) -> (d: usize)
        ensures d == self.depth_spec(),
    {
        self.frames.len()
    }

    /// Remaining mark-depth headroom before the `u32::MAX` frame cap (the
    /// genealogy lives on the owning `History`; see `Vec::restores_remaining`).
    pub fn restores_remaining(&self) -> (r: usize)
        requires self.wf(),
        ensures
            self.depth_spec() < u32::MAX ==>
                r as nat == (u32::MAX - self.depth_spec()) as nat,
            self.depth_spec() >= u32::MAX ==> r == 0,
    {
        (u32::MAX as usize).saturating_sub(self.frames.len())
    }

    /// Push a frame without minting: the structural half of `mark` (what a
    /// typed group drives; the group's `History` mints the token). The new
    /// frame records `data.len()`, keeping `frames` monotone.
    pub(crate) fn push_frame(&mut self, shrink: ShrinkPolicy)
        requires
            old(self).wf(),
            TRACK,
            old(self).depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        crate::guard::check_precondition(TRACK, "mark() called on untracked AppendOnlyVec");
        crate::guard::check_precondition(
            self.frames.len() < u32::MAX as usize,
            "AppendOnlyVec::mark: frame-stack depth would overflow u32",
        );

        // Capacity reclamation, production's AppendOnlyVec variant:
        // condition `cap > len * factor + headroom` (vs Vec's
        // `cap > factor * len`), target `len + headroom`. Observably inert
        // (external_body helper: capacity is unmodeled; contract = element
        // sequence unchanged).
        match shrink {
            ShrinkPolicy::Never => {}
            ShrinkPolicy::IfOverallocated { factor, headroom } => {
                shrink_aov_capacity(&mut self.data, factor, headroom);
            }
        }

        // The saved length is a position, so it is stored as `I`; the conversion
        // is infallible by `wf`.
        let saved_len = I::try_from_usize(self.data.len()).expect("len overflow");
        let ghost old_view = self.view();
        let ghost old_frames = self.frames@;

        self.frames.push(saved_len);
        self.snapshots = Ghost(self.snapshots@.push(old_view));

        proof {
            let data = self.data@;
            let frames = self.frames@;
            let snaps = self.snapshots@;
            let new_top = (frames.len() - 1) as int;
            assert(frames[new_top] == saved_len);
            assert(forall|k: int| 0 <= k < old_frames.len() ==> frames[k] == old_frames[k]);
            // monotone: only the new adjacency (old top, new) to check;
            // old top <= old_data.len() == saved_len == frames[new_top].
            assert forall|k: int| 0 <= k && k + 1 < frames.len() implies
                (#[trigger] frames[k]).as_nat() <= (#[trigger] frames[k + 1]).as_nat() by {
                if k + 1 < new_top {
                } else {
                    assert(frames[k].as_nat() <= data.len());
                    assert(frames[k + 1].as_nat() == saved_len.as_nat() == data.len());
                }
            }
            // snapshots: new top is the full current data prefix; old ones
            // unchanged (data unchanged by mark).
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] snaps[k] == data.subrange(0, frames[k].as_nat() as int) by {
                if k < new_top {
                    assert(old(self).snapshots@[k]
                        == data.subrange(0, frames[k].as_nat() as int));
                } else {
                    assert(snaps[new_top] == old_view);
                    assert(frames[new_top].as_nat() == data.len());
                    assert(old_view =~= data.subrange(0, data.len() as int));
                }
            }
        }
    }


    // ------------------------------------------------------------------
    // Total-operation shell, matching Vec's pattern.
    // ------------------------------------------------------------------

    /// Exec counterpart of `push`'s capacity precondition.
    #[inline(always)]
    pub fn can_push(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() + 1 < I::max_nat()),
    {
        let n = self.data.len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(cap as nat == I::max_nat() - 1);
        }
        n < cap
    }

    /// Total push: refuses at the index word's capacity, returns the new
    /// element's index on success.
    ///
    /// One read of the length serves the capacity test, the returned index and
    /// the append, and the whole path is inlined into the caller: the append
    /// loop a node store or a log writer runs is then a compare, a branch to the
    /// cold growth call, and a store — the same instructions as a bare
    /// `Vec::push` loop — with nothing for the optimiser to hoist or guess.
    #[inline(always)]
    pub fn try_push(&mut self, val: T) -> (r: Result<I, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(idx) ==> idx.as_nat() == old(self).view().len()
                && final(self).view() == old(self).view().push(val),
            r is Err ==> final(self).view() == old(self).view(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        let n = self.data.len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(cap as nat == I::max_nat() - 1);
        }
        if n < cap {
            // `n < cap` puts `n` inside `I`, so the conversion cannot fail.
            let idx = match I::try_from_usize(n) {
                Some(i) => i,
                None => crate::guard::refuse("append-only vec: length inside the index word"),
            };
            let ghost old_data = self.data@;
            self.data.push(val);
            proof {
                let data = self.data@;
                assert(data == old_data.push(val));
                assert forall|k: int| 0 <= k < self.frames@.len() implies
                    #[trigger] self.snapshots@[k] == data.subrange(0, self.frames@[k].as_nat() as int)
                by {
                    assert(old(self).snapshots@[k]
                        == old_data.subrange(0, self.frames@[k].as_nat() as int));
                    assert(self.frames@[k].as_nat() <= old_data.len());
                    assert(data.subrange(0, self.frames@[k].as_nat() as int)
                        =~= old_data.subrange(0, self.frames@[k].as_nat() as int));
                }
            }
            Ok(idx)
        } else {
            Err(crate::error::ContainerError::CapacityExhausted)
        }
    }





    /// The structural core of a pop-style restore (the SMT-LIB `pop`, the
    /// group path): reconstruct to frame `target` and drop frames
    /// `target..`; the cut starts at `target` (that frame's token dies).
    pub(crate) fn restore_frame(&mut self, target: usize)
        requires
            old(self).wf(),
            TRACK,
            (target as nat) < old(self).depth_spec(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).snapshots_view()[target as int],
            final(self).depth_spec() == target as nat,
            final(self).snapshots_view() == old(self).snapshots_view().subrange(0, target as int),
    {
        let saved_len = self.frames[target].as_usize();
        let ghost old_data = self.data@;
        let ghost old_frames = self.frames@;
        let ghost old_snaps = self.snapshots@;
        proof {
            assert(old_snaps[target as int] == old_data.subrange(0, saved_len as int));
            assert(saved_len <= old_data.len());
        }
        self.data.truncate(saved_len);
        self.frames.truncate(target);
        self.snapshots = Ghost(self.snapshots@.subrange(0, target as int));
        proof {
            let data = self.data@;
            let frames = self.frames@;
            let snaps = self.snapshots@;
            assert(data =~= old_data.subrange(0, saved_len as int));
            assert(data =~= old_snaps[target as int]);
            assert(snaps =~= old_snaps.subrange(0, target as int));
            assert(frames =~= old_frames.subrange(0, target as int));
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] frames[k].as_nat() <= data.len() by {
                assert(frames[k] == old_frames[k]);
                assert(k < target);
                lemma_aov_frames_le(old_frames, k, target as int);
            }
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] snaps[k] == data.subrange(0, frames[k].as_nat() as int) by {
                assert(snaps[k] == old_snaps[k]);
                assert(old_snaps[k] == old_data.subrange(0, frames[k].as_nat() as int));
                lemma_aov_frames_le(old_frames, k, target as int);
                assert(frames[k].as_nat() <= saved_len);
                assert(data.subrange(0, frames[k].as_nat() as int)
                    =~= old_data.subrange(0, frames[k].as_nat() as int));
            }
        }
    }

    /// Semantics B (design doc 08 §1): reconstruct to frame `target` and keep
    /// that frame open — frames `target + 1..` are gone, frame `target` stays
    /// (its saved length is the restored length), so its token stays valid and
    /// every later token dies (the cut starts at `target + 1`).
    pub(crate) fn reset_frame(&mut self, target: usize)
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
        let saved_len = self.frames[target].as_usize();
        let ghost old_data = self.data@;
        let ghost old_frames = self.frames@;
        let ghost old_snaps = self.snapshots@;
        proof {
            assert(old_snaps[target as int] == old_data.subrange(0, saved_len as int));
            assert(saved_len <= old_data.len());
        }
        self.data.truncate(saved_len);
        self.frames.truncate(target + 1);
        self.snapshots = Ghost(self.snapshots@.subrange(0, target as int + 1));
        proof {
            let data = self.data@;
            let frames = self.frames@;
            let snaps = self.snapshots@;
            assert(data =~= old_data.subrange(0, saved_len as int));
            assert(data =~= old_snaps[target as int]);
            assert(snaps =~= old_snaps.subrange(0, target as int + 1));
            assert(frames =~= old_frames.subrange(0, target as int + 1));
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] frames[k].as_nat() <= data.len() by {
                assert(frames[k] == old_frames[k]);
                assert(k <= target);
                lemma_aov_frames_le(old_frames, k, target as int);
            }
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] snaps[k] == data.subrange(0, frames[k].as_nat() as int) by {
                assert(snaps[k] == old_snaps[k]);
                assert(old_snaps[k] == old_data.subrange(0, frames[k].as_nat() as int));
                lemma_aov_frames_le(old_frames, k, target as int);
                assert(frames[k].as_nat() <= saved_len);
                assert(data.subrange(0, frames[k].as_nat() as int)
                    =~= old_data.subrange(0, frames[k].as_nat() as int));
            }
        }
    }

    /// Drop the open top frame, undoing its appends (the SMT-LIB `pop`); that
    /// frame's token dies. Refuses on an empty frame stack.
    pub(crate) fn pop_frame(&mut self)
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
        let d = self.frames.len();
        if !(d >= 1) {
            crate::guard::refuse("AppendOnlyVec::pop_scope: no open frame");
        }
        self.restore_frame(d - 1);
    }




}

/// In a monotone non-decreasing frame-length sequence, `frames[k] <=
/// frames[j]` for `k <= j`. (Used to bound a surviving frame by the restore
/// target's saved length.)
pub(crate) proof fn lemma_aov_frames_le<I: IndexLike>(frames: Seq<I>, k: int, j: int)
    requires
        0 <= k <= j < frames.len(),
        forall|a: int| 0 <= a && a + 1 < frames.len() ==>
            (#[trigger] frames[a]).as_nat() <= (#[trigger] frames[a + 1]).as_nat(),
    ensures
        frames[k].as_nat() <= frames[j].as_nat(),
    decreases j - k,
{
    if k < j {
        lemma_aov_frames_le(frames, k, j - 1);
        assert(0 <= (j - 1) && (j - 1) + 1 < frames.len());
        assert(frames[(j - 1)].as_nat() <= frames[(j - 1) + 1].as_nat());  // trigger at a = j-1
    }
}

/// AppendOnlyVec capacity-only shrink: production's variant condition
/// `cap > len * factor + headroom`, target `len + headroom`. `external_body`
/// because Verus does not model `Vec::capacity`/`shrink_to`; trusted contract
/// = element sequence unchanged. Trust ledger: group B.
#[verifier::external_body]
fn shrink_aov_capacity<T>(data: &mut Vec<T>, factor: usize, headroom: usize)
    ensures final(data)@ == old(data)@,
{
    if data.capacity() > data.len().saturating_mul(factor).saturating_add(headroom) {
        data.shrink_to(data.len().saturating_add(headroom));
    }
}

} // verus!

// ---------------------------------------------------------------------------
// Trusted glue (outside verus!{}; trust ledger group E): iteration delegates
// 1:1 to the verified `as_slice` (whose contract proves the slice IS the
// view), then uses std's slice iterator. Read-only — the append-only
// invariant (no mutation of existing elements) is structurally unbreachable
// from a `&self` iterator.
// ---------------------------------------------------------------------------

impl<T, I: IndexLike, const TRACK: bool> AppendOnlyVec<T, I, TRACK> {
    /// Iterate over the elements in insertion order (production parity).
    #[inline(always)]
    pub fn iter(&self) -> core::slice::Iter<'_, T> {
        self.as_slice().iter()
    }
}

// Production-surface parity impls (production derives/ships these).
impl<T, I: IndexLike, const TRACK: bool> core::fmt::Debug for AppendOnlyVec<T, I, TRACK> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AppendOnlyVec")
            .field("len", &self.len().as_usize())
            .field("depth", &self.depth())
            .finish()
    }
}

impl<T, I: IndexLike, const TRACK: bool> Default for AppendOnlyVec<T, I, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}
