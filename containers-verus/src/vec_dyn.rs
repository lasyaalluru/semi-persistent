// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `VecD`: runtime store selection, dispatched once per operation.
//!
//! The three-tier [`Vec`] is generic over its diff store, and a caller who
//! picks the store at runtime used to get `Vec<T, I, DynStore<T, I>>`: one
//! generic vector whose store is an enum, so every store primitive a write
//! touches — the capture and the raw set, two per write; more on a restore —
//! is a `match` on the store's tag, and the tag is reloaded between them
//! because the primitive in between writes through the same `&mut`. Measured
//! on the three-tier write rows that put the runtime-selected columns at
//! 1.26–2.2× the static ones running the same loops.
//!
//! `VecD` is instead an enum over the three STATIC vectors. Each operation
//! matches once and runs the fully specialised body the static column runs,
//! so the runtime-selected column is the static column plus one well-predicted
//! branch per call. Every method here forwards to the arm with the same
//! contract restated over this enum's spec functions, which are themselves the
//! arm's; the proofs are the arms' proofs.
//!
//! [`DynStore`](crate::dyn_store::DynStore) remains for callers that want the
//! per-primitive shape; nothing in the workspace does.

use vstd::prelude::*;

use crate::group::Member;
use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::parallel_store::ParallelStore;
use crate::tagged::Tagged;
use crate::trail_store::TrailStore;
use crate::vec::{MarkOptions, ShrinkPolicy, Vec};

pub use crate::dyn_store::StoreKind;

verus! {

/// Runtime-selected three-tier vector: one of the three static columns.
pub enum VecD<T, I, const TRACK: bool = true>
where
    T: Tagged,
    I: IndexLike,
{
    Inline(Vec<T, I, InlineStore<T, I>, TRACK>),
    Parallel(Vec<T, I, ParallelStore<T, I>, TRACK>),
    Trail(Vec<T, I, TrailStore<T, I>, TRACK>),
}

impl<T, I, const TRACK: bool> VecD<T, I, TRACK>
where
    T: Tagged,
    I: IndexLike,
{
    pub open(crate) spec fn view(&self) -> Seq<T> {
        match self {
            VecD::Inline(v) => v.view(),
            VecD::Parallel(v) => v.view(),
            VecD::Trail(v) => v.view(),
        }
    }

    pub open(crate) spec fn snapshots_view(&self) -> Seq<Seq<T>> {
        match self {
            VecD::Inline(v) => v.snapshots_view(),
            VecD::Parallel(v) => v.snapshots_view(),
            VecD::Trail(v) => v.snapshots_view(),
        }
    }

    pub open(crate) spec fn depth_spec(&self) -> nat {
        match self {
            VecD::Inline(v) => v.depth_spec(),
            VecD::Parallel(v) => v.depth_spec(),
            VecD::Trail(v) => v.depth_spec(),
        }
    }

    pub open(crate) spec fn wf(&self) -> bool {
        match self {
            VecD::Inline(v) => v.wf(),
            VecD::Parallel(v) => v.wf(),
            VecD::Trail(v) => v.wf(),
        }
    }

    pub open(crate) spec fn untracked(&self) -> bool {
        match self {
            VecD::Inline(v) => v.untracked(),
            VecD::Parallel(v) => v.untracked(),
            VecD::Trail(v) => v.untracked(),
        }
    }

    pub open(crate) spec fn diff_log_len_spec(&self) -> nat {
        match self {
            VecD::Inline(v) => v.diff_log_len_spec(),
            VecD::Parallel(v) => v.diff_log_len_spec(),
            VecD::Trail(v) => v.diff_log_len_spec(),
        }
    }

    /// Frame `f` (any tier) captures index `j`.
    pub open(crate) spec fn frame_captures(&self, f: int, j: nat) -> bool {
        match self {
            VecD::Inline(v) => v.frame_captures(f, j),
            VecD::Parallel(v) => v.frame_captures(f, j),
            VecD::Trail(v) => v.frame_captures(f, j),
        }
    }

    pub open(crate) spec fn names_index(out: Seq<I>, j: nat) -> bool {
        exists|i: int| 0 <= i < out.len() && (#[trigger] out[i]).as_nat() == j
    }

    /// The selected store protocol.
    pub fn kind(&self) -> (k: StoreKind)
        ensures
            k == StoreKind::Inline <==> self is Inline,
            k == StoreKind::Parallel <==> self is Parallel,
            k == StoreKind::Trail <==> self is Trail,
    {
        match self {
            VecD::Inline(_) => StoreKind::Inline,
            VecD::Parallel(_) => StoreKind::Parallel,
            VecD::Trail(_) => StoreKind::Trail,
        }
    }

    /// Empty vector on the selected store protocol.
    pub fn new_kind(kind: StoreKind) -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        match kind {
            StoreKind::Inline => VecD::Inline(Vec::<T, I, InlineStore<T, I>, TRACK>::new()),
            StoreKind::Parallel => VecD::Parallel(Vec::<T, I, ParallelStore<T, I>, TRACK>::new()),
            StoreKind::Trail => VecD::Trail(Vec::<T, I, TrailStore<T, I>, TRACK>::new()),
        }
    }

    /// Runtime-selected store protocol with an independent retention policy.
    pub fn new_kind_with_policy(kind: StoreKind, tier_policy: crate::tier_policy::TierPolicy) -> Self {
        match kind {
            StoreKind::Inline => VecD::Inline(
                Vec::<T, I, InlineStore<T, I>, TRACK>::new_with_policy(tier_policy),
            ),
            StoreKind::Parallel => VecD::Parallel(
                Vec::<T, I, ParallelStore<T, I>, TRACK>::new_with_policy(tier_policy),
            ),
            StoreKind::Trail => VecD::Trail(
                Vec::<T, I, TrailStore<T, I>, TRACK>::new_with_policy(tier_policy),
            ),
        }
    }

    pub(crate) proof fn lemma_snapshots_len(&self)
        requires self.wf(),
        ensures self.snapshots_view().len() == self.depth_spec(),
    {
        match self {
            VecD::Inline(v) => v.lemma_snapshots_len(),
            VecD::Parallel(v) => v.lemma_snapshots_len(),
            VecD::Trail(v) => v.lemma_snapshots_len(),
        }
    }

    #[inline(always)]
    pub fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.view().len(),
    {
        match self {
            VecD::Inline(v) => v.len(),
            VecD::Parallel(v) => v.len(),
            VecD::Trail(v) => v.len(),
        }
    }

    #[inline(always)]
    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() == 0),
    {
        match self {
            VecD::Inline(v) => v.is_empty(),
            VecD::Parallel(v) => v.is_empty(),
            VecD::Trail(v) => v.is_empty(),
        }
    }

    #[inline(always)]
    pub fn get_index(&self, i: I) -> (v: T)
        requires self.wf(),
        ensures i.as_nat() < self.view().len() ==> v == self.view()[i.as_nat() as int],
    {
        match self {
            VecD::Inline(v) => v.get_index(i),
            VecD::Parallel(v) => v.get_index(i),
            VecD::Trail(v) => v.get_index(i),
        }
    }

    #[inline(always)]
    pub fn set_index(&mut self, i: I, value: T)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            i.as_nat() < old(self).view().len() ==> {
                &&& final(self).view() == old(self).view().update(i.as_nat() as int, value)
                &&& final(self).snapshots_view() == old(self).snapshots_view()
            },
    {
        match self {
            VecD::Inline(v) => v.set_index(i, value),
            VecD::Parallel(v) => v.set_index(i, value),
            VecD::Trail(v) => v.set_index(i, value),
        }
    }

    pub(crate) fn push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().push(value),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        match self {
            VecD::Inline(v) => v.push(value),
            VecD::Parallel(v) => v.push(value),
            VecD::Trail(v) => v.push(value),
        }
    }

    pub fn can_push(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() + 1 < I::max_nat()),
    {
        match self {
            VecD::Inline(v) => v.can_push(),
            VecD::Parallel(v) => v.can_push(),
            VecD::Trail(v) => v.can_push(),
        }
    }

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
        match self {
            VecD::Inline(v) => v.try_push(value),
            VecD::Parallel(v) => v.try_push(value),
            VecD::Trail(v) => v.try_push(value),
        }
    }

    pub fn try_extend(&mut self, values: &[T]) -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).view() == old(self).view() + values@,
            r is Err ==> final(self).view() == old(self).view(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        match self {
            VecD::Inline(v) => v.try_extend(values),
            VecD::Parallel(v) => v.try_extend(values),
            VecD::Trail(v) => v.try_extend(values),
        }
    }

    pub fn pop(&mut self) -> (r: Option<T>)
        requires old(self).wf(),
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
        match self {
            VecD::Inline(v) => v.pop(),
            VecD::Parallel(v) => v.pop(),
            VecD::Trail(v) => v.pop(),
        }
    }

    pub fn push_untracked(&mut self, value: T)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            (old(self).untracked() && old(self).view().len() + 1 < I::max_nat()) ==> {
                &&& final(self).untracked()
                &&& final(self).view() == old(self).view().push(value)
                &&& final(self).diff_log_len_spec() == 0
            },
    {
        match self {
            VecD::Inline(v) => v.push_untracked(value),
            VecD::Parallel(v) => v.push_untracked(value),
            VecD::Trail(v) => v.push_untracked(value),
        }
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
        match self {
            VecD::Inline(v) => v.pop_untracked(),
            VecD::Parallel(v) => v.pop_untracked(),
            VecD::Trail(v) => v.pop_untracked(),
        }
    }

    pub fn set_untracked(&mut self, i: I, value: T)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            (old(self).untracked() && i.as_nat() < old(self).view().len()) ==> {
                &&& final(self).untracked()
                &&& final(self).view() == old(self).view().update(i.as_nat() as int, value)
                &&& final(self).diff_log_len_spec() == 0
            },
    {
        match self {
            VecD::Inline(v) => v.set_untracked(i, value),
            VecD::Parallel(v) => v.set_untracked(i, value),
            VecD::Trail(v) => v.set_untracked(i, value),
        }
    }

    pub fn depth(&self) -> (d: usize)
        requires self.wf(),
        ensures d == self.depth_spec(),
    {
        match self {
            VecD::Inline(v) => v.depth(),
            VecD::Parallel(v) => v.depth(),
            VecD::Trail(v) => v.depth(),
        }
    }

    pub fn restores_remaining(&self) -> (r: usize)
        requires self.wf(),
        ensures
            self.depth_spec() < u32::MAX ==>
                r as nat == (u32::MAX - self.depth_spec()) as nat,
            self.depth_spec() >= u32::MAX ==> r == 0,
    {
        match self {
            VecD::Inline(v) => v.restores_remaining(),
            VecD::Parallel(v) => v.restores_remaining(),
            VecD::Trail(v) => v.restores_remaining(),
        }
    }

    pub fn as_slice(&self) -> (r: Option<&[T]>)
        ensures r matches Some(s) ==> s@ == self.view(),
    {
        match self {
            VecD::Inline(v) => v.as_slice(),
            VecD::Parallel(v) => v.as_slice(),
            VecD::Trail(v) => v.as_slice(),
        }
    }

    pub fn can_mark(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (TRACK && self.depth_spec() < u32::MAX
            && self.view().len() < I::max_nat()),
    {
        match self {
            VecD::Inline(v) => v.can_mark(),
            VecD::Parallel(v) => v.can_mark(),
            VecD::Trail(v) => v.can_mark(),
        }
    }

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
        match self {
            VecD::Inline(v) => v.try_push_frame_with(options),
            VecD::Parallel(v) => v.try_push_frame_with(options),
            VecD::Trail(v) => v.try_push_frame_with(options),
        }
    }

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
        match self {
            VecD::Inline(v) => v.try_push_frame_adaptive(shrink, input),
            VecD::Parallel(v) => v.try_push_frame_adaptive(shrink, input),
            VecD::Trail(v) => v.try_push_frame_adaptive(shrink, input),
        }
    }

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
        match self {
            VecD::Inline(v) => v.apply_adaptive(input),
            VecD::Parallel(v) => v.apply_adaptive(input),
            VecD::Trail(v) => v.apply_adaptive(input),
        }
    }

    pub fn apply_tier_policy(&mut self)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        match self {
            VecD::Inline(v) => v.apply_tier_policy(),
            VecD::Parallel(v) => v.apply_tier_policy(),
            VecD::Trail(v) => v.apply_tier_policy(),
        }
    }

    pub fn flush_trail(&mut self)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        match self {
            VecD::Inline(v) => v.flush_trail(),
            VecD::Parallel(v) => v.flush_trail(),
            VecD::Trail(v) => v.flush_trail(),
        }
    }

    pub fn compress_hot(&mut self)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).depth_spec() == old(self).depth_spec(),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        match self {
            VecD::Inline(v) => v.compress_hot(),
            VecD::Parallel(v) => v.compress_hot(),
            VecD::Trail(v) => v.compress_hot(),
        }
    }

    pub fn pending_restore_indices_at(&self, depth: usize) -> (r: Option<std::vec::Vec<I>>)
        requires self.wf(),
        ensures
            r is Some <==> (depth as nat) < self.depth_spec(),
            r matches Some(out) ==> forall|j: nat| #[trigger] Self::names_index(out@, j)
                <==> exists|f: int| depth as nat <= f < self.depth_spec()
                    && #[trigger] self.frame_captures(f, j),
    {
        // The arm's `names_index` and this enum's are the same definition on
        // different types; the lemma unfolds both.
        match self {
            VecD::Inline(v) => {
                let r = v.pending_restore_indices_at(depth);
                proof {
                    if r is Some {
                        self.lemma_pending_agrees::<InlineStore<T, I>>(v, depth, r->Some_0@);
                    }
                }
                r
            }
            VecD::Parallel(v) => {
                let r = v.pending_restore_indices_at(depth);
                proof {
                    if r is Some {
                        self.lemma_pending_agrees::<ParallelStore<T, I>>(v, depth, r->Some_0@);
                    }
                }
                r
            }
            VecD::Trail(v) => {
                let r = v.pending_restore_indices_at(depth);
                proof {
                    if r is Some {
                        self.lemma_pending_agrees::<TrailStore<T, I>>(v, depth, r->Some_0@);
                    }
                }
                r
            }
        }
    }

    /// The arm's `pending_restore_indices_at` postcondition, restated on this
    /// enum: its `names_index` and `frame_captures` are the arm's, so each
    /// direction of the equivalence carries its witness across.
    proof fn lemma_pending_agrees<S: crate::diff_store::DiffStore<T, I, TRACK>>(
        &self,
        v: &Vec<T, I, S, TRACK>,
        depth: usize,
        out: Seq<I>,
    )
        requires
            self.depth_spec() == v.depth_spec(),
            forall|f: int, j: nat| #[trigger] self.frame_captures(f, j) == v.frame_captures(f, j),
            forall|j: nat| #[trigger] Vec::<T, I, S, TRACK>::names_index(out, j)
                <==> exists|f: int| depth as nat <= f < v.depth_spec()
                    && #[trigger] v.frame_captures(f, j),
        ensures
            forall|j: nat| #[trigger] Self::names_index(out, j)
                <==> exists|f: int| depth as nat <= f < self.depth_spec()
                    && #[trigger] self.frame_captures(f, j),
    {
        assert forall|j: nat| #[trigger] Self::names_index(out, j)
            <==> exists|f: int| depth as nat <= f < self.depth_spec()
                && #[trigger] self.frame_captures(f, j) by {
            assert(Self::names_index(out, j) == Vec::<T, I, S, TRACK>::names_index(out, j));
            if Vec::<T, I, S, TRACK>::names_index(out, j) {
                let f = choose|f: int| depth as nat <= f < v.depth_spec()
                    && #[trigger] v.frame_captures(f, j);
                assert(self.frame_captures(f, j));
            } else {
                if exists|f: int| depth as nat <= f < self.depth_spec()
                    && #[trigger] self.frame_captures(f, j) {
                    let f = choose|f: int| depth as nat <= f < self.depth_spec()
                        && #[trigger] self.frame_captures(f, j);
                    assert(v.frame_captures(f, j));
                    assert(false);
                }
            }
        }
    }

    pub fn tier_policy(&self) -> crate::tier_policy::TierPolicy {
        match self {
            VecD::Inline(v) => v.tier_policy(),
            VecD::Parallel(v) => v.tier_policy(),
            VecD::Trail(v) => v.tier_policy(),
        }
    }

    pub fn set_tier_policy(&mut self, policy: crate::tier_policy::TierPolicy) {
        match self {
            VecD::Inline(v) => v.set_tier_policy(policy),
            VecD::Parallel(v) => v.set_tier_policy(policy),
            VecD::Trail(v) => v.set_tier_policy(policy),
        }
    }

    pub fn tier_stats(&self) -> crate::tier_policy::TierStats {
        match self {
            VecD::Inline(v) => v.tier_stats(),
            VecD::Parallel(v) => v.tier_stats(),
            VecD::Trail(v) => v.tier_stats(),
        }
    }
}

/// The bridge between the `Member` view of this column and its own spec
/// functions. The impl's spec bodies are `closed`: as open bodies they become
/// crate-wide axioms mentioning every static column's `wf`, `view` and
/// `snapshots_view`, and that alone pushed one of `vec.rs`'s heavier lemmas
/// past Z3's resource limit. A caller that drives the column through the
/// `Member` protocol and reasons about the column's own contents (the hinted
/// arena) calls this where it needs the equalities.
impl<T, I, const TRACK: bool> VecD<T, I, TRACK>
where
    T: Tagged,
    I: IndexLike,
{
    pub(crate) proof fn lemma_member_specs(&self)
        ensures
            <Self as Member>::wf(self) == (self.wf() && TRACK),
            <Self as Member>::depth_spec(self) == self.depth_spec(),
            <Self as Member>::can_push(self)
                == (TRACK && self.depth_spec() < u32::MAX as nat
                    && self.view().len() < I::max_nat()),
            <Self as Member>::model(self) == self.view(),
            <Self as Member>::archive(self) == self.snapshots_view(),
    {
    }
}

impl<T, I, const TRACK: bool> Member for VecD<T, I, TRACK>
where
    T: Tagged,
    I: IndexLike,
{
    /// The selected column's model: the abstract value sequence.
    type Model = Seq<T>;

    closed spec fn wf(&self) -> bool {
        &&& self.wf()
        &&& TRACK
    }

    closed spec fn depth_spec(&self) -> nat {
        self.depth_spec()
    }

    closed spec fn can_push(&self) -> bool {
        &&& TRACK
        &&& self.depth_spec() < u32::MAX as nat
        &&& self.view().len() < I::max_nat()
    }

    closed spec fn model(&self) -> Seq<T> {
        self.view()
    }

    closed spec fn archive(&self) -> Seq<Seq<T>> {
        self.snapshots_view()
    }

    proof fn lemma_archive_depth(&self) {
        self.lemma_snapshots_len();
    }

    fn can_push_now(&self) -> (b: bool) {
        match self {
            VecD::Inline(v) => Member::can_push_now(v),
            VecD::Parallel(v) => Member::can_push_now(v),
            VecD::Trail(v) => Member::can_push_now(v),
        }
    }

    fn depth_exec(&self) -> (d: usize) {
        match self {
            VecD::Inline(v) => Member::depth_exec(v),
            VecD::Parallel(v) => Member::depth_exec(v),
            VecD::Trail(v) => Member::depth_exec(v),
        }
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        match self {
            VecD::Inline(v) => Member::push_frame(v, shrink),
            VecD::Parallel(v) => Member::push_frame(v, shrink),
            VecD::Trail(v) => Member::push_frame(v, shrink),
        }
    }

    fn restore_frame(&mut self, depth: usize) {
        match self {
            VecD::Inline(v) => Member::restore_frame(v, depth),
            VecD::Parallel(v) => Member::restore_frame(v, depth),
            VecD::Trail(v) => Member::restore_frame(v, depth),
        }
    }

    fn reset_frame(&mut self, depth: usize) {
        match self {
            VecD::Inline(v) => Member::reset_frame(v, depth),
            VecD::Parallel(v) => Member::reset_frame(v, depth),
            VecD::Trail(v) => Member::reset_frame(v, depth),
        }
    }

    fn pop_frame(&mut self) {
        match self {
            VecD::Inline(v) => Member::pop_frame(v),
            VecD::Parallel(v) => Member::pop_frame(v),
            VecD::Trail(v) => Member::pop_frame(v),
        }
    }
}

} // verus!

impl<T, I, const TRACK: bool> VecD<T, I, TRACK>
where
    T: Tagged,
    I: IndexLike,
{
    /// Production-shaped `get` (see `Vec::get`).
    #[inline(always)]
    pub fn get(&self, index: impl Into<I>) -> T {
        self.get_index(index.into())
    }

    /// Production-shaped `set` (see `Vec::set`).
    #[inline(always)]
    pub fn set(&mut self, index: impl Into<I>, value: T) {
        self.set_index(index.into(), value)
    }

    /// Heap bytes of the tracking structures (see `Vec::tracking_bytes`).
    pub fn tracking_bytes(&self) -> usize {
        match self {
            VecD::Inline(v) => v.tracking_bytes(),
            VecD::Parallel(v) => v.tracking_bytes(),
            VecD::Trail(v) => v.tracking_bytes(),
        }
    }

    /// Live diff-log length (see `Vec::diff_log_len`).
    pub fn diff_log_len(&self) -> usize {
        match self {
            VecD::Inline(v) => v.diff_log_len(),
            VecD::Parallel(v) => v.diff_log_len(),
            VecD::Trail(v) => v.diff_log_len(),
        }
    }

    /// Whole footprint (see `Vec::total_bytes`).
    pub fn total_bytes(&self) -> usize {
        match self {
            VecD::Inline(v) => v.total_bytes(),
            VecD::Parallel(v) => v.total_bytes(),
            VecD::Trail(v) => v.total_bytes(),
        }
    }
}
