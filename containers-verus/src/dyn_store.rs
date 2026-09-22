// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `DynStore<T, I>`: the runtime-selectable DiffStore. One enum over the
//! three base stores, chosen at construction (`StoreKind`) and immutable for
//! the store's lifetime — every method delegates to its variant, so the
//! discipline answers (`unique_capture_spec`, `needs_replayed_indices_spec`)
//! are functions of the variant and the trait's constancy contract holds
//! structurally: no method changes the discriminant.
//!
//! This is what lets a whole binary flip between the frame-diff disciplines
//! (Inline/Parallel: first-write-wins, bounded log, composes with sealing
//! and compression — the deep-state EqSat trade) and the trail discipline
//! (chronological capture, branch-free writes, no frame finalization — the
//! SMT trade) from a command-line flag, per column, without a type change.
//! The cost over the static aliases (`VecI`/`VecP`/`VecT`) is one
//! well-predicted discriminant branch per store operation.

use vstd::prelude::*;

use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::parallel_store::ParallelStore;
use crate::tagged::Tagged;
use crate::trail_store::TrailStore;

verus! {

/// Runtime store selection for `DynStore`/`VecD` constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StoreKind {
    Inline,
    Parallel,
    Trail,
}

pub enum DynStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    Inline(InlineStore<T, I>),
    Parallel(ParallelStore<T, I>),
    Trail(TrailStore<T, I>),
}

impl<T, I> DynStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    /// Empty store of the selected kind.
    pub fn new_kind<const TRACK: bool>(kind: StoreKind) -> (r: Self)
        ensures
            <Self as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&r),
            <Self as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&r).len() == 0,
            <Self as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::unique_capture_spec(&r)
                == (kind != StoreKind::Trail),
    {
        match kind {
            StoreKind::Inline => DynStore::Inline(InlineStore::new()),
            StoreKind::Parallel => DynStore::Parallel(ParallelStore::new()),
            StoreKind::Trail => DynStore::Trail(TrailStore::new()),
        }
    }
}

impl<T, I, const TRACK: bool> crate::diff_store_ops::DiffStoreOps<T, I, TRACK> for DynStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    open spec fn data(&self) -> Seq<T> {
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(s),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(s),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(s),
        }
    }

    open spec fn captured(&self) -> Seq<bool> {
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(s),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(s),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(s),
        }
    }

    open spec fn wf(&self) -> bool {
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(s),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(s),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(s),
        }
    }

    open spec fn unique_capture_spec(&self) -> bool {
        !(self is Trail)
    }

    open spec fn needs_replayed_indices_spec(&self) -> bool {
        self is Inline
    }

    open spec fn restore_entries_clear_capture_spec(&self) -> bool {
        self is Inline
    }

    #[inline(always)]
    fn get(&self, i: I) -> T {
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::get(s, i),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::get(s, i),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::get(s, i),
        }
    }

    #[inline(always)]
    fn push(&mut self, value: T) {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::push(s, value),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::push(s, value),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::push(s, value),
        }
    }

    #[inline(always)]
    fn set_raw(&mut self, i: I, value: T) {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::set_raw(s, i, value),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::set_raw(s, i, value),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::set_raw(s, i, value),
        }
    }

    fn truncate(&mut self, len: I) {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::truncate(s, len),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::truncate(s, len),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::truncate(s, len),
        }
    }

    #[inline(always)]
    fn mark_captured(&mut self, i: I) {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::mark_captured(s, i),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::mark_captured(s, i),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::mark_captured(s, i),
        }
    }

    fn resize_default(&mut self, len: I)
        where T: core::default::Default
    {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::resize_default(s, len),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::resize_default(s, len),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::resize_default(s, len),
        }
    }

    fn prepare_mark(&mut self, saved_len: I, prev_diffs: &[(T, I)]) {
        broadcast use crate::diff_store::lemma_dyn_views;
        let ghost pre = *self;
        match self {
            DynStore::Inline(s) => {
                proof {
                    assert(pre == DynStore::Inline(*s));
                    assert(pre == *old(self));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&pre)
                        == <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&pre)
                        == <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&pre)
                        == <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&*s));
                }
                <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::prepare_mark(s, saved_len, prev_diffs)
            }
            DynStore::Parallel(s) => {
                proof {
                    assert(pre == DynStore::Parallel(*s));
                    assert(pre == *old(self));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&pre)
                        == <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&pre)
                        == <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&pre)
                        == <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&*s));
                }
                <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::prepare_mark(s, saved_len, prev_diffs)
            }
            DynStore::Trail(s) => {
                proof {
                    assert(pre == DynStore::Trail(*s));
                    assert(pre == *old(self));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&pre)
                        == <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&pre)
                        == <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&pre)
                        == <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&*s));
                }
                <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::prepare_mark(s, saved_len, prev_diffs)
            }
        }
    }

    #[inline(always)]
    fn capture(
        &mut self,
        i: I,
        saved_len: I,
        diff_log: &mut Vec<(T, I)>,
    ) {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::capture(s, i, saved_len, diff_log),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::capture(s, i, saved_len, diff_log),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::capture(s, i, saved_len, diff_log),
        }
    }

    fn force_capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::force_capture(s, i, saved_len, diff_log),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::force_capture(s, i, saved_len, diff_log),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::force_capture(s, i, saved_len, diff_log),
        }
    }

    fn begin_restore(&mut self, replayed_diffs: &[(T, I)]) {
        broadcast use crate::diff_store::lemma_dyn_views;
        let ghost pre = *self;
        match self {
            DynStore::Inline(s) => {
                proof {
                    assert(pre == DynStore::Inline(*s));
                    assert(pre == *old(self));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&pre)
                        == <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&pre)
                        == <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&pre)
                        == <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&*s));
                }
                <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::begin_restore(s, replayed_diffs)
            }
            DynStore::Parallel(s) => {
                proof {
                    assert(pre == DynStore::Parallel(*s));
                    assert(pre == *old(self));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&pre)
                        == <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&pre)
                        == <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&pre)
                        == <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&*s));
                }
                <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::begin_restore(s, replayed_diffs)
            }
            DynStore::Trail(s) => {
                proof {
                    assert(pre == DynStore::Trail(*s));
                    assert(pre == *old(self));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&pre)
                        == <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&pre)
                        == <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&pre)
                        == <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&*s));
                }
                <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::begin_restore(s, replayed_diffs)
            }
        }
    }

    fn restore_overlay(
        &mut self,
        diff_log: &Vec<(T, I)>,
        lo: usize,
        hi: usize,
    ) {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::restore_overlay(s, diff_log, lo, hi),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::restore_overlay(s, diff_log, lo, hi),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::restore_overlay(s, diff_log, lo, hi),
        }
    }

    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I) {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::restore_entry(s, index, old_value, target_saved_len),
            DynStore::Parallel(s) => <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::restore_entry(s, index, old_value, target_saved_len),
            DynStore::Trail(s) => <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::restore_entry(s, index, old_value, target_saved_len),
        }
    }

    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], saved_len: I) {
        broadcast use crate::diff_store::lemma_dyn_views;
        let ghost pre = *self;
        match self {
            DynStore::Inline(s) => {
                proof {
                    assert(pre == DynStore::Inline(*s));
                    assert(pre == *old(self));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&pre)
                        == <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&pre)
                        == <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&pre)
                        == <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&*s));
                }
                <InlineStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::finish_restore(s, current_frame_diffs, saved_len)
            }
            DynStore::Parallel(s) => {
                proof {
                    assert(pre == DynStore::Parallel(*s));
                    assert(pre == *old(self));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&pre)
                        == <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&pre)
                        == <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&pre)
                        == <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&*s));
                }
                <ParallelStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::finish_restore(s, current_frame_diffs, saved_len)
            }
            DynStore::Trail(s) => {
                proof {
                    assert(pre == DynStore::Trail(*s));
                    assert(pre == *old(self));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&pre)
                        == <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::captured(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&pre)
                        == <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::data(&*s));
                    assert(<DynStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&pre)
                        == <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::wf(&*s));
                }
                <TrailStore<T, I> as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::finish_restore(s, current_frame_diffs, saved_len)
            }
        }
    }
}

impl<T, I, const TRACK: bool> DiffStore<T, I, TRACK> for DynStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{

    proof fn lemma_wf_captured_len(&self) {
        match self {
            DynStore::Inline(s) =>
                <InlineStore<T, I> as DiffStore<T, I, TRACK>>::lemma_wf_captured_len(s),
            DynStore::Parallel(s) =>
                <ParallelStore<T, I> as DiffStore<T, I, TRACK>>::lemma_wf_captured_len(s),
            DynStore::Trail(s) =>
                <TrailStore<T, I> as DiffStore<T, I, TRACK>>::lemma_wf_captured_len(s),
        }
    }

    proof fn lemma_wf_data_len(&self) {
        match self {
            DynStore::Inline(s) =>
                <InlineStore<T, I> as DiffStore<T, I, TRACK>>::lemma_wf_data_len(s),
            DynStore::Parallel(s) =>
                <ParallelStore<T, I> as DiffStore<T, I, TRACK>>::lemma_wf_data_len(s),
            DynStore::Trail(s) =>
                <TrailStore<T, I> as DiffStore<T, I, TRACK>>::lemma_wf_data_len(s),
        }
    }

    fn unique_capture(&self) -> bool {
        !matches!(self, DynStore::Trail(_))
    }

    fn needs_replayed_indices(&self) -> bool {
        matches!(self, DynStore::Inline(_))
    }

    #[inline(always)]
    fn restore_entries_clear_capture(&self) -> bool {
        match self {
            DynStore::Inline(s) => {
                <InlineStore<T, I> as DiffStore<T, I, TRACK>>::restore_entries_clear_capture(s)
            }
            DynStore::Parallel(s) => {
                <ParallelStore<T, I> as DiffStore<T, I, TRACK>>::restore_entries_clear_capture(s)
            }
            DynStore::Trail(s) => {
                <TrailStore<T, I> as DiffStore<T, I, TRACK>>::restore_entries_clear_capture(s)
            }
        }
    }

    #[inline(always)]
    fn is_empty(&self) -> bool {
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as DiffStore<T, I, TRACK>>::is_empty(s),
            DynStore::Parallel(s) => <ParallelStore<T, I> as DiffStore<T, I, TRACK>>::is_empty(s),
            DynStore::Trail(s) => <TrailStore<T, I> as DiffStore<T, I, TRACK>>::is_empty(s),
        }
    }

    #[inline(always)]
    fn raw_len(&self) -> (n: usize) {
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as DiffStore<T, I, TRACK>>::raw_len(s),
            DynStore::Parallel(s) => <ParallelStore<T, I> as DiffStore<T, I, TRACK>>::raw_len(s),
            DynStore::Trail(s) => <TrailStore<T, I> as DiffStore<T, I, TRACK>>::raw_len(s),
        }
    }

    #[inline(always)]
    fn len(&self) -> I {
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as DiffStore<T, I, TRACK>>::len(s),
            DynStore::Parallel(s) => <ParallelStore<T, I> as DiffStore<T, I, TRACK>>::len(s),
            DynStore::Trail(s) => <TrailStore<T, I> as DiffStore<T, I, TRACK>>::len(s),
        }
    }

    #[inline(always)]
    fn pop(&mut self) -> Option<T> {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as DiffStore<T, I, TRACK>>::pop(s),
            DynStore::Parallel(s) => <ParallelStore<T, I> as DiffStore<T, I, TRACK>>::pop(s),
            DynStore::Trail(s) => <TrailStore<T, I> as DiffStore<T, I, TRACK>>::pop(s),
        }
    }

    fn restore_run(&mut self, base: I, values: &[T]) {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as DiffStore<T, I, TRACK>>::restore_run(s, base, values),
            DynStore::Parallel(s) => <ParallelStore<T, I> as DiffStore<T, I, TRACK>>::restore_run(s, base, values),
            DynStore::Trail(s) => <TrailStore<T, I> as DiffStore<T, I, TRACK>>::restore_run(s, base, values),
        }
    }

    fn shrink_if(&mut self, factor: usize, headroom: usize) {
        broadcast use crate::diff_store::lemma_dyn_views;
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as DiffStore<T, I, TRACK>>::shrink_if(s, factor, headroom),
            DynStore::Parallel(s) => <ParallelStore<T, I> as DiffStore<T, I, TRACK>>::shrink_if(s, factor, headroom),
            DynStore::Trail(s) => <TrailStore<T, I> as DiffStore<T, I, TRACK>>::shrink_if(s, factor, headroom),
        }
    }

    fn as_slice(&self) -> (r: Option<&[T]>) {
        match self {
            DynStore::Inline(s) => <InlineStore<T, I> as DiffStore<T, I, TRACK>>::as_slice(s),
            DynStore::Parallel(s) => <ParallelStore<T, I> as DiffStore<T, I, TRACK>>::as_slice(s),
            DynStore::Trail(s) => <TrailStore<T, I> as DiffStore<T, I, TRACK>>::as_slice(s),
        }
    }
}

} // verus!

// Byte reporter — OUTSIDE the verified perimeter (stratified; see
// `diagnostics.rs`).
impl<T, I> crate::diagnostics::HeapBytes for DynStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    fn heap_bytes(&self) -> usize {
        match self {
            DynStore::Inline(s) => crate::diagnostics::HeapBytes::heap_bytes(s),
            DynStore::Parallel(s) => crate::diagnostics::HeapBytes::heap_bytes(s),
            DynStore::Trail(s) => crate::diagnostics::HeapBytes::heap_bytes(s),
        }
    }
}
