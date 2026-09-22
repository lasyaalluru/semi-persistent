// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Frame<I>`: a single mark frame on the frame stack.
//!
//! `saved_len: I` matches the vector's index type, so vectors with
//! `I = u64` can grow past `u32::MAX` slots without truncation. The
//! production crate had this field as `u32`, which silently wrapped at
//! 4B slots — fixed in this release alongside the verus port.
//!
//! `diff_start: usize` indexes into the diff log (a `std::Vec`, sized by
//! `usize`), so the natural fit there is `usize`, independent of `I`.
//!
//! The frame-replay invariant says:
//!
//! ```text
//! forall k: snapshots[k] == replay_reverse(view, diff_log[frames[k].diff_start..])
//!                            .subrange(0, frames[k].saved_len.as_nat())
//! ```
//!
//! That invariant is `Vec`'s job to maintain; this file just defines the
//! shape.

use vstd::prelude::*;

use crate::index_like::IndexLike;

verus! {

#[derive(Copy)]
pub struct Frame<I: IndexLike> {
    pub(crate) saved_len: I,
    pub(crate) diff_start: usize,
}

// Hand-written `Clone` (a plain copy) so Verus has a spec for it; the autoderived
// `Clone` on a generic struct emits a "clone is not a copy" warning otherwise.
impl<I: IndexLike> Clone for Frame<I> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

} // verus!

// Production-surface parity (production derives Debug).
impl<I: crate::index_like::IndexLike + core::fmt::Debug> core::fmt::Debug for Frame<I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Frame")
            .field("saved_len", &self.saved_len)
            .field("diff_start", &self.diff_start)
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Ruled layout (doc/tasks/mainline-shape-plus-coldstack-goal.md, 2026-09-13):
// two frame stacks, pooled cold runs.

verus! {

/// A chronological trail frame: extent `[start, end)` in the container's
/// `trail_value_pool`, plus the live vector's length at its mark.
#[derive(Copy)]
pub struct TrailFrame<I: IndexLike> {
    pub(crate) saved_len: I,
    pub(crate) start: usize,
    pub(crate) end: usize,
}

impl<I: IndexLike> Clone for TrailFrame<I> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// A hot frame: extent [start, end) in the container's hot_value_pool, plus
/// the live vector's saved_len at its mark.
#[derive(Copy)]
pub struct HotFrame<I: IndexLike> {
    pub(crate) saved_len: I,
    pub(crate) start: usize,
    pub(crate) end: usize,
}

impl<I: IndexLike> Clone for HotFrame<I> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// One value run of a cold frame: values cold_value_pool[start .. start+len]
/// land at live[base ..].
#[derive(Copy)]
pub struct IndexRun<I: IndexLike> {
    pub(crate) base: I,
    pub(crate) start: usize,
    pub(crate) len: usize,
}

impl<I: IndexLike> Clone for IndexRun<I> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// A cold frame: extent [runs_start, runs_start+runs_len) in
/// cold_index_runs, plus the live vector's saved_len at its mark.
#[derive(Copy)]
pub struct ColdFrameHdr<I: IndexLike> {
    pub(crate) saved_len: I,
    pub(crate) runs_start: usize,
    pub(crate) runs_len: usize,
}

impl<I: IndexLike> Clone for ColdFrameHdr<I> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

} // verus!
