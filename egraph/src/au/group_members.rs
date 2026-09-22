// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The search session's layers as one typed-group member: a borrowed
//! forwarding struct over the five layers the session owns, driven by the
//! session's `History` through `History::{mark_member, restore_member,
//! restore_and_pop_member, pop_member}` (design doc 10, "one external
//! manager").
//!
//! One stamp per checkpoint for the whole search state. Before this, one
//! `SearchSession::mark` minted 62 container tokens — one per column across
//! the space layer, the term pool, the result table, the action cache and the
//! MCGS statistics — and bundled them in a nest of eleven token structs, and
//! `restore` answered validity 62 times. The group answers it once.
//!
//! The two-phase discipline the token version hand-rolled (validate every
//! component, then mutate) is now the group's own contract: `restore_member`
//! checks the token and the members' lockstep before it moves anything, and
//! refuses without mutating, so a foreign or abandoned token still cannot
//! cause a partial restore.
//!
//! The `Member` impl is glue in an unverified crate: its spec parts are
//! trivial, its exec parts forward to the layers' structural frame
//! operations, marking in dependency order and moving back in reverse.

use crate::config::AuIds;
use crate::containers::DenseId;
use crate::containers::ShrinkPolicy;
use crate::containers::group::Member;
use crate::multiplicity::MultiplicityLike;
use vstd::prelude::*;

use super::actions::ActionCache;
use super::mcgs::McgsState;
use super::results::BestResults;
use super::space::SearchSpace;
use super::terms::TermPool;

pub(crate) struct AuMembers<'a, O, V, A, M>
where
    O: DenseId + core::hash::Hash,
    V: DenseId + core::hash::Hash,
    A: AuIds,
    M: MultiplicityLike,
{
    pub space: &'a mut SearchSpace<A>,
    pub pool: &'a mut TermPool<O, V, A>,
    pub results: &'a mut BestResults<A>,
    pub actions: &'a mut ActionCache<O, A, M>,
    pub mcgs: &'a mut McgsState<A, O>,
}

impl<'a, O, V, A, M> AuMembers<'a, O, V, A, M>
where
    O: DenseId + core::hash::Hash,
    V: DenseId + core::hash::Hash,
    A: AuIds,
    M: MultiplicityLike,
{
    fn depth_all(&self) -> usize {
        self.space.frame_depth()
    }

    fn can_push_all(&self) -> bool {
        self.space.frame_depth() < u32::MAX as usize
            && self.pool.frame_depth() < u32::MAX as usize
            && self.results.frame_depth() < u32::MAX as usize
            && self.actions.frame_depth() < u32::MAX as usize
            && self.mcgs.frame_depth() < u32::MAX as usize
    }

    /// Dependency order: structure, then the terms and results that name it,
    /// then the caches and the statistics overlay.
    fn push_all(&mut self, shrink: ShrinkPolicy) {
        self.space.push_frame(shrink);
        self.pool.push_frame(shrink);
        self.results.push_frame(shrink);
        self.actions.push_frame(shrink);
        self.mcgs.push_frame(shrink);
    }

    /// Reverse dependency order: the statistics overlay first, then results and
    /// terms, then the structure they point into.
    fn reset_all(&mut self, depth: usize) {
        self.mcgs.reset_frame(depth);
        self.actions.reset_frame(depth);
        self.results.reset_frame(depth);
        self.pool.reset_frame(depth);
        self.space.reset_frame(depth);
    }

    fn restore_all(&mut self, depth: usize) {
        self.mcgs.restore_frame(depth);
        self.actions.restore_frame(depth);
        self.results.restore_frame(depth);
        self.pool.restore_frame(depth);
        self.space.restore_frame(depth);
    }

    fn pop_all(&mut self) {
        self.mcgs.pop_frame();
        self.actions.pop_frame();
        self.results.pop_frame();
        self.pool.pop_frame();
        self.space.pop_frame();
    }
}

verus! {

// Glue: the spec side is trivial (this crate is not verified); the exec side
// forwards to the fan-out above.
impl<'a, O, V, A, M> Member for AuMembers<'a, O, V, A, M>
where
    O: DenseId + core::hash::Hash,
    V: DenseId + core::hash::Hash,
    A: AuIds,
    M: MultiplicityLike,
{
    type Model = ();

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn depth_spec(&self) -> nat {
        0
    }

    open spec fn can_push(&self) -> bool {
        true
    }

    open spec fn model(&self) -> () {
        ()
    }

    open spec fn archive(&self) -> Seq<()> {
        Seq::empty()
    }

    proof fn lemma_archive_depth(&self) {
    }

    fn can_push_now(&self) -> (b: bool) {
        self.can_push_all()
    }

    fn depth_exec(&self) -> (d: usize) {
        self.depth_all()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        self.push_all(shrink);
    }

    fn restore_frame(&mut self, depth: usize) {
        self.restore_all(depth);
    }

    fn reset_frame(&mut self, depth: usize) {
        self.reset_all(depth);
    }

    fn pop_frame(&mut self) {
        self.pop_all();
    }
}

} // verus!
