// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Shared branch history for hard-synced vectors (`doc/design/10-shared-fork-history.md`).
//!
//! `N` vectors that always `mark`/`restore` together share one `ForkHistory` and
//! one mark depth instead of each carrying an identical copy. `History` owns the
//! genealogy and depth; it is passed `&mut` to members per call and never stored
//! inside one, so there is no shared mutable aliasing for Verus. This module is
//! the extracted genealogy type (doc 10, step 1); the history-less `Vec` and the
//! `Solo`/`SyncGroup` wrappers build on it.

// Extracted genealogy type (doc 10, step 1); wired into `Vec`/`Solo`/`SyncGroup`
// in later steps, so its methods are not yet called.
#![allow(dead_code)]

use vstd::prelude::*;

verus! {

/// A version token for a synced group: the identity of the `History` that
/// minted it (its provenance), the generation stamp minted at mark time and the
/// mark depth. One token names the whole group's version, validated once by
/// the history that minted it: a token presented to any other history is
/// foreign and refused, whatever its numbers.
#[derive(Clone, Copy, Debug)]
pub struct GroupToken {
    pub(crate) history: crate::container_id::ContainerId,
    pub(crate) generation: u64,
    pub(crate) depth: u32,
}

impl GroupToken {
    /// The mark depth this token names (public spec accessor; the raw fields stay
    /// crate-private so a token cannot be forged field-by-field outside).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.depth as nat
    }

    /// The same quantity under its container-side name: for a standalone
    /// container the depth of the mark IS the index of the frame it opened.
    pub open(crate) spec fn frame_idx_spec(self) -> nat {
        self.depth as nat
    }

    /// The minting manager's identity (spec accessor; the field is `pub(crate)`).
    pub open(crate) spec fn history_spec(self) -> nat {
        self.history.id()
    }

    /// Exec twin of `depth_spec`: the consumer restores every member to this
    /// depth after validating the token against the group's `History`.
    pub fn depth(&self) -> (d: u32)
        ensures d as nat == self.depth_spec(),
    {
        self.depth
    }
}

/// The shared depth-indexed generation stamps and mark depth for a synced group.
/// One instance backs all members, so the fork history is held `×1` instead of
/// `×N` — and, unlike the old append-only `origins` (which grew one entry per
/// restore, never reclaimed, O(R)), the stamp array is O(max depth): the leak fix
/// (doc 10). A token minted at depth `d` carries `stamps.mint_at(d)`, a fresh
/// stamp from a counter that only grows; a restore to `d` cuts the live length
/// to `d` (`GenStamps::cut_from`), one write that invalidates the consumed
/// token and the abandoned future together.
/// What a manager mints tokens from: its identity and the per-depth generation
/// stamps. The group `History` wraps one together with the group depth; a
/// standalone container embeds one and uses its own frame count as the depth,
/// so it is a group of one with the same token, the same validation (minting
/// manager, generation, liveness) and the same cut on restore.
pub struct Genealogy {
    /// The minting manager's identity: every token carries it, and validation
    /// refuses a token minted elsewhere.
    pub(crate) id: crate::container_id::ContainerId,
    pub(crate) stamps: crate::gen_stamps::GenStamps,
}

impl Genealogy {
    /// The minting manager's identity (spec accessor; the field is `pub(crate)`).
    pub open(crate) spec fn id_spec(&self) -> nat {
        self.id.id()
    }

    /// Number of stamp levels held (spec accessor).
    /// Live stamp depths (`GenStamps::live_len`): the depths a token can be
    /// valid at.
    pub open(crate) spec fn levels_len(&self) -> nat {
        self.stamps.live_len()
    }

    /// The next stamp this manager will hand out; every stamp it ever handed
    /// out is below it.
    pub open(crate) spec fn next_spec(&self) -> u64 {
        self.stamps.next_spec()
    }

    /// `t` was minted here and its generation is still the live stamp at its
    /// depth (O(1)).
    pub open(crate) spec fn valid_spec(self, t: GroupToken) -> bool {
        &&& t.history.id() == self.id.id()
        &&& self.stamps.valid(t.depth as nat, t.generation)
    }

    pub fn new() -> (r: Genealogy)
        ensures r.levels_len() == 0,
    {
        Genealogy {
            id: crate::container_id::ContainerId::new(),
            stamps: crate::gen_stamps::GenStamps::new(),
        }
    }

    /// Mint the token naming the frame at `depth` (growing the stamp array the
    /// first time a depth is reached). The token is immediately valid, and
    /// every token that was valid stays valid (existing stamps are untouched).
    pub(crate) fn mint(&mut self, depth: usize) -> (t: GroupToken)
        requires depth < u32::MAX,
        ensures
            t.depth_spec() == depth as nat,
            t.history_spec() == old(self).id_spec(),
            final(self).id_spec() == old(self).id_spec(),
            final(self).valid_spec(t),
            forall|u: GroupToken| old(self).valid_spec(u) ==> final(self).valid_spec(u),
            final(self).levels_len() == depth as nat + 1,
            // Freshness: the minted stamp is new, so every token this manager
            // handed out before (its stamp is below the old counter) keeps its
            // validity status — a consumed token stays consumed.
            t.generation >= old(self).next_spec(),
            final(self).next_spec() > t.generation,
            forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] u.generation < old(self).next_spec()
                ==> final(self).valid_spec(u) == old(self).valid_spec(u),
    {
        let g = self.stamps.mint_at(depth);
        GroupToken { history: self.id, generation: g, depth: depth as u32 }
    }

    pub fn is_valid(&self, t: &GroupToken) -> (b: bool)
        ensures b == self.valid_spec(*t),
    {
        self.id.eq(t.history) && self.stamps.is_valid(t.depth as usize, t.generation)
    }

    /// The cut of a restore: every token at `depth` or deeper that is valid now
    /// is dead for good (its stamp changes; stamps never return), tokens above
    /// the cut are untouched.
    /// The cut: every token at or above `depth` is dead for good (the live
    /// length drops to `depth`), tokens below keep their status, the counter
    /// is untouched. One write, whatever the deepest depth ever reached.
    pub fn cut_from(&mut self, depth: usize)
        ensures
            final(self).id_spec() == old(self).id_spec(),
            final(self).next_spec() == old(self).next_spec(),
            final(self).levels_len() == if depth < old(self).levels_len() { depth as nat } else { old(self).levels_len() },
            forall|u: GroupToken| #![trigger final(self).valid_spec(u)] u.depth_spec() >= depth as nat ==> !final(self).valid_spec(u),
            forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] u.depth_spec() < depth as nat
                ==> final(self).valid_spec(u) == old(self).valid_spec(u),
    {
        self.stamps.cut_from(depth);
    }
}

/// The group manager: a `Genealogy` plus the group depth.
pub struct History {
    pub(crate) genealogy: Genealogy,
    pub(crate) depth: u32,
}

impl History {
    /// Every live depth has a stamp level (so a live token's depth is in range).
    pub open(crate) spec fn wf(self) -> bool {
        self.genealogy.levels_len() >= self.depth as nat
    }

    pub open(crate) spec fn depth_spec(self) -> nat {
        self.depth as nat
    }

    /// Validity of `t`: its generation still matches the live stamp at its depth
    /// (O(1)). The shared analogue of `Vec::is_token_valid_spec`, minus the
    /// container check (one history, one group).
    pub open(crate) spec fn valid_spec(self, t: GroupToken) -> bool {
        self.genealogy.valid_spec(t)
    }

    pub fn new() -> (r: History)
        ensures
            r.wf(),
            r.depth_spec() == 0,
    {
        History { genealogy: Genealogy::new(), depth: 0 }
    }

    pub fn depth(&self) -> (d: u32)
        ensures d as nat == self.depth_spec(),
    {
        self.depth
    }

    /// Open a new mark: mint the generation for the current depth (growing the
    /// stamp array the first time a depth is reached), then depth advances by one.
    /// The token is immediately valid.
    pub fn mark(&mut self) -> (t: GroupToken)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            t.depth_spec() == old(self).depth_spec(),
            final(self).valid_spec(t),
    {
        // Total: the depth ceiling is the group's documented trap, not a
        // caller obligation (the marks the engine takes are bounded by its
        // own frame budget long before).
        if !(self.depth < u32::MAX) {
            crate::guard::refuse("History::mark: frame depth at u32 ceiling");
        }
        let d = self.depth;
        let t = self.genealogy.mint(d as usize);
        self.depth = d + 1;
        t
    }

    /// Is `t` valid — does its generation still match the live stamp at its depth?
    /// Computed once for the whole group (versus `N` identical walks today), O(1).
    pub fn is_valid(&self, t: GroupToken) -> (r: bool)
        requires self.wf(),
        ensures r == self.valid_spec(t),
    {
        self.genealogy.is_valid(&t)
    }

    /// Restore to `t` (semantics B, design doc 08 §1): the group goes back to
    /// the checkpoint `t` names and stays in that scope — the cut starts at
    /// `t.depth + 1`, so `t` stays valid and every token minted after it dies
    /// for good; the depth becomes `t.depth + 1` (frame `t.depth` is open
    /// again). One write, no per-restore growth, no overflow precondition:
    /// the stamp counter only grows and refuses at its ceiling.
    pub fn restore_to(&mut self, t: GroupToken)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == t.depth_spec() + 1,
            final(self).valid_spec(t),
            forall|u: GroupToken| #![trigger final(self).valid_spec(u)] u.depth_spec() > t.depth_spec() ==> !final(self).valid_spec(u),
            forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] u.depth_spec() <= t.depth_spec()
                ==> final(self).valid_spec(u) == old(self).valid_spec(u),
    {
        // Total: a stale or reused token, or one at or above the live depth,
        // is the documented trap (production's expect messages).
        if !self.is_valid(t) {
            crate::guard::refuse("History::restore_to: token is stale (its frame was cut)");
        }
        if !(t.depth < self.depth) {
            crate::guard::refuse("History::restore_to: token depth is not below the live depth");
        }
        let d1 = t.depth + 1;
        self.genealogy.cut_from(d1 as usize);
        self.depth = d1;
    }

    /// Drop the open top scope (the SMT-LIB `pop`): the depth decreases by
    /// one and the popped frame's token dies (the cut starts at its depth).
    /// Refuses on an empty stack.
    pub fn pop(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).depth_spec() >= 1 ==> final(self).depth_spec() == old(self).depth_spec() - 1,
            forall|u: GroupToken| #![trigger final(self).valid_spec(u)] old(self).depth_spec() >= 1 && u.depth_spec() >= old(self).depth_spec() - 1
                ==> !final(self).valid_spec(u),
            forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] old(self).depth_spec() >= 1 && u.depth_spec() < old(self).depth_spec() - 1
                ==> final(self).valid_spec(u) == old(self).valid_spec(u),
    {
        if !(self.depth >= 1) {
            crate::guard::refuse("History::pop: no open scope");
        }
        let d = self.depth - 1;
        self.genealogy.cut_from(d as usize);
        self.depth = d;
    }

    /// `restore(t)` then `pop_scope()`, fused (design doc 08 §1): the contents
    /// are the snapshot taken at `t`, the depth is `t.depth`, and `t` and every
    /// token minted after it die. This is the SMT-LIB `pop` to the level below
    /// `t` and exactly the legacy restore, on one pop core: the parent stratum
    /// is reopened once, so it costs what the legacy restore costs. `restore`
    /// alone keeps the checkpoint's frame open instead.
    pub fn restore_and_pop(&mut self, t: GroupToken)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == t.depth_spec(),
            !final(self).valid_spec(t),
            forall|u: GroupToken| #![trigger final(self).valid_spec(u)] u.depth_spec() >= t.depth_spec() ==> !final(self).valid_spec(u),
            forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] u.depth_spec() < t.depth_spec()
                ==> final(self).valid_spec(u) == old(self).valid_spec(u),
    {
        if !self.is_valid(t) {
            crate::guard::refuse("History::restore_and_pop: token is stale (its frame was cut)");
        }
        if !(t.depth < self.depth) {
            crate::guard::refuse("History::restore_and_pop: token depth is not below the live depth");
        }
        // The cut starts AT the target depth: frame `t.depth` itself goes, so
        // `t` dies with it (a later mark at that depth mints a fresh stamp).
        self.genealogy.cut_from(t.depth as usize);
        self.depth = t.depth;
    }
}

} // verus!

// Byte reporter — OUTSIDE the verified perimeter (stratified; see
// `diagnostics.rs`).
impl History {
    /// Heap bytes of the generation-stamp array (read-only).
    pub fn heap_bytes(&self) -> usize {
        crate::diagnostics::HeapBytes::heap_bytes(&self.genealogy.stamps)
    }
}

// Value equality on the whole token (minting manager, generation, depth):
// what tests compare. Outside `verus!` (trait impl on a verified struct; the
// verifier does not need it).
impl PartialEq for GroupToken {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.history == other.history
            && self.generation == other.generation
            && self.depth == other.depth
    }
}
impl Eq for GroupToken {}
