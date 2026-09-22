// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Generation stamps: the token authority's memory, one stamp per live depth.
//!
//! A `GenStamps` hands out stamps from a counter that only grows, so every
//! stamp is handed out exactly once. Depth `d` is live iff `d < len`; a token
//! `(d, g)` is valid iff `d` is live and `levels[d] == g`. A cut at depth `d`
//! is `len := min(len, d)`: one write, no rewriting of the stamps above the
//! cut (they are stale because they are beyond the live length). A mint at
//! the live length stores the next counter value: one write. Both are O(1),
//! whatever the deepest depth ever reached; capacity is kept across cuts so a
//! restore never reallocates, and live memory stays O(deepest depth).
//!
//! Why a consumed token never revives: a token's stamp was `next` when it was
//! minted and `next` only grows, so the stamp is below the counter for ever;
//! re-minting the token's depth stores a value at or above the counter, never
//! the token's own. `mint_at`'s last postcondition states exactly that: every
//! stamp below the old counter keeps its validity status across a mint.
//!
//! Predecessor (2026-09-17, replaced the same day after the provenance
//! benchmarks): one stamp per depth for the deepest depth ever reached, and a
//! cut at `d` bumped every level from `d` up — O(deepest depth) per restore,
//! which cost 1.1–1.7× on every mark/restore-dominated benchmark.
use vstd::prelude::*;

verus! {

pub struct GenStamps {
    /// Stamp storage. Only the first `len` entries are live; the rest are
    /// stale stamps of cut depths, kept so a re-climb reuses the capacity.
    pub(crate) levels: Vec<u64>,
    /// Live length: depth `d` has a stamp iff `d < len`.
    pub(crate) len: usize,
    /// The next stamp to hand out. Starts at 1; every stamp handed out so far
    /// is below it.
    pub(crate) next: u64,
}

impl GenStamps {
    /// Is `(depth, g)` a live stamp? Bounds are part of the definition, so the
    /// exec check needs no invariant.
    pub open(crate) spec fn valid(&self, depth: nat, g: u64) -> bool {
        &&& depth < self.len
        &&& depth < self.levels@.len()
        &&& self.levels@[depth as int] == g
    }

    pub open(crate) spec fn live_len(&self) -> nat {
        self.len as nat
    }

    pub open(crate) spec fn next_spec(&self) -> u64 {
        self.next
    }

    /// The stamp storage, live and stale entries alike.
    pub open(crate) spec fn levels_view(&self) -> Seq<u64> {
        self.levels@
    }

    pub fn new() -> (r: GenStamps)
        ensures r.live_len() == 0, r.next_spec() == 1,
    {
        GenStamps { levels: Vec::new(), len: 0, next: 1 }
    }

    pub fn live_depths(&self) -> (n: usize)
        ensures n == self.live_len(),
    {
        self.len
    }

    pub fn is_valid(&self, depth: usize, g: u64) -> (b: bool)
        ensures b == self.valid(depth as nat, g),
    {
        if depth < self.len && depth < self.levels.len() {
            self.levels[depth] == g
        } else {
            false
        }
    }

    /// Hand out a fresh stamp at the live length (which becomes live). Total:
    /// refuses at the counter ceiling and at the length ceiling, and refuses
    /// a live length beyond the storage (unreachable through this API).
    fn push_fresh(&mut self) -> (g: u64)
        ensures
            final(self).live_len() == old(self).live_len() + 1,
            g == old(self).next_spec(),
            final(self).next_spec() == old(self).next_spec() + 1,
            final(self).valid(old(self).live_len(), g),
            forall|d: nat, x: u64| old(self).valid(d, x) ==> final(self).valid(d, x),
            forall|d: nat, x: u64| x < old(self).next_spec()
                ==> final(self).valid(d, x) == old(self).valid(d, x),
    {
        if !(self.next < u64::MAX) {
            crate::guard::refuse("GenStamps: stamp counter exhausted");
        }
        if !(self.len < usize::MAX) {
            crate::guard::refuse("GenStamps: live length at the usize ceiling");
        }
        let g = self.next;
        if self.len < self.levels.len() {
            self.levels.set(self.len, g);
        } else if self.len == self.levels.len() {
            self.levels.push(g);
        } else {
            crate::guard::refuse("GenStamps: live length beyond the stamp storage");
        }
        self.len = self.len + 1;
        self.next = self.next + 1;
        g
    }

    /// Mint the stamp for depth `depth`, which becomes the last live depth
    /// (`live_len() == depth + 1`). Depths between the live length and `depth`
    /// get fresh stamps of their own (a member driven structurally by a group
    /// has frames its own genealogy never minted). Total: refuses a depth
    /// below the live length — frames were cut without cutting the genealogy,
    /// which this API never does.
    pub fn mint_at(&mut self, depth: usize) -> (g: u64)
        ensures
            final(self).live_len() == depth as nat + 1,
            final(self).valid(depth as nat, g),
            g >= old(self).next_spec(),
            final(self).next_spec() > g,
            forall|d: nat, x: u64| old(self).valid(d, x) ==> final(self).valid(d, x),
            forall|d: nat, x: u64| x < old(self).next_spec()
                ==> final(self).valid(d, x) == old(self).valid(d, x),
    {
        if !(self.len <= depth) {
            crate::guard::refuse("GenStamps::mint_at: depth below the live length");
        }
        if !(depth < usize::MAX) {
            crate::guard::refuse("GenStamps::mint_at: depth at the usize ceiling");
        }
        while self.len < depth
            invariant
                self.len <= depth,
                depth < usize::MAX,
                self.next_spec() >= old(self).next_spec(),
                forall|d: nat, x: u64| old(self).valid(d, x) ==> self.valid(d, x),
                forall|d: nat, x: u64| x < old(self).next_spec()
                    ==> self.valid(d, x) == old(self).valid(d, x),
            decreases depth - self.len,
        {
            let _ = self.push_fresh();
        }
        self.push_fresh()
    }

    /// Cut at `depth`: every stamp at or above `depth` dies, nothing below
    /// changes, the counter is untouched. One write.
    pub fn cut_from(&mut self, depth: usize)
        ensures
            final(self).levels_view() == old(self).levels_view(),
            final(self).next_spec() == old(self).next_spec(),
            final(self).live_len() == if depth < old(self).live_len() { depth as nat } else { old(self).live_len() },
            forall|d: nat, x: u64| d >= depth ==> !final(self).valid(d, x),
            forall|d: nat, x: u64| d < depth ==> final(self).valid(d, x) == old(self).valid(d, x),
    {
        if depth < self.len {
            self.len = depth;
        }
    }
}

} // verus!

// Byte reporter — OUTSIDE the verified perimeter (stratified; see
// `diagnostics.rs`).
impl crate::diagnostics::HeapBytes for GenStamps {
    fn heap_bytes(&self) -> usize {
        self.levels.capacity() * core::mem::size_of::<u64>()
    }
}
