// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `HintedArena<T, I>`: a semi-persistent column paired with a verified
//! content-fingerprint index, proving the collision theorems a hash-consing
//! e-graph needs across backtracking:
//!
//! - SOUNDNESS: `probe(t) == Some(id)` implies the live cell `id` holds
//!   content equal to `t`.
//! - COMPLETENESS (the cannot-miss theorem): `probe(t) == None` implies NO
//!   live cell holds content equal to `t` - a congruence collision cannot be
//!   missed.
//! - Both are preserved by `push`, `set` (a recanonize-style rewrite), `mark`
//!   and `restore`, and `restore` performs ZERO index maintenance: the
//!   HISTORY-COMPLETENESS invariant (every cell of every live snapshot is
//!   hinted under its content's fingerprint, and hints are never removed)
//!   makes post-restore completeness a theorem rather than a rebuilt fact.
//!
//! The index is hints, not authority: a probe validates every candidate
//! against the column's current content, so a stale hint is skipped, never
//! wrong. Fingerprints are an abstract deterministic function of content
//! (`HintContent::fp_spec`); correctness uses only that content-equal values
//! fingerprint equally (`lemma_fp_respects_eq`), never the values themselves,
//! so the hash is swappable. The fingerprint index is the crate's own
//! verified `SpMap` in untracked mode (it must NOT roll back) mapping each
//! fingerprint to a spill bucket of cell ids; buckets only grow. Memory is
//! bounded by distinct (cell, content) write events - the same order as the
//! column's own diff log - and reclaiming provably-dead hints is the recorded
//! follow-up (droppability = "no live mark can revive it"), not a v1 concern.

use vstd::prelude::*;

use crate::dyn_store::StoreKind;
use crate::error::ContainerError;
use crate::index_like::IndexLike;
use crate::tagged::Tagged;
use crate::vec::{ShrinkPolicy, VecToken};

verus! {

/// Content contract for hinted values: a spec-carrying equality (the
/// collision predicate) and a deterministic fingerprint that respects it.
/// `eq_spec` needs no equivalence laws beyond symmetry-of-use here; the
/// theorems quantify it directly.
pub trait HintContent: Sized {
    /// The collision predicate: when do two cells collide?
    spec fn eq_spec(a: &Self, b: &Self) -> bool;

    /// Exec twin, exact.
    fn content_eq(a: &Self, b: &Self) -> (r: bool)
        ensures r == Self::eq_spec(a, b);

    /// Deterministic fingerprint of the content.
    spec fn fp_spec(&self) -> u32;

    /// Exec twin, exact.
    fn fp(&self) -> (r: u32)
        ensures r == self.fp_spec();

    /// The routing axiom: content-equal values fingerprint equally. This is
    /// the ONLY property the completeness theorem needs from the hash.
    proof fn lemma_fp_respects_eq(a: &Self, b: &Self)
        requires Self::eq_spec(a, b)
        ensures a.fp_spec() == b.fp_spec();
}

// "Any key occurring in a log has a LAST occurrence" — the bridge from "the
// log mentions fp" to `index_agrees`'s last-occurrence hypothesis — lives with
// the map: `crate::map::lemma_last_occurrence_exists`.

/// The verified arena + fingerprint index pair.
pub struct HintedArena<T, I, const TRACK: bool = true>
where
    T: Sized + Copy + Tagged + HintContent,
    I: IndexLike,
{
    /// The semi-persistent column (runtime-selected store kind).
    pub(crate) col: crate::VecD<T, I, TRACK>,
    /// Fingerprint -> spill bucket index. UNTRACKED on purpose: restore must
    /// not roll the hint index back - that is the zero-maintenance theorem.
    /// Unique-keyed: a fingerprint is inserted once, so the map's own
    /// discipline carries the key-distinctness `wf_struct` states.
    pub(crate) index: crate::SpUniqueMap<u32, usize, usize, false>,
    /// Hint buckets; entries are cell ids that at some point held content
    /// with the bucket's fingerprint. Push-only.
    pub(crate) spill: Vec<Vec<I>>,
}

impl<T, I, const TRACK: bool> HintedArena<T, I, TRACK>
where
    T: Sized + Copy + Tagged + HintContent,
    I: IndexLike,
{
    /// The bucket ids hinted under `fp` (empty when the fingerprint is
    /// unknown).
    pub open(crate) spec fn bucket_spec(&self, fp: u32) -> Seq<I> {
        if self.index.index_view().contains_key(fp) {
            let pos = self.index.index_view()[fp].as_nat() as int;
            let slot = self.index.log_view()[pos].1 as int;
            self.spill@[slot]@
        } else {
            Seq::empty()
        }
    }

    /// Cell position `j` is hinted under fingerprint `fp`: some bucket entry
    /// names it.
    pub open(crate) spec fn hinted(&self, fp: u32, j: nat) -> bool {
        exists|e: int| 0 <= e < self.bucket_spec(fp).len()
            && (#[trigger] self.bucket_spec(fp)[e]).as_nat() == j
    }

    pub open(crate) spec fn view(&self) -> Seq<T> {
        self.col.view()
    }

    pub open(crate) spec fn snapshots_view(&self) -> Seq<Seq<T>> {
        self.col.snapshots_view()
    }

    /// HISTORY-COMPLETENESS: every cell of the live view AND of every live
    /// snapshot is hinted under its content's fingerprint. The snapshot arm
    /// is what makes restore free: rolling the column back can only surface
    /// contents this invariant already covers.
    pub open(crate) spec fn complete(&self) -> bool {
        &&& forall|j: int| 0 <= j < self.view().len()
                ==> self.hinted((#[trigger] self.view()[j]).fp_spec(), j as nat)
        &&& forall|k: int, j: int|
                0 <= k < self.snapshots_view().len()
                    && 0 <= j < self.snapshots_view()[k].len()
                ==> self.hinted((#[trigger] self.snapshots_view()[k][j]).fp_spec(),
                        j as nat)
    }

    /// Structural well-formedness: the column and index are wf, every slot
    /// stored in the index addresses the spill table, the index log's keys
    /// are distinct (each fingerprint inserted once, so its bucket is
    /// stable), and every hinted id round-trips through `as_nat` (it was
    /// minted from a real cell id).
    /// Structural well-formedness: the column, the index and the spill table
    /// agree. The operations' helper (`note_hint`) is stated over this part
    /// alone, because it runs while a fresh cell is not yet hinted.
    pub open(crate) spec fn wf_struct(&self) -> bool {
        &&& self.col.wf()
        &&& self.index.wf()
        &&& forall|p: int| 0 <= p < self.index.log_view().len()
                ==> (#[trigger] self.index.log_view()[p].1) < self.spill@.len()
        &&& forall|a: int, b: int|
                0 <= a < b < self.index.log_view().len()
                ==> (#[trigger] self.index.log_view()[a].0)
                    != (#[trigger] self.index.log_view()[b].0)
        // Slot injectivity: distinct fingerprints own distinct buckets, so a
        // push into one bucket provably leaves every other fingerprint's
        // hints untouched.
        &&& forall|a: int, b: int|
                0 <= a < b < self.index.log_view().len()
                ==> (#[trigger] self.index.log_view()[a].1)
                    != (#[trigger] self.index.log_view()[b].1)
    }

    /// Well-formedness as callers see it: the structure plus completeness.
    /// Every operation preserves both, so callers owe only `wf` (the
    /// total-API convention).
    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.wf_struct()
        &&& self.complete()
    }

    /// Empty arena of the selected store kind.
    pub fn new_kind(kind: StoreKind) -> (r: Self)
        ensures
            r.wf(),
            r.complete(),
            r.view().len() == 0,
            r.snapshots_view().len() == 0,
    {
        HintedArena {
            col: crate::VecD::new_kind(kind),
            index: crate::SpMap::new(),
            spill: Vec::new(),
        }
    }

    pub fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.view().len(),
    {
        self.col.len()
    }

    pub fn get(&self, i: I) -> (v: T)
        requires self.wf(),
        ensures i.as_nat() < self.view().len() ==> v == self.view()[i.as_nat() as int],
    {
        // Total: an out-of-range id is the documented trap.
        if !(i.as_usize() < self.col.len().as_usize()) {
            crate::guard::refuse("HintedArena::get: id out of bounds");
        }
        self.col.get_index(i)
    }

    /// Append a cell, hinting it. Preserves the collision invariant: the new
    /// live cell is hinted by construction, every old hint survives
    /// (`note_hint`'s preservation clause), and the snapshot stack is
    /// untouched.
    pub fn push(&mut self, t: T) -> (r: Result<I, ContainerError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).complete(),
            r matches Ok(id) ==> id.as_nat() == old(self).view().len()
                && final(self).view() == old(self).view().push(t)
                && final(self).snapshots_view() == old(self).snapshots_view(),
            r is Err ==> final(self).view() == old(self).view()
                && final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let ghost pre = *self;
        proof { assert(pre.complete()); }
        if !self.col.can_push() {
            return Err(ContainerError::CapacityExhausted);
        }
        let id = self.col.len();
        proof { id.lemma_as_nat_bounded(); }
        self.col.push(t);
        let fp = t.fp();
        let ghost mid = *self;
        self.note_hint(fp, id);
        proof {
            // The column write leaves the index and buckets alone, so mid's
            // hints are literally pre's.
            assert(mid.index == pre.index && mid.spill == pre.spill);
            assert forall|f2: u32, j2: nat| pre.hinted(f2, j2)
                implies #[trigger] mid.hinted(f2, j2) by {
                assert(mid.bucket_spec(f2) == pre.bucket_spec(f2));
            }
            assert(self.view() =~= pre.view().push(t));
            assert(self.snapshots_view() =~= pre.snapshots_view());
            assert forall|j: int| 0 <= j < self.view().len()
                implies self.hinted((#[trigger] self.view()[j]).fp_spec(), j as nat) by {
                if j < pre.view().len() {
                    assert(self.view()[j] == pre.view()[j]);
                    assert(pre.hinted(pre.view()[j].fp_spec(), j as nat));
                    assert(mid.hinted(pre.view()[j].fp_spec(), j as nat));
                } else {
                    assert(self.view()[j] == t);
                    assert(id.as_nat() == j);
                }
            }
            assert forall|k: int, j: int|
                0 <= k < self.snapshots_view().len()
                    && 0 <= j < self.snapshots_view()[k].len()
                implies self.hinted((#[trigger] self.snapshots_view()[k][j]).fp_spec(),
                    j as nat) by {
                assert(pre.hinted(pre.snapshots_view()[k][j].fp_spec(), j as nat));
                assert(mid.hinted(pre.snapshots_view()[k][j].fp_spec(), j as nat));
            }
        }
        Ok(id)
    }

    /// Rewrite a live cell (the recanonize shape), hinting the NEW content.
    /// The old content's hint deliberately stays: a restore may bring that
    /// content back, and then the surviving hint is exactly what keeps the
    /// invariant true with no index work.
    pub fn set(&mut self, id: I, t: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).complete(),
            final(self).view() == old(self).view().update(id.as_nat() as int, t),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        // Total: an out-of-range id is the documented trap.
        if !(id.as_usize() < self.col.len().as_usize()) {
            crate::guard::refuse("HintedArena::set: id out of bounds");
        }
        let ghost pre = *self;
        proof { assert(pre.complete()); }
        self.col.set_index(id, t);
        let fp = t.fp();
        let ghost mid = *self;
        self.note_hint(fp, id);
        proof {
            assert(mid.index == pre.index && mid.spill == pre.spill);
            assert forall|f2: u32, j2: nat| pre.hinted(f2, j2)
                implies #[trigger] mid.hinted(f2, j2) by {
                assert(mid.bucket_spec(f2) == pre.bucket_spec(f2));
            }
            assert(self.view() =~= pre.view().update(id.as_nat() as int, t));
            assert forall|j: int| 0 <= j < self.view().len()
                implies self.hinted((#[trigger] self.view()[j]).fp_spec(), j as nat) by {
                if j == id.as_nat() as int {
                    assert(self.view()[j] == t);
                } else {
                    assert(self.view()[j] == pre.view()[j]);
                    assert(pre.hinted(pre.view()[j].fp_spec(), j as nat));
                    assert(mid.hinted(pre.view()[j].fp_spec(), j as nat));
                }
            }
            assert forall|k: int, j: int|
                0 <= k < self.snapshots_view().len()
                    && 0 <= j < self.snapshots_view()[k].len()
                implies self.hinted((#[trigger] self.snapshots_view()[k][j]).fp_spec(),
                    j as nat) by {
                assert(pre.hinted(pre.snapshots_view()[k][j].fp_spec(), j as nat));
                assert(mid.hinted(pre.snapshots_view()[k][j].fp_spec(), j as nat));
            }
        }
    }




    /// THE COLLISION THEOREM. Scan the fingerprint's hint bucket, validating
    /// each candidate against the column's CURRENT content:
    ///
    /// - `Some(id)`: cell `id` is live and its content collides with `t`
    ///   (soundness - a stale hint can never produce a wrong answer, because
    ///   the content compare is the answer).
    /// - `None`: NO live cell collides with `t` (completeness - a congruence
    ///   collision cannot be missed). This is the direction that needs
    ///   `complete()`: a colliding cell would be hinted under ITS
    ///   fingerprint, which equals `t`'s by `lemma_fp_respects_eq`, so the
    ///   scan would have seen it.
    pub fn probe(&self, t: &T) -> (r: Option<I>)
        requires
            self.wf(),
        ensures
            match r {
                Some(id) => id.as_nat() < self.view().len()
                    && T::eq_spec(&self.view()[id.as_nat() as int], t),
                None => forall|j: int| #![trigger self.view()[j]] 0 <= j < self.view().len()
                    ==> !T::eq_spec(&self.view()[j], t),
            },
    {
        proof { assert(self.complete()); }
        let fp = t.fp();
        let live = self.col.len();
        match self.index.get_by_key(&fp) {
            None => {
                proof {
                    // Unknown fingerprint: the bucket is empty, so by
                    // completeness no live cell can carry this fingerprint -
                    // and a colliding cell would.
                    assert(self.bucket_spec(fp).len() == 0);
                    assert forall|j: int| #![trigger self.view()[j]] 0 <= j < self.view().len()
                        implies !T::eq_spec(&self.view()[j], t) by {
                        if T::eq_spec(&self.view()[j], t) {
                            T::lemma_fp_respects_eq(&self.view()[j], t);
                            assert(self.hinted(self.view()[j].fp_spec(), j as nat));
                            assert(self.hinted(fp, j as nat));
                        }
                    }
                }
                None
            }
            Some(slotr) => {
                let slot = *slotr;
                let blen = self.spill[slot].len();
                let mut e: usize = 0;
                while e < blen
                    invariant
                        self.wf(),
                        fp == t.fp_spec(),
                        live.as_nat() == self.view().len(),
                        self.index.index_view().contains_key(fp),
                        slot < self.spill@.len(),
                        self.bucket_spec(fp) == self.spill@[slot as int]@,
                        blen == self.bucket_spec(fp).len(),
                        0 <= e <= blen,
                        // No candidate so far collided while live.
                        forall|q: int| 0 <= q < e ==> {
                            let cid = #[trigger] self.bucket_spec(fp)[q];
                            !(cid.as_nat() < self.view().len()
                                && T::eq_spec(&self.view()[cid.as_nat() as int], t))
                        },
                    decreases blen - e,
                {
                    let cand = self.spill[slot][e];
                    if cand.as_usize() < live.as_usize() {
                        let v = self.col.get_index(cand);
                        if T::content_eq(&v, t) {
                            proof {
                                cand.lemma_as_nat_bounded();
                                live.lemma_as_nat_bounded();
                            }
                            return Some(cand);
                        }
                    }
                    e += 1;
                }
                proof {
                    // Scanned the whole bucket with no live collision. Any
                    // colliding live cell would be hinted under fp (complete
                    // + fp respects eq), hence appear in this bucket, hence
                    // have been rejected by the scan - contradiction.
                    assert forall|j: int| #![trigger self.view()[j]] 0 <= j < self.view().len()
                        implies !T::eq_spec(&self.view()[j], t) by {
                        if T::eq_spec(&self.view()[j], t) {
                            T::lemma_fp_respects_eq(&self.view()[j], t);
                            assert(self.hinted(fp, j as nat));
                            let q = choose|q: int| 0 <= q < self.bucket_spec(fp).len()
                                && (#[trigger] self.bucket_spec(fp)[q]).as_nat() == j as nat;
                            assert(0 <= q < blen);
                        }
                    }
                }
                None
            }
        }
    }

    /// Record a hint: `id` (a real cell id, `id.as_nat() == j`) currently or
    /// historically holds content fingerprinting to `fp`. Never removes or
    /// moves any existing hint (the preservation ensures), which is what the
    /// completeness invariant's restore-freeness rests on. Total: index-word
    /// exhaustion takes the crate's documented trap.
    fn note_hint(&mut self, fp: u32, id: I)
        requires
            old(self).wf_struct(),
        ensures
            final(self).wf_struct(),
            final(self).col == old(self).col,
            // The new hint.
            final(self).hinted(fp, id.as_nat()),
            // Every old hint survives.
            forall|f2: u32, j2: nat| old(self).hinted(f2, j2)
                ==> #[trigger] final(self).hinted(f2, j2),
    {
        broadcast use vstd::seq_lib::group_seq_properties;
        let ghost pre = *self;
        match self.index.get_by_key(&fp) {
            Some(slotr) => {
                let slot = *slotr;
                proof {
                    // get_by_key ties slot to the log entry at index_view[fp];
                    // wf bounds it.
                    assert(self.index.index_view().contains_key(fp));
                    assert(slot < self.spill@.len());
                }
                let ghost old_bucket = self.spill@[slot as int]@;
                // Push into the bucket in place: swap it out against an empty
                // vector (no allocation), push, swap it back. Destination
                // passing, no copy of the bucket.
                let mut b: Vec<I> = Vec::new();
                core::mem::swap(&mut self.spill[slot], &mut b);
                b.push(id);
                core::mem::swap(&mut self.spill[slot], &mut b);
                proof {
                    // wf: log untouched; spill length unchanged, so every
                    // stored slot still addresses the table.
                    assert(self.index.log_view() == pre.index.log_view());
                    assert(self.spill@.len() == pre.spill@.len());
                    assert(self.spill@[slot as int]@ =~= old_bucket.push(id));
                    assert(self.bucket_spec(fp) =~= old_bucket.push(id));
                    assert(self.bucket_spec(fp)[old_bucket.len() as int] == id);
                    assert forall|f2: u32, j2: nat| pre.hinted(f2, j2)
                        implies #[trigger] self.hinted(f2, j2) by {
                        if pre.index.index_view().contains_key(f2) {
                            let pos = pre.index.index_view()[f2].as_nat() as int;
                            let s2 = pre.index.log_view()[pos].1 as int;
                            if s2 == slot as int {
                                // Same bucket: grew by push; old entries keep
                                // their positions.
                                let e = choose|e: int| 0 <= e < pre.bucket_spec(f2).len()
                                    && (#[trigger] pre.bucket_spec(f2)[e]).as_nat() == j2;
                                assert(self.bucket_spec(f2)[e].as_nat() == j2);
                            } else {
                                assert(self.spill@[s2]@ == pre.spill@[s2]@);
                                assert(self.bucket_spec(f2) == pre.bucket_spec(f2));
                            }
                        }
                    }
                }
            }
            None => {
                let slot = self.spill.len();
                let mut b: Vec<I> = Vec::new();
                b.push(id);
                self.spill.push(b);
                match self.index.try_insert(fp, slot) {
                    Ok(_) => {}
                    Err(_) => {
                        crate::guard::refuse("hint index exhausted its index word")
                    }
                }
                proof {
                    // wf: the log grew by one entry (fp, slot) whose key is
                    // fresh (get_by_key said absent, and index_agrees ties
                    // the log's live keys to the index) and whose slot is
                    // fresh (== old spill len, and every old slot was < it).
                    assert(self.index.log_view()
                        =~= pre.index.log_view().push((fp, slot)));
                    assert(self.spill@.len() == pre.spill@.len() + 1);
                    assert forall|a: int, b: int|
                        0 <= a < b < self.index.log_view().len()
                        implies (#[trigger] self.index.log_view()[a].1)
                            != (#[trigger] self.index.log_view()[b].1) by {
                        if b == pre.index.log_view().len() {
                            assert(self.index.log_view()[a].1 < pre.spill@.len());
                            assert(self.index.log_view()[b].1 == pre.spill@.len());
                        }
                    }
                    assert forall|a: int, b: int|
                        0 <= a < b < self.index.log_view().len()
                        implies (#[trigger] self.index.log_view()[a].0)
                            != (#[trigger] self.index.log_view()[b].0) by {
                        if b == pre.index.log_view().len() {
                            // A duplicate key at `a` would make SOME position
                            // the last occurrence of fp in the old log, and
                            // index_agrees would then have fp live - which the
                            // absent lookup refutes.
                            assert(!pre.index.index_view().contains_key(fp));
                            if pre.index.log_view()[a].0 == fp {
                                crate::map::lemma_last_occurrence_exists(pre.index.log_view(), a);
                                let last = choose|q: int|
                                    #[trigger] crate::map::is_last_occurrence(
                                        pre.index.log_view(), q)
                                    && pre.index.log_view()[q].0
                                        == pre.index.log_view()[a].0;
                                assert(pre.index.index_view().contains_key(fp));
                            }
                        }
                    }
                    // Fresh key at a fresh slot: the new bucket is [id]; every
                    // old key's log position, slot and bucket are unchanged.
                    assert(self.index.index_view() =~= pre.index.index_view()
                        .insert(fp, self.index.index_view()[fp]));
                    assert(self.bucket_spec(fp)[0] == id);
                    assert forall|f2: u32, j2: nat| pre.hinted(f2, j2)
                        implies #[trigger] self.hinted(f2, j2) by {
                        if pre.index.index_view().contains_key(f2) {
                            assert(f2 != fp);
                            let pos = pre.index.index_view()[f2].as_nat() as int;
                            assert(self.index.index_view()[f2]
                                == pre.index.index_view()[f2]);
                            assert(self.index.log_view()[pos]
                                == pre.index.log_view()[pos]);
                            let s2 = pre.index.log_view()[pos].1 as int;
                            assert(self.spill@[s2]@ == pre.spill@[s2]@);
                            assert(self.bucket_spec(f2) == pre.bucket_spec(f2));
                            let e = choose|e: int| 0 <= e < pre.bucket_spec(f2).len()
                                && (#[trigger] pre.bucket_spec(f2)[e]).as_nat() == j2;
                            assert(self.bucket_spec(f2)[e].as_nat() == j2);
                        }
                    }
                }
            }
        }
    }
}

/// Worked instance: a two-field pair keyed by both fields, fingerprinted by
/// the first alone (deliberately coarse, so buckets collide and the probe's
/// validity check does real work). This is the shape the e-graph's fixed-arity
/// node content takes.
impl HintContent for crate::tagged::Pair<u32, u32> {
    open spec fn eq_spec(a: &Self, b: &Self) -> bool {
        a.a == b.a && a.b == b.b
    }

    fn content_eq(a: &Self, b: &Self) -> bool {
        a.a == b.a && a.b == b.b
    }

    open spec fn fp_spec(&self) -> u32 {
        self.a
    }

    fn fp(&self) -> u32 {
        self.a
    }

    proof fn lemma_fp_respects_eq(a: &Self, b: &Self) {
    }
}

// ---------------------------------------------------------------------------
// Typed-group member: the column moves, the hint index is not touched (the
// zero-maintenance property `restore` proves, restated per structural
// operation). Completeness survives every operation because the live view
// after it is a covered snapshot or the view the index already covered, and
// the surviving snapshot stack is a prefix (or the old stack plus that view).
// ---------------------------------------------------------------------------

impl<T, I, const TRACK: bool> crate::group::Member for HintedArena<T, I, TRACK>
where
    T: Sized + Copy + Tagged + HintContent + core::default::Default,
    I: IndexLike,
{
    type Model = Seq<T>;

    open spec fn wf(&self) -> bool {
        &&& HintedArena::wf(self)
        &&& self.complete()
        &&& TRACK
    }

    open spec fn depth_spec(&self) -> nat {
        self.snapshots_view().len()
    }

    open spec fn can_push(&self) -> bool {
        &&& self.snapshots_view().len() < u32::MAX as nat
        &&& self.view().len() < I::max_nat()
    }

    open spec fn model(&self) -> Seq<T> {
        self.view()
    }

    open spec fn archive(&self) -> Seq<Seq<T>> {
        self.snapshots_view()
    }

    proof fn lemma_archive_depth(&self) {
    }

    fn can_push_now(&self) -> (b: bool) {
        proof {
            self.col.lemma_snapshots_len();
            self.col.lemma_member_specs();
        }
        <crate::VecD<T, I, TRACK> as crate::group::Member>::can_push_now(&self.col)
    }

    fn depth_exec(&self) -> (d: usize) {
        proof {
            self.col.lemma_snapshots_len();
            self.col.lemma_member_specs();
        }
        <crate::VecD<T, I, TRACK> as crate::group::Member>::depth_exec(&self.col)
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        if !self.can_push_now() {
            crate::guard::refuse("Member::push_frame: the hinted arena cannot open another frame");
        }
        let ghost pre = *self;
        proof { self.col.lemma_member_specs(); }
        <crate::VecD<T, I, TRACK> as crate::group::Member>::push_frame(&mut self.col, shrink);
        proof { self.col.lemma_member_specs(); }
        proof {
            assert(self.index == pre.index && self.spill == pre.spill);
            assert forall|f2: u32, j2: nat| pre.hinted(f2, j2)
                implies #[trigger] self.hinted(f2, j2) by {
                assert(self.bucket_spec(f2) == pre.bucket_spec(f2));
            }
            assert forall|j: int| 0 <= j < self.view().len()
                implies self.hinted((#[trigger] self.view()[j]).fp_spec(), j as nat) by {
                assert(pre.hinted(pre.view()[j].fp_spec(), j as nat));
            }
            assert forall|k: int, j: int|
                0 <= k < self.snapshots_view().len()
                    && 0 <= j < self.snapshots_view()[k].len()
                implies self.hinted((#[trigger] self.snapshots_view()[k][j]).fp_spec(),
                    j as nat) by {
                if k < pre.snapshots_view().len() {
                    assert(self.snapshots_view()[k] == pre.snapshots_view()[k]);
                    assert(pre.hinted(pre.snapshots_view()[k][j].fp_spec(), j as nat));
                } else {
                    assert(self.snapshots_view()[k] == pre.view());
                    assert(pre.hinted(pre.view()[j].fp_spec(), j as nat));
                }
            }
        }
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < self.depth_exec()) {
            crate::guard::refuse("Member::restore_frame: depth is not below the hinted arena's");
        }
        let ghost pre = *self;
        proof { self.col.lemma_member_specs(); }
        <crate::VecD<T, I, TRACK> as crate::group::Member>::restore_frame(&mut self.col, depth);
        proof { self.col.lemma_member_specs(); }
        proof { self.lemma_complete_after_cut(pre, depth as int, depth as int); }
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < self.depth_exec()) {
            crate::guard::refuse("Member::reset_frame: depth is not below the hinted arena's");
        }
        if !(self.depth_exec() < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        let ghost pre = *self;
        proof { self.col.lemma_member_specs(); }
        <crate::VecD<T, I, TRACK> as crate::group::Member>::reset_frame(&mut self.col, depth);
        proof { self.col.lemma_member_specs(); }
        proof { self.lemma_complete_after_cut(pre, depth as int, depth as int + 1); }
    }

    fn pop_frame(&mut self) {
        let d = self.depth_exec();
        if !(d >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        let ghost pre = *self;
        proof { self.col.lemma_member_specs(); }
        <crate::VecD<T, I, TRACK> as crate::group::Member>::pop_frame(&mut self.col);
        proof { self.col.lemma_member_specs(); }
        proof { self.lemma_complete_after_cut(pre, d as int - 1, d as int - 1); }
    }
}

impl<T, I, const TRACK: bool> HintedArena<T, I, TRACK>
where
    T: Sized + Copy + Tagged + HintContent,
    I: IndexLike,
{
    /// The zero-maintenance argument, once: after a column move that lands
    /// the view on `pre`'s archived snapshot `ti` and leaves the first `keep`
    /// snapshots, the untouched index still covers everything.
    proof fn lemma_complete_after_cut(&self, pre: Self, ti: int, keep: int)
        requires
            pre.complete(),
            self.index == pre.index,
            self.spill == pre.spill,
            0 <= ti < pre.snapshots_view().len(),
            self.view() == pre.snapshots_view()[ti],
            self.snapshots_view() == pre.snapshots_view().subrange(0, keep),
            0 <= keep <= pre.snapshots_view().len(),
        ensures
            self.complete(),
    {
        assert forall|f2: u32, j2: nat| pre.hinted(f2, j2)
            implies #[trigger] self.hinted(f2, j2) by {
            assert(self.bucket_spec(f2) == pre.bucket_spec(f2));
        }
        assert forall|j: int| 0 <= j < self.view().len()
            implies self.hinted((#[trigger] self.view()[j]).fp_spec(), j as nat) by {
            assert(pre.hinted(pre.snapshots_view()[ti][j].fp_spec(), j as nat));
        }
        assert forall|k: int, j: int|
            0 <= k < self.snapshots_view().len()
                && 0 <= j < self.snapshots_view()[k].len()
            implies self.hinted((#[trigger] self.snapshots_view()[k][j]).fp_spec(), j as nat) by {
            assert(self.snapshots_view()[k] == pre.snapshots_view()[k]);
            assert(pre.hinted(pre.snapshots_view()[k][j].fp_spec(), j as nat));
        }
    }
}

} // verus!
