// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent map backed by [`AppendOnlyVec`] + a transient hash index.
//!
//! The append-only log `(K, V)` is the source of truth; semi-persistence
//! (mark/restore) lives entirely in that already-verified log. A `HashMap`
//! accelerates key lookup, mapping each key to the dense log index of its MOST
//! RECENT entry. On `restore` the index is unwound over the entries about to
//! be discarded, newest first, so the work is proportional to the truncated
//! suffix, not to the survivors, and no surviving key is cloned. When the
//! suffix outnumbers the survivors the full rebuild (`rebuild_index`) is
//! cheaper and is used instead.
//!
//! The map has two key disciplines, chosen by the `UNIQUE` parameter:
//!
//! * **Last-write-wins** (`UNIQUE = false`, the default and the published
//!   semantics): an insert of a present key appends a new entry and the older
//!   one lingers in the log as a shadow. Each log position then also records
//!   the PREVIOUS occurrence of its key (`prev`, a parallel column filled from
//!   the value `HashMap::insert` hands back), which is what lets the unwind
//!   point a key back at its earlier occurrence instead of dropping it.
//! * **Unique keys** (`UNIQUE = true`, [`SpUniqueMap`]): no key occurs twice in
//!   the log. `try_insert` refuses a present key with `DuplicateKey`, and
//!   `try_intern` returns the existing entry. The previous-occurrence column
//!   is not kept — every link would be `None` — so an insert is one log push
//!   and one hash, and the unwind is a bare removal per discarded entry. Every
//!   interning table in the e-graph is one of these.
//!
//! Verified invariant (`wf`): the exec index agrees with `is_last_occurrence`,
//! the declarative "this position is the latest one holding its key", over the
//! current log; and the discipline's own column invariant holds — `prev`
//! agrees with `is_last_occurrence_prefix` (the same statement cut at the
//! entry's own position) under last-write-wins, or the log's keys are pairwise
//! distinct (`keys_unique`) under unique keys. From that, `get_by_key`/
//! `contains_key` provably read the latest value, and `restore` provably
//! returns the map to its marked logical contents (the log headline theorem
//! composes through). `unwind_index` and `rebuild_index` each re-establish
//! the agreement after a restore.
//!
//! Keys are `K: Clone + Hash + Eq` (production parity — String/Vec keys work).
//! The one clone-spec fact needed is the key model's own requirement (3):
//! `Key::clone` produces a result identical to its input (see
//! `clone_key_exact`).
//!
//! The index's `BuildHasher` is the `S` parameter, any [`ValidHasher`]: a
//! hasher that is `Default` and provably valid in vstd's model, each on one
//! already-shipped axiom. The default, [`crate::hasher_spec::IndexHasher`], uses
//! the same hash ALGORITHM production gets from hashbrown 0.17's default;
//! `std::hash::RandomState` (SipHash, per-process random keys) is the choice
//! for keys from an untrusted source. The rest of this note is about the default. Its
//! seed is DETERMINISTIC by default (a fixed constant, so runs are reproducible)
//! and CONTROLLABLE three ways — `SP_HASHER_SEED`,
//! `hasher_spec::set_default_seed`, or `IndexHasher::with_seed` per instance.
//! The `hasher-random-seed` feature changes only what the seed defaults to.
//! Not literally production's type — hashbrown's `DefaultHashBuilder` is a
//! newtype wrapping `foldhash::fast::RandomState` and forwarding every `write_*`
//! to it.
//!
//! Note the seed is invisible to this map's OBSERVABLE behaviour either way:
//! the log is the source of truth, `iter()` walks it in insertion order,
//! `rebuild_index` replays it in insertion order, `unwind_index` walks it in
//! reverse position order, and the index is never iterated (lookup-only).
//! Fixing the seed makes the internal layout and probe
//! sequences reproducible too. See `hasher_spec` for the full policy.
//!
//! vstd models `std::HashMap<K, V, S>` generically over any `S: BuildHasher`,
//! so every hasher gives the same verified container; the one
//! `builds_valid_hashers::<S>()` fact each operation needs comes from the
//! hasher's `ValidHasher::lemma_builds_valid_hashers` — this crate's
//! `axiom_index_hasher_builds_valid_hashers` for the default, vstd's shipped
//! `RandomState` axiom for std's.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::hash::Hash;
use vstd::prelude::*;

use crate::append_only_vec::AppendOnlyVec;
use crate::index_like::IndexLike;
use crate::vec::{ShrinkPolicy, VecToken};

// The index hasher (and the determinism policy behind it) lives in one place:
// `hasher_spec`. Re-exported here because it appears in `SpMap`'s field type.
pub use crate::hasher_spec::{IndexHasher, ValidHasher};

verus! {

// `std_specs::hash` is the spec-only model of `HashMap`; vstd gates the whole
// module behind `cfg(verus_keep_ghost)` (set by the Verus driver, NOT by plain
// `cargo build`). We mirror that gate on the import, so cargo skips it. Its
// items (`obeys_key_model`, `builds_valid_hashers`, `group_hash_axioms`) are
// used only in spec/`requires`/`broadcast use` positions, which the `verus!`
// macro erases under cargo — so after erasure cargo never references them.
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::*;

/// `true` iff position `i` is the LAST occurrence of key `log[i].0` in `log`
/// (no later entry repeats that key). The exec index points exactly here.
pub open(crate) spec fn is_last_occurrence<K, V>(log: Seq<(K, V)>, i: int) -> bool {
    &&& 0 <= i < log.len()
    &&& (forall|j: int| i < j < log.len() ==> (#[trigger] log[j]).0 != log[i].0)
}

/// No key occurs twice in the log: the unique-keys discipline's invariant.
pub open(crate) spec fn keys_unique<K, V>(log: Seq<(K, V)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < log.len() ==> (#[trigger] log[i]).0 != (#[trigger] log[j]).0
}

/// A value computed on demand, for [`SpMap::try_intern_with`]: the map calls
/// `produce` only after its probe has found the key absent. `produce` has no
/// precondition, which is what keeps the map's operation total; what it
/// promises about the value is `post`, and the map carries that promise into
/// its own postcondition. An unverified caller implements it for a closure
/// wrapper in one line.
pub trait Produce<V> {
    /// What `produce` guarantees about its value.
    spec fn post(&self, v: V) -> bool;

    fn produce(self) -> (v: V)
        ensures
            self.post(v),
    ;
}

/// Semi-persistent map. (`SpMap` rather than `Map` to avoid colliding with
/// `vstd::map::Map`, which is `HashMap`'s view type.)
///
/// `I` is the log's index word, and it is also the hash index's VALUE type — which
/// is where the width is paid for in memory: one entry per live key. A map keyed
/// over a 31-bit id space at `I = u32` stores 4-byte positions instead of 8-byte
/// ones, and `wf` (via the log's) still pins every position inside `I`, so nothing
/// wraps. See [`AppendOnlyVec`] for why the default is `usize`.
///
/// `UNIQUE` selects the key discipline (see the module docs): `false` is
/// last-write-wins, `true` refuses duplicate keys and drops the
/// previous-occurrence column.
#[verifier::reject_recursive_types(S)]
pub struct SpMap<
    K,
    V,
    I: IndexLike = usize,
    const TRACK: bool = true,
    const UNIQUE: bool = false,
    S: ValidHasher = IndexHasher,
> where
    K: Clone + Hash + Eq,
{
    pub(crate) log: AppendOnlyVec<(K, V), I, TRACK>,
    pub(crate) index: HashMap<K, I, S>,
    /// Previous-occurrence chain, parallel to the log: `prev[p]` is the position
    /// of the last entry holding `log[p].0` BEFORE `p`, or `None` when `p` is the
    /// key's first occurrence. It is the value `HashMap::insert` returns when the
    /// entry is indexed, so it costs no extra lookup, and it is what lets
    /// `restore` unwind the index over the truncated suffix alone.
    ///
    /// Under `UNIQUE` the column stays empty (never allocated): every link would
    /// be `None`, and the unwind knows it.
    pub(crate) prev: std::vec::Vec<Option<I>>,
}

/// The unique-keys map: [`SpMap`] with `UNIQUE = true`. An insert of a present
/// key is refused (`try_insert`) or answered with the existing entry
/// (`try_intern`); no previous-occurrence column is kept.
pub type SpUniqueMap<K, V, I = usize, const TRACK: bool = true, S = IndexHasher> =
    SpMap<K, V, I, TRACK, true, S>;

impl<K, V, I: IndexLike, const TRACK: bool, const UNIQUE: bool, S: ValidHasher> SpMap<K, V, I, TRACK, UNIQUE, S>
where
    K: Clone + Hash + Eq,
{
    /// The log sequence (source of truth).
    pub open(crate) spec fn log_view(&self) -> Seq<(K, V)> {
        self.log.view()
    }

    /// The index map (spec counterpart; the field is `pub(crate)` — privacy closeout).
    pub open(crate) spec fn index_view(&self) -> Map<K, I> {
        self.index@
    }

    /// Frame-stack depth of the log (spec counterpart).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.log.depth_spec()
    }

    /// Lifetime restore count of the log (spec counterpart).
    pub open(crate) spec fn fork_count_spec(&self) -> nat {
        self.log.fork_count_spec()
    }

    /// Log snapshot stack (spec counterpart).
    pub open(crate) spec fn log_snapshots_view(&self) -> Seq<Seq<(K, V)>> {
        self.log.snapshots_view()
    }

    /// Index/log agreement: the exec index contains `k → i` iff `i` is the
    /// last occurrence of `k` in the log. (`obeys_key_model` keeps the
    /// HashMap key model well-behaved.)
    ///
    /// Positions are compared through `as_nat()` because the stored value is now
    /// an `I`, not a `usize`. `as_nat` is injective (`lemma_as_nat_injective`), so
    /// "the index value projects to `i`" still pins the stored word uniquely — the
    /// agreement is exactly as strong as before, just stated on the projection.
    pub open(crate) spec fn index_agrees(&self) -> bool {
        &&& obeys_key_model::<K>()
        &&& builds_valid_hashers::<S>()
        &&& index_agrees_seq(self.log_view(), self.index@)
    }

    /// Index/log agreement cut at `bound`: the index describes the last
    /// occurrences WITHIN `[0, bound)`. `unwind_index`'s running invariant; at
    /// `bound == log.len()` it is `index_agrees` minus the key-model facts.
    pub open(crate) spec fn index_agrees_prefix(&self, bound: int) -> bool {
        index_agrees_prefix_seq(self.log_view(), self.index@, bound)
    }

    /// The `prev` column agrees with the log (see [`prev_link_ok`]).
    pub open(crate) spec fn prev_agrees(&self) -> bool {
        prev_agrees_seq(self.log_view(), self.prev@)
    }

    /// The discipline's column invariant, as a relation on the parts:
    /// last-write-wins keeps the previous-occurrence column agreeing with the
    /// log; unique keys keeps no column and has the log's keys distinct.
    pub open(crate) spec fn column_agrees_seq(log: Seq<(K, V)>, prev: Seq<Option<I>>) -> bool {
        if UNIQUE {
            &&& keys_unique(log)
            &&& prev.len() == 0
        } else {
            prev_agrees_seq(log, prev)
        }
    }

    /// [`Self::column_agrees_seq`] on the map's own parts.
    pub open(crate) spec fn column_agrees(&self) -> bool {
        Self::column_agrees_seq(self.log_view(), self.prev@)
    }

    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.log.wf()
        &&& self.index_agrees()
        &&& self.column_agrees()
    }

    /// The column invariant of a truncated log: the previous-occurrence column
    /// is cut with the log (last-write-wins) or was never kept (unique keys).
    proof fn lemma_column_after_truncate(log: Seq<(K, V)>, prev: Seq<Option<I>>, bound: int)
        requires
            Self::column_agrees_seq(log, prev),
            0 <= bound <= log.len(),
        ensures
            Self::column_agrees_seq(
                log.subrange(0, bound),
                if UNIQUE { prev } else { prev.subrange(0, bound) },
            ),
    {
        if UNIQUE {
            let log2 = log.subrange(0, bound);
            assert forall|i: int, j: int| 0 <= i < j < log2.len()
                implies (#[trigger] log2[i]).0 != (#[trigger] log2[j]).0 by {
                assert(log2[i] == log[i]);
                assert(log2[j] == log[j]);
            }
        } else {
            lemma_prev_agrees_after_truncate(log, prev, bound);
        }
    }

    /// Column maintenance for a log already truncated to `saved_len`: cut the
    /// previous-occurrence column with it, or leave the (empty) column alone.
    fn truncate_column(&mut self, Ghost(old_log): Ghost<Seq<(K, V)>>, saved_len: usize)
        requires
            Self::column_agrees_seq(old_log, old(self).prev@),
            saved_len <= old_log.len(),
            old(self).log_view() == old_log.subrange(0, saved_len as int),
        ensures
            final(self).log == old(self).log,
            final(self).index == old(self).index,
            final(self).column_agrees(),
    {
        if !UNIQUE {
            self.prev.truncate(saved_len);
        }
        proof {
            Self::lemma_column_after_truncate(old_log, old(self).prev@, saved_len as int);
            if !UNIQUE {
                assert(self.prev@ == old(self).prev@.subrange(0, saved_len as int));
            }
        }
    }



    /// Total constructor. The map is `wf` for every key type that conforms to
    /// the HashMap key model (`obeys_key_model`: vstd proves it for primitive
    /// keys via `group_hash_axioms`; a verified caller with a custom key type
    /// establishes it once for `K`). It is a property of the TYPE, not of any
    /// value, so it is a conditional postcondition rather than a precondition:
    /// nothing to check at runtime, and a non-conforming key type gets an
    /// ordinary (unverified) map rather than a trap.
    pub fn new() -> (m: Self)
        ensures
            obeys_key_model::<K>() ==> m.wf(),
            m.log_view().len() == 0,
            m.index_view() == Map::<K, I>::empty(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        proof { S::lemma_builds_valid_hashers(); }
        let log = AppendOnlyVec::new();
        // `default()` (not `new()`): `new()` hardcodes std's `RandomState`;
        // `default()` builds the map with our chosen `S = IndexHasher`
        // (foldhash), and vstd specs it to the empty map for any `S: Default`.
        // That generic-over-`S: Default` spec is also why the SEED knob lives in
        // `IndexHasher::default()` rather than a `with_hasher` constructor: vstd
        // does not spec `with_hasher`, so this route keeps seed control free of
        // added trust. See hasher_spec.
        let index: HashMap<K, I, S> = HashMap::default();
        let prev: std::vec::Vec<Option<I>> = std::vec::Vec::new();
        let m = SpMap { log, index, prev };
        proof {
            assert(m.log_view().len() == 0);
            assert(m.index@ =~= Map::<K, I>::empty());
            assert(m.prev@.len() == 0);
        }
        m
    }

    /// Number of entries in the log (including overwritten shadows).
    ///
    /// A count of positions, so it is reported in `I`; `wf` makes the conversion
    /// inside the log's `len` infallible.
    pub fn log_len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.log_view().len(),
    {
        self.log.len()
    }

    /// Current dense index for a key, if present.
    pub fn id_of(&self, key: &K) -> (r: Option<I>)
        requires self.wf(),
        ensures
            match r {
                Some(i) => self.index_view().contains_key(*key) && self.index_view()[*key] == i,
                None => !self.index_view().contains_key(*key),
            },
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        match self.index.get(key) {
            Some(i) => Some(*i),
            None => None,
        }
    }

    /// Whether a key is currently present.
    pub fn contains_key(&self, key: &K) -> (b: bool)
        requires self.wf(),
        ensures b == self.index_view().contains_key(*key),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        self.index.contains_key(key)
    }

    /// Value+key pair at a dense log index.
    pub fn get(&self, idx: I) -> (r: &(K, V))
        requires self.wf(),
        ensures idx.as_nat() < self.log_view().len() ==> *r == self.log_view()[idx.as_nat() as int],
    {
        // Total-with-documented-panic: explicit bound branch (hot family).
        if !(idx.as_usize() < self.log.data.len()) {
            crate::guard::refuse("SpMap::get: index out of bounds");
        }
        self.log.get(idx)
    }

    /// The key at a dense log index (production `Map::key` parity).
    pub fn key(&self, idx: I) -> (r: &K)
        requires self.wf(),
        ensures idx.as_nat() < self.log_view().len() ==> *r == self.log_view()[idx.as_nat() as int].0,
    {
        // Total-with-documented-panic: explicit bound branch (hot family).
        if !(idx.as_usize() < self.log.data.len()) {
            crate::guard::refuse("SpMap::key: index out of bounds");
        }
        &self.log.get(idx).0
    }

    /// The value at a dense log index (production `Map::get` returned `&V`;
    /// under the verus names `get` returns the pair and this returns the
    /// value).
    pub fn get_val(&self, idx: I) -> (r: &V)
        requires self.wf(),
        ensures idx.as_nat() < self.log_view().len() ==> *r == self.log_view()[idx.as_nat() as int].1,
    {
        // Total-with-documented-panic: explicit bound branch (hot family).
        if !(idx.as_usize() < self.log.data.len()) {
            crate::guard::refuse("SpMap::get_val: index out of bounds");
        }
        &self.log.get(idx).1
    }

    /// The current (latest) value for a key, if present (production
    /// `Map::get_by_key` parity). Reads through the index: the entry at
    /// `index[key]` provably holds `key`'s last occurrence (`index_agrees`),
    /// so this is the live value.
    pub fn get_by_key(&self, key: &K) -> (r: Option<&V>)
        requires self.wf(),
        ensures
            match r {
                Some(v) => self.index_view().contains_key(*key)
                    && *v == self.log_view()[self.index_view()[*key].as_nat() as int].1,
                None => !self.index_view().contains_key(*key),
            },
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        match self.index.get(key) {
            Some(i) => {
                let idx = *i;
                // index_agrees gives 0 <= idx < log.len().
                Some(&self.log.get(idx).1)
            }
            None => None,
        }
    }

    /// Number of LIVE keys (production `Map::len` parity): the index's size —
    /// each live key has exactly one index entry (`index_agrees`), so
    /// `index.len()` is the live-key count. O(1); no separate counter field.
    ///
    /// `usize`, not `I`: this is the hash index's cardinality, not a log position.
    /// It is bounded by the log — `index_agrees` injects live keys into distinct
    /// positions — but that is a finite-cardinality argument, and the count is
    /// never stored, so narrowing it would cost a proof and save nothing.
    /// [`log_len`](Self::log_len) is the position count.
    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.index_view().len(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        self.index.len()
    }

    /// No live keys (production parity).
    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.index_view().len() == 0),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        self.index.len() == 0
    }

    pub fn depth(&self) -> (d: usize)
        ensures d == self.depth_spec(),
    {
        self.log.depth()
    }

    /// Insert or overwrite. Appends `(key, val)` to the log (the new last
    /// occurrence of `key`) and points the index at it. Returns the dense
    /// log index of the new entry. Under `UNIQUE` the key must be absent: this
    /// is the one-hash insert for a caller that has already established that
    /// (`try_insert` establishes it itself through the entry API).
    pub(crate) fn insert(&mut self, key: K, val: V) -> (id: I)
        requires
            old(self).wf(),
            // Room for one more position in the index word; see `AppendOnlyVec::push`.
            old(self).log_view().len() + 1 < I::max_nat(),
            UNIQUE ==> !old(self).index_view().contains_key(key),
        ensures
            final(self).wf(),
            id.as_nat() == old(self).log_view().len(),
            final(self).log_view() == old(self).log_view().push((key, val)),
            final(self).index_view() == old(self).index_view().insert(key, id),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        proof { S::lemma_builds_valid_hashers(); }
        let ghost old_log = self.log_view();
        let ghost old_prev = self.prev@;
        let key_for_index = clone_key_exact(&key);
        let id = self.log.push((key, val));
        // The index's former answer for `key` is exactly the new entry's
        // previous occurrence (or `None` for a fresh key): record it — unless
        // the discipline says it is always `None`.
        let shadowed = self.index.insert(key_for_index, id);
        if !UNIQUE {
            self.prev.push(shadowed);
        }
        proof {
            let log = self.log_view();
            let m = self.index@;
            let idn = id.as_nat() as int;
            if UNIQUE {
                lemma_absent_from_index_absent_from_log(old_log, old(self).index@, key);
                lemma_append_fresh_keys_unique(old_log, key, val);
            } else {
                assert(self.prev@ =~= old_prev.push(shadowed));
                lemma_insert_prev_link(old_log, old_prev, old(self).index@, log, self.prev@, shadowed);
            }
            assert(log == old_log.push((key, val)));
            assert(log[idn] == (key, val));
            // The appended entry is the unique new last-occurrence of `key`;
            // every other position's last-occurrence status is unchanged
            // (only an entry with key `key` could lose it, and the new tail
            // entry has key `key`, so prior `key` entries are no longer last —
            // but the index now maps `key` to `id`, matching).
            assert(is_last_occurrence(log, idn));
            assert forall|i: int| #[trigger] is_last_occurrence(log, i)
                implies m.contains_key(log[i].0) && m[log[i].0].as_nat() == i by {
                if i == idn {
                    assert(m[key] == id);
                } else {
                    // i < id; entry unchanged from old_log. It's still a last
                    // occurrence in the longer log only if its key != key
                    // (else the tail entry shadows it). So log[i].0 != key,
                    // and the index entry for log[i].0 is untouched by insert.
                    assert(log[i] == old_log[i]);
                    assert(log[i].0 != key);
                    assert(is_last_occurrence(old_log, i)) by {
                        assert forall|j: int| i < j < old_log.len()
                            implies (#[trigger] old_log[j]).0 != old_log[i].0 by {
                            assert(old_log[j] == log[j]);
                        }
                    }
                    assert(old(self).index@.contains_key(log[i].0));
                    assert(old(self).index@[log[i].0].as_nat() == i);
                    assert(m[log[i].0] == old(self).index@[log[i].0]);
                }
            }
            assert forall|k: K| #[trigger] m.contains_key(k)
                implies m[k].as_nat() < log.len() && log[m[k].as_nat() as int].0 == k
                    && is_last_occurrence(log, m[k].as_nat() as int) by {
                if k == key {
                    assert(m[k] == id);
                } else {
                    assert(m[k] == old(self).index@[k]);
                    assert(old(self).index@.contains_key(k));
                    // old last-occurrence of k is still last (the new tail has
                    // key `key` != k, doesn't shadow k).
                    let p = old(self).index@[k].as_nat() as int;
                    assert(is_last_occurrence(old_log, p));
                    assert(log[p] == old_log[p]);
                    assert forall|j: int| p < j < log.len()
                        implies (#[trigger] log[j]).0 != log[p].0 by {
                        if j < old_log.len() {
                            assert(log[j] == old_log[j]);
                        } else {
                            assert(log[j].0 == key);
                            assert(log[p].0 == k);
                        }
                    }
                }
            }
        }
        id
    }


    /// Push a frame without minting (what a typed group drives): the log
    /// seals its stratum, the index and the previous-occurrence column are
    /// untouched.
    pub(crate) fn push_frames(&mut self, shrink: ShrinkPolicy)
        requires old(self).wf(), TRACK, old(self).depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).log_view() == old(self).log_view(),
            final(self).index_view() == old(self).index_view(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).log_snapshots_view() == old(self).log_snapshots_view().push(old(self).log_view()),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        self.log.push_frame(shrink);
        proof {
            assert(self.log_view() == old(self).log_view());
            assert(self.index@ == old(self).index@);
        }
    }

    // ------------------------------------------------------------------
    // Total-operation shell: the map
    // delegates every capacity/validity question to its single component.
    // ------------------------------------------------------------------

    /// Exec counterpart of `insert`'s capacity precondition (the log's).
    pub fn can_insert(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.log_view().len() + 1 < I::max_nat()),
    {
        self.log.can_push()
    }

    /// Total insert: refuses at the log's index-word capacity, and under
    /// `UNIQUE` refuses a present key (`DuplicateKey`, one hash: the entry API
    /// decides membership and inserts through the same probe).
    pub fn try_insert(&mut self, key: K, val: V)
        -> (r: Result<I, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(id) ==> id.as_nat() == old(self).log_view().len()
                && final(self).log_view() == old(self).log_view().push((key, val))
                && final(self).index_view() == old(self).index_view().insert(key, id),
            r is Err ==> final(self).log_view() == old(self).log_view()
                && final(self).index_view() == old(self).index_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted
                || (UNIQUE && e == crate::error::ContainerError::DuplicateKey
                    && old(self).index_view().contains_key(key)),
            !UNIQUE ==> (r is Err <==> !(old(self).log_view().len() + 1 < I::max_nat())),
    {
        if !self.can_insert() {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        if UNIQUE {
            let (id, fresh) = self.intern_entry(key, val);
            if fresh {
                Ok(id)
            } else {
                Err(crate::error::ContainerError::DuplicateKey)
            }
        } else {
            Ok(self.insert(key, val))
        }
    }

    /// Interning insert in ONE hash of the key: the id of the existing entry, or
    /// a fresh one appended at the end. The `bool` says which happened.
    ///
    /// This is what every interning caller in this workspace wants. Written with
    /// a membership check followed by `try_insert`, a caller hashes the key
    /// twice; the entry API decides membership and inserts through the same
    /// probe, so this hashes it once. On a `String` or a `Vec` key that is the
    /// dominant cost of an insert.
    pub fn try_intern(&mut self, key: K, val: V) -> (r: Result<(I, bool), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok((id, fresh)) ==> !fresh ==> (
                final(self).log_view() == old(self).log_view()
                && final(self).index_view() == old(self).index_view()
                && old(self).index_view().contains_key(key)
                && old(self).index_view()[key] == id),
            r matches Ok((id, fresh)) ==> fresh ==> (
                id.as_nat() == old(self).log_view().len()
                && final(self).log_view() == old(self).log_view().push((key, val))
                && final(self).index_view() == old(self).index_view().insert(key, id)),
            r is Err ==> final(self).log_view() == old(self).log_view()
                && final(self).index_view() == old(self).index_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        if !self.can_insert() {
            // No room to append, but a hit still has an answer: one lookup.
            return match self.id_of(&key) {
                Some(id) => Ok((id, false)),
                None => Err(crate::error::ContainerError::CapacityExhausted),
            };
        }
        Ok(self.intern_entry(key, val))
    }

    /// `try_intern` whose value is computed only on a miss: the id of the
    /// existing entry, or a fresh one holding `f()`. One hash of the key either
    /// way, and `f` runs at most once, after the probe has decided the key is
    /// absent.
    ///
    /// This is the shape for a caller whose value is expensive to build — an
    /// action list, a statistics node — and who would otherwise look the key up,
    /// compute, and insert: two hashes, or three with a read-back. The producer
    /// may borrow anything but this map.
    ///
    /// The producer is a [`Produce`] rather than a bare closure so that this
    /// stays a total operation: a closure carries its own precondition, which
    /// this map could only pass through as a `requires` of its own, while
    /// `Produce::produce` has none.
    pub fn try_intern_with<P: Produce<V>>(&mut self, key: K, f: P)
        -> (r: Result<(I, bool), crate::error::ContainerError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok((id, fresh)) ==> !fresh ==> (
                final(self).log_view() == old(self).log_view()
                && final(self).index_view() == old(self).index_view()
                && old(self).index_view().contains_key(key)
                && old(self).index_view()[key] == id),
            r matches Ok((id, fresh)) ==> fresh ==> (
                id.as_nat() == old(self).log_view().len()
                && final(self).log_view().len() == old(self).log_view().len() + 1
                && final(self).log_view()[id.as_nat() as int].0 == key
                && f.post(final(self).log_view()[id.as_nat() as int].1)
                && final(self).log_view()
                    == old(self).log_view().push(final(self).log_view()[id.as_nat() as int])
                && final(self).index_view() == old(self).index_view().insert(key, id)),
            r is Err ==> final(self).log_view() == old(self).log_view()
                && final(self).index_view() == old(self).index_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        proof { S::lemma_builds_valid_hashers(); }
        if !self.can_insert() {
            return match self.id_of(&key) {
                Some(id) => Ok((id, false)),
                None => Err(crate::error::ContainerError::CapacityExhausted),
            };
        }
        let ghost old_log = self.log_view();
        let ghost old_index = self.index@;
        let ghost old_prev = self.prev@;
        let key_for_index = clone_key_exact(&key);
        match self.index.entry(key_for_index) {
            Entry::Occupied(e) => {
                let id = *e.get();
                Ok((id, false))
            }
            Entry::Vacant(e) => {
                proof {
                    lemma_absent_from_index_absent_from_log(old_log, old_index, key);
                }
                let val = f.produce();
                let id = self.log.push((key, val));
                if !UNIQUE {
                    self.prev.push(None);
                }
                e.insert(id);
                proof {
                    let log = self.log_view();
                    assert(log == old_log.push((key, val)));
                    if UNIQUE {
                        lemma_append_fresh_keys_unique(old_log, key, val);
                    } else {
                        assert(self.prev@ =~= old_prev.push(None::<I>));
                        lemma_insert_prev_link(old_log, old_prev, old_index, log, self.prev@, None);
                    }
                    lemma_append_fresh_preserves_index::<K, V, I>(old_log, old_index, key, val, id);
                    assert(self.index@ =~= old_index.insert(key, id));
                }
                Ok((id, true))
            }
        }
    }

    /// The interning core behind `try_intern` and unique-mode `try_insert`:
    /// one probe through the entry API, appending only when the key is vacant.
    ///
    /// The vacant case is what makes the discipline invariant provable without
    /// a lookup: the entry's contract says the key was absent from the index,
    /// and `index_agrees` turns that into "absent from the log", which is
    /// exactly the `None` link (last-write-wins) or the fresh key that keeps
    /// the log's keys distinct (unique keys).
    ///
    /// Inlined unconditionally: the two disciplines are separate
    /// monomorphizations of this body, and left to the inliner the unique one
    /// came out 4–5 per cent slower than the general one on heap keys despite
    /// doing strictly less work — a code-layout artefact, reproducible per
    /// binary. Forcing the inline puts both in the same context, and the
    /// expected order holds: unique keys is the faster path on every key shape.
    #[inline(always)]
    fn intern_entry(&mut self, key: K, val: V) -> (r: (I, bool))
        requires
            old(self).wf(),
            old(self).log_view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            !r.1 ==> (
                final(self).log_view() == old(self).log_view()
                && final(self).index_view() == old(self).index_view()
                && old(self).index_view().contains_key(key)
                && old(self).index_view()[key] == r.0),
            r.1 ==> (
                r.0.as_nat() == old(self).log_view().len()
                && final(self).log_view() == old(self).log_view().push((key, val))
                && final(self).index_view() == old(self).index_view().insert(key, r.0)),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        proof { S::lemma_builds_valid_hashers(); }
        let ghost old_log = self.log_view();
        let ghost old_index = self.index@;
        let ghost old_prev = self.prev@;
        let key_for_index = clone_key_exact(&key);
        match self.index.entry(key_for_index) {
            Entry::Occupied(e) => {
                let id = *e.get();
                (id, false)
            }
            Entry::Vacant(e) => {
                proof {
                    lemma_absent_from_index_absent_from_log(old_log, old_index, key);
                }
                let id = self.log.push((key, val));
                if !UNIQUE {
                    self.prev.push(None);
                }
                e.insert(id);
                proof {
                    let log = self.log_view();
                    assert(log == old_log.push((key, val)));
                    if UNIQUE {
                        lemma_append_fresh_keys_unique(old_log, key, val);
                    } else {
                        assert(self.prev@ =~= old_prev.push(None::<I>));
                        lemma_insert_prev_link(old_log, old_prev, old_index, log, self.prev@, None);
                    }
                    lemma_append_fresh_preserves_index::<K, V, I>(old_log, old_index, key, val, id);
                    assert(self.index@ =~= old_index.insert(key, id));
                }
                (id, true)
            }
        }
    }








    /// Semantics B, token-free (what a typed group drives): the log resets
    /// to its snapshot at `target` and keeps that frame open; the index is
    /// unwound or rebuilt exactly as `restore` does.
    pub(crate) fn reset_frames(&mut self, target: usize)
        requires
            old(self).wf(),
            TRACK,
            (target as nat) < old(self).depth_spec(),
            old(self).depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).log_view() == old(self).log_snapshots_view()[target as int],
            final(self).depth_spec() == target as nat + 1,
            final(self).log_snapshots_view()
                == old(self).log_snapshots_view().subrange(0, target as int + 1),
    {
        let ghost old_log = self.log_view();
        // The target frame's saved length: what the log restore truncates to.
        let saved_len = self.log.frames[target].as_usize();
        let n = self.log.len().as_usize();
        proof {
            // The log's `wf`: a saved length is within the data and names the
            // snapshot prefix.
            assert(self.log.frames@[target as int].as_nat() <= n);
            assert(old(self).log_snapshots_view()[target as int]
                == old_log.subrange(0, saved_len as int));
        }
        if n - saved_len <= saved_len {
            self.unwind_index(saved_len);
            self.log.reset_frame(target);
            proof {
                assert(self.log_view() == old_log.subrange(0, saved_len as int));
                lemma_index_agrees_after_truncate(old_log, self.index@, saved_len as int);
            }
            self.truncate_column(Ghost(old_log), saved_len);
        } else {
            self.log.reset_frame(target);
            proof {
                assert(self.log_view() == old_log.subrange(0, saved_len as int));
            }
            self.truncate_column(Ghost(old_log), saved_len);
            self.rebuild_index();
        }
    }


    /// The structural pop core: undo and drop the open top frame (index
    /// maintenance exactly as a restore to the frame below).
    pub(crate) fn pop_frame(&mut self)
        requires
            old(self).wf(),
            TRACK,
            old(self).depth_spec() >= 1,
        ensures
            final(self).wf(),
            final(self).log_view() == old(self).log_snapshots_view()[old(self).depth_spec() - 1],
            final(self).depth_spec() == old(self).depth_spec() - 1,
            final(self).log_snapshots_view()
                == old(self).log_snapshots_view().subrange(0, old(self).depth_spec() - 1),
    {
        let ghost old_log = self.log_view();
        // The target frame's saved length: what the log restore truncates to.
        let target = self.log.frames.len() - 1;
        let saved_len = self.log.frames[target].as_usize();
        let n = self.log.len().as_usize();
        proof {
            // The log's `wf`: a saved length is within the data and names the
            // snapshot prefix.
            assert(self.log.frames@[target as int].as_nat() <= n);
            assert(old(self).log_snapshots_view()[target as int]
                == old_log.subrange(0, saved_len as int));
        }
        if n - saved_len <= saved_len {
            self.unwind_index(saved_len);
            self.log.pop_frame();
            proof {
                assert(self.log_view() == old_log.subrange(0, saved_len as int));
                lemma_index_agrees_after_truncate(old_log, self.index@, saved_len as int);
            }
            self.truncate_column(Ghost(old_log), saved_len);
        } else {
            self.log.pop_frame();
            proof {
                assert(self.log_view() == old_log.subrange(0, saved_len as int));
            }
            self.truncate_column(Ghost(old_log), saved_len);
            self.rebuild_index();
        }
    }

    /// The legacy pop-restore, token-free (what a typed group drives): the
    /// log restores to its snapshot at `target` and drops that frame with
    /// everything above it; the index is unwound or rebuilt as `pop_frame`
    /// does.
    pub(crate) fn restore_frames(&mut self, target: usize)
        requires
            old(self).wf(),
            TRACK,
            (target as nat) < old(self).depth_spec(),
        ensures
            final(self).wf(),
            final(self).log_view() == old(self).log_snapshots_view()[target as int],
            final(self).depth_spec() == target as nat,
            final(self).log_snapshots_view()
                == old(self).log_snapshots_view().subrange(0, target as int),
    {
        let ghost old_log = self.log_view();
        // The target frame's saved length: what the log restore truncates to.
        let saved_len = self.log.frames[target].as_usize();
        let n = self.log.len().as_usize();
        proof {
            // The log's `wf`: a saved length is within the data and names the
            // snapshot prefix.
            assert(self.log.frames@[target as int].as_nat() <= n);
            assert(old(self).log_snapshots_view()[target as int]
                == old_log.subrange(0, saved_len as int));
        }
        if n - saved_len <= saved_len {
            self.unwind_index(saved_len);
            self.log.restore_frame(target);
            proof {
                assert(self.log_view() == old_log.subrange(0, saved_len as int));
                lemma_index_agrees_after_truncate(old_log, self.index@, saved_len as int);
            }
            self.truncate_column(Ghost(old_log), saved_len);
        } else {
            self.log.restore_frame(target);
            proof {
                assert(self.log_view() == old_log.subrange(0, saved_len as int));
            }
            self.truncate_column(Ghost(old_log), saved_len);
            self.rebuild_index();
        }
    }

    /// Restore's index maintenance, run BEFORE the log truncates to
    /// `saved_len`: walk the entries about to be discarded, newest first, and
    /// point each one's key back at its previous occurrence (`prev`) or drop
    /// it. Touches only the truncated suffix — `log.len() - saved_len` hash
    /// operations, and a key clone only for the entries whose key survives at
    /// an earlier position. Leaves the index agreeing with the log's
    /// `[0, saved_len)` prefix, which is what the truncated log will be.
    ///
    /// Under `UNIQUE` every link is `None` without being stored: a discarded
    /// entry's key leaves the map, and no key is ever cloned.
    fn unwind_index(&mut self, saved_len: usize)
        requires
            old(self).wf(),
            saved_len <= old(self).log_view().len(),
        ensures
            final(self).log == old(self).log,
            final(self).prev == old(self).prev,
            final(self).index_agrees_prefix(saved_len as int),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        proof { S::lemma_builds_valid_hashers(); }
        let ghost log = self.log_view();
        // The chain links the walk consults: the stored column, or the all-`None`
        // column the unique discipline never materializes.
        let ghost links: Seq<Option<I>> = if UNIQUE {
            Seq::new(log.len(), |i: int| None::<I>)
        } else {
            self.prev@
        };
        let n = self.log.len().as_usize();
        let mut bound: usize = n;
        proof {
            lemma_index_agrees_prefix_full(log, self.index@);
            if UNIQUE {
                assert forall|p: int| 0 <= p < log.len() implies #[trigger] prev_link_ok(log, links, p) by {
                    assert(links[p] is None);
                    assert forall|j: int| 0 <= j < p implies (#[trigger] log[j]).0 != log[p].0 by {}
                }
            }
            assert(prev_agrees_seq(log, links));
        }
        // Invariant: the index agrees with last-occurrence RESTRICTED to the
        // prefix `[0, bound)`; each step retires the entry at `bound - 1`.
        while bound > saved_len
            invariant
                self.log == old(self).log,
                self.prev == old(self).prev,
                log == self.log_view(),
                n == log.len(),
                log.len() < I::max_nat(),
                saved_len <= bound <= n,
                obeys_key_model::<K>(),
                builds_valid_hashers::<S>(),
                !UNIQUE ==> links == self.prev@,
                UNIQUE ==> (forall|i: int| 0 <= i < links.len() ==> #[trigger] links[i] is None),
                prev_agrees_seq(log, links),
                self.index_agrees_prefix(bound as int),
            decreases bound,
        {
            let p = bound - 1;
            let pos = I::try_from_usize(p).expect("log position exceeds the map's index word");
            let entry = self.log.get(pos);
            let link: Option<I> = if UNIQUE { None } else { self.prev[p] };
            let ghost before = self.index@;
            proof {
                assert(link == links[p as int]);
            }
            match link {
                Some(q) => {
                    // The key survives at `q`: point the index there. This is
                    // the one place restore clones a key.
                    let key = clone_key_exact(&entry.0);
                    self.index.insert(key, q);
                }
                None => {
                    // First occurrence: the key leaves the map.
                    self.index.remove(&entry.0);
                }
            }
            proof {
                lemma_unwind_step(log, links, before, self.index@, bound as int);
            }
            bound = p;
        }
    }

    /// Rebuild the index from the current log: scan left-to-right, mapping each
    /// key to the position seen so far. After the full scan each key maps to
    /// its last occurrence.
    fn rebuild_index(&mut self)
        requires old(self).log.wf(), obeys_key_model::<K>(), old(self).column_agrees(),
        ensures
            final(self).wf(),
            final(self).log_view() == old(self).log_view(),
            final(self).log == old(self).log,
            final(self).prev == old(self).prev,
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;
        proof { S::lemma_builds_valid_hashers(); }
        let ghost log = self.log_view();
        self.index.clear();
        // The scan counter stays `usize` — it is a loop variable, never stored —
        // and is converted to the stored width once per iteration for the entry it
        // names. The conversion is infallible: `i < n == log.len() < I::max_nat()`
        // by the log's `wf`.
        let n = self.log.len().as_usize();
        let mut i: usize = 0;
        // Invariant: index agrees with last-occurrence RESTRICTED to the prefix
        // [0, i): a key maps to its last occurrence within [0, i), and every
        // index entry is such a last-occurrence-within-prefix.
        while i < n
            invariant
                self.log == old(self).log,
                self.prev == old(self).prev,
                log == self.log_view(),
                n == log.len(),
                log.len() < I::max_nat(),
                0 <= i <= n,
                obeys_key_model::<K>(),
                builds_valid_hashers::<S>(),
                forall|p: int| 0 <= p < i && is_last_occurrence_prefix(log, p, i as int)
                    ==> #[trigger] self.index@.contains_key(log[p].0)
                        && self.index@[log[p].0].as_nat() == p,
                forall|k: K| #[trigger] self.index@.contains_key(k)
                    ==> self.index@[k].as_nat() < i && log[self.index@[k].as_nat() as int].0 == k
                        && is_last_occurrence_prefix(log, self.index@[k].as_nat() as int, i as int),
            decreases n - i,
        {
            let pos = I::try_from_usize(i).expect("log position exceeds the map's index word");
            let entry = self.log.get(pos);
            let key = clone_key_exact(&entry.0);
            self.index.insert(key, pos);
            proof {
                let m = self.index@;
                // After inserting (key, i): key's last-occ-in-[0,i+1) is i.
                assert forall|p: int| 0 <= p < (i + 1) && is_last_occurrence_prefix(log, p, (i + 1) as int)
                    implies #[trigger] m.contains_key(log[p].0) && m[log[p].0].as_nat() == p by {
                    if p == i as int {
                        assert(m[key] == pos);
                    } else {
                        // p < i and last-occ in [0,i+1): so log[p].0 != log[i].0
                        // (else i would shadow it), hence it was last-occ in
                        // [0,i) and the index for it is unchanged.
                        assert(log[p].0 != log[i as int].0);
                        assert(is_last_occurrence_prefix(log, p, i as int));
                    }
                }
                assert forall|kk: K| #[trigger] m.contains_key(kk)
                    implies m[kk].as_nat() < (i + 1) && log[m[kk].as_nat() as int].0 == kk
                        && is_last_occurrence_prefix(log, m[kk].as_nat() as int, (i + 1) as int) by {
                    if kk == key {
                        assert(m[kk] == pos);
                    } else {
                        // unchanged entry; was last-occ in [0,i), still is in
                        // [0,i+1) because log[i].0 == key != kk.
                        assert(log[i as int].0 != kk);
                    }
                }
            }
            i = i + 1;
        }
        proof {
            // At i == n, last-occurrence-in-prefix-[0,n) == last-occurrence.
            let m = self.index@;
            assert forall|p: int| #[trigger] is_last_occurrence(log, p)
                implies m.contains_key(log[p].0) && m[log[p].0].as_nat() == p by {
                assert(is_last_occurrence_prefix(log, p, n as int));
            }
            assert forall|k: K| #[trigger] m.contains_key(k)
                implies m[k].as_nat() < log.len() && log[m[k].as_nat() as int].0 == k
                    && is_last_occurrence(log, m[k].as_nat() as int) by {
                assert(is_last_occurrence_prefix(log, m[k].as_nat() as int, n as int));
            }
        }
    }
}

/// Like `is_last_occurrence` but only within the prefix `[0, bound)`: position
/// `i` holds a key not repeated in `(i, bound)`. (Used as the rebuild loop's
/// running invariant; at `bound == log.len()` it coincides with
/// `is_last_occurrence`.)
pub open(crate) spec fn is_last_occurrence_prefix<K, V>(log: Seq<(K, V)>, i: int, bound: int) -> bool {
    &&& 0 <= i < bound <= log.len()
    &&& (forall|j: int| i < j < bound ==> (#[trigger] log[j]).0 != log[i].0)
}

/// Index/log agreement as a relation on the parts: the index contains `k → i`
/// iff `i` is the last occurrence of `k` in `log`.
pub open(crate) spec fn index_agrees_seq<K, V, I: IndexLike>(log: Seq<(K, V)>, m: Map<K, I>) -> bool {
    &&& (forall|i: int| #[trigger] is_last_occurrence(log, i)
            ==> m.contains_key(log[i].0) && m[log[i].0].as_nat() == i)
    &&& (forall|k: K| #[trigger] m.contains_key(k)
            ==> m[k].as_nat() < log.len() && log[m[k].as_nat() as int].0 == k
                && is_last_occurrence(log, m[k].as_nat() as int))
}

/// `index_agrees_seq` cut at `bound`: the index describes the last occurrences
/// within `[0, bound)` and nothing beyond.
pub open(crate) spec fn index_agrees_prefix_seq<K, V, I: IndexLike>(
    log: Seq<(K, V)>,
    m: Map<K, I>,
    bound: int,
) -> bool {
    &&& 0 <= bound <= log.len()
    &&& (forall|p: int| #[trigger] is_last_occurrence_prefix(log, p, bound)
            ==> m.contains_key(log[p].0) && m[log[p].0].as_nat() == p)
    &&& (forall|k: K| #[trigger] m.contains_key(k)
            ==> m[k].as_nat() < bound && log[m[k].as_nat() as int].0 == k
                && is_last_occurrence_prefix(log, m[k].as_nat() as int, bound))
}

/// The chain link at `p`: `prev[p]` is the last occurrence of `log[p].0`
/// strictly before `p`, or `None` when no earlier entry holds that key.
pub open(crate) spec fn prev_link_ok<K, V, I: IndexLike>(log: Seq<(K, V)>, prev: Seq<Option<I>>, p: int) -> bool {
    match prev[p] {
        Some(q) => q.as_nat() < p && log[q.as_nat() as int].0 == log[p].0
            && is_last_occurrence_prefix(log, q.as_nat() as int, p),
        None => forall|j: int| 0 <= j < p ==> (#[trigger] log[j]).0 != log[p].0,
    }
}

/// The whole `prev` column agrees with the log.
pub open(crate) spec fn prev_agrees_seq<K, V, I: IndexLike>(log: Seq<(K, V)>, prev: Seq<Option<I>>) -> bool {
    &&& prev.len() == log.len()
    &&& (forall|p: int| 0 <= p < log.len() ==> #[trigger] prev_link_ok(log, prev, p))
}

/// Any key occurring in a log has a LAST occurrence: walk down from the
/// highest occurrence. The bridge from "the log mentions this key" to
/// `index_agrees`'s last-occurrence hypothesis, which is what turns an absent
/// index entry into "the log does not mention this key at all".
pub proof fn lemma_last_occurrence_exists<K, V>(log: Seq<(K, V)>, i: int)
    requires
        0 <= i < log.len(),
    ensures
        exists|q: int| #[trigger] is_last_occurrence(log, q) && log[q].0 == log[i].0,
    decreases log.len() - i,
{
    if is_last_occurrence(log, i) {
        assert(is_last_occurrence(log, i) && log[i].0 == log[i].0);
    } else {
        let j = choose|j: int| i < j < log.len() && (#[trigger] log[j]).0 == log[i].0;
        lemma_last_occurrence_exists(log, j);
        let q = choose|q: int| #[trigger] is_last_occurrence(log, q) && log[q].0 == log[j].0;
        assert(is_last_occurrence(log, q) && log[q].0 == log[i].0);
    }
}

/// A key absent from an agreeing index is absent from the log: an occurrence
/// would have a last occurrence, which `index_agrees` would have indexed.
pub proof fn lemma_absent_from_index_absent_from_log<K, V, I: IndexLike>(
    log: Seq<(K, V)>,
    m: Map<K, I>,
    key: K,
)
    requires
        index_agrees_seq(log, m),
        !m.contains_key(key),
    ensures
        forall|j: int| 0 <= j < log.len() ==> (#[trigger] log[j]).0 != key,
{
    assert forall|j: int| 0 <= j < log.len() implies (#[trigger] log[j]).0 != key by {
        if log[j].0 == key {
            lemma_last_occurrence_exists::<K, V>(log, j);
            let q = choose|q: int| #[trigger] is_last_occurrence(log, q) && log[q].0 == log[j].0;
            assert(m.contains_key(log[q].0));
        }
    }
}

/// Appending a key absent from a key-distinct log keeps its keys distinct.
proof fn lemma_append_fresh_keys_unique<K, V>(old_log: Seq<(K, V)>, key: K, val: V)
    requires
        keys_unique(old_log),
        forall|j: int| 0 <= j < old_log.len() ==> (#[trigger] old_log[j]).0 != key,
    ensures
        keys_unique(old_log.push((key, val))),
{
    let log = old_log.push((key, val));
    assert forall|i: int, j: int| 0 <= i < j < log.len()
        implies (#[trigger] log[i]).0 != (#[trigger] log[j]).0 by {
        assert(log[i] == old_log[i]);
        if j < old_log.len() {
            assert(log[j] == old_log[j]);
        } else {
            assert(log[j] == (key, val));
        }
    }
}

/// Full agreement is prefix agreement at the log's own length.
proof fn lemma_index_agrees_prefix_full<K, V, I: IndexLike>(log: Seq<(K, V)>, m: Map<K, I>)
    requires index_agrees_seq(log, m),
    ensures index_agrees_prefix_seq(log, m, log.len() as int),
{
    let n = log.len() as int;
    assert forall|p: int| #[trigger] is_last_occurrence_prefix(log, p, n)
        implies m.contains_key(log[p].0) && m[log[p].0].as_nat() == p by {
        assert(is_last_occurrence(log, p));
    }
    assert forall|k: K| #[trigger] m.contains_key(k)
        implies m[k].as_nat() < n && log[m[k].as_nat() as int].0 == k
            && is_last_occurrence_prefix(log, m[k].as_nat() as int, n) by {
        assert(is_last_occurrence(log, m[k].as_nat() as int));
    }
}

/// Prefix agreement survives truncation to its bound: once the log is cut to
/// `bound`, agreement on `[0, bound)` is full agreement.
proof fn lemma_index_agrees_after_truncate<K, V, I: IndexLike>(log: Seq<(K, V)>, m: Map<K, I>, bound: int)
    requires index_agrees_prefix_seq(log, m, bound),
    ensures index_agrees_seq(log.subrange(0, bound), m),
{
    let log2 = log.subrange(0, bound);
    assert forall|i: int| #[trigger] is_last_occurrence(log2, i)
        implies m.contains_key(log2[i].0) && m[log2[i].0].as_nat() == i by {
        assert forall|j: int| i < j < bound implies (#[trigger] log[j]).0 != log[i].0 by {
            assert(log2[j] == log[j]);
            assert(log2[i] == log[i]);
        }
        assert(is_last_occurrence_prefix(log, i, bound));
        assert(log2[i] == log[i]);
    }
    assert forall|k: K| #[trigger] m.contains_key(k)
        implies m[k].as_nat() < log2.len() && log2[m[k].as_nat() as int].0 == k
            && is_last_occurrence(log2, m[k].as_nat() as int) by {
        let pos = m[k].as_nat() as int;
        assert(is_last_occurrence_prefix(log, pos, bound));
        assert(log2[pos] == log[pos]);
        assert forall|j: int| pos < j < log2.len() implies (#[trigger] log2[j]).0 != log2[pos].0 by {
            assert(log2[j] == log[j]);
        }
    }
}

/// A chain link depends only on the log up to its own position, so it is
/// stable under any change beyond it (an append, a truncation above it).
proof fn lemma_prev_link_stable<K, V, I: IndexLike>(
    log1: Seq<(K, V)>,
    prev1: Seq<Option<I>>,
    log2: Seq<(K, V)>,
    prev2: Seq<Option<I>>,
    p: int,
)
    requires
        0 <= p < log1.len(),
        p < log2.len(),
        p < prev1.len(),
        p < prev2.len(),
        forall|j: int| 0 <= j <= p ==> #[trigger] log2[j] == log1[j],
        prev2[p] == prev1[p],
        prev_link_ok(log1, prev1, p),
    ensures
        prev_link_ok(log2, prev2, p),
{
    assert(log2[p] == log1[p]);
    match prev1[p] {
        Some(q) => {
            let qi = q.as_nat() as int;
            assert(log2[qi] == log1[qi]);
            assert forall|j: int| qi < j < p implies (#[trigger] log2[j]).0 != log2[qi].0 by {
                assert(log2[j] == log1[j]);
            }
        }
        None => {
            assert forall|j: int| 0 <= j < p implies (#[trigger] log2[j]).0 != log2[p].0 by {
                assert(log2[j] == log1[j]);
            }
        }
    }
}

/// The `prev` column of a truncated log is the truncated `prev` column.
proof fn lemma_prev_agrees_after_truncate<K, V, I: IndexLike>(log: Seq<(K, V)>, prev: Seq<Option<I>>, bound: int)
    requires
        prev_agrees_seq(log, prev),
        0 <= bound <= log.len(),
    ensures
        prev_agrees_seq(log.subrange(0, bound), prev.subrange(0, bound)),
{
    let log2 = log.subrange(0, bound);
    let prev2 = prev.subrange(0, bound);
    assert forall|p: int| 0 <= p < log2.len() implies #[trigger] prev_link_ok(log2, prev2, p) by {
        assert(prev_link_ok(log, prev, p));
        assert forall|j: int| 0 <= j <= p implies #[trigger] log2[j] == log[j] by {}
        assert(prev2[p] == prev[p]);
        lemma_prev_link_stable(log, prev, log2, prev2, p);
    }
}

/// `insert`'s chain maintenance: appending `(key, val)` and recording the
/// index's former answer for `key` as the new entry's link keeps the whole
/// Appending an entry whose key does not occur in the log preserves index
/// agreement. The fresh-key specialization of what `insert` proves inline: no
/// position loses its last-occurrence status, because the new tail's key is
/// absent from the prefix, and the new tail is that key's last occurrence.
pub proof fn lemma_append_fresh_preserves_index<K, V, I: IndexLike>(
    old_log: Seq<(K, V)>,
    old_index: Map<K, I>,
    key: K,
    val: V,
    id: I,
)
    requires
        index_agrees_seq(old_log, old_index),
        forall|j: int| 0 <= j < old_log.len() ==> (#[trigger] old_log[j]).0 != key,
        id.as_nat() == old_log.len(),
    ensures
        index_agrees_seq(old_log.push((key, val)), old_index.insert(key, id)),
{
    let log = old_log.push((key, val));
    let m = old_index.insert(key, id);
    let idn = id.as_nat() as int;
    assert(log[idn] == (key, val));
    assert(is_last_occurrence(log, idn));
    assert forall|i: int| #[trigger] is_last_occurrence(log, i)
        implies m.contains_key(log[i].0) && m[log[i].0].as_nat() == i by {
        if i == idn {
            assert(m[key] == id);
        } else {
            assert(log[i] == old_log[i]);
            assert(log[i].0 != key);
            assert(is_last_occurrence(old_log, i)) by {
                assert forall|j: int| i < j < old_log.len()
                    implies (#[trigger] old_log[j]).0 != old_log[i].0 by {
                    assert(old_log[j] == log[j]);
                }
            }
            assert(old_index.contains_key(log[i].0));
            assert(old_index[log[i].0].as_nat() == i);
            assert(m[log[i].0] == old_index[log[i].0]);
        }
    }
    assert forall|k: K| #[trigger] m.contains_key(k)
        implies m[k].as_nat() < log.len() && log[m[k].as_nat() as int].0 == k
            && is_last_occurrence(log, m[k].as_nat() as int) by {
        if k == key {
            assert(m[k] == id);
        } else {
            assert(m[k] == old_index[k]);
            assert(old_index.contains_key(k));
            let p = old_index[k].as_nat() as int;
            assert(is_last_occurrence(old_log, p));
            assert(log[p] == old_log[p]);
            assert forall|j: int| p < j < log.len() implies (#[trigger] log[j]).0 != log[p].0 by {
                if j < old_log.len() {
                    assert(log[j] == old_log[j]);
                } else {
                    assert(log[j] == (key, val));
                    assert(log[p].0 == k);
                }
            }
        }
    }
}

/// column agreeing. The former answer is `key`'s last occurrence in the old log
/// (index agreement), or `None` exactly when the old log never mentions `key`.
proof fn lemma_insert_prev_link<K, V, I: IndexLike>(
    old_log: Seq<(K, V)>,
    old_prev: Seq<Option<I>>,
    old_m: Map<K, I>,
    log: Seq<(K, V)>,
    prev: Seq<Option<I>>,
    shadowed: Option<I>,
)
    requires
        prev_agrees_seq(old_log, old_prev),
        index_agrees_seq(old_log, old_m),
        log.len() == old_log.len() + 1,
        forall|j: int| 0 <= j < old_log.len() ==> #[trigger] log[j] == old_log[j],
        prev == old_prev.push(shadowed),
        match shadowed {
            Some(q) => old_m.contains_key(log[old_log.len() as int].0)
                && q == old_m[log[old_log.len() as int].0],
            None => !old_m.contains_key(log[old_log.len() as int].0),
        },
    ensures
        prev_agrees_seq(log, prev),
{
    let idn = old_log.len() as int;
    let key = log[idn].0;
    assert forall|p: int| 0 <= p < log.len() implies #[trigger] prev_link_ok(log, prev, p) by {
        if p == idn {
            match shadowed {
                Some(q) => {
                    let qi = q.as_nat() as int;
                    assert(is_last_occurrence(old_log, qi));
                    assert(log[qi] == old_log[qi]);
                    assert forall|j: int| qi < j < idn implies (#[trigger] log[j]).0 != log[qi].0 by {
                        assert(log[j] == old_log[j]);
                    }
                }
                None => {
                    assert forall|j: int| 0 <= j < idn implies (#[trigger] log[j]).0 != key by {
                        if log[j].0 == key {
                            assert(old_log[j].0 == key);
                            lemma_last_occurrence_exists(old_log, j);
                            let q = choose|q: int| #[trigger] is_last_occurrence(old_log, q)
                                && old_log[q].0 == old_log[j].0;
                            assert(old_m.contains_key(old_log[q].0));
                            assert(false);
                        }
                    }
                }
            }
        } else {
            assert(prev_link_ok(old_log, old_prev, p));
            assert(prev[p] == old_prev[p]);
            lemma_prev_link_stable(old_log, old_prev, log, prev, p);
        }
    }
}

/// One `unwind_index` step. With the index agreeing on `[0, bound)`, the entry
/// at `bound - 1` is the last occurrence of its key there, so pointing that key
/// at the entry's chain link (or dropping it when the link is `None`) leaves the
/// index agreeing on `[0, bound - 1)`.
proof fn lemma_unwind_step<K, V, I: IndexLike>(
    log: Seq<(K, V)>,
    prev: Seq<Option<I>>,
    m0: Map<K, I>,
    m1: Map<K, I>,
    bound: int,
)
    requires
        1 <= bound <= log.len(),
        prev.len() == log.len(),
        prev_link_ok(log, prev, bound - 1),
        index_agrees_prefix_seq(log, m0, bound),
        m1 == (match prev[bound - 1] {
            Some(q) => m0.insert(log[bound - 1].0, q),
            None => m0.remove(log[bound - 1].0),
        }),
    ensures
        index_agrees_prefix_seq(log, m1, bound - 1),
{
    let p = bound - 1;
    let k = log[p].0;
    assert(is_last_occurrence_prefix(log, p, bound));
    assert(m0.contains_key(k) && m0[k].as_nat() == p);
    // (1) Every last occurrence within [0, p) is indexed at itself.
    assert forall|r: int| #[trigger] is_last_occurrence_prefix(log, r, p)
        implies m1.contains_key(log[r].0) && m1[log[r].0].as_nat() == r by {
        if log[r].0 == k {
            match prev[p] {
                Some(q) => {
                    let qi = q.as_nat() as int;
                    // `r` and `q` are both the last occurrence of `k` in [0, p).
                    if r < qi {
                        assert(log[qi].0 != log[r].0);
                        assert(false);
                    }
                    if qi < r {
                        assert(log[r].0 != log[qi].0);
                        assert(false);
                    }
                    assert(m1[k] == q);
                }
                None => {
                    assert(log[r].0 != log[p].0);
                    assert(false);
                }
            }
        } else {
            // `r < p` and `log[p].0 != log[r].0`: `r` is last within [0, bound) too.
            assert forall|j: int| r < j < bound implies (#[trigger] log[j]).0 != log[r].0 by {
                if j == p {
                    assert(log[j].0 == k);
                }
            }
            assert(is_last_occurrence_prefix(log, r, bound));
            assert(m0.contains_key(log[r].0) && m0[log[r].0].as_nat() == r);
            assert(m1.contains_key(log[r].0) && m1[log[r].0] == m0[log[r].0]);
        }
    }
    // (2) Every indexed key points at its last occurrence within [0, p).
    assert forall|kk: K| #[trigger] m1.contains_key(kk)
        implies m1[kk].as_nat() < p && log[m1[kk].as_nat() as int].0 == kk
            && is_last_occurrence_prefix(log, m1[kk].as_nat() as int, p) by {
        if kk == k {
            match prev[p] {
                Some(q) => {
                    assert(m1[k] == q);
                }
                None => {
                    assert(!m1.contains_key(k));
                    assert(false);
                }
            }
        } else {
            assert(m0.contains_key(kk) && m1[kk] == m0[kk]);
            let pos = m0[kk].as_nat() as int;
            assert(pos < bound && log[pos].0 == kk && is_last_occurrence_prefix(log, pos, bound));
            assert(pos != p);
            assert forall|j: int| pos < j < p implies (#[trigger] log[j]).0 != log[pos].0 by {}
        }
    }
}

/// Clone a map key, with the clone PROVABLY identical to the original.
///
/// This is requirement (3) of vstd's hash-table key model — "the executable
/// `Key::clone` function produces a result identical to its input" — which
/// `SpMap` already assumes for every key type via `obeys_key_model::<K>()`
/// (`new`'s precondition, threaded through `wf`). vstd states that
/// requirement in prose on the `uninterp obeys_key_model` and provides no
/// lemma projecting it out, so this helper carries it as its contract:
/// `external_body`, trusted content exactly = key-model requirement (3),
/// no NEW assumption beyond what `obeys_key_model` already asserts.
/// Trust ledger: group D (key-model facts).
#[verifier::external_body]
fn clone_key_exact<K: Clone>(key: &K) -> (r: K)
    requires obeys_key_model::<K>(),
    ensures r == *key,
{
    key.clone()
}

} // verus!

// prod-parity: production derives `Debug` on `Map`; the consumer's registries and
// literal stores hold an `SpMap` in a `#[derive(Debug)]` struct
// (`egraph/src/registry.rs`, `literal.rs`). Manual because deriving inside
// `verus!{}` is unsupported. Prints the live entries via the public `iter`
// (the log is the source of truth); shadowed/overwritten log entries are not
// shown, matching the map's logical contents.
impl<K, V, I: IndexLike, const TRACK: bool, const UNIQUE: bool, S: ValidHasher> core::fmt::Debug
    for SpMap<K, V, I, TRACK, UNIQUE, S>
where
    K: Clone + core::hash::Hash + Eq + core::fmt::Debug,
    V: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // Production's shape: counters, not entries. (Printing entries walks
        // the log and shows shadowed keys twice; production avoids both.)
        f.debug_struct("SpMap")
            .field("len", &self.len())
            .field("log_len", &self.log_len().as_usize())
            .finish()
    }
}

impl<K, V, I: IndexLike, const TRACK: bool, const UNIQUE: bool, S: ValidHasher> Default
    for SpMap<K, V, I, TRACK, UNIQUE, S>
where
    K: Clone + core::hash::Hash + Eq,
{
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Trusted glue (outside verus!{}; trust ledger group E): log iteration in
// insertion order, including overwritten shadows (production `Map::iter`
// semantics). Delegates to the verified AppendOnlyVec::as_slice.
// ---------------------------------------------------------------------------

impl<K, V, I: IndexLike, const TRACK: bool, const UNIQUE: bool, S: ValidHasher>
    SpMap<K, V, I, TRACK, UNIQUE, S>
where
    K: Clone + std::hash::Hash + Eq,
{
    /// Iterate over the log entries in insertion order, including shadows
    /// (production parity: production's `Map::iter` also yields shadows).
    #[inline(always)]
    pub fn iter(&self) -> core::slice::Iter<'_, (K, V)> {
        self.log.as_slice().iter()
    }
}
