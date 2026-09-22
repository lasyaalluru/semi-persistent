// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Store policy for the composite containers.
//!
//! Every tracked column of a composite (`UnionFind`'s forest, `SparseSet`'s
//! index columns, the list and ring arenas, the B+ tree's nodes, the e-class
//! table) is a [`crate::vec::Vec`] over some `DiffStore`. Which store fits
//! depends on the workload, not on the composite: a column that is written
//! many times per frame and restored rarely (equality saturation, which
//! iterates rewrite rounds to a fixpoint between marks) wants the Hot-first
//! stores, whose first-capture dedupe keeps one saved word per touched slot;
//! a column that is marked and restored constantly with few writes per frame
//! (SMT-style backtracking) wants the Trail store, whose append-only ingress
//! costs no lookup per write.
//!
//! A composite therefore takes a POLICY type parameter `P`, defaulting to
//! [`HotFirst`] (today's choices), and builds each column through
//! `Vec::with_store(P::empty())`. The policy is looked up per column through
//! one of two families, chosen by the column's element type — plain traits,
//! no generic associated types, no specialization:
//!
//! - [`TaggedFamily`] for a column whose element type is [`Tagged`] (carries
//!   a spare tag bit), where `HotFirst` picks the `InlineStore`;
//! - [`PlainFamily`] for any other `Copy` element, where `HotFirst` picks the
//!   `ParallelStore` (flag vector).
//!
//! [`TrailFirst`] picks the `TrailStore` for both. Nothing observable changes
//! under the default; a consumer that knows its workload names the policy.

use vstd::prelude::*;

verus! {

use crate::diff_store::DiffStore;
use crate::diff_store_ops::DiffStoreOps;
use crate::index_like::IndexLike;
use crate::tagged::Tagged;

/// Chooses the store of a column whose element type is [`Tagged`].
pub trait TaggedFamily<T: Tagged, I: IndexLike, const TRACK: bool> {
    /// The store this policy builds for such a column. `Send`, like every
    /// concrete store, because consumers fan mark/restore out across threads.
    type Store: DiffStore<T, I, TRACK> + Send;

    /// An empty store, ready for `Vec::with_store`.
    fn empty() -> (s: Self::Store)
        ensures
            s.wf(),
            s.data().len() == 0;
}

/// Chooses the store of a column with any `Copy` element type.
pub trait PlainFamily<T: Sized + Copy, I: IndexLike, const TRACK: bool> {
    /// The store this policy builds for such a column (`Send`, as above).
    type Store: DiffStore<T, I, TRACK> + Send;

    /// An empty store, ready for `Vec::with_store`.
    fn empty() -> (s: Self::Store)
        ensures
            s.wf(),
            s.data().len() == 0;
}

/// Hot-first ingress: `InlineStore` for tagged columns, `ParallelStore`
/// otherwise — the composites' choices before policies existed. Fits
/// workloads with many writes per frame (equality saturation).
pub struct HotFirst;

/// Trail-first ingress: `TrailStore` for every column. Fits workloads that
/// mark and restore far more often than they write (SMT-style backtracking).
pub struct TrailFirst;

impl<T: Tagged, I: IndexLike, const TRACK: bool> TaggedFamily<T, I, TRACK> for HotFirst {
    type Store = crate::inline_store::InlineStore<T, I>;

    fn empty() -> (s: Self::Store) {
        crate::inline_store::InlineStore::new()
    }
}

impl<T: Sized + Copy + Send, I: IndexLike, const TRACK: bool> PlainFamily<T, I, TRACK> for HotFirst {
    type Store = crate::parallel_store::ParallelStore<T, I>;

    fn empty() -> (s: Self::Store) {
        crate::parallel_store::ParallelStore::new()
    }
}

impl<T: Tagged + Send, I: IndexLike, const TRACK: bool> TaggedFamily<T, I, TRACK> for TrailFirst {
    type Store = crate::trail_store::TrailStore<T, I>;

    fn empty() -> (s: Self::Store) {
        crate::trail_store::TrailStore::new()
    }
}

impl<T: Sized + Copy + Send, I: IndexLike, const TRACK: bool> PlainFamily<T, I, TRACK> for TrailFirst {
    type Store = crate::trail_store::TrailStore<T, I>;

    fn empty() -> (s: Self::Store) {
        crate::trail_store::TrailStore::new()
    }
}

/// An empty tracked vector over the store the policy `P` chooses for a
/// tagged column: the public, total form of `Vec::with_store(P::empty())`
/// for consumers that build their own policy-parameterized columns.
pub fn tagged_vec<T: Tagged, I: IndexLike, const TRACK: bool, P: TaggedFamily<T, I, TRACK>>()
    -> (v: crate::vec::Vec<T, I, P::Store, TRACK>)
    ensures
        v.wf(),
        v.view().len() == 0,
        v.snapshots_view().len() == 0,
{
    crate::vec::Vec::with_store(P::empty())
}

/// An empty tracked vector over the store the policy `P` chooses for a plain
/// column.
pub fn plain_vec<T: Sized + Copy, I: IndexLike, const TRACK: bool, P: PlainFamily<T, I, TRACK>>()
    -> (v: crate::vec::Vec<T, I, P::Store, TRACK>)
    ensures
        v.wf(),
        v.view().len() == 0,
        v.snapshots_view().len() == 0,
{
    crate::vec::Vec::with_store(P::empty())
}

} // verus!
