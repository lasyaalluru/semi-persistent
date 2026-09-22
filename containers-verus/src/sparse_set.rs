// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent sparse set with stable IDs, composed from three verified
//! `Vec`s:
//!   - `dense`:   packed values `[0, n)`, no gaps   (`Vec<T, Idx, S>`)
//!   - `sparse`:  id → position                      (`Vec<Idx, Idx, P::Store>`)
//!   - `indices`: position → id                      (`Vec<Idx, Idx, P::Store>`)
//!
//! The two index columns take their store from the policy parameter `P`
//! (`crate::store_policy`; the default `HotFirst` gives `InlineStore`, as
//! before). The proofs use only the `Vec` contract, so every policy fits.
//!
//! ## The real invariant (`wf`)
//! Let `cap = sparse.len() = indices.len()`, `n = dense.len() <= cap`.
//!   1. `indices` is a PERMUTATION of `[0, cap)`: each `indices[p] < cap`, and
//!      `indices` is injective (hence bijective position→id).
//!   2. INVERSE-ON-LIVE: for live positions `p in [0, n)`,
//!      `sparse[indices[p]] == p`.
//! Positions `[n, cap)` are the FREE region — recently-removed ids parked for
//! recycling; their `sparse` entries may be stale, which is harmless because
//! injectivity (1) stops a free id from passing the liveness test.
//!
//! From this:
//!   - **liveness**: `contains(id) = id<cap && sparse[id]<n &&
//!     indices[sparse[id]]==id` holds iff `id` is some `indices[p]` with `p<n`
//!     (proved: a free id fails the test by injectivity).
//!   - **stable identity**: a live id's value is `dense[sparse[id]]`; other
//!     ops keep that mapping (remove's swap updates `sparse[last_id]`).
//!   - **id recycling**: `remove` parks the freed id at `indices[n-1]`; `add`
//!     recycles exactly `indices[n]` and repairs its `sparse` entry.
//!   - **semi-persistence**: `mark`/`restore` delegate to the three inner
//!     vectors; restore composition gives back the marked state.
//!
//! Inherits the crate's `Copy + Default` convention (dense `T` and `Idx` both
//! need `Default` for `Vec::restore`'s resize regrow).

use vstd::prelude::*;

use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;
use crate::store_policy::{HotFirst, TaggedFamily};
use crate::tagged::Tagged;
use crate::vec::{ShrinkPolicy, Vec as SpVec, VecToken};

verus! {

/// Semi-persistent sparse set with stable IDs.
pub struct SparseSet<T, Idx, S, const TRACK: bool = true, VC = crate::value_compressor::NoValueCompression, P = HotFirst>
where
    T: Sized + Copy,
    Idx: IndexLike + Tagged,
    S: DiffStore<T, Idx, TRACK>,
    VC: crate::value_compressor::ValueCompressor<T>,
    P: TaggedFamily<Idx, Idx, TRACK>,
{
    pub(crate) dense: SpVec<T, Idx, S, TRACK, VC>,
    pub(crate) sparse: SpVec<Idx, Idx, <P as TaggedFamily<Idx, Idx, TRACK>>::Store, TRACK>,
    pub(crate) indices: SpVec<Idx, Idx, <P as TaggedFamily<Idx, Idx, TRACK>>::Store, TRACK>,
}

impl<T, Idx, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>, P> SparseSet<T, Idx, S, TRACK, VC, P>
where
    T: Sized + Copy,
    Idx: IndexLike + Tagged,
    S: DiffStore<T, Idx, TRACK>,
    P: TaggedFamily<Idx, Idx, TRACK>,
{
    /// The packed values currently in the set, in dense order.
    pub open(crate) spec fn dense_view(&self) -> Seq<T> {
        self.dense.view()
    }

    pub open(crate) spec fn cap_spec(&self) -> nat {
        self.sparse.view().len()
    }

    /// Sparse column (spec counterpart; fields are `pub(crate)` — privacy closeout).
    pub open(crate) spec fn indices_view(&self) -> Seq<Idx> {
        self.indices.view()
    }

    pub open(crate) spec fn sparse_snapshots_view(&self) -> Seq<Seq<Idx>> {
        self.sparse.snapshots_view()
    }

    pub open(crate) spec fn indices_snapshots_view(&self) -> Seq<Seq<Idx>> {
        self.indices.snapshots_view()
    }

    pub open(crate) spec fn dense_depth_spec(&self) -> nat {
        self.dense.depth_spec()
    }

    pub open(crate) spec fn sparse_depth_spec(&self) -> nat {
        self.sparse.depth_spec()
    }

    pub open(crate) spec fn indices_depth_spec(&self) -> nat {
        self.indices.depth_spec()
    }

    pub open(crate) spec fn sparse_view(&self) -> Seq<Idx> {
        self.sparse.view()
    }

    /// Dense-column reference (spec counterpart, for `data()`'s ensures).
    pub open(crate) spec fn dense_ref(&self) -> &SpVec<T, Idx, S, TRACK, VC> {
        &self.dense
    }


    /// Composite mark preconditions (headrooms on all three columns).
    pub open(crate) spec fn can_mark_spec(&self) -> bool {
        &&& self.dense.view().len() < Idx::max_nat()
        &&& self.sparse.view().len() < Idx::max_nat()
        &&& self.indices.view().len() < Idx::max_nat()
        &&& self.dense.depth_spec() < u32::MAX
        &&& self.sparse.depth_spec() < u32::MAX
        &&& self.indices.depth_spec() < u32::MAX
    }



    /// Dense snapshot stack (spec counterpart).
    pub open(crate) spec fn dense_snapshots_view(&self) -> Seq<Seq<T>> {
        self.dense.snapshots_view()
    }

    /// Add-capacity headroom (spec counterpart for `add`'s requires).
    pub open(crate) spec fn can_add_spec(&self) -> bool {
        &&& self.dense.view().len() + 1 < Idx::max_nat()
        &&& self.sparse.view().len() + 1 < Idx::max_nat()
        &&& self.indices.view().len() + 1 < Idx::max_nat()
    }

    pub open(crate) spec fn n_spec(&self) -> nat {
        self.dense.view().len()
    }

    /// The structural sparse-set invariant (permutation + inverse-on-live),
    /// on top of the three inner vectors' own well-formedness.
    pub open(crate) spec fn wf(&self) -> bool {
        let sparse = self.sparse.view();
        let indices = self.indices.view();
        let cap = self.cap_spec();
        let n = self.n_spec();
        &&& self.dense.wf()
        &&& self.sparse.wf()
        &&& self.indices.wf()
        // Archive (total `restore`): the three snapshot stacks move in lockstep
        // and every archived triple is itself a valid sparse-set state, so a
        // restore needs only per-column token validity plus equal frame
        // indices — both runtime-checkable — to land in a `wf` state.
        &&& self.sparse.snapshots_view().len() == self.dense.snapshots_view().len()
        &&& self.indices.snapshots_view().len() == self.dense.snapshots_view().len()
        &&& (forall|k: int| 0 <= k < self.dense.snapshots_view().len() ==>
                sparse_set_snap_wf(#[trigger] self.dense.snapshots_view()[k],
                    self.sparse.snapshots_view()[k], self.indices.snapshots_view()[k]))
        &&& indices.len() == cap
        &&& n <= cap
        // (1a) indices in range [0, cap)
        &&& (forall|p: int| 0 <= p < cap ==> (#[trigger] indices[p]).as_nat() < cap)
        // (1b) indices injective ⇒ permutation of [0, cap)
        &&& (forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q ==>
                (#[trigger] indices[p]).as_nat() != (#[trigger] indices[q]).as_nat())
        // (2) inverse on the live region [0, n)
        &&& (forall|p: int| 0 <= p < n ==>
                sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p)
    }

    /// `id` is live: allocated, its position is in `[0, n)`, and the position
    /// maps back to it. (Proved equivalent to "id == indices[p] for p < n".)
    pub open(crate) spec fn contains_spec(&self, id: Idx) -> bool {
        let sparse = self.sparse.view();
        let indices = self.indices.view();
        let n = self.n_spec();
        &&& id.as_nat() < sparse.len()
        &&& sparse[id.as_nat() as int].as_nat() < n
        &&& indices[sparse[id.as_nat() as int].as_nat() as int].as_nat() == id.as_nat()
    }

    // ===================================================================
    // Abstraction: the sparse set IS a ghost set of live ids together with a
    // hand-rolled index pool of recycled ids (user-requested refinement). The
    // permutation invariant (`wf`) is exactly what makes this abstraction sound.
    // ===================================================================

    /// The abstract set of live ids: the image of `indices` over `[0, n)`.
    ///
    /// `ISet`, not `Set`: since vstd made `Set` inherently finite, its
    /// comprehension constructor returns `Option<Set>` (`None` on an infinite
    /// predicate). `ISet::new` is total with the same membership axiom the old
    /// `Set::new` had, so the comprehension layer uses `ISet` and finiteness
    /// stays where it always was — a proved property (`lemma_image_prefix_card`),
    /// not a construction obligation.
    pub open(crate) spec fn id_set(&self) -> ISet<nat> {
        let indices = self.indices.view();
        ISet::new(|id: nat| exists|p: int| 0 <= p < self.n_spec()
            && (#[trigger] indices[p]).as_nat() == id)
    }

    /// The index pool of recycled-but-not-reallocated ids: `indices[n .. cap)`,
    /// as a sequence (the parking order; `add` reuses the slot at position `n`,
    /// `remove` parks at `n-1`). Its multiset is the free ids.
    pub open(crate) spec fn free_pool(&self) -> Seq<nat> {
        let indices = self.indices.view();
        Seq::new((self.cap_spec() - self.n_spec()) as nat,
            |k: int| indices[self.n_spec() as int + k].as_nat())
    }

    /// Membership refinement: the runtime liveness test decides exactly the
    /// abstract set. (⟸ uses inverse-on-live; ⟹ uses the round-trip test.)
    pub(crate) proof fn lemma_contains_iff_id_set(&self, id: Idx)
        requires self.wf(),
        ensures self.contains_spec(id) <==> self.id_set().contains(id.as_nat()),
    {
        let indices = self.indices.view();
        let sparse = self.sparse.view();
        let n = self.n_spec();
        if self.contains_spec(id) {
            // position p = sparse[id] < n witnesses membership.
            let p = sparse[id.as_nat() as int].as_nat() as int;
            assert(0 <= p < n && indices[p].as_nat() == id.as_nat());
        }
        if self.id_set().contains(id.as_nat()) {
            // some p<n has indices[p]==id; inverse-on-live ⇒ sparse[id]==p<n,
            // and indices[sparse[id]]==indices[p]==id ⇒ contains_spec.
            let p = choose|p: int| 0 <= p < n && (#[trigger] indices[p]).as_nat() == id.as_nat();
            assert(sparse[indices[p].as_nat() as int].as_nat() == p);  // inverse
            assert(id.as_nat() < sparse.len());  // id == indices[p] < cap == sparse.len()
        }
    }

    /// Set and pool are DISJOINT and together exhaust the allocated id space:
    /// every id in `[0, cap)` is either live or free, never both. (Direct from
    /// the permutation invariant: `indices` bijects positions to ids, the live
    /// positions `[0,n)` give the set, the free positions `[n,cap)` give the
    /// pool.)
    pub(crate) proof fn lemma_set_pool_partition(&self)
        requires self.wf(),
        ensures
            // disjoint
            forall|id: nat| self.id_set().contains(id) ==> !self.free_pool().contains(id),
            // every allocated id is in exactly one
            forall|id: nat| id < self.cap_spec() ==>
                (self.id_set().contains(id) || self.free_pool().contains(id)),
    {
        let indices = self.indices.view();
        let n = self.n_spec();
        let cap = self.cap_spec();
        // disjoint: a live id has a witness p<n; a pooled id has witness k with
        // position n+k >= n. Same id at two positions violates injectivity.
        assert forall|id: nat| self.id_set().contains(id) implies
            !self.free_pool().contains(id) by {
            let p = choose|p: int| 0 <= p < n && (#[trigger] indices[p]).as_nat() == id;
            if self.free_pool().contains(id) {
                let k = choose|k: int| 0 <= k < (cap - n)
                    && (#[trigger] self.free_pool()[k]) == id;
                assert(indices[n + k].as_nat() == id);
                assert(p != n + k);  // p < n <= n+k
                // injectivity: indices[p] != indices[n+k], contradiction.
                assert(indices[p].as_nat() != indices[n + k].as_nat());
            }
        }
        // exhaustive: id < cap. By surjectivity of the permutation (in-range +
        // injective on a finite set ⇒ bijective), id == indices[p] for some
        // p < cap; p < n ⇒ live, else pooled.
        assert forall|id: nat| id < cap implies
            (self.id_set().contains(id) || self.free_pool().contains(id)) by {
            lemma_perm_surjective(indices, cap as int, id);
            let p = choose|p: int| 0 <= p < cap && (#[trigger] indices[p]).as_nat() == id;
            if p < n {
                assert(self.id_set().contains(id));
            } else {
                assert(self.free_pool()[p - n] == id);
                assert(self.free_pool().contains(id));
            }
        }
    }

    pub fn len(&self) -> (n: Idx)
        requires self.wf(),
        ensures n.as_nat() == self.dense_view().len(),
    {
        self.dense.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.dense_view().len() == 0),
    {
        self.dense.is_empty()
    }

    /// Liveness test. Returns exactly `contains_spec(id)`.
    pub fn contains(&self, id: Idx) -> (b: bool)
        requires self.wf(),
        ensures b == self.contains_spec(id),
    {
        let cap = self.sparse.len();
        if id.as_usize() >= cap.as_usize() {
            return false;
        }
        let pos = self.sparse.get_index(id);
        let nlen = self.dense.len();
        if pos.as_usize() >= nlen.as_usize() {
            return false;
        }
        let idx_at = self.indices.get_index(pos);
        idx_at.as_usize() == id.as_usize()
    }

    /// Value of a live id (through the stable indirection).
    pub fn get(&self, id: Idx) -> (v: T)
        requires self.wf(),
        ensures self.contains_spec(id)
            ==> v == self.dense_view()[self.sparse_view()[id.as_nat() as int].as_nat() as int],
    {
        // Total-with-documented-panic: liveness is an explicit branch. A dead
        // id previously read a stale dense slot silently (production asserts;
        // the verified core relied on the erased requires).
        if !self.contains(id) {
            crate::guard::refuse("SparseSet::get: id not present");
        }
        let pos = self.sparse.get_index(id);
        self.dense.get_index(pos)
    }

    /// Value of a live id whose liveness the caller has already established
    /// (pub(crate): the aggregate checks once, or holds it as a proof fact,
    /// and reads without the public form's re-check).
    pub(crate) fn get_live(&self, id: Idx) -> (v: T)
        requires
            self.wf(),
            self.contains_spec(id),
        ensures
            v == self.dense_view()[self.sparse_view()[id.as_nat() as int].as_nat() as int],
    {
        let pos = self.sparse.get_index(id);
        self.dense.get_index(pos)
    }

    /// Overwrite a live id's value, liveness already established (the
    /// pub(crate) counterpart of `set`, same effects without the re-check).
    pub(crate) fn set_live(&mut self, id: Idx, value: T)
        requires
            old(self).wf(),
            old(self).contains_spec(id),
        ensures
            final(self).wf(),
            final(self).cap_spec() == old(self).cap_spec(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).sparse_view() == old(self).sparse_view(),
            final(self).indices_view() == old(self).indices_view(),
            final(self).dense_view() == old(self).dense_view().update(
                old(self).sparse_view()[id.as_nat() as int].as_nat() as int, value),
            final(self).id_set() == old(self).id_set(),
            final(self).free_pool() == old(self).free_pool(),
            final(self).dense_snapshots_view() == old(self).dense_snapshots_view(),
            final(self).sparse_snapshots_view() == old(self).sparse_snapshots_view(),
            final(self).indices_snapshots_view() == old(self).indices_snapshots_view(),
    {
        let pos = self.sparse.get_index(id);
        self.dense.set_index(pos, value);
        proof {
            assert(self.sparse.view() == old(self).sparse.view());
            assert(self.indices.view() == old(self).indices.view());
            assert(self.dense.view().len() == old(self).dense.view().len());
        }
    }

    /// Overwrite a live id's value in place (position and id unchanged).
    pub fn set(&mut self, id: Idx, value: T)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            old(self).contains_spec(id) ==> {
                &&& final(self).cap_spec() == old(self).cap_spec()
                &&& final(self).n_spec() == old(self).n_spec()
                &&& final(self).sparse_view() == old(self).sparse_view()
                &&& final(self).indices_view() == old(self).indices_view()
                &&& final(self).dense_view() == old(self).dense_view().update(
                        old(self).sparse_view()[id.as_nat() as int].as_nat() as int, value)
                &&& final(self).id_set() == old(self).id_set()
                &&& final(self).free_pool() == old(self).free_pool()
            },
            // snapshot-stack framing (eclasses: the aggregate's archive is
            // keyed on the component stacks).
            final(self).dense_snapshots_view() == old(self).dense_snapshots_view(),
            final(self).sparse_snapshots_view() == old(self).sparse_snapshots_view(),
            final(self).indices_snapshots_view() == old(self).indices_snapshots_view(),
    {
        // Total-with-documented-panic: see `get`.
        if !self.contains(id) {
            crate::guard::refuse("SparseSet::set: id not present");
        }
        let pos = self.sparse.get_index(id);
        self.dense.set_index(pos, value);
        proof {
            // dense.set changes only dense's values, not lengths; sparse and
            // indices are untouched, so the permutation + inverse carry.
            assert(self.sparse.view() == old(self).sparse.view());
            assert(self.indices.view() == old(self).indices.view());
            assert(self.dense.view().len() == old(self).dense.view().len());
        }
    }

    /// Add a value, returning a stable id. If a free slot exists (`n < cap`),
    /// recycle the id parked at `indices[n]`; otherwise allocate a fresh id
    /// `== n`. The new element occupies dense position `n`.
    pub(crate) fn add(&mut self, value: T) -> (id: Idx)
        requires
            old(self).wf(),
            old(self).can_add_spec(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec() + 1,
            // the returned id is now live
            final(self).contains_spec(id),
            // ABSTRACT EFFECT: the live set gains exactly `id`, which was not
            // live before.
            !old(self).id_set().contains(id.as_nat()),
            final(self).id_set() =~= old(self).id_set().insert(id.as_nat()),
            // INDEX-POOL REUSE: if a free id was available, `add` recycles the
            // one parked at the pool front (LIFO with `remove`), and the pool
            // shrinks by that element; otherwise a fresh id `== old cap` is
            // allocated and the (empty) pool stays empty.
            old(self).free_pool().len() > 0 ==>
                (id.as_nat() == old(self).free_pool()[0]
                 && final(self).free_pool() =~= old(self).free_pool().drop_first()),
            old(self).free_pool().len() == 0 ==>
                (id.as_nat() == old(self).cap_spec() && final(self).free_pool().len() == 0),
            // capacity: recycling keeps it, a fresh id grows it by one, and
            // either way the minted id is within the old capacity.
            id.as_nat() <= old(self).cap_spec(),
            final(self).cap_spec() == if old(self).free_pool().len() == 0 {
                old(self).cap_spec() + 1
            } else {
                old(self).cap_spec()
            },
            // the stored value is readable back at the new id.
            final(self).dense_view()[
                final(self).sparse_view()[id.as_nat() as int].as_nat() as int] == value,
            // survivors: every previously live id stays live with its value.
            forall|k: Idx| #[trigger] old(self).contains_spec(k)
                ==> final(self).contains_spec(k)
                    && final(self).dense_view()[
                            final(self).sparse_view()[k.as_nat() as int].as_nat() as int]
                        == old(self).dense_view()[
                            old(self).sparse_view()[k.as_nat() as int].as_nat() as int],
            // snapshot-stack framing (eclasses: the aggregate's archive is
            // keyed on the component stacks).
            final(self).dense_snapshots_view() == old(self).dense_snapshots_view(),
            final(self).sparse_snapshots_view() == old(self).sparse_snapshots_view(),
            final(self).indices_snapshots_view() == old(self).indices_snapshots_view(),
    {
        let ghost old_n = self.dense.view().len();
        let ghost old_cap = self.sparse.view().len();
        let pos = self.dense.len();
        self.dense.push(value);

        let cap = self.sparse.len();
        if pos.as_usize() < cap.as_usize() {
            // Recycle: indices[pos] is the first free id (pos == old_n).
            let recycled_id = self.indices.get_index(pos);
            self.sparse.set_index(recycled_id, pos);
            proof {
                let sparse = self.sparse.view();
                let indices = self.indices.view();
                let n = self.dense.view().len();  // old_n + 1
                assert(indices == old(self).indices.view());
                assert(n == old_n + 1);
                assert(pos.as_nat() == old_n);
                // indices unchanged ⇒ permutation (1a,1b) carry.
                // inverse-on-live now needs to hold for p in [0, old_n+1):
                //  - p < old_n: indices[p] != recycled_id (= indices[old_n], and
                //    injectivity with p != old_n), so sparse[indices[p]] is
                //    unchanged == p (old inverse).
                //  - p == old_n: indices[old_n] == recycled_id and we just set
                //    sparse[recycled_id] = old_n == pos.
                assert forall|p: int| 0 <= p < n implies
                    sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p by {
                    if p == old_n as int {
                        assert(indices[p].as_nat() == recycled_id.as_nat());
                        assert(sparse[recycled_id.as_nat() as int].as_nat() == old_n);
                    } else {
                        assert(indices[p].as_nat() != indices[old_n as int].as_nat());
                        assert(indices[old_n as int].as_nat() == recycled_id.as_nat());
                        assert(sparse[indices[p].as_nat() as int]
                            == old(self).sparse.view()[indices[p].as_nat() as int]);
                    }
                }
                // returned id (recycled_id) is live: sparse[recycled_id]=old_n<n,
                // indices[old_n]==recycled_id.
                assert(recycled_id.as_nat() < old_cap);

                // --- abstract effect: set gains recycled_id, pool drops front.
                // indices unchanged, n: old_n -> old_n+1. id_set is the image of
                // [0,n); the only new position is old_n, whose value is
                // recycled_id == old free_pool[0].
                assert(old(self).free_pool().len() > 0);   // old_n < old_cap
                assert(old(self).free_pool()[0] == recycled_id.as_nat()) by {
                    assert(old(self).indices.view()[old_n as int].as_nat()
                        == recycled_id.as_nat());
                }
                assert(!old(self).id_set().contains(recycled_id.as_nat())) by {
                    // recycled_id at position old_n >= old_n; a live witness p
                    // would be < old_n, violating injectivity.
                    if old(self).id_set().contains(recycled_id.as_nat()) {
                        let p = choose|p: int| 0 <= p < old_n
                            && (#[trigger] old(self).indices.view()[p]).as_nat()
                                == recycled_id.as_nat();
                        assert(old(self).indices.view()[p].as_nat()
                            != old(self).indices.view()[old_n as int].as_nat());
                    }
                }
                assert(self.id_set() =~= old(self).id_set().insert(recycled_id.as_nat())) by {
                    assert forall|v: nat| #![auto] self.id_set().contains(v)
                        <==> old(self).id_set().insert(recycled_id.as_nat()).contains(v) by {
                        if self.id_set().contains(v) {
                            let p = choose|p: int| 0 <= p < n
                                && (#[trigger] indices[p]).as_nat() == v;
                            if p < old_n { } else { assert(v == recycled_id.as_nat()); }
                        }
                    }
                }
                assert(self.free_pool() =~= old(self).free_pool().drop_first()) by {
                    // both have length old_cap - old_n - 1; element k of the new
                    // pool is indices[(old_n+1)+k] == old pool element k+1.
                    assert(self.free_pool().len() == old(self).free_pool().drop_first().len());
                    assert forall|k: int| #![auto] 0 <= k < self.free_pool().len() implies
                        self.free_pool()[k] == old(self).free_pool().drop_first()[k] by {
                        assert(self.free_pool()[k] == indices[(old_n + 1) + k].as_nat());
                        assert(old(self).free_pool().drop_first()[k]
                            == old(self).free_pool()[k + 1]);
                    }
                }
            }
            recycled_id
        } else {
            // Fresh id == pos == old_n == old_cap.
            self.sparse.push(pos);
            self.indices.push(pos);
            proof {
                let sparse = self.sparse.view();
                let indices = self.indices.view();
                let cap = sparse.len();   // old_cap + 1
                let n = self.dense.view().len();  // old_n + 1, and old_n == old_cap
                assert(pos.as_nat() == old_n);
                assert(old_n == old_cap);
                assert(cap == old_cap + 1);
                assert(indices[old_cap as int].as_nat() == pos.as_nat() == old_cap);
                // (1a) in range: old entries < old_cap < cap; new entry == old_cap < cap.
                assert forall|p: int| 0 <= p < cap implies (#[trigger] indices[p]).as_nat() < cap by {
                    if p < old_cap { } else { assert(indices[p].as_nat() == old_cap); }
                }
                // (1b) injective: new value old_cap differs from all old (< old_cap).
                assert forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q implies
                    (#[trigger] indices[p]).as_nat() != (#[trigger] indices[q]).as_nat() by {
                    if p < old_cap && q < old_cap {
                    } else {
                        // one is the new slot (value old_cap), the other old (< old_cap).
                    }
                }
                // (2) inverse-on-live for [0, old_cap+1): old positions carry
                // (sparse extended, prefix unchanged); new position old_cap has
                // indices[old_cap]==old_cap and sparse[old_cap]==pos==old_cap.
                assert forall|p: int| 0 <= p < n implies
                    sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p by {
                    if p < old_n as int {
                        assert(indices[p] == old(self).indices.view()[p]);
                        assert(indices[p].as_nat() < old_cap);
                        assert(sparse[indices[p].as_nat() as int]
                            == old(self).sparse.view()[indices[p].as_nat() as int]);
                    } else {
                        assert(p == old_cap as int);
                        assert(indices[p].as_nat() == old_cap);
                        assert(sparse[old_cap as int].as_nat() == pos.as_nat() == old_cap);
                    }
                }
                // --- abstract effect: fresh allocation. old pool was empty
                // (old_n == old_cap), new id == old_cap, new pool empty too.
                assert(old(self).free_pool().len() == 0);   // old_cap - old_n == 0
                assert(!old(self).id_set().contains(old_cap as nat)) by {
                    // a live witness p < old_n would have indices[p] < old_cap.
                    if old(self).id_set().contains(old_cap as nat) {
                        let p = choose|p: int| 0 <= p < old_n
                            && (#[trigger] old(self).indices.view()[p]).as_nat() == old_cap as nat;
                    }
                }
                assert(self.id_set() =~= old(self).id_set().insert(old_cap as nat)) by {
                    assert forall|v: nat| #![auto] self.id_set().contains(v)
                        <==> old(self).id_set().insert(old_cap as nat).contains(v) by {
                        if self.id_set().contains(v) {
                            let p = choose|p: int| 0 <= p < n
                                && (#[trigger] indices[p]).as_nat() == v;
                            if p < old_n {
                                assert(indices[p] == old(self).indices.view()[p]);
                            } else {
                                assert(v == old_cap);
                            }
                        }
                        // reverse: old members keep their witness; old_cap is at
                        // position old_n == old_cap.
                        if old(self).id_set().contains(v) {
                            let q = choose|q: int| 0 <= q < old_n
                                && (#[trigger] old(self).indices.view()[q]).as_nat() == v;
                            assert(indices[q] == old(self).indices.view()[q]);
                            assert(0 <= q < n);
                        }
                        if v == old_cap as nat {
                            assert(indices[old_cap as int].as_nat() == old_cap);
                            assert(0 <= old_cap < n);
                        }
                    }
                }
                assert(self.free_pool().len() == 0);  // cap == n == old_cap+1
            }
            pos
        }
    }

    /// Remove a live id. Swap-removes its dense slot with the last element and
    /// parks the freed id at the new boundary `indices[n-1]` (the first free
    /// slot), preserving the permutation by a transposition.
    pub fn remove(&mut self, id: Idx)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            // Every clause is conditional on liveness at entry; a dead id
            // refuses at the branch and reaches none of this.
            old(self).contains_spec(id) ==> {
                &&& final(self).n_spec() == old(self).n_spec() - 1
                &&& final(self).cap_spec() == old(self).cap_spec()
                // ABSTRACT EFFECT: the live set loses exactly `id`.
                &&& final(self).id_set() =~= old(self).id_set().remove(id.as_nat())
                // INDEX-POOL PARKING: the freed id is pushed to the pool FRONT
                // (so the next `add` recycles it — LIFO), the rest shifts back.
                &&& final(self).free_pool() =~= old(self).free_pool().insert(0, id.as_nat())
                // survivors: every other live id stays live with its value
                // (the swap-remove moves the last dense slot, not its id map).
                &&& (forall|k: Idx| #[trigger] old(self).contains_spec(k)
                        && k.as_nat() != id.as_nat()
                        ==> final(self).contains_spec(k)
                            && final(self).dense_view()[
                                    final(self).sparse_view()[k.as_nat() as int].as_nat() as int]
                                == old(self).dense_view()[
                                    old(self).sparse_view()[k.as_nat() as int].as_nat() as int])
            },
            // snapshot-stack framing (eclasses: the aggregate's archive is
            // keyed on the component stacks).
            final(self).dense_snapshots_view() == old(self).dense_snapshots_view(),
            final(self).sparse_snapshots_view() == old(self).sparse_snapshots_view(),
            final(self).indices_snapshots_view() == old(self).indices_snapshots_view(),
    {
        // Total-with-documented-panic: see `get`.
        if !self.contains(id) {
            crate::guard::refuse("SparseSet::remove: id not present");
        }
        let ghost old_n = self.dense.view().len();
        let ghost old_cap = self.sparse.view().len();
        let ghost old_sparse = self.sparse.view();
        let ghost old_indices = self.indices.view();
        let pos = self.sparse.get_index(id);
        let nlen = self.dense.len();
        // last_pos = n - 1 (n >= 1 since id is live ⇒ pos < n).
        proof { nlen.lemma_as_nat_bounded(); }
        let last_pos = match Idx::try_from_usize(nlen.as_usize() - 1) {
            Some(x) => x,
            None => { assert(false); return; },
        };

        if pos.as_usize() != last_pos.as_usize() {
            let last_id = self.indices.get_index(last_pos);
            let last_val = self.dense.get_index(last_pos);
            proof {
                // From inverse-on-live: indices[pos]==id and sparse[last_id]==last_pos.
                assert(pos.as_nat() < old_n);          // id live
                assert(old_indices[pos.as_nat() as int].as_nat() == id.as_nat());
                assert(last_pos.as_nat() == old_n - 1);
                assert(old_sparse[old_indices[(old_n - 1) as int].as_nat() as int].as_nat()
                    == (old_n - 1));  // inverse at last_pos
                assert(last_id.as_nat() == old_indices[(old_n - 1) as int].as_nat());
            }
            self.dense.set_index(pos, last_val);
            self.indices.set_index(pos, last_id);
            self.indices.set_index(last_pos, id);
            self.sparse.set_index(last_id, pos);
            self.dense.pop();
            proof {
                let sparse = self.sparse.view();
                let indices = self.indices.view();
                let n = self.dense.view().len();   // old_n - 1
                let cap = sparse.len();
                assert(n == old_n - 1);
                assert(cap == old_cap);
                // indices' is old_indices with [pos]:=last_id, [last_pos]:=id —
                // a transposition of the values at pos and last_pos (old
                // indices[pos]==id, indices[last_pos]==last_id), so still a
                // permutation of [0, cap).
                assert(indices =~= old_indices.update(pos.as_nat() as int, last_id)
                    .update(last_pos.as_nat() as int, id));
                // (1a) in range: values unchanged as a multiset.
                assert forall|p: int| 0 <= p < cap implies (#[trigger] indices[p]).as_nat() < cap by {
                    if p == pos.as_nat() {
                        assert(indices[p].as_nat() == last_id.as_nat());
                        assert(old_indices[(old_n - 1) as int].as_nat() < old_cap);
                    } else if p == last_pos.as_nat() {
                        assert(indices[p].as_nat() == id.as_nat());
                        assert(old_indices[pos.as_nat() as int].as_nat() == id.as_nat());
                    } else {
                        assert(indices[p] == old_indices[p]);
                    }
                }
                // (1b) injective: a transposition of an injective seq.
                lemma_transposition_injective(old_indices, indices,
                    pos.as_nat() as int, last_pos.as_nat() as int, cap as int);
                // (2) inverse-on-live for [0, n) = [0, old_n - 1):
                assert forall|p: int| 0 <= p < n implies
                    sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p by {
                    if p == pos.as_nat() {
                        // indices[pos]==last_id, sparse[last_id]:=pos.
                        assert(indices[p].as_nat() == last_id.as_nat());
                        assert(sparse[last_id.as_nat() as int].as_nat() == pos.as_nat());
                    } else {
                        // p < n-1... actually p in [0,n) with p != pos, and
                        // p != last_pos (since last_pos == old_n-1 == n >= p+? );
                        // p < n = old_n-1 < last_pos, so p != last_pos.
                        assert(p < (old_n - 1));
                        assert(p != last_pos.as_nat());
                        assert(indices[p] == old_indices[p]);
                        // indices[p] != last_id (injective, p != last_pos), so
                        // sparse[indices[p]] unchanged from old (only last_id set).
                        assert(old_indices[p].as_nat() != old_indices[(old_n - 1) as int].as_nat());
                        assert(indices[p].as_nat() != last_id.as_nat());
                        assert(sparse[indices[p].as_nat() as int]
                            == old_sparse[indices[p].as_nat() as int]);
                        assert(old_sparse[old_indices[p].as_nat() as int].as_nat() == p);
                    }
                }
            }
        } else {
            // Removing the last live element: just shrink. The id stays parked
            // at indices[last_pos] = indices[n-1] (now the first free slot).
            self.dense.pop();
            proof {
                let sparse = self.sparse.view();
                let indices = self.indices.view();
                let n = self.dense.view().len();  // old_n - 1
                assert(n == old_n - 1);
                assert(indices == old_indices);
                assert(sparse == old_sparse);
                // sparse/indices untouched; inverse-on-live shrinks to [0,n).
                assert forall|p: int| 0 <= p < n implies
                    sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p by {
                    assert(p < old_n);
                }
            }
        }
        // --- abstract effect (both branches): set loses `id`, pool gains it
        // at the front. Branch-uniform facts established locally above:
        //   - indices[n].as_nat() == id  (id parked at the new pool front);
        //   - for every OLD live position q < old_n with old value v != id, the
        //     NEW indices still has v at some position < n (proved per branch
        //     into `old_to_new_live` below);
        //   - the prefix relation for the pool tail.
        proof {
            let indices = self.indices.view();
            let n = self.dense.view().len();   // old_n - 1
            assert(n == old_n - 1);
            assert(indices[n as int].as_nat() == id.as_nat());
            // id is NOT in the new live image (it sits at position n; a live
            // witness q < n would collide by injectivity).
            assert(!self.id_set().contains(id.as_nat())) by {
                if self.id_set().contains(id.as_nat()) {
                    let q = choose|q: int| 0 <= q < n && (#[trigger] indices[q]).as_nat() == id.as_nat();
                    assert(indices[q].as_nat() != indices[n as int].as_nat());
                }
            }
            assert(self.id_set() =~= old(self).id_set().remove(id.as_nat())) by {
                assert forall|v: nat| #![auto] self.id_set().contains(v)
                    <==> old(self).id_set().remove(id.as_nat()).contains(v) by {
                    // forward: v new-live ⇒ v old-live (its new witness q<n maps,
                    // in both branches, back to an old live position) and v != id.
                    if self.id_set().contains(v) {
                        let q = choose|q: int| 0 <= q < n && (#[trigger] indices[q]).as_nat() == v;
                        assert(indices[q].as_nat() != indices[n as int].as_nat());  // v != id
                        // q's value came from some old live position:
                        //  - last-element branch: indices==old_indices, q<n<old_n.
                        //  - swap branch: if q==pos, indices[pos]==last_id==
                        //    old_indices[old_n-1] (old live); else indices[q]==
                        //    old_indices[q] (old live, q<n<old_n).
                        assert(old(self).id_set().contains(v)) by {
                            if pos.as_nat() == last_pos.as_nat() {
                                assert(old_indices[q].as_nat() == v);
                            } else if q == pos.as_nat() {
                                assert(indices[pos.as_nat() as int].as_nat()
                                    == old_indices[(old_n - 1) as int].as_nat());
                            } else {
                                assert(old_indices[q].as_nat() == v);
                            }
                        }
                    }
                    // reverse: v old-live and v != id ⇒ v new-live. v's old
                    // witness q0 < old_n. The only old live position that loses
                    // its value is `pos` (held id, now last_id) — but v != id,
                    // so v survives at some new position < n.
                    if old(self).id_set().remove(id.as_nat()).contains(v) {
                        let q0 = choose|q0: int| 0 <= q0 < old_n
                            && (#[trigger] old_indices[q0]).as_nat() == v;
                        assert(v != id.as_nat());
                        // old_indices[pos]==id (inverse-on-live), so q0 != pos.
                        assert(old_indices[pos.as_nat() as int].as_nat() == id.as_nat());
                        assert(q0 != pos.as_nat());
                        if pos.as_nat() == last_pos.as_nat() {
                            // last-element: indices==old_indices, q0 != pos==n,
                            // so q0 < n and indices[q0]==v.
                            assert(q0 < n);
                            assert(indices[q0].as_nat() == v);
                        } else {
                            // swap: last value (old_indices[old_n-1]) moved to pos.
                            if q0 == old_n - 1 {
                                assert(indices[pos.as_nat() as int].as_nat() == v);
                                assert(pos.as_nat() < n);
                            } else {
                                // q0 < old_n-1 == n and q0 != pos ⇒ unchanged.
                                assert(q0 < n);
                                assert(indices[q0].as_nat() == v);
                            }
                        }
                    }
                }
            }
            // pool gains id at the front: new pool is indices[n..cap], and
            // indices[n] == id, indices[n+1..cap] == old indices[n+1..cap]
            // == old pool (old pool was indices[old_n..cap] = indices[n+1..cap]).
            assert(self.free_pool() =~= old(self).free_pool().insert(0, id.as_nat())) by {
                let np = self.free_pool();
                let op = old(self).free_pool().insert(0, id.as_nat());
                assert(np.len() == op.len());
                assert forall|k: int| 0 <= k < np.len() implies np[k] == op[k] by {
                    if k == 0 {
                        assert(np[0] == indices[n as int].as_nat());
                    } else {
                        assert(np[k] == indices[n as int + k].as_nat());
                        assert(op[k] == old(self).free_pool()[k - 1]);
                        assert(old(self).free_pool()[k - 1]
                            == old_indices[old_n as int + (k - 1)].as_nat());
                        // position n+k == old_n+k-1 > n is unchanged: the swap
                        // touched only pos (< n) and last_pos (== n); the
                        // last-element branch left indices == old_indices.
                        assert(n as int + k > n);
                        assert(indices[n as int + k] == old_indices[n as int + k]);
                        assert(n as int + k == old_n as int + (k - 1));
                    }
                }
            }
        }
    }

    /// Remove the first live entry whose VALUE equals `val` (production
    /// `remove_value` parity: linear scan of the dense region, then the
    /// verified `remove` on the id found at that position).
    pub fn remove_value(&mut self, val: &T) -> (removed: bool)
        where T: PartialEq
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).cap_spec() == old(self).cap_spec(),
            removed ==> final(self).n_spec() == old(self).n_spec() - 1,
            !removed ==> *final(self) == *old(self),
    {
        let n = self.dense.len();
        proof { n.lemma_as_nat_bounded(); }  // n.as_nat() < Idx::max_nat()
        let n_u = n.as_usize();
        let mut pos_u: usize = 0;
        while pos_u < n_u
            invariant
                self.wf(),
                *self == *old(self),
                n_u == self.n_spec(),
                self.n_spec() < Idx::max_nat(),
                self.n_spec() <= self.cap_spec(),
                pos_u <= n_u,
            decreases n_u - pos_u,
        {
            let pos = match Idx::try_from_usize(pos_u) {
                Some(p) => p,
                None => {
                    proof { assert(false); }  // pos_u < n_u < max_nat ⇒ Some
                    return false;
                }
            };
            let cur = self.dense.get_index(pos);
            if values_equal(&cur, val) {
                let id = self.indices.get_index(pos);
                proof {
                    // indices[pos] for pos < n is live: inverse-on-live gives
                    // sparse[indices[pos]] == pos < n, and the round-trip
                    // indices[sparse[id]] == id — exactly contains_spec.
                    let indices = self.indices.view();
                    let p = pos.as_nat() as int;
                    assert(self.sparse.view()[indices[p].as_nat() as int].as_nat() == p);
                    assert(self.contains_spec(id));
                }
                self.remove(id);
                return true;
            }
            pos_u = pos_u + 1;
        }
        false
    }

    /// Read-only access to the dense value vector (production `data()`
    /// parity: exposes the packed live values for iteration).
    pub fn data(&self) -> (r: &SpVec<T, Idx, S, TRACK, VC>)
        ensures r == self.dense_ref(),
    {
        &self.dense
    }

    // ---- semi-persistence: delegate to the three inner vectors ----


    /// Archive step shared by `mark` and `push_frames`: pushing the live triple
    /// onto three lockstep stacks keeps every archived triple `snap_wf` (the
    /// old entries are untouched, the new one is the old live state, which is
    /// `snap_wf` by the old `wf`).
    proof fn lemma_archive_after_push(&self, pre: &Self)
        requires
            pre.wf(),
            self.dense.snapshots_view() == pre.dense.snapshots_view().push(pre.dense_view()),
            self.sparse.snapshots_view() == pre.sparse.snapshots_view().push(pre.sparse_view()),
            self.indices.snapshots_view() == pre.indices.snapshots_view().push(pre.indices_view()),
        ensures
            self.sparse.snapshots_view().len() == self.dense.snapshots_view().len(),
            self.indices.snapshots_view().len() == self.dense.snapshots_view().len(),
            forall|k: int| 0 <= k < self.dense.snapshots_view().len() ==>
                sparse_set_snap_wf(#[trigger] self.dense.snapshots_view()[k],
                    self.sparse.snapshots_view()[k], self.indices.snapshots_view()[k]),
    {
        let od = pre.dense.snapshots_view();
        assert forall|k: int| 0 <= k < self.dense.snapshots_view().len() implies
            sparse_set_snap_wf(#[trigger] self.dense.snapshots_view()[k],
                self.sparse.snapshots_view()[k], self.indices.snapshots_view()[k]) by {
            if k < od.len() {
                assert(self.dense.snapshots_view()[k] == od[k]);
                assert(self.sparse.snapshots_view()[k] == pre.sparse.snapshots_view()[k]);
                assert(self.indices.snapshots_view()[k] == pre.indices.snapshots_view()[k]);
            } else {
                assert(self.dense.snapshots_view()[k] == pre.dense_view());
                assert(self.sparse.snapshots_view()[k] == pre.sparse_view());
                assert(self.indices.snapshots_view()[k] == pre.indices_view());
                assert(sparse_set_snap_wf(pre.dense_view(), pre.sparse_view(), pre.indices_view()));
            }
        }
    }

    // ------------------------------------------------------------------
    // Total-operation shell. `restore` itself is total (panic guard, below):
    // the archive clauses of `wf` guarantee that the triple a valid token names
    // is a valid sparse-set state, so the guard checks only what
    // `is_valid_token` answers plus the agreement of the three frame indices.
    // ------------------------------------------------------------------

    /// Exec counterpart of `add`'s three-column capacity precondition.
    pub fn can_add(&self) -> (b: bool)
        requires self.wf(),
        ensures b == self.can_add_spec(),
    {
        self.dense.can_push() && self.sparse.can_push() && self.indices.can_push()
    }

    /// Total add.
    pub fn try_add(&mut self, value: T) -> (r: Result<Idx, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted
                && final(self).id_set() == old(self).id_set(),
            r matches Ok(id) ==> {
                &&& final(self).n_spec() == old(self).n_spec() + 1
                &&& final(self).contains_spec(id)
                &&& !old(self).id_set().contains(id.as_nat())
                &&& final(self).id_set() =~= old(self).id_set().insert(id.as_nat())
                &&& id.as_nat() <= old(self).cap_spec()
                &&& final(self).cap_spec() == if old(self).free_pool().len() == 0 {
                        old(self).cap_spec() + 1
                    } else {
                        old(self).cap_spec()
                    }
                &&& final(self).dense_view()[
                        final(self).sparse_view()[id.as_nat() as int].as_nat() as int] == value
                &&& (forall|k: Idx| #[trigger] old(self).contains_spec(k)
                        ==> final(self).contains_spec(k)
                            && final(self).dense_view()[
                                    final(self).sparse_view()[k.as_nat() as int].as_nat() as int]
                                == old(self).dense_view()[
                                    old(self).sparse_view()[k.as_nat() as int].as_nat() as int])
            },
            // snapshot-stack framing (eclasses: the aggregate's archive is
            // keyed on the component stacks).
            final(self).dense_snapshots_view() == old(self).dense_snapshots_view(),
            final(self).sparse_snapshots_view() == old(self).sparse_snapshots_view(),
            final(self).indices_snapshots_view() == old(self).indices_snapshots_view(),
    {
        if self.can_add() {
            Ok(self.add(value))
        } else {
            Err(crate::error::ContainerError::CapacityExhausted)
        }
    }

    /// Total get: `Err(IndexOutOfBounds)` for an id that is not live.
    pub fn try_get(&self, id: Idx) -> (r: Result<T, crate::error::ContainerError>)
        requires self.wf(),
        ensures
            r is Ok <==> self.contains_spec(id),
            r matches Ok(v) ==> v
                == self.dense_view()[self.sparse_view()[id.as_nat() as int].as_nat() as int],
    {
        if self.contains(id) {
            Ok(self.get(id))
        } else {
            Err(crate::error::ContainerError::IndexOutOfBounds)
        }
    }





    // --------------------------------------------------------------------
    // Shared-history variants (doc 10): the same three-member fan-out driven by
    // ONE external `History` via the genealogy-free `push_frame`/`restore_frame`
    // primitives, so the branch genealogy lives once instead of once per member
    // vector. Additive — the `mark`/`restore` above and their theorems are
    // untouched; a caller opts into sharing by using these and never the per-vec
    // genealogy path, leaving each member's own `forks` empty. The synced-depth
    // precondition (all members and the history at one depth) is the group
    // invariant, carried explicitly since `wf` does not track a history.
    #[allow(dead_code)]
    pub(crate) fn push_frames(&mut self, shrink: ShrinkPolicy)
        requires
            old(self).wf(),
            TRACK,
            old(self).can_mark_spec(),
            old(self).dense.depth_spec() == old(self).sparse.depth_spec(),
            old(self).dense.depth_spec() == old(self).indices.depth_spec(),
        ensures
            final(self).wf(),
            final(self).dense_view() == old(self).dense_view(),
            final(self).sparse_view() == old(self).sparse_view(),
            final(self).indices_view() == old(self).indices_view(),
            final(self).dense_snapshots_view()
                == old(self).dense_snapshots_view().push(old(self).dense_view()),
            final(self).sparse_snapshots_view()
                == old(self).sparse_snapshots_view().push(old(self).sparse_view()),
            final(self).indices_snapshots_view()
                == old(self).indices_snapshots_view().push(old(self).indices_view()),
            final(self).dense.depth_spec() == old(self).dense.depth_spec() + 1,
            final(self).dense.depth_spec() == final(self).sparse.depth_spec(),
            final(self).dense.depth_spec() == final(self).indices.depth_spec(),
    {
        self.dense.push_frame(shrink);
        self.sparse.push_frame(shrink);
        self.indices.push_frame(shrink);
        proof { self.lemma_archive_after_push(old(self)); }
    }


    #[allow(dead_code)]
    pub(crate) fn restore_frames(&mut self, target: usize)
        where T: core::default::Default, Idx: core::default::Default
        requires
            old(self).wf(),
            TRACK,
            old(self).dense.depth_spec() == old(self).sparse.depth_spec(),
            old(self).dense.depth_spec() == old(self).indices.depth_spec(),
            (target as nat) < old(self).dense.depth_spec(),
            sparse_set_snap_wf(
                old(self).dense.snapshots_view()[target as int],
                old(self).sparse.snapshots_view()[target as int],
                old(self).indices.snapshots_view()[target as int]),
        ensures
            final(self).wf(),
            final(self).dense_view() == old(self).dense.snapshots_view()[target as int],
            final(self).sparse_view() == old(self).sparse.snapshots_view()[target as int],
            final(self).indices_view() == old(self).indices.snapshots_view()[target as int],
            final(self).dense_snapshots_view()
                == old(self).dense_snapshots_view().subrange(0, target as int),
            final(self).sparse_snapshots_view()
                == old(self).sparse_snapshots_view().subrange(0, target as int),
            final(self).indices_snapshots_view()
                == old(self).indices_snapshots_view().subrange(0, target as int),
            final(self).dense.depth_spec() == target as nat,
            final(self).dense.depth_spec() == final(self).sparse.depth_spec(),
            final(self).dense.depth_spec() == final(self).indices.depth_spec(),
    {
        self.dense.restore_frame(target);
        self.sparse.restore_frame(target);
        self.indices.restore_frame(target);
    }

    /// Semantics B, token-free (what a typed group drives): reset the three
    /// columns to their snapshot at `target` and keep frame `target` open. The
    /// archive clause of `wf` at `target` is the restored triple's validity.
    pub(crate) fn reset_frames(&mut self, target: usize)
        where T: core::default::Default, Idx: core::default::Default
        requires
            old(self).wf(),
            TRACK,
            old(self).dense.depth_spec() == old(self).sparse.depth_spec(),
            old(self).dense.depth_spec() == old(self).indices.depth_spec(),
            (target as nat) < old(self).dense.depth_spec(),
            old(self).dense.depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).dense_view() == old(self).dense.snapshots_view()[target as int],
            final(self).sparse_view() == old(self).sparse.snapshots_view()[target as int],
            final(self).indices_view() == old(self).indices.snapshots_view()[target as int],
            final(self).dense_snapshots_view()
                == old(self).dense_snapshots_view().subrange(0, target as int + 1),
            final(self).sparse_snapshots_view()
                == old(self).sparse_snapshots_view().subrange(0, target as int + 1),
            final(self).indices_snapshots_view()
                == old(self).indices_snapshots_view().subrange(0, target as int + 1),
            final(self).dense.depth_spec() == target as nat + 1,
            final(self).dense.depth_spec() == final(self).sparse.depth_spec(),
            final(self).dense.depth_spec() == final(self).indices.depth_spec(),
    {
        proof {
            self.dense.lemma_partition_counts();
            self.sparse.lemma_partition_counts();
            self.indices.lemma_partition_counts();
            assert(sparse_set_snap_wf(
                self.dense.snapshots_view()[target as int],
                self.sparse.snapshots_view()[target as int],
                self.indices.snapshots_view()[target as int]));
        }
        self.dense.reset_frame(target);
        self.sparse.reset_frame(target);
        self.indices.reset_frame(target);
    }
}

/// The sparse-set structural invariant stated over raw snapshot sequences (for
/// `restore`: the three snapshots being restored must jointly form a valid
/// state, so the restored set is `wf`). Mirrors `wf`'s clauses (2)/(1).
pub open(crate) spec fn sparse_set_snap_wf<T, Idx: IndexLike>(
    dense: Seq<T>, sparse: Seq<Idx>, indices: Seq<Idx>,
) -> bool {
    let cap = sparse.len();
    let n = dense.len();
    &&& indices.len() == cap
    &&& n <= cap
    &&& (forall|p: int| 0 <= p < cap ==> (#[trigger] indices[p]).as_nat() < cap)
    &&& (forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q ==>
            (#[trigger] indices[p]).as_nat() != (#[trigger] indices[q]).as_nat())
    &&& (forall|p: int| 0 <= p < n ==>
            sparse[(#[trigger] indices[p]).as_nat() as int].as_nat() == p)
}

/// The set of values `{ indices[p].as_nat() : 0 <= p < m }`. (`ISet` for the
/// same reason as `id_set`: total comprehension, finiteness proved below.)
pub open(crate) spec fn image_prefix<Idx: IndexLike>(indices: Seq<Idx>, m: int) -> ISet<nat> {
    ISet::new(|id: nat| exists|p: int| 0 <= p < m && (#[trigger] indices[p]).as_nat() == id)
}

/// An injective, in-range `indices` (over `[0, cap)`) hits every value in
/// `[0, cap)`: there is a `p < cap` with `indices[p].as_nat() == id` for each
/// `id < cap`. This is finite surjectivity-from-injectivity (pigeonhole),
/// proved via image cardinality: `|image_prefix(cap)| == cap` (each position
/// contributes a fresh value, by injectivity), and a `cap`-sized subset of the
/// `cap`-sized range `[0, cap)` must be the whole range.
pub(crate) proof fn lemma_perm_surjective<Idx: IndexLike>(indices: Seq<Idx>, cap: int, id: nat)
    requires
        cap <= indices.len(),
        id < cap,
        forall|p: int| 0 <= p < cap ==> (#[trigger] indices[p]).as_nat() < cap,
        forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q ==>
            (#[trigger] indices[p]).as_nat() != (#[trigger] indices[q]).as_nat(),
    ensures
        exists|p: int| 0 <= p < cap && (#[trigger] indices[p]).as_nat() == id,
{
    lemma_image_prefix_card(indices, cap);
    let img = image_prefix(indices, cap);
    let rng = ISet::new(|v: nat| v < cap);
    // img subset of rng (in-range), both size cap ⇒ equal ⇒ id in img.
    assert(img.subset_of(rng)) by {
        assert forall|v: nat| img.contains(v) implies rng.contains(v) by {
            let p = choose|p: int| 0 <= p < cap && (#[trigger] indices[p]).as_nat() == v;
        }
    }
    lemma_nat_range_card(cap);
    vstd::iset_lib::lemma_len_subset(img, rng);
    vstd::iset_lib::lemma_subset_equality(img, rng);
    assert(rng.contains(id));
    assert(img.contains(id));
}

/// `|image_prefix(indices, m)| == m` for injective in-range `indices`, by
/// induction on `m`: the value at position `m-1` is fresh (injectivity), so it
/// extends the prefix image by exactly one.
pub(crate) proof fn lemma_image_prefix_card<Idx: IndexLike>(indices: Seq<Idx>, m: int)
    requires
        0 <= m <= indices.len(),
        forall|p: int, q: int| 0 <= p < m && 0 <= q < m && p != q ==>
            (#[trigger] indices[p]).as_nat() != (#[trigger] indices[q]).as_nat(),
    ensures
        image_prefix(indices, m).finite(),
        image_prefix(indices, m).len() == m,
    decreases m,
{
    if m == 0 {
        assert(image_prefix(indices, 0) =~= ISet::<nat>::empty());
    } else {
        lemma_image_prefix_card(indices, m - 1);
        let prev = image_prefix(indices, m - 1);
        let cur = image_prefix(indices, m);
        let last = indices[m - 1].as_nat();
        // last is not in prev (injectivity: no p < m-1 equals position m-1).
        assert(!prev.contains(last)) by {
            if prev.contains(last) {
                let p = choose|p: int| 0 <= p < m - 1 && (#[trigger] indices[p]).as_nat() == last;
                assert(indices[p].as_nat() != indices[m - 1].as_nat());
            }
        }
        // cur == prev ∪ {last}.
        assert(cur =~= prev.insert(last)) by {
            assert forall|v: nat| #![auto] cur.contains(v) <==> prev.insert(last).contains(v) by {
                if cur.contains(v) {
                    let p = choose|p: int| 0 <= p < m && (#[trigger] indices[p]).as_nat() == v;
                    if p < m - 1 { assert(prev.contains(v)); } else { assert(v == last); }
                }
            }
        }
        assert(cur.len() == prev.len() + 1);
    }
}

/// `{ v : v < cap }` is finite with size `cap`.
pub(crate) proof fn lemma_nat_range_card(cap: int)
    requires cap >= 0,
    ensures
        ISet::new(|v: nat| v < cap).finite(),
        ISet::new(|v: nat| v < cap).len() == cap,
    decreases cap,
{
    if cap == 0 {
        assert(ISet::new(|v: nat| v < 0) =~= ISet::<nat>::empty());
    } else {
        lemma_nat_range_card(cap - 1);
        assert(ISet::new(|v: nat| v < cap)
            =~= ISet::new(|v: nat| v < cap - 1).insert((cap - 1) as nat));
    }
}

/// A transposition of two positions in an injective sequence is injective.
/// `b` is `a` with values at `i` and `j` swapped (`a[i]==b[j]`, `a[j]==b[i]`,
/// equal elsewhere); both same length `cap`.
pub(crate) proof fn lemma_transposition_injective<Idx: IndexLike>(
    a: Seq<Idx>, b: Seq<Idx>, i: int, j: int, cap: int,
)
    requires
        0 <= i < cap <= a.len(),
        0 <= j < cap,
        b.len() == a.len(),
        i != j,
        b[i].as_nat() == a[j].as_nat(),
        b[j].as_nat() == a[i].as_nat(),
        forall|k: int| #![auto] 0 <= k < cap && k != i && k != j ==> b[k].as_nat() == a[k].as_nat(),
        forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q ==>
            (#[trigger] a[p]).as_nat() != (#[trigger] a[q]).as_nat(),
    ensures
        forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q ==>
            (#[trigger] b[p]).as_nat() != (#[trigger] b[q]).as_nat(),
{
    assert forall|p: int, q: int| 0 <= p < cap && 0 <= q < cap && p != q implies
        (#[trigger] b[p]).as_nat() != (#[trigger] b[q]).as_nat() by {
        // b's value at any position equals a's value at the transposed position;
        // since a is injective and the transposition is a bijection on indices,
        // distinct p,q map to distinct source positions, hence distinct values.
        let sp = if p == i { j } else if p == j { i } else { p };
        let sq = if q == i { j } else if q == j { i } else { q };
        assert(b[p].as_nat() == a[sp].as_nat());
        assert(b[q].as_nat() == a[sq].as_nat());
        assert(sp != sq);
        assert(0 <= sp < cap && 0 <= sq < cap);
    }
}

/// Value equality via `PartialEq`, verified through vstd's external trait
/// specification. Nothing is trusted here: that specification's `eq` promises
/// `obeys_eq_spec() ==> r == eq_spec(..)`, and this crate never establishes
/// `obeys_eq_spec` for a caller's `T`, so the result is an unconstrained bool as
/// far as proofs are concerned — which is exactly what the scan needs.
/// `remove_value`'s contract consequently promises which STRUCTURAL change
/// happened (an element left), not which value matched, and the scan behaviour
/// is pinned by the ported production proptests.
fn values_equal<T: PartialEq>(a: &T, b: &T) -> bool {
    PartialEq::eq(a, b)
}

// ---------------------------------------------------------------------------
// Production-compatible constructors. Generic `with_store`
// plus the two concrete instantiations production exposes; all establish the
// empty `wf` (the permutation invariant is vacuous at cap == n == 0).
// ---------------------------------------------------------------------------

impl<T, Idx, S, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>, P> SparseSet<T, Idx, S, TRACK, VC, P>
where
    T: Sized + Copy,
    Idx: IndexLike + Tagged,
    S: DiffStore<T, Idx, TRACK>,
    P: TaggedFamily<Idx, Idx, TRACK>,
{
    /// Empty sparse set over a caller-supplied (empty, well-formed) dense
    /// store. Production `with_store` parity.
    pub(crate) fn with_store(store: S) -> (s: Self)
        requires
            store.wf(),
            store.data().len() == 0,
        ensures
            s.wf(),
            s.n_spec() == 0,
            s.cap_spec() == 0,
            s.dense_snapshots_view().len() == 0,
            s.sparse_snapshots_view().len() == 0,
            s.indices_snapshots_view().len() == 0,
    {
        let s = SparseSet {
            dense: SpVec::with_store(store),
            sparse: SpVec::with_store(<P as TaggedFamily<Idx, Idx, TRACK>>::empty()),
            indices: SpVec::with_store(<P as TaggedFamily<Idx, Idx, TRACK>>::empty()),
        };
        proof {
            // Empty everything: every wf clause quantifies over [0, 0).
            assert(s.cap_spec() == 0);
            assert(s.n_spec() == 0);
        }
        s
    }
}

impl<T, Idx, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>, P> SparseSet<T, Idx, crate::parallel_store::ParallelStore<T, Idx>, TRACK, VC, P>
where
    T: Sized + Copy,
    Idx: IndexLike + Tagged,
    P: TaggedFamily<Idx, Idx, TRACK>,
{
    /// Empty sparse set over a `ParallelStore` (any `T: Copy`; production
    /// `SparseSet::new` parity).
    pub fn new() -> (s: Self)
        ensures s.wf(), s.n_spec() == 0, s.cap_spec() == 0,
    {
        Self::with_store(crate::parallel_store::ParallelStore::new())
    }
}

impl<T, Idx, const TRACK: bool, VC: crate::value_compressor::ValueCompressor<T>, P> SparseSet<T, Idx, crate::inline_store::InlineStore<T, Idx>, TRACK, VC, P>
where
    T: Tagged + Sized + Copy,
    Idx: IndexLike + Tagged,
    P: TaggedFamily<Idx, Idx, TRACK>,
{
    /// Empty sparse set over an `InlineStore` (`T: Tagged`; production
    /// `SparseSet::new_inline` parity).
    pub fn new_inline() -> (s: Self)
        ensures s.wf(), s.n_spec() == 0, s.cap_spec() == 0,
            s.dense_snapshots_view().len() == 0,
            s.sparse_snapshots_view().len() == 0,
            s.indices_snapshots_view().len() == 0,
    {
        Self::with_store(crate::inline_store::InlineStore::new())
    }
}

} // verus!

// Production-surface parity (production ships Default on this variant).
impl<T, Idx, const TRACK: bool, P> Default
    for SparseSet<
        T,
        Idx,
        crate::parallel_store::ParallelStore<T, Idx>,
        TRACK,
        crate::value_compressor::NoValueCompression,
        P,
    >
where
    T: Sized + Copy,
    Idx: IndexLike + Tagged,
    P: TaggedFamily<Idx, Idx, TRACK>,
{
    fn default() -> Self {
        Self::new()
    }
}
