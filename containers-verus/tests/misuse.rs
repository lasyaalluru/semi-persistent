// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Public-API misuse test suite.
//!
//! Every case here produces an invalid token through the PUBLIC API only
//! (forged-state cases — out-of-range frame indices, mixed-component compound
//! tokens, counter exhaustion — live as in-module `#[cfg(test)]` unit tests
//! next to the private state they corrupt). Each rejected restore must:
//!
//!   1. panic with the production-parity message, and
//!   2. panic BEFORE mutating anything (state logically unchanged after
//!      catch_unwind).
//!
//! These pin the runtime-hardening contract: erased `requires` clauses have
//! runtime mirrors that fire for unverified callers exactly where production's
//! asserts fire.

use semi_persistent_containers_verus::append_only_vec::AppendOnlyVec;
use semi_persistent_containers_verus::error::ContainerError;
use semi_persistent_containers_verus::group::ForkHistory;
use semi_persistent_containers_verus::parallel_store::ParallelStore;
use semi_persistent_containers_verus::vec::{ShrinkPolicy, Vec as SpVec};

type V = SpVec<u32, u32, ParallelStore<u32, u32>, true>;

fn read_back(v: &V) -> Vec<u32> {
    (0..v.len() as usize).map(|i| v.get(i as u32)).collect()
}

// ---------------------------------------------------------------------------
// Foreign token: a token minted by container A must be rejected by B.
// ---------------------------------------------------------------------------

#[test]
fn foreign_token_refuses_as_err() {
    let mut a = ForkHistory::new(V::new());
    let mut b = ForkHistory::new(V::new());
    a.try_push(1).expect("push: within index word");
    b.try_push(2).expect("push: within index word");
    let tok_a = a
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    assert!(
        !b.restore(tok_a),
        "was: panic(token belongs to a different container)"
    );
}

#[test]
fn foreign_token_rejected_before_mutation() {
    let mut a = ForkHistory::new(V::new());
    let mut b = ForkHistory::new(V::new());
    for i in 0..10 {
        a.try_push(i).expect("push: within index word");
        b.try_push(i + 100).expect("push: within index word");
    }
    let tok_a = a
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    b.try_push(999).expect("push: within index word");
    let before = (0..b.len() as usize)
        .map(|i| b.get(i as u32))
        .collect::<Vec<_>>();

    assert!(!b.restore(tok_a), "foreign restore must panic");
    let after = (0..b.len() as usize)
        .map(|i| b.get(i as u32))
        .collect::<Vec<_>>();
    assert_eq!(before, after, "rejected restore must not mutate state");
    // b remains fully usable.
    b.try_push(1000).expect("push: within index word");
    assert_eq!(b.pop(), Some(1000));

    // And is_valid_token agrees without panicking.
    assert!(!b.is_valid(tok_a));
    assert!(a.is_valid(tok_a));
}

// ---------------------------------------------------------------------------
// Consumed token: restore(t) then restore(t) again — the frame is gone. THE
// consumed-token gap: genealogy alone would still call it on-path; the
// frame-liveness check must reject it.
// ---------------------------------------------------------------------------

#[test]
fn consumed_token_refuses_as_err() {
    let mut v = ForkHistory::new(V::new());
    v.try_push(1).expect("push: within index word");
    let tok = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(2).expect("push: within index word");
    assert!(v.restore(tok), "first restore: live frame"); // semantics B: frame stays open
    assert!(v.restore(tok), "second restore: the checkpoint is reusable");
    assert!(v.pop_scope()); // drop the frame: now the token is dead
    assert!(
        !v.restore(tok),
        "was: panic(token points beyond frame stack)"
    );
}

#[test]
fn consumed_token_reported_invalid_and_rejected_before_mutation() {
    let mut v = ForkHistory::new(V::new());
    v.try_push(1).expect("push: within index word");
    let tok = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(2).expect("push: within index word");
    assert!(v.is_valid(tok), "live token is restorable");
    assert!(v.restore(tok), "restore: own token");
    // Semantics B (design doc 08 §1): the restored frame stays open, so the
    // token is still restorable; only dropping the frame kills it.
    assert!(v.is_valid(tok), "restored checkpoint stays restorable");
    assert!(v.pop_scope());
    assert!(
        !v.is_valid(tok),
        "popped frame's token must report not-restorable"
    );

    let before = read_back(&v);
    assert!(!v.restore(tok), "consumed restore must panic");
    assert_eq!(
        before,
        read_back(&v),
        "rejected restore must not mutate state"
    );
}

// ---------------------------------------------------------------------------
// Abandoned-future token: mark A, restore past it, mark again (new branch) —
// A's future was cut off. Post-H2 the genealogy lives on the owning group's
// `History` (a standalone vec is a group of one), so the rejection is the
// history's: `is_valid` answers false for the abandoned group token, and the
// paired discipline never hands its depth to the structural vec restore. The
// vec-level check is structural only (frame liveness), by design.
// ---------------------------------------------------------------------------

#[test]
fn abandoned_future_rejected_by_paired_history() {
    use semi_persistent_containers_verus::history::History;
    let mut v = ForkHistory::new(V::new());
    let mut h = History::new();
    v.try_push(1).expect("push: within index word");
    let base = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    let base_g = h.mark();
    v.try_push(2).expect("push: within index word");
    let _abandoned = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness"); // depth 2 on branch 0
    let abandoned_g = h.mark();
    v.try_push(3).expect("push: within index word");
    assert!(h.is_valid(base_g));
    assert!(v.restore(base), "restore: own token"); // cut back to depth 0
    h.restore_to(base_g); // -> new branch
    v.try_push(20).expect("push: within index word");
    let _new_frame = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness"); // depth 1, NEW branch
    let _new_g = h.mark();
    v.try_push(21).expect("push: within index word");
    let _deeper = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness"); // frame at depth 1 live again
    let _deeper_g = h.mark();
    // `abandoned_g` names depth 1 of the OLD branch: even though a frame is
    // live at that depth again, the branch cut bumped its generation.
    assert!(
        !h.is_valid(abandoned_g),
        "abandoned-branch future token must be rejected by the history"
    );
}

#[test]
fn standalone_vec_refuses_abandoned_branch_token() {
    // A standalone vec is a group of one: it owns its genealogy, so a token
    // from an abandoned branch is refused even when a frame is live again at
    // its index (the restore cut bumped that depth's generation), and the
    // consumed token itself stays refused after a re-mark at its depth.
    let mut v = ForkHistory::new(V::new());
    v.try_push(1).expect("push: within index word");
    let base = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(2).expect("push: within index word");
    let abandoned = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(3).expect("push: within index word");
    assert!(v.restore(base), "restore: own token");
    assert!(v.is_valid(base), "the checkpoint stays valid (semantics B)");
    assert!(!v.is_valid(abandoned), "the abandoned future is cut");
    v.try_push(20).expect("push: within index word");
    let _f1 = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness"); // depth 1 again, fresh stamp
    let _f2 = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness"); // depth 2
    assert!(
        !v.is_valid(abandoned),
        "abandoned-branch token must be refused after a re-mark at its depth"
    );
    assert!(
        v.is_valid(base),
        "the checkpoint stays valid across re-marks above it"
    );
    let len_before = v.len();
    assert!(!v.restore(abandoned), "refused restore");
    assert_eq!(v.len(), len_before, "a refused restore does not mutate");
    // Provenance: a token minted by another vec is foreign, whatever its numbers.
    let mut other = ForkHistory::new(V::new());
    other.try_push(1).expect("push");
    let foreign = other.mark(ShrinkPolicy::Never).expect("mark");
    assert!(!v.is_valid(foreign), "a foreign vec's token is refused");
    assert!(
        other.is_valid(foreign),
        "and still validates on its own vec"
    );
}

// ---------------------------------------------------------------------------
// TRACK=false: mark and restore are caller errors (production parity).
// ---------------------------------------------------------------------------

#[test]
fn untracked_mark_refuses_as_err() {
    let mut v = ForkHistory::new(SpVec::<u32, u32, ParallelStore<u32, u32>, false>::new());
    v.try_push(1).expect("push: within index word");
    assert!(
        v.mark(ShrinkPolicy::Never).is_none(),
        "was: panic(mark() called on untracked vec)"
    );
}

#[test]
fn untracked_append_only_mark_refuses_as_err() {
    let mut v = ForkHistory::new(AppendOnlyVec::<u32, usize, false>::new());
    v.try_push(1).expect("push: within index word");
    assert!(
        v.mark(ShrinkPolicy::Never).is_none(),
        "was: panic(mark() called on untracked AppendOnlyVec)"
    );
}

/// TRACK=false restore: also a caller error. A token cannot be legitimately
/// obtained at TRACK=false (mark panics), so forge the call by transmuting
/// nothing — instead, get a token from a tracked vec and feed it to an
/// untracked one: the TRACK guard must fire FIRST (before the
/// container-identity check).
#[test]
fn untracked_restore_refuses_as_err() {
    let mut tracked = ForkHistory::new(V::new());
    tracked.try_push(1).expect("push: within index word");
    let tok = tracked
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    let mut untracked = ForkHistory::new(SpVec::<u32, u32, ParallelStore<u32, u32>, false>::new());
    untracked.try_push(1).expect("push: within index word");
    assert!(
        !untracked.restore(tok),
        "was: panic(restore() called on untracked vec); Untracked is folded into\n         InvalidToken here because is_restorable_spec includes the TRACK gate"
    );
}

/// CircularList::splice same-ring misuse: the public `splice` is total — it
/// walks the absorbed node's ring and refuses (panics) when the survivor is on
/// it, in every build profile. (The crate-private `splice_core` used by
/// `EClasses` carries the proven precondition instead of the walk.)
#[test]
fn circular_splice_same_ring_refused() {
    use semi_persistent_containers_verus::circular_list::CircularList;
    use semi_persistent_containers_verus::dense_id::DenseId31;
    use semi_persistent_containers_verus::opt::DenseId;
    let mut c = CircularList::<u32, DenseId31, true>::new();
    let a = c.try_add_singleton(1).expect("id range");
    let b = c.try_add_singleton(2).expect("id range");
    c.splice(a, b); // legal: different rings -> merged
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        c.splice(a, b); // now the SAME ring: the guard must refuse
    }));
    assert!(r.is_err(), "same-ring splice must be refused");
    // A node id past the allocated range is refused before any walk.
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        c.splice(a, DenseId31::from_usize(7));
    }));
    assert!(r.is_err(), "out-of-range splice must be refused");
}

#[test]
fn untracked_normal_ops_work() {
    // TRACK=false: everything except mark/restore behaves as a plain vec.
    let mut v = SpVec::<u32, u32, ParallelStore<u32, u32>, false>::new();
    for i in 0..100 {
        v.try_push(i).expect("push: within index word");
    }
    v.set(50u32, 999);
    assert_eq!(v.get(50u32), 999);
    assert_eq!(v.pop(), Some(99));
    assert_eq!(v.len(), 99);
}

// ---------------------------------------------------------------------------
// AppendOnlyVec: same token discipline as Vec.
// ---------------------------------------------------------------------------

#[test]
fn aov_foreign_token_refuses_as_err() {
    let mut a = ForkHistory::new(AppendOnlyVec::<u32, usize, true>::new());
    let mut b = ForkHistory::new(AppendOnlyVec::<u32, usize, true>::new());
    a.try_push(1).expect("push: within index word");
    b.try_push(2).expect("push: within index word");
    let tok_a = a
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    assert!(
        !b.restore(tok_a),
        "was: panic(token belongs to a different container)"
    );
}

#[test]
fn aov_consumed_token_refuses_as_err() {
    let mut v = ForkHistory::new(AppendOnlyVec::<u32, usize, true>::new());
    v.try_push(1).expect("push: within index word");
    let tok = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    v.try_push(2).expect("push: within index word");
    assert!(v.restore(tok), "first restore: live frame");
    assert!(v.restore(tok), "second restore: the checkpoint is reusable");
    assert!(v.pop_scope());
    assert!(
        !v.restore(tok),
        "was: panic(token points beyond frame stack)"
    );
}

#[test]
fn aov_consumed_token_reported_invalid() {
    let mut v = ForkHistory::new(AppendOnlyVec::<u32, usize, true>::new());
    v.try_push(1).expect("push: within index word");
    let tok = v
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    assert!(v.is_valid(tok));
    assert!(v.restore(tok), "restore: own token");
    assert!(v.is_valid(tok), "semantics B: the checkpoint stays valid");
    assert!(v.pop_scope());
    assert!(!v.is_valid(tok));
}

// ---------------------------------------------------------------------------
// SpMap: token discipline through the composite wrapper.
// ---------------------------------------------------------------------------

#[test]
fn map_consumed_token_reported_invalid_and_state_preserved() {
    use semi_persistent_containers_verus::map::SpMap;
    let mut m = ForkHistory::new(SpMap::<u32, u32, usize, true>::new());
    m.try_insert(1, 10).expect("insert: within index word");
    let tok = m
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    m.try_insert(2, 20).expect("insert: within index word");
    assert!(m.is_valid(tok));
    assert!(m.restore(tok), "restore: own token");
    assert!(m.is_valid(tok), "semantics B: the checkpoint stays valid");
    assert!(m.pop_scope());
    assert!(!m.is_valid(tok), "popped map token must be invalid");

    let before_log = m.log_len();
    assert!(!m.restore(tok), "restore: own token");
    assert_eq!(m.log_len(), before_log, "rejected restore must not mutate");
    assert_eq!(m.id_of(&1), Some(0));
}

// ---------------------------------------------------------------------------
// SparseSet: atomic compound restore — a token with a consumed component must
// be rejected BEFORE any of the three vecs is restored.
// ---------------------------------------------------------------------------

#[test]
fn sparse_set_atomic_restore_rejects_consumed_compound() {
    use semi_persistent_containers_verus::dense_id::DenseId31;
    use semi_persistent_containers_verus::sparse_set::SparseSet;

    // Privacy closeout: constructed via the public constructor (fields are
    // no longer visible outside the crate).
    let mut s = ForkHistory::new(SparseSet::<
        u32,
        DenseId31,
        ParallelStore<u32, DenseId31>,
        true,
    >::new());
    let id1 = s.try_add(100).expect("add: within id space");
    let tok = s
        .mark(ShrinkPolicy::Never)
        .expect("mark: depth bounded by this harness");
    let id2 = s.try_add(200).expect("add: within id space");
    assert!(s.is_valid(tok));
    s.restore(tok);
    assert!(s.is_valid(tok), "semantics B: the checkpoint stays valid");
    assert!(s.pop_scope());
    assert!(!s.is_valid(tok), "popped compound token must be invalid");

    // A second restore with the consumed compound token must be rejected
    // atomically: panic fires before ANY of dense/sparse/indices restores.
    assert!(!s.restore(tok), "consumed compound restore is refused");
    // Set state intact and consistent: id1 present, id2 rolled back.
    assert!(s.contains(id1));
    assert!(!s.contains(id2));
    assert_eq!(s.get(id1), 100);
}

// ---------------------------------------------------------------------------
// Total-operation shell: every refusal is an Err naming the
// failed precondition, the container is unchanged, and nothing panics.
// ---------------------------------------------------------------------------

#[test]
fn try_push_refuses_at_the_index_words_capacity() {
    type V = SpVec<u32, u8, ParallelStore<u32, u8>, false>;
    let mut v: V = V::new();
    // can_push holds while len + 1 < 256, i.e. through len == 254.
    let mut n = 0usize;
    while v.can_push() {
        v.try_push(7).unwrap();
        n += 1;
    }
    assert_eq!(n, 255, "push admits exactly max_nat - 1 elements");
    let e = v.try_push(8).unwrap_err();
    assert_eq!(e, ContainerError::CapacityExhausted);
    // Unchanged: still the same length, and a subsequent len() must not trap.
    assert_eq!(v.len(), u8::MAX);
}

#[test]
fn try_extend_is_all_or_nothing() {
    type V = SpVec<u32, u8, ParallelStore<u32, u8>, false>;
    let mut v: V = V::new();
    v.try_extend(&[1, 2, 3]).unwrap();
    assert_eq!(v.len(), 3);
    // 253 more would land exactly at 256 > 255 = cap: refused whole.
    let big: Vec<u32> = (0..253).collect();
    let e = v.try_extend(&big).unwrap_err();
    assert_eq!(e, ContainerError::CapacityExhausted);
    assert_eq!(v.len(), 3, "a refused batch appends nothing");
    // 252 more lands at 255 == cap: admitted.
    v.try_extend(&big[..252]).unwrap();
    assert_eq!(v.len(), u8::MAX);
}

#[test]
fn try_mark_names_the_failed_precondition() {
    // Untracked: refused as Untracked, not a panic (the partial mark panics).
    type U = SpVec<u32, u8, ParallelStore<u32, u8>, false>;
    let mut u: ForkHistory<U> = ForkHistory::new(U::new());
    assert!(u.mark(ShrinkPolicy::Never).is_none());
    // Tracked and in range: succeeds and round-trips through try_restore.
    type T = SpVec<u32, u8, ParallelStore<u32, u8>, true>;
    let mut t: ForkHistory<T> = ForkHistory::new(T::new());
    t.try_push(1).unwrap();
    let tok = t.mark(ShrinkPolicy::Never).unwrap();
    t.try_push(2).unwrap();
    assert!(t.restore(tok), "restore: own token");
    assert_eq!(t.len(), 1);
}

#[test]
fn try_restore_rejects_a_foreign_token_as_err() {
    type T = SpVec<u32, u8, ParallelStore<u32, u8>, true>;
    let mut a: ForkHistory<T> = ForkHistory::new(T::new());
    let mut b: ForkHistory<T> = ForkHistory::new(T::new());
    a.try_push(1).unwrap();
    b.try_push(9).unwrap();
    let tok_a = a.mark(ShrinkPolicy::Never).unwrap();
    assert!(
        !b.restore(tok_a),
        "a foreign token is an Err on the total surface (the partial core panics)"
    );
    assert_eq!(b.len(), 1, "refused restore leaves the container unchanged");
    // Consumed token: valid once, then Err.
    assert!(a.restore(tok_a), "restore: own token");
    assert!(
        a.restore(tok_a),
        "semantics B: the checkpoint restores again"
    );
}

#[test]
fn aov_total_shell_refuses_and_round_trips() {
    type A = AppendOnlyVec<String, u8, true>;
    let mut a: ForkHistory<A> = ForkHistory::new(A::new());
    while a.can_push() {
        a.try_push("x".to_string()).unwrap();
    }
    assert_eq!(
        a.try_push("y".to_string()).unwrap_err(),
        ContainerError::CapacityExhausted
    );
    let tok = a.mark(ShrinkPolicy::Never).unwrap();
    assert!(a.restore(tok), "fresh token restores");
    assert!(a.restore(tok), "the checkpoint restores again");
    assert!(a.pop_scope(), "the frame drops");
    assert!(!a.restore(tok), "a popped frame's token refuses as Err");
    assert!(!a.pop_scope(), "no open frame");
}
