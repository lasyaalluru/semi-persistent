// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `restore_and_pop(t)` is `restore(t)` then `pop_scope()`, fused (design doc
//! 08 §1): same contents, same depth, same token fate — on one pop core, so it
//! costs what the legacy restore costs. These tests pin the equivalence on a
//! column and a composite, the depth and token fate, and the refusal path.

use semi_persistent_containers_verus::group::ForkHistory;
use semi_persistent_containers_verus::map::SpMap;
use semi_persistent_containers_verus::{ShrinkPolicy, VecP};

type V = VecP<u64, u32, true>;
type M = SpMap<u64, (), usize, true>;

fn column(n: u64) -> V {
    let mut v = V::new();
    for i in 0..n {
        v.try_push(i).unwrap();
    }
    v
}

fn values(v: &V) -> Vec<u64> {
    (0..v.len()).map(|i| v.get(i)).collect()
}

#[test]
fn fused_equals_restore_then_pop_on_a_column() {
    let mut a = ForkHistory::new(column(8));
    let mut b = ForkHistory::new(column(8));
    let ta = a.mark(ShrinkPolicy::Never).unwrap();
    let tb = b.mark(ShrinkPolicy::Never).unwrap();
    for v in [&mut a, &mut b] {
        v.set(1u32, 100);
        v.try_push(200).unwrap();
        v.mark(ShrinkPolicy::Never).unwrap();
        v.set(2u32, 300);
    }
    assert_eq!(a.depth(), 2);

    assert!(a.restore(ta), "restore: own token");
    assert!(a.is_valid(ta), "restore keeps the checkpoint open");
    assert!(a.pop_scope());
    assert!(b.restore_and_pop(tb), "restore: own token");

    assert_eq!(values(&a), values(&b));
    assert_eq!(values(&b), (0..8u64).collect::<Vec<_>>());
    assert_eq!(a.depth(), 0);
    assert_eq!(b.depth(), 0);
    assert!(!a.is_valid(ta), "the pop kills the checkpoint");
    assert!(!b.is_valid(tb), "the fused op kills the checkpoint");
    assert!(!b.restore_and_pop(tb));
    assert!(!b.restore(tb));
}

#[test]
fn fused_op_lands_at_the_token_depth_and_kills_deeper_tokens() {
    let mut v = ForkHistory::new(column(4));
    let t0 = v.mark(ShrinkPolicy::Never).unwrap();
    v.set(0u32, 9);
    let t1 = v.mark(ShrinkPolicy::Never).unwrap();
    v.set(1u32, 9);
    let t2 = v.mark(ShrinkPolicy::Never).unwrap();
    v.set(2u32, 9);
    assert_eq!(v.depth(), 3);

    assert!(v.restore_and_pop(t1), "restore: own token");
    assert_eq!(v.depth(), 1, "frame t1 and everything above it are gone");
    assert_eq!(values(&v), vec![9, 1, 2, 3]);
    assert!(v.is_valid(t0), "the ancestor survives");
    assert!(!v.is_valid(t1));
    assert!(!v.is_valid(t2));
    // A fresh mark at depth 1 mints a new stamp: the old t1 never revives.
    let t1b = v.mark(ShrinkPolicy::Never).unwrap();
    assert!(!v.is_valid(t1));
    assert!(v.is_valid(t1b));
    assert!(v.restore_and_pop(t0), "restore: own token");
    assert_eq!(v.depth(), 0);
    assert_eq!(values(&v), vec![0, 1, 2, 3]);
}

#[test]
fn fused_op_refuses_a_foreign_token_without_mutating() {
    let mut a = ForkHistory::new(column(3));
    let mut b = ForkHistory::new(column(3));
    let tb = b.mark(ShrinkPolicy::Never).unwrap();
    a.mark(ShrinkPolicy::Never).unwrap();
    a.set(0u32, 7);
    assert!(!a.restore_and_pop(tb));
    assert_eq!(values(&a), vec![7, 1, 2]);
    assert_eq!(a.depth(), 1);
}

#[test]
fn fused_equals_restore_then_pop_on_a_map() {
    let mut a: ForkHistory<M> = ForkHistory::new(SpMap::new());
    let mut b: ForkHistory<M> = ForkHistory::new(SpMap::new());
    for m in [&mut a, &mut b] {
        for k in 0..16u64 {
            m.try_insert(k, ()).unwrap();
        }
    }
    let ta = a.mark(ShrinkPolicy::Never).unwrap();
    let tb = b.mark(ShrinkPolicy::Never).unwrap();
    for m in [&mut a, &mut b] {
        for k in 100..140u64 {
            m.try_insert(k, ()).unwrap();
        }
    }
    assert!(a.restore(ta), "restore: own token");
    assert!(a.pop_scope());
    assert!(b.restore_and_pop(tb), "restore: own token");
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), 16);
    assert_eq!(a.depth(), 0);
    assert_eq!(b.depth(), 0);
    for k in 0..16u64 {
        assert!(a.contains_key(&k) && b.contains_key(&k));
    }
    assert!(!a.contains_key(&120) && !b.contains_key(&120));
    assert!(!b.restore_and_pop(tb));
}
