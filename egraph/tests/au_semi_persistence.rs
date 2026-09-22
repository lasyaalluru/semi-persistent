// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Tests for semi-persistence of the AU search layers: BestResults, TermPool,
//! ContextStore, and the whole-search SearchSession mark/restore.

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::AuClassId;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::results::BestResults;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, anti_unify};
use semi_persistent_egraph::au::space::{ContextStore, OrId};
use semi_persistent_egraph::au::terms::{TermId, TermOp, TermPool};
use semi_persistent_egraph::containers::DenseId;
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::OpId;
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::LitValId;

type Eg = EGraph31<NiraLitVal, false, false>;

// ── BestResults ──

#[test]
fn best_results_mark_restore_undoes_overwrites() {
    let mut results: BestResults = BestResults::new();
    let or0 = OrId::from_usize(0);
    let t0 = TermId::from_usize(0);
    let t1 = TermId::from_usize(1);

    results.offer(or0, t0, (10, 10));
    let token = results.frame_depth();
    results.push_frame(ShrinkPolicy::Never);

    results.offer(or0, t1, (5, 3));
    assert_eq!(results.best_quality(or0), (5, 3));

    results.reset_frame(token);
    assert_eq!(results.best_quality(or0), (10, 10));
    assert_eq!(results.best_term(or0), Some(t0));
}

#[test]
fn best_results_mark_restore_truncates_new_entries() {
    let mut results: BestResults = BestResults::new();
    let or0 = OrId::from_usize(0);
    let or1 = OrId::from_usize(1);
    let t0 = TermId::from_usize(0);

    results.offer(or0, t0, (5, 5));
    let token = results.frame_depth();
    results.push_frame(ShrinkPolicy::Never);

    results.offer(or1, t0, (3, 3));
    assert_eq!(results.best_term(or1), Some(t0));

    results.reset_frame(token);
    assert_eq!(results.best_term(or1), None);
    assert_eq!(results.best_term(or0), Some(t0));
}

#[test]
fn best_results_nested_marks() {
    let mut results: BestResults = BestResults::new();
    let or0 = OrId::from_usize(0);
    let t0 = TermId::from_usize(0);
    let t1 = TermId::from_usize(1);
    let t2 = TermId::from_usize(2);

    results.offer(or0, t0, (20, 20));
    let outer = results.frame_depth();
    results.push_frame(ShrinkPolicy::Never);

    results.offer(or0, t1, (10, 10));
    let inner = results.frame_depth();
    results.push_frame(ShrinkPolicy::Never);

    results.offer(or0, t2, (5, 5));
    assert_eq!(results.best_quality(or0), (5, 5));

    results.reset_frame(inner);
    assert_eq!(results.best_quality(or0), (10, 10));

    results.reset_frame(outer);
    assert_eq!(results.best_quality(or0), (20, 20));
}

// ── TermPool ──

#[test]
fn term_pool_mark_restore_truncates() {
    let mut pool = TermPool::<OpId, LitValId>::new();
    let a = pool.intern(TermOp::EGraph(OpId::from_usize(0)), &[]);
    assert_eq!(pool.len(), 1);

    let token = pool.frame_depth();
    pool.push_frame(ShrinkPolicy::Never);

    let _b = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
    let _f = pool.intern(TermOp::EGraph(OpId::from_usize(2)), &[a, _b]);
    assert_eq!(pool.len(), 3);

    pool.reset_frame(token);
    assert_eq!(pool.len(), 1);
    assert_eq!(pool.size(a), 1);
}

#[test]
fn term_pool_hash_cons_survives_restore() {
    let mut pool = TermPool::<OpId, LitValId>::new();
    let a = pool.intern(TermOp::EGraph(OpId::from_usize(0)), &[]);
    let token = pool.frame_depth();
    pool.push_frame(ShrinkPolicy::Never);
    let _b = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
    pool.reset_frame(token);

    // Re-intern: same id (hash-cons survived).
    let a2 = pool.intern(TermOp::EGraph(OpId::from_usize(0)), &[]);
    assert_eq!(a, a2);
}

// ── ContextStore ──

#[test]
fn context_store_mark_restore() {
    let mut store: ContextStore = ContextStore::new();
    let c0 = AuClassId::from_usize(0);
    let c1 = AuClassId::from_usize(1);

    let ctx1 = store.intern(&[c0]);
    assert_eq!(store.len(), 2); // empty + ctx1

    let token = store.frame_depth();
    store.push_frame(ShrinkPolicy::Never);

    let _ctx2 = store.intern(&[c0, c1]);
    assert_eq!(store.len(), 3);

    store.reset_frame(token);
    assert_eq!(store.len(), 2);

    // ctx1 still works.
    assert!(store.contains(ctx1, c0));
    assert!(!store.contains(ctx1, c1));
}

// ── End-to-end: anti_unify produces consistent results ──

#[test]
fn anti_unify_deterministic_across_calls() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a = eg.register_op0("a", sort);
    let b = eg.register_op0("b", sort);
    let c = eg.register_op0("c", sort);
    let f = eg.register_op2("f", sort, sort, sort);
    let av = eg.add(a, &[]);
    let bv = eg.add(b, &[]);
    let cv = eg.add(c, &[]);
    let fab = eg.add(f, &[av, bv]);
    let fac = eg.add(f, &[av, cv]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let cfg = AuConfig {
        algorithm: AuAlgorithm::Exact,
        ..Default::default()
    };

    let r1 = anti_unify(&snap, fab, fac, &cfg).unwrap();
    let r2 = anti_unify(&snap, fab, fac, &cfg).unwrap();
    assert_eq!(r1.size, r2.size);
    assert_eq!(r1.pool.quality(r1.term_id), r2.pool.quality(r2.term_id));
}

#[test]
fn anti_unify_independent_across_different_pairs() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let ops: Vec<_> = (0..4)
        .map(|i| eg.register_op0(&format!("v{i}"), sort))
        .collect();
    let f = eg.register_op2("f", sort, sort, sort);
    let leaves: Vec<_> = ops.iter().map(|&o| eg.add(o, &[])).collect();
    let n1 = eg.add(f, &[leaves[0], leaves[1]]);
    let n2 = eg.add(f, &[leaves[0], leaves[2]]);
    let n3 = eg.add(f, &[leaves[2], leaves[3]]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let cfg = AuConfig {
        algorithm: AuAlgorithm::Exact,
        ..Default::default()
    };

    // Running AU on one pair should not affect the result of another.
    let r1 = anti_unify(&snap, n1, n2, &cfg).unwrap();
    let r2 = anti_unify(&snap, n1, n3, &cfg).unwrap();
    let r1b = anti_unify(&snap, n1, n2, &cfg).unwrap();
    assert_eq!(r1.size, r1b.size);
    // Both calls succeed without panic; sizes may or may not differ.
    let _ = r2.size;
}

// ── Token ownership ──
