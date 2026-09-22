// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The typed external history manager (`group::ForkHistory<M>`): a group of
//! one column, a pair of columns driven as one, the lockstep theorem at
//! runtime, and the refusals (drift behind the group's back, foreign and
//! dead tokens, adopting a member that already has frames).

use semi_persistent_containers_verus::append_only_vec::AppendOnlyVec;
use semi_persistent_containers_verus::bplus::BPlusTreeSet;
use semi_persistent_containers_verus::bplus_layout::Layout64U32;
use semi_persistent_containers_verus::bplus_search::BinarySearch;
use semi_persistent_containers_verus::circular_list::CircularList;
use semi_persistent_containers_verus::dense_id::{DenseId31, DenseId63};
use semi_persistent_containers_verus::diff_compress::CompressionMode;
use semi_persistent_containers_verus::eclasses::EClasses;
use semi_persistent_containers_verus::group::{ForkHistory, Member, Pair};
use semi_persistent_containers_verus::index_like::IndexLike;
use semi_persistent_containers_verus::list::ListArena;
use semi_persistent_containers_verus::map::SpMap;
use semi_persistent_containers_verus::opt::DenseId;
use semi_persistent_containers_verus::sparse_set::SparseSet;
use semi_persistent_containers_verus::union_find::{NoJust, UnionFind};
use semi_persistent_containers_verus::{ParallelStore, ShrinkPolicy, VecP};

semi_persistent_containers_verus::define_id31! {
    pub struct GroupClassKey / StoredGroupClassKey, "gk";
}

type Col = VecP<u32, u32, true>;
type Log = AppendOnlyVec<u64, u32, true>;

fn col(n: u32) -> Col {
    let mut v = Col::new();
    for i in 0..n {
        v.try_push(i).unwrap();
    }
    v
}

fn vals(v: &Col) -> Vec<u32> {
    (0..v.len()).map(|i| v.get(i)).collect()
}

#[test]
fn group_of_one_marks_restores_and_pops_in_lockstep() {
    let mut g = ForkHistory::new(col(4));
    assert_eq!(g.depth(), 0);
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.set(0u32, 9);
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.set(1u32, 9);
    assert_eq!(g.depth(), 2);
    assert_eq!(g.member.depth(), 2);
    assert!(g.in_lockstep());

    // Semantics B: back to the checkpoint, its frame stays open, the token
    // stays valid and can be restored to again.
    assert!(g.restore(t1));
    assert_eq!(vals(&g.member), vec![9, 1, 2, 3]);
    assert_eq!(g.depth(), 2);
    assert!(g.is_valid(t1));
    g.member.set(2u32, 9);
    assert!(g.restore(t1));
    assert_eq!(vals(&g.member), vec![9, 1, 2, 3]);

    // The pop drops that frame and kills its token; the ancestor survives.
    assert!(g.pop_scope());
    assert_eq!(g.depth(), 1);
    assert!(!g.is_valid(t1));
    assert!(g.is_valid(t0));
    assert!(!g.restore(t1));

    // The fused pop lands at the token's depth and kills it.
    assert!(g.restore_and_pop(t0));
    assert_eq!(vals(&g.member), vec![0, 1, 2, 3]);
    assert_eq!(g.depth(), 0);
    assert_eq!(g.member.depth(), 0);
    assert!(!g.is_valid(t0));
    assert!(!g.restore(t0));
    assert!(!g.restore_and_pop(t0));
    assert!(!g.pop_scope(), "nothing to pop");
}

#[test]
fn a_frame_pushed_behind_the_groups_back_is_refused_until_repaired() {
    let mut g = ForkHistory::new(col(2));
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.set(0u32, 5);
    // Drift: the member's own frame stack moves without the group.
    g.member.push_frame(ShrinkPolicy::Never);
    assert!(!g.in_lockstep());
    assert!(g.mark(ShrinkPolicy::Never).is_none());
    assert!(!g.restore(t0));
    assert!(!g.restore_and_pop(t0));
    assert!(!g.pop_scope());
    assert_eq!(vals(&g.member), vec![5, 1], "a refusal changes nothing");
    // Repair the drift and the group answers again.
    g.member.pop_frame();
    assert!(g.in_lockstep());
    assert!(g.restore(t0));
    assert_eq!(vals(&g.member), vec![0, 1]);
    assert_eq!(g.depth(), 1);
}

#[test]
fn foreign_tokens_are_refused() {
    let mut a = ForkHistory::new(col(1));
    let mut b = ForkHistory::new(col(1));
    let tb = b.mark(ShrinkPolicy::Never).expect("mark");
    let ta = a.mark(ShrinkPolicy::Never).expect("mark");
    assert!(!a.is_valid(tb));
    assert!(!a.restore(tb));
    assert!(!a.restore_and_pop(tb));
    assert!(a.is_valid(ta));
    assert!(b.is_valid(tb));
    assert!(!b.is_valid(ta));
}

#[test]
fn a_pair_of_columns_moves_as_one() {
    let mut g = ForkHistory::new(Pair::new(col(2), Log::new()));
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.a.set(0u32, 7);
    g.member.b.try_push(42).unwrap();
    g.member.b.try_push(43).unwrap();
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.a.set(1u32, 8);
    g.member.b.try_push(44).unwrap();
    assert_eq!(g.member.a.depth(), 2);
    assert_eq!(g.member.b.depth(), 2);

    assert!(g.restore(t1));
    assert_eq!(vals(&g.member.a), vec![7, 1]);
    assert_eq!(g.member.b.as_slice(), &[42, 43]);
    assert_eq!(g.depth(), 2);

    assert!(g.restore_and_pop(t0));
    assert_eq!(vals(&g.member.a), vec![0, 1]);
    assert!(g.member.b.as_slice().is_empty());
    assert_eq!(g.depth(), 0);
    assert_eq!(g.member.a.depth(), 0);
    assert_eq!(g.member.b.depth(), 0);
}

#[test]
#[should_panic(expected = "already has open frames")]
fn adopting_a_member_with_open_frames_is_refused() {
    let mut v = col(1);
    v.push_frame(ShrinkPolicy::Never);
    let _g = ForkHistory::new(v);
}

#[test]
#[should_panic(expected = "not at the same depth")]
fn pairing_members_out_of_step_is_refused() {
    let mut v = col(1);
    v.push_frame(ShrinkPolicy::Never);
    let _p = Pair::new(v, Log::new());
}

/// A restored-below token is cut for good: a NEW mark at its depth mints a
/// fresh token and never revives it; a popped frame's token is refused too.
#[test]
fn a_cut_token_is_not_revived_by_a_new_mark_at_its_depth() {
    let mut g = ForkHistory::new(col(4));
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark"); // depth 0, state S0
    g.member.set(0u32, 1); // S1
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark"); // depth 1
    g.member.set(1u32, 2); // S2
    assert!(g.restore(t0), "t0 is live");
    assert_eq!(vals(&g.member), vec![0, 1, 2, 3], "back to S0");
    assert_eq!(g.depth(), 1, "semantics B: the restored frame stays open");
    assert!(g.restore(t0), "the checkpoint is reusable");
    assert!(!g.restore(t1), "abandoned future: refused");
    g.member.set(2u32, 3); // S3, in t0's reopened frame
    let t0b = g
        .mark(ShrinkPolicy::Never)
        .expect("mark above the checkpoint"); // depth 1
    g.member.set(3u32, 4); // S4
    assert!(
        !g.restore(t1),
        "the abandoned token stays refused after a re-mark at its depth"
    );
    assert!(g.restore(t0b), "the new mark's own token restores");
    assert_eq!(vals(&g.member), vec![0, 1, 3, 3], "to S3");
    assert!(g.restore(t0), "the checkpoint below is still valid");
    assert_eq!(vals(&g.member), vec![0, 1, 2, 3], "back to S0 again");
    assert!(!g.restore(t0b), "restoring below it cut the newer token");
    assert!(g.pop_scope(), "drop the checkpoint's frame");
    assert_eq!(g.depth(), 0);
    assert!(!g.restore(t0), "a popped frame's token is refused");
    g.member.set(2u32, 3); // S3 again
    let t0c = g.mark(ShrinkPolicy::Never).expect("mark");
    assert!(
        !g.restore(t0),
        "the old token stays dead under a fresh mark at its depth"
    );
    assert!(g.restore(t0c), "the new mark's own token restores");
    assert_eq!(vals(&g.member), vec![0, 1, 3, 3], "to S3");
}

// ---------------------------------------------------------------------------
// Grouped history, randomized: three columns of different widths under one
// `ForkHistory` (a nested `Pair`), driven by random marks, writes and
// restores to any live token. After every restore each column equals its own
// typed oracle snapshot taken at that mark, the group sits one above the
// depth it had when the token was minted (semantics B), the checkpoint
// restores again, and every token minted after it is refused forever.
// ---------------------------------------------------------------------------

type V32 = VecP<u32, u32, true>;
type V64 = VecP<u64, u64, true>;
type V16 = VecP<u16, u32, true>;
type Trio = Pair<Pair<V32, V64>, V16>;

const TRIO_N: usize = 64;

fn trio() -> Trio {
    let mut a = V32::new_with_mode(CompressionMode::Auto);
    let mut b = V64::new_with_mode(CompressionMode::Auto);
    let mut c = V16::new_with_mode(CompressionMode::Auto);
    for _ in 0..TRIO_N {
        a.try_push(0).unwrap();
        b.try_push(0).unwrap();
        c.try_push(0).unwrap();
    }
    Pair::new(Pair::new(a, b), c)
}

fn trio_poke(t: &mut Trio, m: usize, i: usize, v: usize) {
    match m {
        0 => t.a.a.set(i as u32, v as u32),
        1 => t.a.b.set(i as u64, v as u64),
        _ => t.b.set(i as u32, v as u16),
    }
}

fn trio_contents(t: &Trio) -> [Vec<usize>; 3] {
    [
        (0..TRIO_N).map(|i| t.a.a.get(i as u32) as usize).collect(),
        (0..TRIO_N).map(|i| t.a.b.get(i as u64) as usize).collect(),
        (0..TRIO_N).map(|i| t.b.get(i as u32) as usize).collect(),
    ]
}

#[test]
fn grouped_history_random_sequences_land_in_lockstep() {
    use proptest::prelude::*;
    use proptest::test_runner::{Config, TestRunner};
    use semi_persistent_containers_verus::history::GroupToken;

    #[derive(Clone, Debug)]
    enum Op {
        Mark,
        Poke(usize, usize, usize),
        Restore(usize),
    }
    let strat = proptest::collection::vec(
        prop_oneof![
            2 => Just(Op::Mark),
            6 => (0..3usize, 0..TRIO_N, 0..61usize).prop_map(|(m, i, v)| Op::Poke(m, i, v)),
            2 => (0..16usize).prop_map(Op::Restore),
        ],
        1..96,
    );
    let mut runner = TestRunner::new(Config {
        cases: 256,
        ..Config::default()
    });
    runner
        .run(&strat, |ops| {
            let mut g = ForkHistory::new(trio());
            let mut oracles: [Vec<usize>; 3] = [vec![0; TRIO_N], vec![0; TRIO_N], vec![0; TRIO_N]];
            // Live tokens with the depth before the mark and the oracle
            // snapshot at the mark; tokens the restores abandon go stale.
            let mut live: Vec<(GroupToken, usize, [Vec<usize>; 3])> = Vec::new();
            let mut stale: Vec<GroupToken> = Vec::new();
            for op in ops {
                match op {
                    Op::Mark => {
                        let depth = g.depth();
                        let t = g.mark(ShrinkPolicy::Never).expect("mark headroom");
                        prop_assert_eq!(g.depth(), depth + 1, "mark bumps the group depth");
                        live.push((t, depth, oracles.clone()));
                    }
                    Op::Poke(m, i, v) => {
                        trio_poke(&mut g.member, m, i, v);
                        oracles[m][i] = v;
                    }
                    Op::Restore(k) => {
                        if live.is_empty() {
                            continue;
                        }
                        let k = k % live.len();
                        let (t, depth, snap) = live[k].clone();
                        prop_assert!(g.restore(t), "live token must restore");
                        prop_assert_eq!(
                            g.depth(),
                            depth + 1,
                            "restore keeps the mark's frame open (semantics B)"
                        );
                        prop_assert!(g.restore(t), "the checkpoint is reusable");
                        prop_assert_eq!(
                            g.depth(),
                            depth + 1,
                            "a repeated restore lands on the same depth"
                        );
                        oracles = snap;
                        // The checkpoint stays live; the deeper tokens (the
                        // abandoned future) are refused forever.
                        for t in live.drain(k + 1..) {
                            stale.push(t.0);
                        }
                    }
                }
                prop_assert!(g.in_lockstep(), "every column at the history depth");
                let got = trio_contents(&g.member);
                for m in 0..3 {
                    prop_assert_eq!(
                        &got[m],
                        &oracles[m],
                        "column {} diverged from its oracle",
                        m
                    );
                }
                for &t in &stale {
                    prop_assert!(!g.restore(t), "stale token must be refused");
                }
            }
            Ok(())
        })
        .unwrap();
}

// ---------------------------------------------------------------------------
// Composites as members: the same group protocol over their token-free cores.
// ---------------------------------------------------------------------------

#[test]
fn a_sparse_set_is_a_member() {
    let mut g = ForkHistory::new(SparseSet::<u32, u32, ParallelStore<u32, u32>, true>::new());
    let a = g.member.try_add(10).unwrap();
    let b = g.member.try_add(20).unwrap();
    let c = g.member.try_add(30).unwrap();
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.remove(b);
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    let d = g.member.try_add(40).unwrap();
    assert!(g.member.contains(d));
    assert_eq!(g.depth(), 2);

    assert!(g.restore(t1));
    assert!(g.member.contains(a) && !g.member.contains(b) && g.member.contains(c));
    assert_eq!(g.member.len().as_usize(), 2);
    assert_eq!(g.depth(), 2);
    assert!(g.is_valid(t1), "semantics B: the checkpoint stays valid");

    assert!(g.restore_and_pop(t0));
    assert!(g.member.contains(a) && g.member.contains(b) && g.member.contains(c));
    assert_eq!(g.member.len().as_usize(), 3);
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0) && !g.is_valid(t1));
}

#[test]
fn a_ring_is_a_member() {
    let mut g = ForkHistory::new(CircularList::<u32, DenseId63, true>::new());
    let a = g.member.try_add_singleton(1).unwrap();
    let b = g.member.try_add_singleton(2).unwrap();
    let c = g.member.try_add_singleton(3).unwrap();
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.splice(a, b);
    g.member.splice(a, c);
    assert_ne!(
        g.member.next_of(a).to_usize(),
        a.to_usize(),
        "a's ring grew"
    );
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.set_payload(a, 100);

    assert!(g.restore(t1));
    assert_eq!(g.member.payload_of(a), 1);
    assert_ne!(g.member.next_of(a).to_usize(), a.to_usize());
    assert!(g.is_valid(t1));

    assert!(g.restore_and_pop(t0));
    assert_eq!(
        g.member.next_of(a).to_usize(),
        a.to_usize(),
        "singletons again"
    );
    assert_eq!(g.member.next_of(b).to_usize(), b.to_usize());
    assert_eq!(g.member.len().as_usize(), 3);
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0));
}

#[test]
fn a_list_arena_is_a_member() {
    let mut g = ForkHistory::new(ListArena::<u32, DenseId63, DenseId63, true>::new());
    let l = g.member.try_new_list().unwrap();
    g.member.try_append(l, 1).unwrap();
    g.member.try_append(l, 2).unwrap();
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.try_append(l, 3).unwrap();
    assert_eq!(g.member.len(l).as_usize(), 3);

    assert!(g.restore(t0));
    assert_eq!(g.member.len(l).as_usize(), 2);
    g.member.try_append(l, 4).unwrap();
    assert_eq!(g.member.len(l).as_usize(), 3);
    assert!(g.restore(t0), "the checkpoint is reusable");
    assert_eq!(g.member.len(l).as_usize(), 2);
    assert_eq!(g.depth(), 1);

    assert!(g.pop_scope());
    assert_eq!(g.member.len(l).as_usize(), 2);
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0));
    assert!(!g.restore(t0));
}

#[test]
fn a_union_find_is_a_member() {
    let mut g = ForkHistory::new(UnionFind::<DenseId63, NoJust, true, false>::new());
    let a = g.member.try_make_set().unwrap();
    let b = g.member.try_make_set().unwrap();
    let c = g.member.try_make_set().unwrap();
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.union(a, b);
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.union(b, c);
    assert_eq!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(c).to_usize()
    );

    assert!(g.restore(t1));
    assert_eq!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(b).to_usize()
    );
    assert_ne!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(c).to_usize()
    );
    assert_eq!(g.depth(), 2);
    assert!(g.is_valid(t1));
    g.member.union(a, c);
    assert!(g.restore(t1), "the checkpoint is reusable");
    assert_ne!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(c).to_usize()
    );

    assert!(g.restore_and_pop(t0));
    assert_ne!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(b).to_usize()
    );
    assert_eq!(g.member.len().as_usize(), 3);
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0) && !g.is_valid(t1));
}

#[test]
fn a_map_is_a_member() {
    let mut g = ForkHistory::new(SpMap::<u64, (), usize, true>::new());
    for k in 0..8u64 {
        g.member.try_insert(k, ()).unwrap();
    }
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    for k in 100..104u64 {
        g.member.try_insert(k, ()).unwrap();
    }
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.try_insert(200, ()).unwrap();
    assert_eq!(g.member.len(), 13);

    assert!(g.restore(t1));
    assert_eq!(g.member.len(), 12);
    assert!(g.member.contains_key(&103) && !g.member.contains_key(&200));
    assert!(g.is_valid(t1));
    g.member.try_insert(300, ()).unwrap();
    assert!(g.restore(t1), "the checkpoint is reusable");
    assert_eq!(g.member.len(), 12);

    assert!(g.restore_and_pop(t0));
    assert_eq!(g.member.len(), 8);
    assert!(!g.member.contains_key(&100));
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0) && !g.is_valid(t1));
}

#[test]
fn a_bplus_tree_is_a_member() {
    let mut g = ForkHistory::new(BPlusTreeSet::<DenseId31, Layout64U32, BinarySearch, true>::new());
    for k in 0..40u32 {
        g.member.try_insert(DenseId31::new(k)).unwrap();
    }
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    for k in 100..130u32 {
        g.member.try_insert(DenseId31::new(k)).unwrap();
    }
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.try_insert(DenseId31::new(500)).unwrap();
    assert_eq!(g.member.len(), 71);

    assert!(g.restore(t1));
    assert_eq!(g.member.len(), 70);
    assert!(g.member.contains(DenseId31::new(129)) && !g.member.contains(DenseId31::new(500)));
    assert!(g.is_valid(t1));
    g.member.try_insert(DenseId31::new(600)).unwrap();
    assert!(g.restore(t1), "the checkpoint is reusable");
    assert_eq!(g.member.len(), 70);

    assert!(g.restore_and_pop(t0));
    assert_eq!(g.member.len(), 40);
    assert!(!g.member.contains(DenseId31::new(100)));
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0) && !g.is_valid(t1));
}

#[test]
fn e_classes_are_a_member() {
    let mut g = ForkHistory::new(EClasses::<
        DenseId31,
        GroupClassKey,
        DenseId31,
        DenseId31,
        NoJust,
        true,
        false,
    >::new());
    let (a, _) = g.member.try_add_singleton();
    let (b, _) = g.member.try_add_singleton();
    let (c, _) = g.member.try_add_singleton();
    let t0 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.merge(a, b);
    let t1 = g.mark(ShrinkPolicy::Never).expect("mark");
    g.member.merge(b, c);
    assert_eq!(g.member.num_classes().as_usize(), 1);

    assert!(g.restore(t1));
    assert_eq!(g.member.num_classes().as_usize(), 2);
    assert_eq!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(b).to_usize()
    );
    assert_ne!(
        g.member.find_const(a).to_usize(),
        g.member.find_const(c).to_usize()
    );
    assert!(g.is_valid(t1));
    g.member.merge(a, c);
    assert!(g.restore(t1), "the checkpoint is reusable");
    assert_eq!(g.member.num_classes().as_usize(), 2);

    assert!(g.restore_and_pop(t0));
    assert_eq!(g.member.num_classes().as_usize(), 3);
    assert_eq!(g.depth(), 0);
    assert!(!g.is_valid(t0) && !g.is_valid(t1));
}
