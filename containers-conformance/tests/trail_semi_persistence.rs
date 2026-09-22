// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Property tests for the trail diff store's semi-persistence: random
//! op sequences (writes, marks, restores to any live token, pushes) against
//! a pure snapshot-stack model, with enough marks per case to cross
//! HOT_BUFFER so hot->cold compression fires mid-sequence and restores
//! cross the tier boundary. The trail store appends every write (no
//! capture check), so within-frame duplicates are the NORM here, and the
//! model's semantics - restore returns the state at mark, i.e. the
//! chronologically first capture wins - is exactly what the dedupe-first
//! fold must preserve through compression.

use proptest::prelude::*;
use semi_persistent_containers_verus as verus;
use semi_persistent_containers_verus::group::ForkHistory;
use verus::VecT;
use verus::vec::ShrinkPolicy;

#[derive(Clone, Debug)]
enum Op {
    /// Write value to cell (idx % len).
    Set { idx: u16, val: u64 },
    /// Same cell written `reps` times with varying values (duplicate burst).
    SetBurst { idx: u16, val: u64, reps: u8 },
    /// Mark; remembers the token and the model snapshot.
    Mark,
    /// Restore to the `sel % live_tokens`-th outstanding token (drops it and
    /// everything above).
    Restore { sel: u8 },
    /// Append a fresh cell (untracked region growth is exercised by pushes
    /// under a live frame).
    Push { val: u64 },
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        4 => (any::<u16>(), any::<u64>()).prop_map(|(idx, val)| Op::Set { idx, val }),
        2 => (any::<u16>(), any::<u64>(), 2u8..6).prop_map(|(idx, val, reps)| Op::SetBurst { idx, val, reps }),
        3 => Just(Op::Mark),
        2 => any::<u8>().prop_map(|sel| Op::Restore { sel }),
        1 => any::<u64>().prop_map(|val| Op::Push { val }),
    ]
}

fn config() -> ProptestConfig {
    ProptestConfig {
        cases: std::env::var("PROPTEST_CASES")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(64),
        ..ProptestConfig::default()
    }
}

const INIT_LEN: usize = 48;

proptest! {
    #![proptest_config(config())]

    /// Contents track the model after every op, and every restore lands
    /// exactly on the snapshot taken at its mark - through compression,
    /// duplicate bursts, and pushes.
    #[test]
    fn trail_random_ops_track_snapshot_model(ops in proptest::collection::vec(op_strategy(), 1..250)) {
        let mut v: ForkHistory<VecT<u64, u32>> = ForkHistory::new(VecT::new());
        let mut model: Vec<u64> = (0..INIT_LEN as u64).collect();
        for i in 0..INIT_LEN {
            v.try_push(i as u64).expect("seed push");
        }
        // (token, model snapshot at that mark)
        let mut marks: Vec<(verus::vec::VecToken, Vec<u64>)> = Vec::new();

        for op in ops {
            match op {
                Op::Set { idx, val } => {
                    if !model.is_empty() {
                        let i = (idx as usize) % model.len();
                        v.set_index(i as u32, val);
                        model[i] = val;
                    }
                }
                Op::SetBurst { idx, val, reps } => {
                    if !model.is_empty() {
                        let i = (idx as usize) % model.len();
                        for r in 0..reps {
                            let w = val.wrapping_add(r as u64);
                            v.set_index(i as u32, w);
                            model[i] = w;
                        }
                    }
                }
                Op::Mark => {
                    let t = v.mark(ShrinkPolicy::Never).expect("mark");
                    marks.push((t, model.clone()));
                }
                Op::Restore { sel } => {
                    if !marks.is_empty() {
                        let pick = (sel as usize) % marks.len();
                        let tok = marks[pick].0;
                        let snap = marks[pick].1.clone();
                        assert!(v.restore(tok), "restore");
                        model = snap;
                        marks.truncate(pick);
                    }
                }
                Op::Push { val } => {
                    if v.try_push(val).is_ok() {
                        model.push(val);
                    }
                }
            }
            // Differential check after EVERY op.
            prop_assert_eq!(model.len(), v.len() as usize);
            for (i, &expected) in model.iter().enumerate() {
                prop_assert_eq!(v.get_index(i as u32), expected, "cell {} diverged", i);
            }
        }
    }

    /// Deep-history stress: many marks with duplicate-heavy frames force
    /// several compression passes, then unwind the entire stack token by
    /// token; every level must reproduce its snapshot exactly.
    #[test]
    fn trail_deep_unwind_after_compression(seed in any::<u64>(), frames in 10usize..24) {
        let mut v: ForkHistory<VecT<u64, u32>> = ForkHistory::new(VecT::new());
        let mut model: Vec<u64> = (0..INIT_LEN as u64).collect();
        for i in 0..INIT_LEN {
            v.try_push(i as u64).expect("seed push");
        }
        let mut marks: Vec<(verus::vec::VecToken, Vec<u64>)> = Vec::new();
        let mut s = seed | 1;
        for _f in 0..frames {
            let t = v.mark(ShrinkPolicy::Never).expect("mark");
            marks.push((t, model.clone()));
            // Duplicate-heavy frame: 6 cells, 3 writes each.
            for _r in 0..3 {
                for _w in 0..6 {
                    s = s.wrapping_mul(6364136223846793005).wrapping_add(1);
                    let i = ((s >> 33) as usize) % INIT_LEN;
                    v.set_index(i as u32, s);
                    model[i] = s;
                }
            }
        }
        while let Some((tok, snap)) = marks.pop() {
            assert!(v.restore(tok), "restore");
            for (i, &expected) in snap.iter().enumerate().take(INIT_LEN) {
                prop_assert_eq!(v.get_index(i as u32), expected, "cell {} diverged at depth {}", i, marks.len());
            }
            model = snap;
        }
        let _ = model;
    }
}
