// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exercises the fork-history reclamation core (GenStamps): a restore cuts the
//! live length at the restored depth, O(1)-invalidating the consumed token and
//! the abandoned future while the surviving spine's tokens stay valid, and a
//! re-mint at a cut depth hands out a fresh stamp so the consumed token never
//! revives. The invalidation is proved (`GenStamps::cut_from`/`mint_at`
//! postconditions); this runs the executable path Verus erases.

use semi_persistent_containers_verus as verus;
use verus::GenStamps;

#[test]
fn cut_invalidates_from_the_depth_up_keeps_spine() {
    let mut g = GenStamps::new();

    // Mint a stamp per depth on the current branch.
    let stamps: Vec<u64> = (0..8).map(|d| g.mint_at(d)).collect();
    let (t2, t5, t6) = (stamps[2], stamps[5], stamps[6]);
    assert!(g.is_valid(2, t2) && g.is_valid(5, t5) && g.is_valid(6, t6));
    assert_eq!(g.live_depths(), 8);

    // A restore to depth 5: the token at 5 is consumed, everything deeper is
    // the abandoned future.
    g.cut_from(5);
    assert_eq!(g.live_depths(), 5);

    assert!(g.is_valid(2, t2), "shallow token survives the backjump");
    assert!(!g.is_valid(5, t5), "the consumed token is dead");
    assert!(!g.is_valid(6, t6), "deeper token is dead");

    // A fresh mint at depth 5 after the cut is valid; the consumed stamp is not.
    let t5b = g.mint_at(5);
    assert!(g.is_valid(5, t5b));
    assert!(t5b != t5, "the new stamp differs from the consumed one");
    assert!(
        !g.is_valid(5, t5),
        "a re-mint at the same depth does not revive the consumed token"
    );
    assert_eq!(g.live_depths(), 6);
}

#[test]
fn stamps_are_never_handed_out_twice() {
    let mut g = GenStamps::new();
    let mut seen = std::collections::HashSet::new();
    for round in 0..50 {
        for d in 0..20 {
            assert!(
                seen.insert(g.mint_at(d)),
                "round {round} depth {d}: stamp reused"
            );
        }
        g.cut_from(0);
    }
}

#[test]
fn out_of_range_depth_is_invalid() {
    let mut g = GenStamps::new();
    for d in 0..4 {
        g.mint_at(d);
    }
    assert!(!g.is_valid(4, 1));
    assert!(!g.is_valid(100, 1));
}
