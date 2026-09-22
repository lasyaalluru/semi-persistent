// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Proves the SEMPER_COMPRESS=auto lever ACTIVATES (not merely that runs under it
//! stay green): a default-constructed ParallelStore-backed vec becomes the
//! per-frame-adaptive representation (marks observably seal cold frames), and its
//! restore matches an uncompressed oracle. Own test file = own process, so the
//! in-process set_var lands before the lever's OnceLock caches.

use semi_persistent_containers_verus as verus;
use semi_persistent_containers_verus::group::ForkHistory;
use verus::vec::ShrinkPolicy;

type V = verus::Vec<u32, u32, verus::parallel_store::ParallelStore<u32, u32>, true>;

#[test]
fn env_auto_activates_and_matches_oracle() {
    // Single-threaded test binary (one test), set before any construction.
    unsafe { std::env::set_var("SEMPER_COMPRESS", "auto") };

    const N: u32 = 500;
    let mut v = ForkHistory::new(V::new()); // default constructor: the lever's target
    let mut oracle = ForkHistory::new(V::new_with_mode(
        verus::diff_compress::CompressionMode::None,
    ));
    for _ in 0..N {
        v.try_push(0).unwrap();
        oracle.try_push(0).unwrap();
    }
    let t0 = v.mark(ShrinkPolicy::Never).unwrap();
    let o0 = oracle.mark(ShrinkPolicy::Never).unwrap();
    // ACTIVATION under the ruled cadence: an activated column compresses
    // once more than HOT_BUFFER (8) hot frames exist, folding each frame's
    // contiguous distinct-valued writes into run cold frames; the plain
    // oracle never compresses. March both columns past the buffer with
    // identical writes, then compare tracking sizes.
    for round in 1..12u32 {
        for i in 0..N {
            v.set_index(i, i + round);
            oracle.set_index(i, i + round);
        }
        // The activated column reclaims at mark (ruled order: compress,
        // then release over-committed capacity); the plain oracle keeps
        // ShrinkPolicy::Never so its log capacity reflects its length.
        let _ = v
            .mark(ShrinkPolicy::IfOverallocated {
                factor: 2,
                headroom: 64,
            })
            .unwrap();
        let _ = oracle.mark(ShrinkPolicy::Never).unwrap();
    }
    let bytes_after = v.tracking_bytes();
    let plain_bytes = oracle.tracking_bytes();
    assert!(
        bytes_after < plain_bytes,
        "lever did not activate: compressed {bytes_after} !< plain {plain_bytes}"
    );

    for i in 0..N {
        v.set_index(i, i * 2);
        oracle.set_index(i, i * 2);
    }
    assert!(v.restore(t0), "restore: own token");
    assert!(oracle.restore(o0), "restore: own token");
    let a: Vec<u32> = (0..N).map(|i| v.get_index(i)).collect();
    let b: Vec<u32> = (0..N).map(|i| oracle.get_index(i)).collect();
    assert_eq!(a, b, "compressed restore diverged from the oracle");
}
