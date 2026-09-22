// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance for the value-dictionary encoder's hashmap dedup.
//!
//! `assign_codes` is `external_body` (a hash map dedup, O(N)); the verified
//! surface is `compress`'s bijection `decode(compress(d)) == d`, which rests on
//! assign_codes's trusted contract (codes parallel to input, each indexes the
//! dict, dict[codes[t]] == value[t]). This test backs that trust: the full
//! compress -> decode round-trip reproduces the input exactly (order and all),
//! for arbitrary value/index streams — including heavy value repetition, the
//! dedup's job.

use proptest::prelude::*;
use semi_persistent_containers_verus as verus;
use verus::diff_compress::compress;

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    #[test]
    fn dict_compress_roundtrips_exactly(
        // Values from a small alphabet so the dedup actually coalesces; indices
        // arbitrary (value-major keeps them verbatim, in order).
        pairs in prop::collection::vec((0u32..8u32, any::<u32>()), 0..300)
    ) {
        let diffs: Vec<(u32, u32)> = pairs;
        let frame = compress::<u32, u32>(&diffs);
        let decoded: Vec<(u32, u32)> = frame.decode_exec();
        // Value-major preserves order exactly (it is not a reordering codec).
        prop_assert_eq!(decoded, diffs);
    }
}
