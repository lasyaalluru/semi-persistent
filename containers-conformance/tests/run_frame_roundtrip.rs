// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance for the index-major run encoder's decode.
//!
//! `RunFrame::decode_exec_i` is `external_body` (its verified reference is
//! `compress_runs_writeorder`'s bijection `decode() == mapped_diffs` plus the
//! `decode_i` spec; doc 09: verified scalar reference, exec path
//! conformance-checked). This test backs that trust: for randomized diff streams,
//! compressing in write order and decoding back reproduces the exact input
//! sequence — the round-trip the proofs assert at the spec level but that Verus
//! does not run under `cargo test` (requires/ensures erase).
//!
//! What is asserted, for every generated stream of `(value, index)` diffs:
//!   - `decode_exec_i(compress_runs_writeorder(d)) == d` exactly (order and all),
//!   - so the encoder never drops, duplicates, or reorders a diff, and the
//!     index-column reconstruction via `from_nat(start + offset)` is exact.

use proptest::prelude::*;
use semi_persistent_containers_verus as verus;
use verus::diff_compress::compress_runs_writeorder;

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    #[test]
    fn run_frame_writeorder_roundtrips(
        // Values arbitrary; indices bounded so runs actually form (clustered
        // ranges) but also scatter, exercising both coalesced and singleton runs.
        diffs in prop::collection::vec(
            (any::<u32>(), 0u32..64u32),
            0..200usize,
        )
    ) {
        // usize indices for the encoder.
        let input: Vec<(u32, usize)> =
            diffs.iter().map(|&(v, i)| (v, i as usize)).collect();

        let frame = compress_runs_writeorder(&input);
        // Decode reconstructing u32 indices via from_nat(start + offset).
        let decoded: Vec<(u32, u32)> = frame.decode_exec_i::<u32>();

        // Exact round-trip against the original (value, index) sequence.
        prop_assert_eq!(decoded.len(), diffs.len());
        for (got, want) in decoded.iter().zip(diffs.iter()) {
            prop_assert_eq!(got.0, want.0);
            prop_assert_eq!(got.1, want.1);
        }
    }
}
