// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Round-trip check for the bit-packed dictionary code column
//! (`Codes::Packed`, `pack_codes` / `packed_get`). The pack/extract pair is
//! `external_body` (variable-width bit arithmetic is not a tractable proof surface),
//! so its contract — `from_usize` produces a column whose `get(i)` reproduces the
//! input code — is checked here: this is the trust-ledger obligation the
//! `Codes::Packed` doc names. Covers all three sub-byte widths (1/2/4 bits, for
//! D <= 2/4/16), the boundary where a code fills its field, and cross-word packing.

use proptest::prelude::*;

use semi_persistent_containers_verus as verus;
use verus::diff_compress::Codes;

fn roundtrip(codes: &[usize], dict_len: usize) {
    let v: Vec<usize> = codes.to_vec();
    let packed = Codes::from_usize(&v, dict_len);
    assert_eq!(packed.len(), codes.len());
    for (i, &c) in codes.iter().enumerate() {
        assert_eq!(packed.get(i), c, "code {i} (dict_len {dict_len})");
    }
}

proptest! {
    // D <= 2 -> 1 bit per code. Enough codes to span several u64 words (64/word).
    #[test]
    fn packed_1bit(codes in prop::collection::vec(0usize..2, 0..300)) {
        roundtrip(&codes, 2);
    }

    // D <= 4 -> 2 bits per code (32/word).
    #[test]
    fn packed_2bit(codes in prop::collection::vec(0usize..4, 0..300)) {
        roundtrip(&codes, 4);
    }

    // D <= 16 -> 4 bits per code (16/word), including max-value codes filling the field.
    #[test]
    fn packed_4bit(codes in prop::collection::vec(0usize..16, 0..300)) {
        roundtrip(&codes, 16);
    }
}

#[test]
fn packed_boundaries() {
    // Empty and single-element frames, and the max code in each width.
    roundtrip(&[], 2);
    roundtrip(&[1], 2);
    roundtrip(&[3, 0, 3, 3], 4);
    roundtrip(&[15; 20], 16);
    // A code at every position of one full 1-bit word plus one into the next.
    let ones: Vec<usize> = (0..65).map(|i| i % 2).collect();
    roundtrip(&ones, 2);
}
