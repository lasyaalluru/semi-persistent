// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance for the value-layer codecs (F2.1): every `ValueCompressor`
//! round-trips exactly (`decode == input`, checked element-wise through
//! `decode_at` and in total through `decoded_len`), over 1000 proptest cases
//! per codec. The verified ensures say the same; this closes the trusted
//! leaves (`byte_len`, the `Codes` bit packing under `ValueDictC`) and pins
//! the exec surface.

use proptest::prelude::*;
use semi_persistent_containers_verus::value_compressor::{
    EqSpec, NoValueCompression, ValueCompressor, ValueDelta, ValueDictC, ValueRle,
};

fn roundtrip<VC: ValueCompressor<u32>>(vals: &Vec<u32>) -> usize {
    let c = VC::compress(vals);
    assert_eq!(VC::decoded_len(&c), vals.len());
    for (i, &v) in vals.iter().enumerate() {
        assert_eq!(VC::decode_at(&c, i), v, "position {i}");
    }
    VC::byte_len(&c)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn no_compression_roundtrip(vals in proptest::collection::vec(0u32..1000, 0..200)) {
        roundtrip::<NoValueCompression>(&vals);
    }

    #[test]
    fn rle_roundtrip(vals in proptest::collection::vec(0u32..8, 0..200)) {
        roundtrip::<ValueRle>(&vals);
    }

    #[test]
    fn dict_roundtrip(vals in proptest::collection::vec(0u32..16, 0..200)) {
        roundtrip::<ValueDictC>(&vals);
    }

    #[test]
    fn delta_roundtrip(vals in proptest::collection::vec(0u32..1_000_000, 0..200)) {
        roundtrip::<ValueDelta>(&vals);
    }

    /// RLE on a constant column pays runs, not entries; dict on a
    /// small-alphabet column packs below a byte per code. Size claims the
    /// selector will lean on, pinned at the codec level.
    #[test]
    fn codec_sizes_behave(n in 16usize..200) {
        let constant: Vec<u32> = vec![7; n];
        let rle = ValueRle::compress(&constant);
        let plain = <NoValueCompression as ValueCompressor<u32>>::compress(&constant);
        prop_assert!(
            <ValueRle as ValueCompressor<u32>>::byte_len(&rle)
                < <NoValueCompression as ValueCompressor<u32>>::byte_len(&plain),
            "one run must undercut n plain entries"
        );
        let small_alphabet: Vec<u32> = (0..n as u32).map(|i| i % 4).collect();
        let dict = <ValueDictC as ValueCompressor<u32>>::compress(&small_alphabet);
        prop_assert!(
            <ValueDictC as ValueCompressor<u32>>::byte_len(&dict)
                < <NoValueCompression as ValueCompressor<u32>>::byte_len(&plain),
            "4-symbol dict codes must pack below 4 bytes per entry"
        );
    }
}

#[test]
fn eq_spec_words() {
    assert!(3u32.eq_exec(&3));
    assert!(!3u32.eq_exec(&4));
    assert!(9usize.eq_exec(&9));
}
