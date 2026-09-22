// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Differential test: cold restore against the hot-restore oracle.
//!
//! Seals randomized strata into a `ColdStack` (both modes) and checks that
//! `restore_frame_into` produces byte-identical results to the oracle — a
//! plain backward replay of the same stratum over the same base. This is the
//! content check the verified `wf` does not carry yet (the decode-level
//! contract is scaffolding-free but the seal-to-decode link lands with the
//! apply_all bridge): the oracle pins it operationally over random workloads
//! meanwhile.

use semi_persistent_containers_verus::cold_stack::ColdStack;

/// Xorshift so runs are reproducible; seeds printed on failure.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

/// The oracle: production-shaped backward replay of interleaved pairs.
fn oracle_restore(base: &mut [u64], stratum: &[(u64, u32)]) {
    for &(v, idx) in stratum.iter().rev() {
        let iu = idx as usize;
        if iu < base.len() {
            base[iu] = v;
        }
    }
}

/// A random stratum with unique indices (the seal_runs precondition),
/// clustered so RLE has real runs to find.
fn unique_clustered_stratum(rng: &mut Rng, n: usize, index_space: u32) -> Vec<(u64, u32)> {
    let mut used = std::collections::HashSet::new();
    let mut out = Vec::new();
    let mut cursor: u32 = (rng.next() % index_space as u64) as u32;
    while out.len() < n {
        // Mostly walk (clusters), sometimes jump (run boundaries).
        if rng.next().is_multiple_of(4) {
            cursor = (rng.next() % index_space as u64) as u32;
        } else {
            cursor = cursor.wrapping_add(1) % index_space;
        }
        if used.insert(cursor) {
            out.push((rng.next(), cursor));
        }
    }
    out
}

#[test]
fn cold_restore_matches_oracle() {
    for seed in 1..=32u64 {
        let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
        let target_len = 64 + (rng.next() % 512) as usize;
        let base: Vec<u64> = (0..target_len as u64).collect();

        let mut stack: ColdStack<u64, u32> = ColdStack::new();
        let mut scratch: Vec<u64> = Vec::new();
        let mut strata: Vec<(usize, Vec<(u64, u32)>)> = Vec::new();

        // Seal a mixed pile of frames: rotating through all three modes,
        // varying sizes, some indices intentionally past the target (clamp
        // coverage). RunsDict strata draw values from a small set so the
        // dictionary actually deduplicates.
        let frames = 3 + (rng.next() % 6) as usize;
        for k in 0..frames {
            let n = 1 + (rng.next() % 96) as usize;
            let mut stratum = unique_clustered_stratum(&mut rng, n, (target_len as u32) + 32);
            match k % 3 {
                0 => stack.seal_runs(&stratum),
                1 => stack.seal_plain(stratum.as_slice()),
                _ => {
                    for e in stratum.iter_mut() {
                        e.0 %= 7;
                    }
                    stack.seal_runs_dict(&stratum);
                }
            }
            strata.push((k % 3, stratum));
        }
        assert_eq!(stack.depth(), frames, "seed {seed}: depth after seals");

        // Restore each frame over an independent copy of the base and
        // compare with the oracle. For a Runs frame the oracle must see the
        // SORTED stratum (sealing reorders; unique indices make the write
        // set order-free, but the oracle is order-sensitive only for
        // duplicates, which uniqueness excludes).
        for (f, (_mode, stratum)) in strata.iter().enumerate() {
            let mut got = base.clone();
            stack.restore_frame_into(f, &mut got, &mut scratch);
            let mut want = base.clone();
            oracle_restore(&mut want, stratum);
            assert_eq!(got, want, "seed {seed}: frame {f} diverged from oracle");
        }

        // Pop everything, resealing after each pop to exercise the
        // truncate-reseal cycle, then check a fresh seal still restores.
        while stack.depth() > 0 {
            stack.pop_frame();
        }
        let stratum = unique_clustered_stratum(&mut rng, 40, target_len as u32);
        stack.seal_runs(&stratum);
        let mut got = base.clone();
        stack.restore_frame_into(0, &mut got, &mut scratch);
        let mut want = base.clone();
        oracle_restore(&mut want, &stratum);
        assert_eq!(got, want, "seed {seed}: post-pop reseal diverged");

        // Dict-mode pop-reseal: pop, reseal as RunsDict, restore, compare.
        stack.pop_frame();
        let mut dstr = unique_clustered_stratum(&mut rng, 40, (target_len as u32) + 16);
        for e in dstr.iter_mut() {
            e.0 %= 5;
        }
        stack.seal_runs_dict(&dstr);
        let mut got = base.clone();
        stack.restore_frame_into(0, &mut got, &mut scratch);
        let mut want = base.clone();
        oracle_restore(&mut want, &dstr);
        assert_eq!(got, want, "seed {seed}: dict reseal diverged");
    }
}
