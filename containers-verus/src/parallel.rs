// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Parallel compress/restore dispatch across a composite structure's disjoint
//! columns, on the rayon thread pool (a maintained pool, so no per-mark thread
//! creation). The per-column ops (`push_frame`/`restore_frame`/`flush_cold`) stay
//! fully verified; only the fan-out is `external_body` (rayon closures are outside
//! the verified surface). Trust ledger group B: scoped joins over disjoint `&mut`
//! borrows, no `unsafe`. A composite's `_parallel` twin has the SAME contract as
//! its sequential method and is checked against the sequential oracle by the
//! differential conformance tests.
//!
//! Parallelism pays only when the per-column frame work outweighs coordination, so
//! callers gate on `PAR_THRESHOLD` (set from `parallel_restore_bench`); below it the
//! sequential verified path runs.

use vstd::prelude::*;

verus! {

/// Break-even column-work threshold (total live diff entries across the composite)
/// below which the sequential path is faster. Provisional; pinned by
/// `parallel_restore_bench` before the parallel path is defaulted on.
pub const PAR_THRESHOLD: usize = 4096;

} // verus!

// ---------------------------------------------------------------------------
// Build canary — OUTSIDE the verified perimeter: it only confirms rayon links
// and runs under the Verus toolchain. Nothing verified calls it, so it is
// neither proved nor trusted.
// ---------------------------------------------------------------------------
/// Canary: confirms rayon coexists with `cargo verus verify` — the crate must
/// still compile and verify with rayon linked.
pub fn par_sum_canary(n: usize) -> usize {
    use rayon::prelude::*;
    (0..n).into_par_iter().sum()
}
