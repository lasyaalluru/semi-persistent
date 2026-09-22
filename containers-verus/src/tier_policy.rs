// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Execution policy for the three-tier Vec history.
//!
//! Limits apply only to closed frames. The newest ingress frame is always
//! retained and writable. `Unbounded` is explicit and never rolls history
//! automatically.

use vstd::prelude::*;

/// Controls Trail -> Hot -> Cold conversion performed by one mark.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RolloverPolicy {
    /// Seal the old frame and open the new frame without converting history.
    Defer,
    /// Apply the vector's configured tier limits (and legacy cadence).
    ApplyConfigured,
    /// Convert every closed prefix selected by each enabled edge.
    ///
    /// When both edges are enabled, Trail -> Hot always runs before
    /// Hot -> Cold so newly deduplicated frames can become cold in the same
    /// mark.
    ForceClosed {
        trail_to_hot: bool,
        hot_to_cold: bool,
    },
}

impl Default for RolloverPolicy {
    fn default() -> Self {
        Self::ApplyConfigured
    }
}

/// Automatic retention limit for one non-terminal tier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TierLimit {
    /// Never migrate this tier automatically.
    Unbounded,
    /// Retain at most this many closed frames.
    Frames(usize),
    /// Retain the newest closed-frame suffix whose payload fits this count.
    Entries(usize),
    /// Retain the newest closed-frame suffix whose payload fits this many bytes.
    Bytes(usize),
    /// Use representation-specific density/locality heuristics.
    Adaptive,
}

/// Capacity treatment for history pools after eligible migration or restore.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReclaimPolicy {
    /// Preserve allocations for reuse.
    RetainCapacity,
    /// Release unused capacity after migration or restore. An explicit
    /// adaptive pass that migrates frames reclaims all Trail, Hot, and Cold
    /// payload and header pools after both migration stages complete.
    ShrinkToFit,
}

/// Independent retention policy for chronological and unique history.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TierPolicy {
    pub trail: TierLimit,
    pub hot: TierLimit,
    pub cold_reclaim: ReclaimPolicy,
}

impl TierPolicy {
    /// Frequent-backtrack profile: formation is append-only and no automatic
    /// conversion occurs.
    pub const fn smt() -> Self {
        Self {
            trail: TierLimit::Unbounded,
            hot: TierLimit::Unbounded,
            cold_reclaim: ReclaimPolicy::RetainCapacity,
        }
    }

    /// Duplicate-sensitive profile. Trail frames dedupe when writes are at
    /// least twice their unique set. Unique hot frames remain buffered until
    /// explicit compression; a future pressure signal may trigger that same
    /// transition without making locality alone a pressure proxy.
    pub const fn adaptive() -> Self {
        Self {
            trail: TierLimit::Adaptive,
            hot: TierLimit::Unbounded,
            cold_reclaim: ReclaimPolicy::RetainCapacity,
        }
    }

    /// Direct-unique profile: every closed unique frame is run-compressed.
    pub const fn restore_optimized() -> Self {
        Self {
            trail: TierLimit::Frames(0),
            hot: TierLimit::Frames(0),
            cold_reclaim: ReclaimPolicy::RetainCapacity,
        }
    }

    /// Unique ingress with arbitrary hot buffering and no automatic cold work.
    pub const fn fully_buffered_unique() -> Self {
        Self {
            trail: TierLimit::Frames(0),
            hot: TierLimit::Unbounded,
            cold_reclaim: ReclaimPolicy::RetainCapacity,
        }
    }
}

impl Default for TierPolicy {
    fn default() -> Self {
        Self::fully_buffered_unique()
    }
}

/// Observable physical occupancy for policy tests and operational diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TierStats {
    pub trail_frames: usize,
    pub trail_entries: usize,
    pub hot_frames: usize,
    pub hot_entries: usize,
    pub cold_frames: usize,
    pub cold_runs: usize,
    pub cold_values: usize,
}

verus! {

/// A non-negative integer ratio used by explicit adaptive history planning.
///
/// Construction validates that the denominator is nonzero. Comparisons use
/// cross multiplication, so planning never depends on floating-point rounding.
#[derive(Clone, Copy)]
pub struct Ratio {
    numerator: usize,
    denominator: usize,
}

/// Returned when a [`Ratio`] is constructed with a zero denominator.
#[derive(Clone, Copy)]
pub struct InvalidRatio;

impl Ratio {
    /// The denominator is never zero; every constructor checks it.
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.denominator != 0
    }

    /// Ghost denominator value.
    pub closed spec fn denominator_spec(self) -> usize {
        self.denominator
    }

    /// Ghost numerator value.
    pub closed spec fn numerator_spec(self) -> usize {
        self.numerator
    }

    /// Construct an exact integer ratio.
    pub const fn new(numerator: usize, denominator: usize) -> (r: Result<Self, InvalidRatio>)
        ensures
            r is Ok <==> denominator != 0,
            r is Ok ==> r->Ok_0.numerator_spec() == numerator && r->Ok_0.denominator_spec() == denominator,
    {
        if denominator == 0 {
            Err(InvalidRatio)
        } else {
            Ok(Self {
                numerator,
                denominator,
            })
        }
    }

    pub const fn numerator(self) -> (r: usize)
        ensures r == self.numerator_spec(),
    {
        self.numerator
    }

    pub const fn denominator(self) -> (r: usize)
        ensures r == self.denominator_spec(),
    {
        self.denominator
    }

    /// Return whether `left / right` is at least this ratio.
    pub(crate) fn accepts(self, left: usize, right: usize) -> (r: bool)
        ensures r == (left * self.denominator_spec() >= right * self.numerator_spec()),
    {
        let den = self.denominator();
        proof {
            assert((left as u128) * (den as u128) <= (u64::MAX as u128) * (u64::MAX as u128)) by (nonlinear_arith)
                requires left <= u64::MAX, den <= u64::MAX;
            assert((right as u128) * (self.numerator as u128) <= (u64::MAX as u128) * (u64::MAX as u128)) by (nonlinear_arith)
                requires right <= u64::MAX, self.numerator <= u64::MAX;
        }
        (left as u128) * (den as u128) >= (right as u128) * (self.numerator as u128)
    }
}

} // verus!

impl core::fmt::Debug for Ratio {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Ratio")
            .field("numerator", &self.numerator)
            .field("denominator", &self.denominator)
            .finish()
    }
}
impl PartialEq for Ratio {
    fn eq(&self, other: &Self) -> bool {
        self.numerator == other.numerator && self.denominator == other.denominator
    }
}
impl Eq for Ratio {}

impl core::fmt::Debug for InvalidRatio {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("InvalidRatio")
    }
}
impl PartialEq for InvalidRatio {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl Eq for InvalidRatio {}

impl core::fmt::Display for InvalidRatio {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("ratio denominator must be nonzero")
    }
}

impl std::error::Error for InvalidRatio {}

/// Explicit inputs for one deterministic adaptive closed-history pass.
///
/// The byte budget is logical occupancy only: closed Trail/Hot/Cold headers
/// and payload lengths multiplied by `size_of`. It excludes the writable
/// ingress frame, live store, allocation capacity, allocator state, RSS, and
/// time. Inputs are passed per operation and are never persisted in a vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AdaptiveInput {
    pub max_closed_history_bytes: usize,
    pub min_writes_per_unique: Ratio,
    pub min_uniques_per_run: Ratio,
}

/// Exact observations and effects of one adaptive closed-history pass.
///
/// W/U/R totals count each inspected logical frame once across the two-stage
/// pass: U from a Trail frame is not counted again if that same frame then
/// cascades through Hot to Cold. `budget_unmet_bytes` is exactly
/// `logical_bytes_after.saturating_sub(input.max_closed_history_bytes)`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct AdaptiveReport {
    pub inspected_frames: usize,
    pub migrated_frames: usize,
    pub inspected_trail_frames: usize,
    pub migrated_trail_frames: usize,
    pub inspected_hot_frames: usize,
    pub migrated_hot_frames: usize,
    pub writes: usize,
    pub uniques: usize,
    pub runs: usize,
    pub logical_bytes_before: usize,
    pub logical_bytes_after: usize,
    pub budget_unmet_bytes: usize,
}

#[cfg(test)]
mod tests {
    use super::Ratio;

    #[test]
    fn ratio_accepts_exact_boundaries_and_extreme_products() {
        let two_thirds = Ratio::new(2, 3).unwrap();
        assert!(two_thirds.accepts(2, 3));
        assert!(two_thirds.accepts(3, 4));
        assert!(!two_thirds.accepts(1, 2));

        assert!(Ratio::new(0, 1).unwrap().accepts(0, usize::MAX));
        assert!(!Ratio::new(1, usize::MAX).unwrap().accepts(0, usize::MAX));

        let max = usize::MAX;
        let near_one = Ratio::new(max, max - 1).unwrap();
        assert!(near_one.accepts(max, max - 1));
        assert!(!near_one.accepts(max - 1, max - 1));
        assert!(!near_one.accepts(max, max));
    }
}
