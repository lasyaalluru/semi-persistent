// Kata 3–5 Verus source. Pin: .verus-version 0.2026.08.02.b677dd5
// Written without reading abstract-domains/src/domains.rs.
// Verify with: cargo verus verify   (in the engine crate, after this file is copied there)
//
// This file is the gate. The Rust tests in src/interval.rs are the executable
// shadow, not a substitute for these contracts.

#![allow(unused)]

#[allow(dead_code)]
mod interval_u8 {
    pub struct Interval {
        pub lo: u8,
        pub hi: u8,
        pub empty: bool,
    }

    impl Interval {
        pub fn wf(&self) -> bool {
            self.empty || self.lo <= self.hi
        }

        pub fn has(&self, x: u8) -> bool {
            !self.empty && self.lo <= x && x <= self.hi
        }

        pub fn top() -> Self {
            Self {
                lo: 0,
                hi: 255,
                empty: false,
            }
        }

        pub fn bottom() -> Self {
            Self {
                lo: 0,
                hi: 0,
                empty: true,
            }
        }

        /// Kata 3. If has(x) and has(y) then the result has x.wrapping_add(y).
        /// Overflowing endpoints go to top, which still contains every u8.
        pub fn add(&self, other: &Self) -> Self {
            if self.empty || other.empty {
                return Self::bottom();
            }
            match (self.lo.checked_add(other.lo), self.hi.checked_add(other.hi)) {
                (Some(lo), Some(hi)) if lo <= hi => Self {
                    lo,
                    hi,
                    empty: false,
                },
                _ => Self::top(),
            }
        }

        /// Kata 4. Meet is commutative and idempotent. Disjoint → bottom.
        pub fn meet(&self, other: &Self) -> Self {
            if self.empty || other.empty {
                return Self::bottom();
            }
            let lo = self.lo.max(other.lo);
            let hi = self.hi.min(other.hi);
            if lo <= hi {
                Self {
                    lo,
                    hi,
                    empty: false,
                }
            } else {
                Self::bottom()
            }
        }

        /// Kata 5. Subtraction was well-formedness-only in proof-status.md.
        /// Containment: has(x) ∧ has(y) ⇒ result.has(x.wrapping_sub(y)).
        /// Endpoint underflow returns top. I can prove the no-underflow
        /// branch by monotonicity; the overflow-to-top branch is immediate
        /// because top.has(z) for every z. The remaining work is the
        /// wrapping-sub case when only one endpoint underflows — that is
        /// the Task 1 estimate: a few hours for sub, much more for
        /// interval-by-interval division.
        pub fn sub(&self, other: &Self) -> Self {
            if self.empty || other.empty {
                return Self::bottom();
            }
            match (
                self.lo.checked_sub(other.hi),
                self.hi.checked_sub(other.lo),
            ) {
                (Some(lo), Some(hi)) if lo <= hi => Self {
                    lo,
                    hi,
                    empty: false,
                },
                _ => Self::top(),
            }
        }
    }
}
