//! u8 interval used for katas 3–5.
//! Written without reading `abstract-domains/src/domains.rs`.
//!
//! Kata 3: `has` and `add`, with containment of `x.wrapping_add(y)`.
//! Kata 4: meet laws; then a real bottom.
//! Kata 5: subtraction — first only well-formed, then a containment postcondition.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Interval {
    Bottom,
    Range { lo: u8, hi: u8 },
}

impl Interval {
    pub fn range(lo: u8, hi: u8) -> Self {
        if lo <= hi {
            Self::Range { lo, hi }
        } else {
            Self::Bottom
        }
    }

    pub fn top() -> Self {
        Self::Range { lo: 0, hi: 255 }
    }

    pub fn wf(self) -> bool {
        match self {
            Self::Bottom => true,
            Self::Range { lo, hi } => lo <= hi,
        }
    }

    pub fn has(self, x: u8) -> bool {
        match self {
            Self::Bottom => false,
            Self::Range { lo, hi } => lo <= x && x <= hi,
        }
    }

    /// If either endpoint sum overflows, return top. Still contains every
    /// wrapping concrete sum, because top contains every `u8`.
    pub fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => {
                match (a.checked_add(c), b.checked_add(d)) {
                    (Some(lo), Some(hi)) if lo <= hi => Self::Range { lo, hi },
                    _ => Self::top(),
                }
            }
        }
    }

    pub fn sub(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => {
                match (a.checked_sub(d), b.checked_sub(c)) {
                    (Some(lo), Some(hi)) if lo <= hi => Self::Range { lo, hi },
                    _ => Self::top(),
                }
            }
        }
    }

    pub fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => {
                let lo = a.max(c);
                let hi = b.min(d);
                if lo <= hi {
                    Self::Range { lo, hi }
                } else {
                    Self::Bottom
                }
            }
        }
    }

    /// The pre-bottom meet: disjoint operands become top. Sound, unusable.
    pub fn meet_no_bottom(self, other: Self) -> Self {
        match (self, other) {
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => {
                let lo = a.max(c);
                let hi = b.min(d);
                if lo <= hi {
                    Self::Range { lo, hi }
                } else {
                    Self::top()
                }
            }
            _ => Self::top(),
        }
    }

    pub fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => Self::Range {
                lo: a.min(c),
                hi: b.max(d),
            },
        }
    }

    pub fn refines(self, other: Self) -> bool {
        match (self, other) {
            (Self::Bottom, _) => true,
            (_, Self::Bottom) => false,
            (Self::Range { lo: a, hi: b }, Self::Range { lo: c, hi: d }) => a >= c && b <= d,
        }
    }
}
