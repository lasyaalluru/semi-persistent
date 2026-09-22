// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Session-level bare-pair memo for the exact solver.
//!
//! One entry per class pair `(l, r)`: the term and support of the first
//! context-clean solve, exactly the payload of the exact solver's in-call
//! `SubsumptionState::by_pair`. Promoted to a session container so
//! consecutive hybrid calls (`hybrid_exact`, `rollout_hybrid`) reuse each
//! other's clean solves instead of re-solving overlapping subgraphs; the
//! reuse rule is unchanged: a clean entry re-executes under any entry
//! context disjoint from its support, and the re-execution is the identical
//! derivation, so reuse is equality. Entries are valid for one snapshot and
//! one cycle mode, which is the session's own scope.
//!
//! Semi-persistence is the verified map's, not this module's: the memo *is* an
//! `SpMap` keyed by the class pair, so a frame move rolls the entries back and
//! unwinds the index through the map's own previous-occurrence column. Nothing
//! here maintains a derived index or a per-frame length any more (before
//! 2026-09-19 it kept both, and a move walked the log above the checkpoint to
//! drop its keys by hand). Terms reference the session term pool; the session
//! moves the pool in the same group operation, so a rolled-back entry never
//! outlives the term it points to.

use crate::containers::error::ContainerError;
use crate::containers::group::Member;
use crate::containers::{IndexLike, ShrinkPolicy, SpUniqueMap};

/// One memoized clean solve. Supports are sorted and deduplicated at
/// publication (the exact solver sorts before it writes). The class pair is the
/// map's key, so it is not repeated here.
struct MemoEntry<T, C> {
    term: T,
    support_l: Vec<C>,
    support_r: Vec<C>,
}

/// The session memo: one verified map from the class pair to its clean solve.
/// `T` is the term id type, `C` the class id type, `I` the session index word.
pub struct ExactMemo<T: Copy, C: Copy + Ord, I: IndexLike = usize> {
    entries: SpUniqueMap<(u64, u64), MemoEntry<T, C>, I>,
}

impl<T: Copy, C: Copy + Ord, I: IndexLike> ExactMemo<T, C, I> {
    pub fn new() -> Self {
        ExactMemo {
            entries: SpUniqueMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The clean entry for `(l, r)`, if one was recorded: its term and its
    /// per-side support (sorted, deduplicated).
    pub fn get(&self, l: u64, r: u64) -> Option<(T, &[C], &[C])> {
        let entry = self.entries.get_by_key(&(l, r))?;
        Some((entry.term, &entry.support_l, &entry.support_r))
    }

    /// Record the first clean solve of `(l, r)`; later writers lose, matching
    /// the in-call memo's `or_insert`.
    pub fn insert_if_absent(
        &mut self,
        l: u64,
        r: u64,
        term: T,
        support_l: Vec<C>,
        support_r: Vec<C>,
    ) -> Result<(), ContainerError> {
        // One hash of the pair on both paths; first writer wins because a
        // present key leaves the map untouched (`SpMap::try_intern`).
        self.entries.try_intern(
            (l, r),
            MemoEntry {
                term,
                support_l,
                support_r,
            },
        )?;
        Ok(())
    }

    // Structural frame operations: the typed-group member protocol (design doc
    // 10). No tokens, and no bookkeeping of our own — the map rolls its own
    // index back, which is the whole point of keeping the memo in one.
    pub fn push_frame(&mut self, shrink: ShrinkPolicy) {
        Member::push_frame(&mut self.entries, shrink);
    }

    pub fn reset_frame(&mut self, depth: usize) {
        Member::reset_frame(&mut self.entries, depth);
    }

    pub fn restore_frame(&mut self, depth: usize) {
        Member::restore_frame(&mut self.entries, depth);
    }

    pub fn pop_frame(&mut self) {
        Member::pop_frame(&mut self.entries);
    }

    pub fn frame_depth(&self) -> usize {
        Member::depth_exec(&self.entries)
    }
}

impl<T: Copy, C: Copy + Ord, I: IndexLike> Default for ExactMemo<T, C, I> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Memo = ExactMemo<u32, u16>;

    #[test]
    fn first_writer_wins() {
        let mut m = Memo::new();
        m.insert_if_absent(1, 2, 10, vec![3u16], vec![4u16])
            .unwrap();
        m.insert_if_absent(1, 2, 99, vec![], vec![]).unwrap();
        let (t, sl, sr) = m.get(1, 2).unwrap();
        assert_eq!((t, sl, sr), (10, &[3u16][..], &[4u16][..]));
        assert!(m.get(2, 1).is_none());
    }

    #[test]
    fn mark_restore_truncates_and_unindexes() {
        let mut m = Memo::new();
        m.insert_if_absent(1, 2, 10, vec![], vec![]).unwrap();
        let token = m.frame_depth();
        m.push_frame(ShrinkPolicy::Never);
        m.insert_if_absent(3, 4, 20, vec![], vec![]).unwrap();
        assert_eq!(m.len(), 2);

        m.reset_frame(token);
        assert_eq!(m.len(), 1);
        assert!(m.get(1, 2).is_some());
        assert!(m.get(3, 4).is_none());

        // A re-insert after the rollback lands at the recycled position.
        m.insert_if_absent(3, 4, 21, vec![], vec![]).unwrap();
        assert_eq!(m.get(3, 4).unwrap().0, 21);
    }

    #[test]
    fn nested_marks() {
        let mut m = Memo::new();
        let outer = m.frame_depth();
        m.push_frame(ShrinkPolicy::Never);
        m.insert_if_absent(1, 1, 1, vec![], vec![]).unwrap();
        let inner = m.frame_depth();
        m.push_frame(ShrinkPolicy::Never);
        m.insert_if_absent(2, 2, 2, vec![], vec![]).unwrap();
        m.reset_frame(inner);
        assert!(m.get(1, 1).is_some() && m.get(2, 2).is_none());
        m.reset_frame(outer);
        assert!(m.get(1, 1).is_none());
        assert!(m.is_empty());
    }
}
