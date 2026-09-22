// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `ColdStack<T, I>`: the pooled cold tier of the tiered diff design
//! (doc/tasks/restore-from-compressed-frames-goal.md §3).
//!
//! A LIFO stack of sealed frames whose storage is bump-allocated out of shared
//! pools: pushing a frame appends to each pool, popping truncates each pool to
//! the header's recorded offsets. Fragmentation cannot occur and a frame costs
//! zero allocations. Runs are CSR: run `i` of a frame occupies
//! `values[offs[i] .. offs[i+1]]` and lands at `target[starts[i] ..]`, so the
//! end and the length are derived, not stored.
//!
//! Offsets, not slices: a `&[T]` into a sibling pool is self-referential and
//! unsound regardless of the borrow checker, because a pool `push` may
//! reallocate. Integer offsets are half a fat pointer's size, keep the
//! structure relocatable, and stay inside the verifiable subset.
//!
//! The restore contract (§4) is deliberately NOT implemented here yet: this
//! file is the layout and its invariants. Direct cold restore lands with the
//! extensionality lemma in the next step, and until then nothing constructs a
//! `ColdStack` on a live path.

use vstd::prelude::*;

use crate::diff_compress::sort_frame_by_index;
use crate::index_like::{IndexFromNat, IndexLike};

verus! {

/// How one cold frame's diffs are encoded (§5). The selector chooses per
/// frame; restore dispatches per frame.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum ColdMode {
    /// Interleaved `(T, I)` pairs in the `pairs` pool: one sequential pass to
    /// restore. Chosen for singleton-heavy frames, where run-chasing loses to
    /// a straight walk.
    Plain,
    /// CSR runs over the `values` pool: one `copy_from_slice` per run.
    Runs,
    /// Runs whose values are dictionary codes: per run, decode
    /// `codes[data_off + pos ..]` through the frame's dictionary slice of
    /// `dicts` into a container-owned scratch, then one `copy_from_slice`
    /// (design doc §4, "RLE with dictionary values"). Run boundaries live in
    /// `druns` as (target start, cumulative end position) pairs - frame-local
    /// CSR, because these boundaries index the codes pool, not `values`, and
    /// a shared `offs` column cannot stay monotone across two independent
    /// cursors.
    RunsDict,
}

/// One sealed frame's extent in every pool. Pop truncates each pool back to
/// the `*_off` fields, so the header IS the undo record for the seal.
pub struct ColdHdr<I: IndexLike> {
    pub mode: ColdMode,
    /// Extent in `starts`/the run structure: `[runs_off, runs_off + runs_len)`.
    pub runs_off: I,
    pub runs_len: I,
    /// Extent in `pairs` (Plain) or `values` (Runs).
    pub data_off: I,
    pub data_len: I,
    /// Decoded entry count of the frame (== data_len for every current mode;
    /// kept separate so a mode whose stored length diverges can diverge).
    pub entries: I,
    /// RunsDict only: extent in `druns` (frame-local CSR run pairs). Zero for
    /// the other modes.
    pub druns_off: I,
    pub druns_len: I,
    /// RunsDict only: extent in `dicts` (this frame's dictionary). Zero for
    /// the other modes.
    pub dict_off: I,
    pub dict_len: I,
}

/// The pooled cold tier. All pools are append-only between pops; `frames` is
/// the stack.
pub struct ColdStack<T: Copy, I: IndexLike> {
    pub frames: Vec<ColdHdr<I>>,
    /// Target index where each run lands (CSR row starts, all frames
    /// concatenated).
    pub starts: Vec<I>,
    /// CSR offsets into `values`: `offs.len() == starts.len() + 1` whenever
    /// any Runs frame exists; `offs[i]..offs[i+1]` is run `i`'s value range.
    /// Monotone, and `offs.last() == values.len()`.
    pub offs: Vec<I>,
    /// Plain frames' interleaved pairs.
    pub pairs: Vec<(T, I)>,
    /// Runs frames' values, concatenated in index order.
    pub values: Vec<T>,
    /// RunsDict frames' run boundaries: (target start, cumulative end
    /// position within the frame). Frame-local CSR: run r of a frame whose
    /// first run is `first` covers frame positions
    /// `[dpos_base(first, r), druns[r].1)`.
    pub druns: Vec<(I, I)>,
    /// Per-frame dictionaries, pooled (§3: per-frame logically because a
    /// shared dictionary cannot be truncated on pop; pooled physically for
    /// the zero-allocation property).
    pub dicts: Vec<T>,
    /// RunsDict frames' code columns, flattened. Byte-width variants only
    /// (see `Codes::width_cap`): the width widens monotonically as larger
    /// dictionaries arrive and pop stays a truncate.
    pub codes: crate::diff_compress::Codes,
}

/// One clamped block write: `vals` lands at `[s, s + vals.len())`, entries at
/// or past `base.len()` drop (apply_all's out-of-range rule), and the length
/// never changes.
pub open spec fn write_block<T>(base: Seq<T>, s: nat, vals: Seq<T>) -> Seq<T> {
    Seq::new(base.len(), |j: int|
        if s <= j as nat && (j as nat) < s + vals.len() { vals[j - s as int] } else { base[j] })
}

/// Fold the block writes of frame `f`'s runs `[r0, r0 + cnt)` over `base`,
/// first run first. Runs within a frame land at disjoint ascending ranges,
/// so the order is immaterial; first-to-last matches the exec loop.
pub open spec fn runs_overlay<T: Copy, I: IndexLike>(
    stack: &ColdStack<T, I>, base: Seq<T>, r0: int, cnt: int,
) -> Seq<T>
    decreases cnt,
{
    if cnt <= 0 {
        base
    } else {
        let r = r0 + cnt - 1;
        let lo = stack.offs@[r].as_nat();
        let hi = stack.offs@[r + 1].as_nat();
        write_block(
            runs_overlay(stack, base, r0, cnt - 1),
            stack.starts@[r].as_nat(),
            stack.values@.subrange(lo as int, hi as int),
        )
    }
}

// The Runs decode synthesizes landing indices (`starts[r] + k`), which needs
// the ghost inverse `from_nat` — the `IndexFromNat` boundary the A2 experiment
// recorded. Plain-mode-only use of the stack does not need it, so only the
// decode family carries the stronger bound.
impl<T: Copy, I: IndexFromNat> ColdStack<T, I> {
    /// The decoded diff sequence of frame `f`, oldest-first within the frame.
    /// For `Plain` it is the stored pairs; for `Runs` it is the CSR expansion:
    /// entry `k` of run `r` is `(values[offs[r] + k], starts[r] + k)`.
    pub open spec fn frame_decode(&self, f: int) -> Seq<(T, I)>
        recommends 0 <= f < self.frames@.len()
    {
        let h = self.frames@[f];
        match h.mode {
            ColdMode::Plain => self.pairs@.subrange(
                h.data_off.as_nat() as int,
                h.data_off.as_nat() as int + h.data_len.as_nat() as int,
            ),
            ColdMode::Runs => Seq::new(
                h.entries.as_nat(),
                |k: int| self.run_entry_at(f, k),
            ),
            ColdMode::RunsDict => Seq::new(
                h.entries.as_nat(),
                |k: int| self.dict_entry_at(f, k),
            ),
        }
    }

    /// Entry `k` of a RunsDict frame `f`: the run containing frame position
    /// `k`, the value decoded through the frame's dictionary, the landing
    /// index derived from the run start.
    pub open spec fn dict_entry_at(&self, f: int, k: int) -> (T, I)
        recommends 0 <= f < self.frames@.len()
    {
        let h = self.frames@[f];
        let first = h.druns_off.as_nat() as int;
        let r = self.drun_of(f, k);
        let pos_in_run = k - self.dpos_base(first, r);
        (
            self.dicts@[h.dict_off.as_nat()
                + self.codes.view()[h.data_off.as_nat() + k] as int],
            I::from_nat((self.druns@[r].0.as_nat() + pos_in_run) as nat),
        )
    }

    /// The druns row (absolute index) containing frame position `k` of a
    /// RunsDict frame: the unique `r` in the frame's run range with
    /// `dpos_base(first, r) <= k < druns[r].1`.
    pub open spec fn drun_of(&self, f: int, k: int) -> int
        recommends 0 <= f < self.frames@.len()
    {
        let h = self.frames@[f];
        let first = h.druns_off.as_nat() as int;
        choose|r: int| #![trigger self.druns@[r]] {
            &&& first <= r < first + h.druns_len.as_nat() as int
            &&& self.dpos_base(first, r) <= k as nat
            &&& (k as nat) < self.druns@[r].1.as_nat()
        }
    }

    /// Entry `k` of a Runs frame `f`: locate the run containing global
    /// position `k` (positions are cumulative over the frame's runs), then
    /// read the value and derive the landing index.
    pub open spec fn run_entry_at(&self, f: int, k: int) -> (T, I)
        recommends 0 <= f < self.frames@.len()
    {
        let h = self.frames@[f];
        let r = self.run_of(f, k);
        let base = self.offs@[r].as_nat() as int;
        let pos_in_run = (self.offs@[h.runs_off.as_nat() as int].as_nat() as int + k) - base;
        (
            self.values@[base + pos_in_run],
            I::from_nat((self.starts@[r].as_nat() + pos_in_run) as nat),
        )
    }

    /// The run (absolute index into `starts`/`offs`) containing the frame's
    /// cumulative entry position `k`: the unique `r` in the frame's run range
    /// with `offs[r] <= first_off + k < offs[r+1]`, where `first_off` is the
    /// frame's first run's value offset.
    pub open spec fn run_of(&self, f: int, k: int) -> int
        recommends 0 <= f < self.frames@.len()
    {
        let h = self.frames@[f];
        let lo = h.runs_off.as_nat() as int;
        let target = self.offs@[lo].as_nat() as int + k;
        choose|r: int| #![trigger self.offs@[r]] {
            &&& lo <= r < lo + h.runs_len.as_nat() as int
            &&& self.offs@[r].as_nat() <= target as nat
            &&& (target as nat) < self.offs@[r + 1].as_nat()
        }
    }

}

impl<T: Copy, I: IndexLike> ColdStack<T, I> {
    /// Structural well-formedness: every header's extents nest inside the
    /// pools, CSR offsets are monotone, and the pools end exactly at the top
    /// frame's end (the bump-allocator property that makes pop a truncate).
    pub open spec fn wf(&self) -> bool {
        // Headers tile the pools in stack order with no gaps.
        &&& (forall|f: int| 0 <= f < self.frames@.len()
                ==> #[trigger] self.hdr_wf(f))
        &&& self.tiling_wf()
        // CSR offsets monotone non-decreasing over the whole pool.
        &&& (forall|r: int| 0 <= r < self.offs@.len() - 1
                ==> (#[trigger] self.offs@[r]).as_nat() <= self.offs@[r + 1].as_nat())
        // The offs column exists iff runs exist, closing at values' end.
        &&& (self.starts@.len() == 0 ==> self.offs@.len() == 0)
        &&& (self.starts@.len() > 0 ==> {
                &&& self.offs@.len() == self.starts@.len() + 1
                &&& self.offs@[self.offs@.len() - 1].as_nat() == self.values@.len()
                &&& self.offs@[0].as_nat() == 0
            })
        // The code pool stays byte-width so pop can truncate it.
        &&& !(self.codes is Packed)
        &&& self.codes.wf()
    }

    /// Cumulative base position of run `r` in a frame whose first run is
    /// `first`: 0 for the first run, the previous run's recorded end
    /// otherwise.
    pub open spec fn dpos_base(&self, first: int, r: int) -> nat {
        if r <= first { 0 } else { self.druns@[r - 1].1.as_nat() }
    }

    /// RunsDict content clauses: nonempty runs chaining strictly up to the
    /// frame's entry count, and every code indexing the frame's dictionary.
    /// Opaque so the nested quantifiers only unfold where a proof needs
    /// them - inlining them into every `wf` context wedged the solver in
    /// `pop_frame`, the same failure mode the restore loop's trimmed
    /// invariants fixed.
    #[verifier::opaque]
    pub open spec fn dict_content_wf(&self, f: int) -> bool
        recommends 0 <= f < self.frames@.len()
    {
        let h = self.frames@[f];
        let first = h.druns_off.as_nat() as int;
        &&& (forall|r: int| first <= r < first + h.druns_len.as_nat()
                ==> self.dpos_base(first, r)
                    < (#[trigger] self.druns@[r]).1.as_nat())
        &&& self.druns@[first + h.druns_len.as_nat() - 1].1.as_nat()
                == h.entries.as_nat()
        &&& (forall|k: int| 0 <= k < h.data_len.as_nat()
                ==> #[trigger] self.codes.view()[h.data_off.as_nat() + k]
                    < h.dict_len.as_nat())
    }

    /// Transfer `dict_content_wf` between two stacks whose header and pool
    /// contents agree on the frame's extents. Opacity removes congruence, so
    /// every state change - even one that leaves druns/codes untouched -
    /// routes the clause through this lemma.
    pub proof fn lemma_dict_content_transfer(&self, other: Self, f: int)
        requires
            0 <= f < self.frames@.len(),
            0 <= f < other.frames@.len(),
            self.frames@[f] == other.frames@[f],
            self.frames@[f].mode is RunsDict,
            self.frames@[f].druns_len.as_nat() > 0,
            other.dict_content_wf(f),
            self.frames@[f].druns_off.as_nat() + self.frames@[f].druns_len.as_nat()
                <= self.druns@.len(),
            self.frames@[f].druns_off.as_nat() + self.frames@[f].druns_len.as_nat()
                <= other.druns@.len(),
            forall|r: int| self.frames@[f].druns_off.as_nat() as int <= r
                < self.frames@[f].druns_off.as_nat() + self.frames@[f].druns_len.as_nat()
                ==> #[trigger] self.druns@[r] == other.druns@[r],
            forall|q: int| 0 <= q < self.frames@[f].data_len.as_nat()
                ==> #[trigger] self.codes.view()[self.frames@[f].data_off.as_nat() + q]
                    == other.codes.view()[self.frames@[f].data_off.as_nat() + q],
        ensures
            self.dict_content_wf(f),
    {
        reveal(ColdStack::dict_content_wf);
        let hf = self.frames@[f];
        let firstf = hf.druns_off.as_nat() as int;
        assert forall|r: int| firstf <= r < firstf + hf.druns_len.as_nat()
            implies self.dpos_base(firstf, r)
                < (#[trigger] self.druns@[r]).1.as_nat() by {
            assert(other.dpos_base(firstf, r) < other.druns@[r].1.as_nat());
            assert(self.druns@[r] == other.druns@[r]);
            if r > firstf {
                assert(self.druns@[r - 1] == other.druns@[r - 1]);
            }
        }
        assert(self.druns@[firstf + hf.druns_len.as_nat() - 1]
            == other.druns@[firstf + hf.druns_len.as_nat() - 1]);
        assert forall|q: int| 0 <= q < hf.data_len.as_nat()
            implies #[trigger] self.codes.view()[hf.data_off.as_nat() + q]
                < hf.dict_len.as_nat() by {
            assert(other.codes.view()[hf.data_off.as_nat() + q]
                < hf.dict_len.as_nat());
        }
    }

    /// One header's extents are in-bounds and internally consistent.
    pub open spec fn hdr_wf(&self, f: int) -> bool
        recommends 0 <= f < self.frames@.len()
    {
        let h = self.frames@[f];
        match h.mode {
            ColdMode::Plain => {
                &&& h.runs_len.as_nat() == 0
                &&& h.data_off.as_nat() + h.data_len.as_nat() <= self.pairs@.len()
                &&& h.entries.as_nat() == h.data_len.as_nat()
            }
            ColdMode::Runs => {
                &&& h.runs_len.as_nat() > 0
                &&& h.runs_off.as_nat() + h.runs_len.as_nat() < self.offs@.len()
                &&& h.runs_off.as_nat() + h.runs_len.as_nat() <= self.starts@.len()
                &&& h.data_off.as_nat() + h.data_len.as_nat() <= self.values@.len()
                &&& h.entries.as_nat() == h.data_len.as_nat()
            }
            ColdMode::RunsDict => {
                &&& h.runs_len.as_nat() == 0
                &&& h.druns_len.as_nat() > 0
                &&& h.druns_off.as_nat() + h.druns_len.as_nat() <= self.druns@.len()
                &&& h.dict_len.as_nat() > 0
                &&& h.dict_off.as_nat() + h.dict_len.as_nat() <= self.dicts@.len()
                &&& h.data_off.as_nat() + h.data_len.as_nat() <= self.codes.view().len()
                &&& h.entries.as_nat() == h.data_len.as_nat()
                &&& self.dict_content_wf(f)
            }
        }
    }

    /// Pool cursors: how much of each pool the first `upto` frames consume.
    /// These are the tiling invariant: every header's offsets equal the
    /// cursor at its own position, and each pool's length equals the cursor
    /// at the stack's end, which is exactly what makes pop a truncate.
    pub open spec fn runs_used(&self, upto: int) -> nat
        decreases upto,
    {
        if upto <= 0 { 0 }
        else { self.runs_used(upto - 1) + self.frames@[upto - 1].runs_len.as_nat() }
    }

    pub open spec fn pairs_used(&self, upto: int) -> nat
        decreases upto,
    {
        if upto <= 0 { 0 }
        else {
            self.pairs_used(upto - 1)
                + if self.frames@[upto - 1].mode is Plain {
                    self.frames@[upto - 1].data_len.as_nat()
                } else { 0 }
        }
    }

    pub open spec fn values_used(&self, upto: int) -> nat
        decreases upto,
    {
        if upto <= 0 { 0 }
        else {
            self.values_used(upto - 1)
                + if self.frames@[upto - 1].mode is Runs {
                    self.frames@[upto - 1].data_len.as_nat()
                } else { 0 }
        }
    }

    pub open spec fn druns_used(&self, upto: int) -> nat
        decreases upto,
    {
        if upto <= 0 { 0 }
        else {
            self.druns_used(upto - 1)
                + if self.frames@[upto - 1].mode is RunsDict {
                    self.frames@[upto - 1].druns_len.as_nat()
                } else { 0 }
        }
    }

    pub open spec fn dicts_used(&self, upto: int) -> nat
        decreases upto,
    {
        if upto <= 0 { 0 }
        else {
            self.dicts_used(upto - 1)
                + if self.frames@[upto - 1].mode is RunsDict {
                    self.frames@[upto - 1].dict_len.as_nat()
                } else { 0 }
        }
    }

    pub open spec fn codes_used(&self, upto: int) -> nat
        decreases upto,
    {
        if upto <= 0 { 0 }
        else {
            self.codes_used(upto - 1)
                + if self.frames@[upto - 1].mode is RunsDict {
                    self.frames@[upto - 1].data_len.as_nat()
                } else { 0 }
        }
    }

    /// Every frame's offsets sit exactly at the pool cursors, and the pools
    /// end exactly at the last cursor.
    pub open spec fn tiling_wf(&self) -> bool {
        let n = self.frames@.len() as int;
        &&& (forall|f: int| 0 <= f < n ==> {
                let h = #[trigger] self.frames@[f];
                &&& h.runs_off.as_nat() == self.runs_used(f)
                &&& (h.mode is Plain ==> h.data_off.as_nat() == self.pairs_used(f))
                &&& (h.mode is Runs ==> h.data_off.as_nat() == self.values_used(f))
                &&& (h.mode is RunsDict ==> {
                        &&& h.druns_off.as_nat() == self.druns_used(f)
                        &&& h.dict_off.as_nat() == self.dicts_used(f)
                        &&& h.data_off.as_nat() == self.codes_used(f)
                    })
            })
        &&& self.starts@.len() == self.runs_used(n)
        &&& self.pairs@.len() == self.pairs_used(n)
        &&& self.values@.len() == self.values_used(n)
        &&& self.druns@.len() == self.druns_used(n)
        &&& self.dicts@.len() == self.dicts_used(n)
        &&& self.codes.view().len() == self.codes_used(n)
        // CSR anchor: at every frame boundary, the offs entry at the runs
        // cursor equals the values cursor. This is what lets a pop re-close
        // the offs column mid-stack: without it only the outermost closing
        // clause exists and popping a Runs frame could not re-establish
        // `offs.last == values.len`.
        &&& (self.starts@.len() > 0 ==> forall|f: int| 0 <= f <= n
                ==> (#[trigger] self.offs@[self.runs_used(f) as int]).as_nat()
                    == self.values_used(f))
    }

    /// The decoded value block of RunsDict run `r` of frame `f`: the run's
    /// codes, looked up through the frame's dictionary slice.
    pub open spec fn dict_run_vals(&self, f: int, r: int) -> Seq<T>
        recommends 0 <= f < self.frames@.len()
    {
        let h = self.frames@[f];
        let first = h.druns_off.as_nat() as int;
        let base = self.dpos_base(first, r);
        Seq::new(
            (self.druns@[r].1.as_nat() - base) as nat,
            |j: int| self.dicts@[h.dict_off.as_nat()
                + self.codes.view()[h.data_off.as_nat() + base + j] as int],
        )
    }

    /// Fold the decoded block writes of RunsDict frame `f`'s first `cnt`
    /// runs over `base`, first run first - `runs_overlay`'s shape with the
    /// dictionary decode in place of the values-pool subrange.
    pub open spec fn dict_runs_overlay(&self, base: Seq<T>, f: int, cnt: int) -> Seq<T>
        recommends 0 <= f < self.frames@.len()
        decreases cnt,
    {
        if cnt <= 0 {
            base
        } else {
            let h = self.frames@[f];
            let r = h.druns_off.as_nat() as int + cnt - 1;
            write_block(
                self.dict_runs_overlay(base, f, cnt - 1),
                self.druns@[r].0.as_nat(),
                self.dict_run_vals(f, r),
            )
        }
    }

    /// The cumulative run ends of a frame-local CSR chain are bounded by the
    /// closing entry: `druns[r].1 <= entries` for every run in the range.
    /// Stated over the raw chain facts, not `hdr_wf`, so loop bodies with
    /// trimmed invariants can use it.
    #[verifier::rlimit(600)]
    #[verifier::spinoff_prover]
    pub proof fn lemma_druns_bounded(&self, first: int, cnt: int, r: int, entries: nat)
        requires
            0 <= first,
            first <= r < first + cnt,
            first + cnt <= self.druns@.len(),
            forall|rr: int| first <= rr < first + cnt
                ==> self.dpos_base(first, rr)
                    < (#[trigger] self.druns@[rr]).1.as_nat(),
            self.druns@[first + cnt - 1].1.as_nat() == entries,
        ensures
            self.druns@[r].1.as_nat() <= entries,
        decreases first + cnt - r,
    {
        let last = first + cnt - 1;
        if r < last {
            self.lemma_druns_bounded(first, cnt, r + 1, entries);
            assert(self.dpos_base(first, r + 1) < self.druns@[r + 1].1.as_nat());
        }
    }

    /// Cursors are monotone in the frame prefix.
    pub proof fn lemma_cursors_monotone(&self, a: int, b: int)
        requires 0 <= a <= b <= self.frames@.len(),
        ensures
            self.runs_used(a) <= self.runs_used(b),
            self.pairs_used(a) <= self.pairs_used(b),
            self.values_used(a) <= self.values_used(b),
            self.druns_used(a) <= self.druns_used(b),
            self.dicts_used(a) <= self.dicts_used(b),
            self.codes_used(a) <= self.codes_used(b),
        decreases b - a,
    {
        if a < b {
            self.lemma_cursors_monotone(a, b - 1);
        }
    }

    pub fn new() -> (r: Self)
        ensures r.wf(), r.frames@.len() == 0,
    {
        ColdStack {
            frames: Vec::new(),
            starts: Vec::new(),
            offs: Vec::new(),
            pairs: Vec::new(),
            values: Vec::new(),
            druns: Vec::new(),
            dicts: Vec::new(),
            codes: crate::diff_compress::Codes::U8(Vec::new()),
        }
    }

    pub fn depth(&self) -> (n: usize)
        ensures n == self.frames@.len(),
    {
        self.frames.len()
    }

    /// Restore frame `f` directly from the pools — the compressed form IS the
    /// restore plan (design doc §4). `Plain` walks its pooled pairs backward
    /// in place (overlay semantics: duplicate-safe, so a trail-sealed frame
    /// restores correctly). `Runs` copies each run with one `copy_from_slice`
    /// out of the values pool, clamped to the target's length, never grown.
    /// No allocation on either path, and `decode_exec_cold`-style
    /// materialization does not exist here at all.
    /// `scratch` is the container-owned decode buffer for RunsDict frames
    /// (design doc §4): each run's codes decode into it once, then one
    /// `copy_from_slice` writes the target, so the target write is the same
    /// uniform block copy in every run-encoded mode and the buffer's
    /// allocation amortizes across runs and frames.
    #[verifier::rlimit(600)]
    pub fn restore_frame_into(&self, f: usize, target: &mut Vec<T>, scratch: &mut Vec<T>)
        requires
            self.wf(),

        ensures
            final(target)@.len() == old(target)@.len(),
            self.frames@[f as int].mode is Plain ==> final(target)@
                == crate::vec::overlay::<T, I>(
                    old(target)@,
                    self.pairs@.subrange(
                        self.frames@[f as int].data_off.as_nat() as int,
                        self.frames@[f as int].data_off.as_nat() as int
                            + self.frames@[f as int].data_len.as_nat() as int),
                    0,
                    self.frames@[f as int].data_len.as_nat() as int),
            self.frames@[f as int].mode is Runs ==> final(target)@
                == runs_overlay(
                    self,
                    old(target)@,
                    self.frames@[f as int].runs_off.as_nat() as int,
                    self.frames@[f as int].runs_len.as_nat() as int),
            self.frames@[f as int].mode is RunsDict ==> final(target)@
                == self.dict_runs_overlay(
                    old(target)@,
                    f as int,
                    self.frames@[f as int].druns_len.as_nat() as int),
    {
        // Total: a frame index past the stack is the documented trap.
        if !(f < self.frames.len()) {
            crate::guard::refuse("ColdStack::restore_frame_into: frame index out of range");
        }
        let h = &self.frames[f];
        proof { assert(self.hdr_wf(f as int)); }
        match h.mode {
            ColdMode::Plain => {
                let lo = h.data_off.as_usize();
                let n = h.data_len.as_usize();
                let ghost dsub = self.pairs@.subrange(lo as int, lo as int + n as int);
                let ghost base = target@;
                // usize witness: spec-side nat lengths do not bound usize
                // adds; the exec pool length does.
                let pl = self.pairs.len();
                let mut i: usize = n;
                while i > 0
                    invariant
                        i <= n,
                        self.pairs@.len() == pl as nat,
                        lo + n <= pl,
                        dsub == self.pairs@.subrange(lo as int, lo as int + n as int),
                        dsub.len() == n as nat,
                        target@.len() == base.len(),
                        target@ == crate::vec::overlay::<T, I>(base, dsub, i as int, n as int),
                    decreases i,
                {
                    i -= 1;
                    let (v, idx) = self.pairs[lo + i];
                    proof {
                        assert(self.pairs@[(lo + i) as int] == dsub[i as int]);
                        crate::vec::lemma_overlay_len::<T, I>(base, dsub, (i + 1) as int, n as int);
                    }
                    let iu = idx.as_usize();
                    if iu < target.len() {
                        target.set(iu, v);
                    }
                    proof {
                        assert(target@ =~= crate::vec::overlay::<T, I>(
                            base, dsub, i as int, n as int));
                    }
                }
            }
            ColdMode::Runs => {
                let r0 = h.runs_off.as_usize();
                let cnt = h.runs_len.as_usize();
                let ghost base = target@;
                // usize witnesses for the run arithmetic.
                let ol = self.offs.len();
                let sl = self.starts.len();
                let vl = self.values.len();
                let mut r: usize = 0;
                while r < cnt
                    invariant
                        r <= cnt,
                        self.offs@.len() == ol as nat,
                        self.starts@.len() == sl as nat,
                        self.values@.len() == vl as nat,
                        r0 + cnt < ol,
                        r0 + cnt <= sl,
                        // The two offs facts the body needs, carried directly
                        // rather than through self.wf() (whose full unfolding
                        // made the loop VC large enough to wedge the solver).
                        forall|a: int| 0 <= a < self.offs@.len() - 1
                            ==> (#[trigger] self.offs@[a]).as_nat() <= self.offs@[a + 1].as_nat(),
                        (self.offs@[self.offs@.len() - 1]).as_nat() == self.values@.len(),
                        target@.len() == base.len(),
                        target@ == runs_overlay(self, base, r0 as int, r as int),
                    decreases cnt - r,
                {
                    let ridx = r0 + r;
                    proof {
                        assert(ridx + 1 < self.offs@.len());
                        assert(ridx < self.starts@.len());
                        assert(self.offs@[ridx as int].as_nat()
                            <= self.offs@[ridx as int + 1].as_nat());
                    }
                    let lo = self.offs[ridx].as_usize();
                    let hi = self.offs[ridx + 1].as_usize();
                    let start = self.starts[ridx].as_usize();
                    proof {
                        // hi = offs[ridx + 1] is what bounds the run's value
                        // range inside the pool.
                        self.lemma_offs_bounded(ridx as int + 1);
                    }
                    let run_len = hi - lo;
                    let tlen = target.len();
                    let ghost pre_run = target@;
                    let ghost vals = self.values@.subrange(lo as int, hi as int);
                    proof {
                        assert(lo as nat == self.offs@[ridx as int].as_nat());
                        assert(hi as nat == self.offs@[ridx as int + 1].as_nat());
                        assert(vals.len() == run_len as nat);
                        assert(start as nat == self.starts@[ridx as int].as_nat());
                    }
                    if start < tlen {
                        // Overflow-safe clamp: compare against the remaining
                        // room instead of adding to `start`.
                        let cl = if run_len <= tlen - start { run_len } else { tlen - start };
                        // The memcpy: one copy_from_slice per run, straight
                        // out of the values pool through the vstd-specified
                        // as_mut_slice / split_at_mut / copy_from_slice chain.
                        // No external_body: every primitive carries a vstd
                        // contract, and their ensures compose to exactly the
                        // written-window facts the extensionality proof reads.
                        let src = vstd::slice::slice_subrange(
                            self.values.as_slice(), lo, lo + cl);
                        let tslice = target.as_mut_slice();
                        let (_, rest) = tslice.split_at_mut(start);
                        let (dst, tail) = rest.split_at_mut(cl);
                        dst.copy_from_slice(src);
                        proof {
                            // Reassemble: final(tslice) == final(pre) + final(rest),
                            // final(rest) == final(dst) + final(tail).
                            assert(target@.len() == tlen as nat);
                            assert forall|j: int| 0 <= j < cl
                                implies #[trigger] target@[start + j]
                                    == self.values@[lo + j] by {
                                assert(target@[start + j] == src@[j]);
                            }
                            assert forall|j: int| 0 <= j < target@.len()
                                && !(start <= j && j < start + cl)
                                implies #[trigger] target@[j] == pre_run[j] by {}
                        }
                        proof {
                            // The written window mirrors the pool; the clamp
                            // cut exactly the tail write_block drops.
                            if run_len <= tlen - start {
                                assert(cl == run_len);
                            } else {
                                assert(start + cl == tlen);
                            }
                            assert forall|j: int| 0 <= j < target@.len() implies
                                (#[trigger] target@[j]) == write_block(pre_run, start as nat, vals)[j] by {
                                if start as int <= j && j < start as int + cl as int {
                                    // Written: the loop's mirror forall, and
                                    // vals is the same pool subrange.
                                    assert(target@[start as int + (j - start as int)]
                                        == self.values@[lo as int + (j - start as int)]);
                                    assert(vals[j - start as int]
                                        == self.values@[lo as int + (j - start as int)]);
                                } else if start as int + cl as int <= j
                                    && j < start as int + vals.len() {
                                    // Clamped tail: only nonempty when the
                                    // clamp fired, and then it starts at tlen,
                                    // past every valid j.
                                    assert(cl < run_len);
                                    assert(start + cl == tlen);
                                    assert(j >= tlen as int);
                                    assert(false);
                                } else {
                                    assert(target@[j] == pre_run[j]);
                                }
                            }
                            assert(target@ =~= write_block(
                                pre_run, start as nat, vals));
                        }
                    } else {
                        proof {
                            // Skip branch: the whole window is past the
                            // target, so write_block writes nothing.
                            assert(target@ =~= write_block(
                                pre_run, start as nat, vals));
                        }
                    }
                    proof {
                        assert(target@ =~= runs_overlay(self, base, r0 as int, r as int + 1));
                    }
                    r += 1;
                }
            }
            ColdMode::RunsDict => {
                let r0 = h.druns_off.as_usize();
                let cnt = h.druns_len.as_usize();
                let coff = h.data_off.as_usize();
                let doff = h.dict_off.as_usize();
                let entries = h.entries.as_usize();
                let ghost base = target@;
                let ghost fh = self.frames@[f as int];
                proof {
                    // Unpack the opaque content clauses once; the loops carry
                    // them as raw invariants.
                    reveal(ColdStack::dict_content_wf);
                    assert(self.dict_content_wf(f as int));
                }
                // usize witnesses for the pool arithmetic.
                let dl = self.druns.len();
                let cl_pool = self.codes.len();
                let dictl = self.dicts.len();
                let mut pos: usize = 0;
                let mut r: usize = 0;
                while r < cnt
                    invariant
                        r <= cnt,
                        fh == self.frames@[f as int],
                        f < self.frames@.len(),
                        fh.mode is RunsDict,
                        forall|rr: int| r0 as int <= rr < r0 + cnt
                            ==> self.dpos_base(r0 as int, rr)
                                < (#[trigger] self.druns@[rr]).1.as_nat(),
                        cnt > 0 ==> self.druns@[r0 + cnt - 1].1.as_nat() == entries as nat,
                        forall|q: int| 0 <= q < entries
                            ==> #[trigger] self.codes.view()[fh.data_off.as_nat() + q]
                                < fh.dict_len.as_nat(),
                        self.codes.wf(),
                        r0 == fh.druns_off.as_nat(),
                        cnt == fh.druns_len.as_nat(),
                        coff == fh.data_off.as_nat(),
                        doff == fh.dict_off.as_nat(),
                        entries == fh.entries.as_nat(),
                        self.druns@.len() == dl as nat,
                        self.codes.view().len() == cl_pool as nat,
                        self.dicts@.len() == dictl as nat,
                        r0 + cnt <= dl,
                        coff + entries <= cl_pool,
                        doff + fh.dict_len.as_nat() <= dictl as nat,
                        pos as nat == self.dpos_base(r0 as int, r0 + r),
                        pos <= entries,
                        target@.len() == base.len(),
                        target@ == self.dict_runs_overlay(base, f as int, r as int),
                    decreases cnt - r,
                {
                    let ridx = r0 + r;
                    proof {
                        assert(self.dpos_base(r0 as int, ridx as int)
                            < self.druns@[ridx as int].1.as_nat());
                        self.lemma_druns_bounded(
                            r0 as int, cnt as int, ridx as int, entries as nat);
                    }
                    let (start_i, end_i) = self.druns[ridx];
                    let start = start_i.as_usize();
                    let endp = end_i.as_usize();
                    let run_len = endp - pos;
                    let tlen = target.len();
                    let ghost pre_run = target@;
                    let ghost vals = self.dict_run_vals(f as int, ridx as int);
                    proof {
                        assert(vals.len() == run_len as nat);
                        assert(start as nat == self.druns@[ridx as int].0.as_nat());
                    }
                    if start < tlen {
                        let cl = if run_len <= tlen - start { run_len } else { tlen - start };
                        // Decode this run's codes through the frame's
                        // dictionary into the scratch buffer.
                        scratch.clear();
                        let mut j: usize = 0;
                        while j < cl
                            invariant
                                j <= cl,
                                cl <= run_len,
                                fh == self.frames@[f as int],
                                f < self.frames@.len(),
                                fh.mode is RunsDict,
                                forall|q: int| 0 <= q < entries
                                    ==> #[trigger] self.codes.view()[fh.data_off.as_nat() + q]
                                        < fh.dict_len.as_nat(),
                                self.codes.wf(),
                                coff == fh.data_off.as_nat(),
                                doff == fh.dict_off.as_nat(),
                                self.codes.view().len() == cl_pool as nat,
                                self.dicts@.len() == dictl as nat,
                                coff + entries <= cl_pool,
                                doff + fh.dict_len.as_nat() <= dictl as nat,
                                pos as nat == self.dpos_base(r0 as int, ridx as int),
                                r0 == fh.druns_off.as_nat(),
                                r0 as int <= ridx as int,
                                ridx < r0 + fh.druns_len.as_nat(),
                                entries == fh.entries.as_nat(),
                                pos + run_len == self.druns@[ridx as int].1.as_nat(),
                                pos + run_len <= entries,
                                vals == self.dict_run_vals(f as int, ridx as int),
                                vals.len() == run_len as nat,
                                scratch@.len() == j as nat,
                                forall|q: int| 0 <= q < j
                                    ==> #[trigger] scratch@[q] == vals[q],
                            decreases cl - j,
                        {
                            proof {
                                assert(pos + j < fh.entries.as_nat());
                                // The codes-in-range invariant, at its own
                                // trigger shape.
                                assert(self.codes.view()[
                                    fh.data_off.as_nat() + (pos + j) as int]
                                    < fh.dict_len.as_nat());
                                assert(coff + pos + j < cl_pool);
                                assert(self.codes.view()[coff + pos + j]
                                    < fh.dict_len.as_nat());
                            }
                            let c = self.codes.get(coff + pos + j);
                            scratch.push(self.dicts[doff + c]);
                            j += 1;
                        }
                        // Overflow-safe clamp, then the same uniform block
                        // copy as the Runs arm - source is the scratch.
                        let src = vstd::slice::slice_subrange(
                            scratch.as_slice(), 0, cl);
                        let tslice = target.as_mut_slice();
                        let (_, rest) = tslice.split_at_mut(start);
                        let (dst, tail) = rest.split_at_mut(cl);
                        dst.copy_from_slice(src);
                        proof {
                            assert(target@.len() == tlen as nat);
                            assert forall|q: int| 0 <= q < cl
                                implies #[trigger] target@[start + q]
                                    == vals[q] by {
                                assert(target@[start + q] == src@[q]);
                                assert(src@[q] == scratch@[q]);
                            }
                            assert forall|q: int| 0 <= q < target@.len()
                                && !(start <= q && q < start + cl)
                                implies #[trigger] target@[q] == pre_run[q] by {}
                        }
                        proof {
                            if run_len <= tlen - start {
                                assert(cl == run_len);
                            } else {
                                assert(start + cl == tlen);
                            }
                            assert forall|q: int| 0 <= q < target@.len() implies
                                (#[trigger] target@[q]) == write_block(pre_run, start as nat, vals)[q] by {
                                if start as int <= q && q < start as int + cl as int {
                                    assert(target@[start as int + (q - start as int)]
                                        == vals[q - start as int]);
                                } else if start as int + cl as int <= q
                                    && q < start as int + vals.len() {
                                    assert(cl < run_len);
                                    assert(start + cl == tlen);
                                    assert(q >= tlen as int);
                                    assert(false);
                                } else {
                                    assert(target@[q] == pre_run[q]);
                                }
                            }
                            assert(target@ =~= write_block(
                                pre_run, start as nat, vals));
                        }
                    } else {
                        proof {
                            assert(target@ =~= write_block(
                                pre_run, start as nat, vals));
                        }
                    }
                    proof {
                        assert(target@ =~= self.dict_runs_overlay(
                            base, f as int, r as int + 1));
                    }
                    pos = endp;
                    r += 1;
                }
            }
        }
    }

    /// Every offs entry is bounded by the values pool (monotone chain to the
    /// closing entry). Requires exactly the two offs facts rather than full
    /// `wf`, so callers that carry a trimmed invariant can use it.
    pub proof fn lemma_offs_bounded(&self, r: int)
        requires
            0 <= r < self.offs@.len(),
            forall|a: int| 0 <= a < self.offs@.len() - 1
                ==> (#[trigger] self.offs@[a]).as_nat() <= self.offs@[a + 1].as_nat(),
            (self.offs@[self.offs@.len() - 1]).as_nat() == self.values@.len(),
        ensures self.offs@[r].as_nat() <= self.values@.len(),
        decreases self.offs@.len() - r,
    {
        if r < self.offs@.len() - 1 {
            self.lemma_offs_bounded(r + 1);
        }
    }

    /// Seal one hot stratum as a `Plain` cold frame: append the pairs to the
    /// pool and push a header whose offsets are the current cursors. The
    /// caller guarantees representability of the new cursor positions in `I`
    /// (checked by the eviction policy before evicting; a column that cannot
    /// represent its own pool position cannot hold the frame at all).
    #[verifier::rlimit(1800)]
    pub fn seal_plain(&mut self, stratum: &[(T, I)])
        requires
            old(self).wf(),

        ensures
            final(self).wf(),
            final(self).frames@.len() == old(self).frames@.len() + 1,
    {
        // Total: the capacity bounds are checked, not assumed (each refusal
        // is the documented trap).
        if !(self.frames.len() < usize::MAX) {
            crate::guard::refuse("ColdStack::seal_plain: frame stack at usize::MAX");
        }
        if !(<I as crate::index_like::IndexLike>::try_from_usize(self.starts.len()).is_some()) {
            crate::guard::refuse("ColdStack::seal_plain: run table at the index word");
        }
        if !(stratum.len() <= usize::MAX - self.pairs.len()) {
            crate::guard::refuse("ColdStack::seal_plain: pair pool would overflow usize");
        }
        if !(<I as crate::index_like::IndexLike>::try_from_usize(self.pairs.len() + stratum.len()).is_some()) {
            crate::guard::refuse("ColdStack::seal_plain: pair pool at the index word");
        }
        let off = self.pairs.len();
        let slen = stratum.len();
        // Append per element: verified, and off the hot path (sealing is the
        // rare arm of the eviction policy). A memcpy upgrade needs a vstd
        // spec for extend_from_slice.
        let mut k: usize = 0;
        while k < slen
            invariant
                k <= slen,
                slen == stratum@.len(),
                self.pairs@.len() == off + k,
                off == old(self).pairs@.len(),
                forall|m: int| 0 <= m < off ==> #[trigger] self.pairs@[m] == old(self).pairs@[m],
                forall|m: int| 0 <= m < k ==> #[trigger] self.pairs@[off + m] == stratum@[m],
                self.frames@ == old(self).frames@,
                self.starts@ == old(self).starts@,
                self.offs@ == old(self).offs@,
                self.values@ == old(self).values@,
                self.druns@ == old(self).druns@,
                self.dicts@ == old(self).dicts@,
                self.codes == old(self).codes,
            decreases slen - k,
        {
            self.pairs.push(stratum[k]);
            k += 1;
        }
        let data_off = match I::try_from_usize(off) {
            Some(v) => v,
            None => { crate::guard::refuse("ColdStack::seal_plain: pairs cursor overflow"); }
        };
        let data_len = match I::try_from_usize(slen) {
            Some(v) => v,
            None => { crate::guard::refuse("ColdStack::seal_plain: stratum length overflow"); }
        };
        let runs_off = match I::try_from_usize(self.starts.len()) {
            Some(v) => v,
            None => { crate::guard::refuse("ColdStack::seal_plain: runs cursor overflow"); }
        };
        let zero = match I::try_from_usize(0) {
            Some(v) => v,
            None => { crate::guard::refuse("ColdStack::seal_plain: zero unrepresentable"); }
        };
        let hdr = ColdHdr {
            mode: ColdMode::Plain,
            runs_off,
            runs_len: zero,
            data_off,
            data_len,
            entries: data_len,
            druns_off: zero,
            druns_len: zero,
            dict_off: zero,
            dict_len: zero,
        };
        let ghost pre = *self;
        self.frames.push(hdr);
        proof {
            let n0 = pre.frames@.len() as int;
            self.lemma_cursors_prefix_all(pre, n0);
            self.lemma_cursors_prefix_all(*old(self), n0);
            // One unfold each at the new top.
            assert(self.frames@[n0].mode is Plain);
            assert(self.frames@[n0].data_len.as_nat() == slen as nat);
            assert(self.pairs_used(n0 + 1)
                == self.pairs_used(n0) + slen as nat);
            assert(self.runs_used(n0 + 1) == self.runs_used(n0));
            assert(self.values_used(n0 + 1) == self.values_used(n0));
            assert(self.druns_used(n0 + 1) == self.druns_used(n0));
            assert(self.dicts_used(n0 + 1) == self.dicts_used(n0));
            assert(self.codes_used(n0 + 1) == self.codes_used(n0));
            assert forall|f: int| 0 <= f < self.frames@.len()
                implies #[trigger] self.hdr_wf(f) by {
                if f < n0 {
                    // Bridge old -> pre: the append only grew `pairs`, and a
                    // header's bounds are monotone in pool length. The
                    // opaque dict-content clause needs its transfer lemma
                    // (opacity removes congruence) even though druns/codes
                    // are untouched here.
                    assert(old(self).hdr_wf(f));
                    assert(old(self).pairs@.len() <= self.pairs@.len());
                    if self.frames@[f].mode is RunsDict {
                        self.lemma_dict_content_transfer(*old(self), f);
                    }
                }
            }
            // CSR anchors survive: no run and no value was added, and every
            // cursor at or below n0 is unchanged; the new boundary n0+1 has
            // the same cursors as n0. Facts come from old(self): `pre` is a
            // mid-mutation snapshot whose wf is not known, but the run and
            // value pools are untouched between old and now.
            if self.starts@.len() > 0 {
                assert(old(self).starts@.len() > 0);
                assert forall|f: int| 0 <= f <= n0 + 1
                    implies (#[trigger] self.offs@[self.runs_used(f) as int]).as_nat()
                        == self.values_used(f) by {
                    let g = if f <= n0 { f } else { n0 };
                    assert(old(self).offs@[old(self).runs_used(g) as int].as_nat()
                        == old(self).values_used(g));
                    assert(self.offs@ == old(self).offs@);
                }
            }
        }
    }

    /// Seal one hot stratum as a `Runs` cold frame: sort by index, coalesce
    /// consecutive indices into CSR runs, and append to the pools. The
    /// uniqueness of the stratum's indices is a REQUIRES, not a structural
    /// invariant: it is established by the unique-capture discipline or by
    /// `dedupe_first` at trail eviction, and required here because runs
    /// cannot encode a duplicate index (goal deliverable 6's factoring).
    ///
    /// The wf-level contract is what this slice proves; the decode-level
    /// contract (frame_decode == the sorted stratum) lands with the restore
    /// extensionality work, and until then the differential test is the
    /// check on content.
    #[verifier::rlimit(1800)]
    pub fn seal_runs(&mut self, stratum: &Vec<(T, I)>)
        requires
            old(self).wf(),

        ensures
            final(self).wf(),
            final(self).frames@.len() == old(self).frames@.len() + 1,
    {
        // Total: every bound the sealing needs is checked here, not assumed
        // (each refusal is the documented trap); the uniqueness scan is one
        // sort of the stratum, which the sealing performs anyway.
        if stratum.len() == 0 {
            crate::guard::refuse("ColdStack::seal_runs: empty stratum");
        }
        if !crate::diff_compress::is_unique_idx(stratum) {
            crate::guard::refuse("ColdStack::seal_runs: stratum has duplicate indices");
        }
        if !(self.frames.len() < usize::MAX) {
            crate::guard::refuse("ColdStack::seal_runs: frame stack at usize::MAX");
        }
        if !(stratum.len() <= usize::MAX - self.values.len()) {
            crate::guard::refuse("ColdStack::seal_runs: value pool would overflow usize");
        }
        if !(<I as crate::index_like::IndexLike>::try_from_usize(self.values.len() + stratum.len()).is_some()) {
            crate::guard::refuse("ColdStack::seal_runs: value pool at the index word");
        }
        if !(stratum.len() < usize::MAX - self.starts.len()) {
            crate::guard::refuse("ColdStack::seal_runs: run table would overflow usize");
        }
        if !(<I as crate::index_like::IndexLike>::try_from_usize(self.starts.len() + stratum.len() + 1).is_some()) {
            crate::guard::refuse("ColdStack::seal_runs: run table at the index word");
        }
        let slen = stratum.len();
        let mut k: usize = 0;
        while k < slen
            invariant
                k <= slen,
                slen == stratum@.len(),
                forall|j: int| 0 <= j < k ==> (#[trigger] stratum@[j]).1.as_nat() + 1 < I::max_nat(),
            decreases slen - k,
        {
            let ix = stratum[k].1.as_usize();
            if !(ix < usize::MAX) || !(<I as crate::index_like::IndexLike>::try_from_usize(ix + 1).is_some()) {
                crate::guard::refuse("ColdStack::seal_runs: index plus one leaves the index word");
            }
            k += 1;
        }
        let sorted = sort_frame_by_index(stratum);
        let n = sorted.len();
        let ghost pre = *self;
        // Open the offs column if this is the first run ever.
        if self.starts.len() == 0 {
            proof {
                // No runs anywhere means no values anywhere, so the fresh
                // offs column's closing entry (0) is honest.
                let np = pre.frames@.len() as int;
                assert(pre.runs_used(np) == 0);
                pre.lemma_no_runs_no_values(np);
                assert(pre.values@.len() == 0);
            }
            let zero = match I::try_from_usize(0) {
                Some(v) => v,
                None => { crate::guard::refuse("ColdStack::seal_runs: zero unrepresentable"); }
            };
            self.offs.push(zero);
        }
        let runs_off_us = self.starts.len();
        let voff_us = self.values.len();
        // Walk the sorted stratum, opening a run at every discontinuity.
        let mut k: usize = 0;
        let mut run_count: usize = 0;
        while k < n
            invariant
                0 < n == sorted@.len(),
                // Loop bodies see only invariants: the requires-derived
                // bounds must ride along explicitly.
                sorted@.len() == stratum@.len(),
                runs_off_us + stratum@.len() + 1 < I::max_nat(),
                voff_us + stratum@.len() < I::max_nat(),
                crate::diff_compress::unique_idx(sorted@),
                forall|a: int, b: int| 0 <= a < b < sorted@.len()
                    ==> (#[trigger] sorted@[a]).1.as_nat() <= (#[trigger] sorted@[b]).1.as_nat(),
                k <= n,
                // pools only grow, and only in this frame's region
                self.values@.len() == voff_us + k,
                self.starts@.len() == runs_off_us + run_count,
                self.offs@.len() == self.starts@.len() + 1,
                voff_us == pre.values@.len(),
                runs_off_us == pre.starts@.len(),
                run_count <= k,
                k > 0 ==> run_count > 0,
                self.frames@ == pre.frames@,
                self.pairs@ == pre.pairs@,
                self.druns@ == pre.druns@,
                self.dicts@ == pre.dicts@,
                self.codes == pre.codes,
                // the offs column stays monotone and closed at values' end
                forall|r: int| 0 <= r < self.offs@.len() - 1
                    ==> (#[trigger] self.offs@[r]).as_nat() <= self.offs@[r + 1].as_nat(),
                (#[trigger] self.offs@[self.offs@.len() - 1]).as_nat() == self.values@.len(),
                self.offs@[0].as_nat() == 0,
                // prefix of the pools is untouched
                forall|m: int| 0 <= m < voff_us ==> #[trigger] self.values@[m] == pre.values@[m],
                forall|m: int| 0 <= m < runs_off_us ==> #[trigger] self.starts@[m] == pre.starts@[m],
                forall|m: int| 0 <= m < runs_off_us + 1 && m < pre.offs@.len()
                    ==> #[trigger] self.offs@[m] == pre.offs@[m],
                self.values@.len() < I::max_nat(),
                self.starts@.len() < I::max_nat(),
            decreases n - k,
        {
            let (v, idx) = sorted[k];
            let open_new_run = if k == 0 {
                true
            } else {
                let (_, prev_idx) = sorted[k - 1];
                proof {
                    // sorted (<=) plus unique (!=) gives strict order, which
                    // both justifies the subtraction and is what makes the
                    // successor test the only continuation case.
                    assert(sorted@[(k - 1) as int].1.as_nat() <= sorted@[k as int].1.as_nat());
                    assert(sorted@[(k - 1) as int].1.as_nat() != sorted@[k as int].1.as_nat());
                }
                idx.as_usize() - 1 != prev_idx.as_usize()
            };
            if open_new_run {
                self.starts.push(idx);
                if self.values.len() == usize::MAX {
                    crate::guard::refuse("ColdStack::seal_runs: values pool at usize::MAX");
                }
                let end = match I::try_from_usize(self.values.len() + 1) {
                    Some(e) => e,
                    None => { crate::guard::refuse("ColdStack::seal_runs: values cursor overflow"); }
                };
                self.values.push(v);
                self.offs.push(end);
                run_count += 1;
            } else {
                if self.values.len() == usize::MAX {
                    crate::guard::refuse("ColdStack::seal_runs: values pool at usize::MAX");
                }
                let end = match I::try_from_usize(self.values.len() + 1) {
                    Some(e) => e,
                    None => { crate::guard::refuse("ColdStack::seal_runs: values cursor overflow"); }
                };
                self.values.push(v);
                let last = self.offs.len() - 1;
                self.offs.set(last, end);
            }
            proof {
                assert(n as nat == stratum@.len());
                assert(run_count <= k + 1);
                assert(runs_off_us + n < I::max_nat());
            }
            k += 1;
        }
        let hdr = ColdHdr {
            mode: ColdMode::Runs,
            runs_off: match I::try_from_usize(runs_off_us) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs: runs cursor overflow"); }
            },
            runs_len: match I::try_from_usize(run_count) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs: run count overflow"); }
            },
            data_off: match I::try_from_usize(voff_us) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs: values offset overflow"); }
            },
            data_len: match I::try_from_usize(n) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs: frame length overflow"); }
            },
            entries: match I::try_from_usize(n) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs: entry count overflow"); }
            },
            druns_off: match I::try_from_usize(0) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs: zero unrepresentable"); }
            },
            druns_len: match I::try_from_usize(0) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs: zero unrepresentable"); }
            },
            dict_off: match I::try_from_usize(0) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs: zero unrepresentable"); }
            },
            dict_len: match I::try_from_usize(0) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs: zero unrepresentable"); }
            },
        };
        let ghost mid = *self;
        self.frames.push(hdr);
        proof {
            let n0 = pre.frames@.len() as int;
            self.lemma_cursors_prefix_all(mid, n0);
            mid.lemma_cursors_prefix_all(pre, n0);
            assert(self.runs_used(n0 + 1) == self.runs_used(n0) + run_count as nat);
            assert(self.values_used(n0 + 1) == self.values_used(n0) + n as nat);
            assert(self.pairs_used(n0 + 1) == self.pairs_used(n0));
            assert(self.druns_used(n0 + 1) == self.druns_used(n0));
            assert(self.dicts_used(n0 + 1) == self.dicts_used(n0));
            assert(self.codes_used(n0 + 1) == self.codes_used(n0));
            assert forall|f: int| 0 <= f < self.frames@.len()
                implies #[trigger] self.hdr_wf(f) by {
                if f < n0 {
                    assert(pre.hdr_wf(f));
                    if self.frames@[f].mode is RunsDict {
                        self.lemma_dict_content_transfer(pre, f);
                    }
                }
            }
            self.lemma_cursors_prefix_all(*old(self), n0);
            old(self).lemma_cursors_monotone_all(n0);
            if self.starts@.len() > 0 {
                assert forall|f: int| 0 <= f <= n0 + 1
                    implies (#[trigger] self.offs@[self.runs_used(f) as int]).as_nat()
                        == self.values_used(f) by {
                    if f <= n0 {
                        if old(self).starts@.len() > 0 {
                            // Prior anchors survive: the offs prefix below the
                            // frame's first run is untouched by the append.
                            assert(old(self).offs@[old(self).runs_used(f) as int].as_nat()
                                == old(self).values_used(f));
                        } else {
                            // First runs ever: every earlier boundary has zero
                            // cursors, and the fresh offs column opens at 0.
                            assert(old(self).runs_used(n0) == 0);
                            old(self).lemma_no_runs_no_values(n0);
                            assert(old(self).values_used(n0) == 0);
                            assert(old(self).runs_used(f) == 0);
                            assert(old(self).values_used(f) == 0);
                            assert(self.offs@[0].as_nat() == 0);
                        }
                    }
                }
            }
        }
    }

    /// Cursor prefix-stability over a whole range at once: the forall form
    /// keeps assert-forall by-blocks call-free, which keeps their VCs small
    /// (per-instantiation lemma calls inside by-blocks blew the prover's
    /// resource limit and provoked worker crashes).
    pub proof fn lemma_cursors_prefix_all(&self, other: Self, upto: int)
        requires
            0 <= upto,
            upto <= self.frames@.len(),
            upto <= other.frames@.len(),
            forall|g: int| 0 <= g < upto ==> #[trigger] self.frames@[g] == other.frames@[g],
        ensures
            forall|f: int| 0 <= f <= upto ==> #[trigger] self.runs_used(f) == other.runs_used(f),
            forall|f: int| 0 <= f <= upto ==> #[trigger] self.pairs_used(f) == other.pairs_used(f),
            forall|f: int| 0 <= f <= upto ==> #[trigger] self.values_used(f) == other.values_used(f),
            forall|f: int| 0 <= f <= upto ==> #[trigger] self.druns_used(f) == other.druns_used(f),
            forall|f: int| 0 <= f <= upto ==> #[trigger] self.dicts_used(f) == other.dicts_used(f),
            forall|f: int| 0 <= f <= upto ==> #[trigger] self.codes_used(f) == other.codes_used(f),
        decreases upto,
    {
        if upto > 0 {
            self.lemma_cursors_prefix_all(other, upto - 1);
        }
        // Boundary case: the foralls above stop at upto - 1.
        self.lemma_cursors_prefix(other, upto);
    }

    /// A stack with no runs holds no values: every Runs frame carries at
    /// least one run (hdr_wf), so a zero runs cursor forces every frame Plain
    /// and the values cursor to zero.
    #[verifier::spinoff_prover]
    pub proof fn lemma_no_runs_no_values(&self, upto: int)
        requires
            0 <= upto <= self.frames@.len(),
            forall|f: int| 0 <= f < self.frames@.len() ==> #[trigger] self.hdr_wf(f),
            self.runs_used(upto) == 0,
        ensures self.values_used(upto) == 0,
        decreases upto,
    {
        if upto > 0 {
            assert(self.hdr_wf(upto - 1));
            self.lemma_no_runs_no_values(upto - 1);
        }
    }

    /// Cursor monotonicity over a whole range at once, same rationale.
    pub proof fn lemma_cursors_monotone_all(&self, upto: int)
        requires 0 <= upto <= self.frames@.len(),
        ensures
            forall|a: int, b: int| 0 <= a <= b <= upto
                ==> #[trigger] self.runs_used(a) <= #[trigger] self.runs_used(b)
                    && self.pairs_used(a) <= self.pairs_used(b)
                    && self.values_used(a) <= self.values_used(b)
                    && self.druns_used(a) <= self.druns_used(b)
                    && self.dicts_used(a) <= self.dicts_used(b)
                    && self.codes_used(a) <= self.codes_used(b),
        decreases upto,
    {
        if upto > 0 {
            self.lemma_cursors_monotone_all(upto - 1);
            assert forall|a: int| 0 <= a <= upto
                implies self.runs_used(a) <= self.runs_used(upto)
                    && self.pairs_used(a) <= self.pairs_used(upto)
                    && self.values_used(a) <= self.values_used(upto)
                    && self.druns_used(a) <= self.druns_used(upto)
                    && self.dicts_used(a) <= self.dicts_used(upto)
                    && self.codes_used(a) <= self.codes_used(upto) by {
                self.lemma_cursors_monotone(a, upto);
            }
        }
    }

    /// Cursor prefix-stability: two stacks agreeing on the first `f` frames
    /// have equal cursors at `f`.
    pub proof fn lemma_cursors_prefix(&self, other: Self, f: int)
        requires
            0 <= f,
            f <= self.frames@.len(),
            f <= other.frames@.len(),
            forall|g: int| 0 <= g < f ==> #[trigger] self.frames@[g] == other.frames@[g],
        ensures
            self.runs_used(f) == other.runs_used(f),
            self.pairs_used(f) == other.pairs_used(f),
            self.values_used(f) == other.values_used(f),
            self.druns_used(f) == other.druns_used(f),
            self.dicts_used(f) == other.dicts_used(f),
            self.codes_used(f) == other.codes_used(f),
        decreases f,
    {
        if f > 0 {
            self.lemma_cursors_prefix(other, f - 1);
        }
    }

    /// Survivor headers stay well-formed after a pop. Stated over exactly
    /// the pool-prefix facts the truncations establish, so the by-block's VC
    /// stays small (the inline form wedged the solver - the same failure
    /// mode the restore loop's trimmed invariants fixed).
    pub proof fn lemma_pop_survivors_hdr_wf(&self, pre: Self, n1: int)
        requires
            pre.wf(),
            0 <= n1 < pre.frames@.len(),
            self.frames@.len() == n1,
            forall|g: int| 0 <= g < n1 ==> #[trigger] self.frames@[g] == pre.frames@[g],
            self.pairs@.len() == pre.pairs_used(n1),
            self.values@.len() == pre.values_used(n1),
            self.starts@.len() == pre.runs_used(n1),
            self.druns@.len() == pre.druns_used(n1),
            self.dicts@.len() == pre.dicts_used(n1),
            self.codes.view().len() == pre.codes_used(n1),
            forall|m: int| 0 <= m < self.pairs@.len()
                ==> #[trigger] self.pairs@[m] == pre.pairs@[m],
            forall|m: int| 0 <= m < self.values@.len()
                ==> #[trigger] self.values@[m] == pre.values@[m],
            forall|m: int| 0 <= m < self.druns@.len()
                ==> #[trigger] self.druns@[m] == pre.druns@[m],
            forall|m: int| 0 <= m < self.dicts@.len()
                ==> #[trigger] self.dicts@[m] == pre.dicts@[m],
            forall|m: int| 0 <= m < self.codes.view().len()
                ==> #[trigger] self.codes.view()[m] == pre.codes.view()[m],
            self.starts@.len() > 0 ==> self.offs@.len() == self.starts@.len() + 1,
        ensures
            forall|f: int| 0 <= f < n1 ==> #[trigger] self.hdr_wf(f),
    {
        pre.lemma_cursors_monotone_all(n1 + 1);
        assert forall|f: int| 0 <= f < n1 implies #[trigger] self.hdr_wf(f) by {
            assert(pre.hdr_wf(f));
            assert(self.frames@[f] == pre.frames@[f]);
            let hf = pre.frames@[f];
            assert(hf.runs_off.as_nat() == pre.runs_used(f));
            assert(pre.runs_used(f + 1)
                == pre.runs_used(f) + hf.runs_len.as_nat());
            match hf.mode {
                ColdMode::Plain => {
                    assert(hf.data_off.as_nat() == pre.pairs_used(f));
                    assert(pre.pairs_used(f + 1)
                        == pre.pairs_used(f) + hf.data_len.as_nat());
                }
                ColdMode::Runs => {
                    assert(hf.data_off.as_nat() == pre.values_used(f));
                    assert(pre.values_used(f + 1)
                        == pre.values_used(f) + hf.data_len.as_nat());
                    // A surviving Runs frame witnesses runs below the popped
                    // cursor, so the offs column cannot be empty.
                    assert(hf.runs_len.as_nat() > 0);
                    assert(pre.runs_used(f + 1) > 0);
                }
                ColdMode::RunsDict => {
                    assert(hf.druns_off.as_nat() == pre.druns_used(f));
                    assert(pre.druns_used(f + 1)
                        == pre.druns_used(f) + hf.druns_len.as_nat());
                    assert(hf.dict_off.as_nat() == pre.dicts_used(f));
                    assert(pre.dicts_used(f + 1)
                        == pre.dicts_used(f) + hf.dict_len.as_nat());
                    assert(hf.data_off.as_nat() == pre.codes_used(f));
                    assert(pre.codes_used(f + 1)
                        == pre.codes_used(f) + hf.data_len.as_nat());
                    self.lemma_dict_content_transfer(pre, f);
                }
            }
        }
    }

    /// The offs-column clauses of `wf` after a pop: monotone, opening at 0,
    /// closing at the values pool's end, and anchored at every surviving
    /// frame boundary. Same trimming rationale as the survivors lemma.
    pub proof fn lemma_pop_offs_wf(&self, pre: Self, n1: int)
        requires
            pre.wf(),
            0 <= n1 < pre.frames@.len(),
            self.frames@.len() == n1,
            forall|g: int| 0 <= g < n1 ==> #[trigger] self.frames@[g] == pre.frames@[g],
            self.starts@.len() == pre.runs_used(n1),
            self.values@.len() == pre.values_used(n1),
            forall|m: int| 0 <= m < self.offs@.len()
                ==> #[trigger] self.offs@[m] == pre.offs@[m],
            self.offs@.len() <= pre.offs@.len(),
            self.starts@.len() == 0 ==> self.offs@.len() == 0,
            self.starts@.len() > 0 ==> self.offs@.len() == self.starts@.len() + 1,
        ensures
            forall|r: int| 0 <= r < self.offs@.len() - 1
                ==> (#[trigger] self.offs@[r]).as_nat() <= self.offs@[r + 1].as_nat(),
            self.starts@.len() > 0 ==> {
                &&& self.offs@[self.offs@.len() - 1].as_nat() == self.values@.len()
                &&& self.offs@[0].as_nat() == 0
            },
            self.starts@.len() > 0 ==> forall|f: int| 0 <= f <= n1
                ==> (#[trigger] self.offs@[self.runs_used(f) as int]).as_nat()
                    == self.values_used(f),
    {
        self.lemma_cursors_prefix_all(pre, n1);
        pre.lemma_cursors_monotone_all(n1);
        assert forall|r: int| 0 <= r < self.offs@.len() - 1
            implies (#[trigger] self.offs@[r]).as_nat()
                <= self.offs@[r + 1].as_nat() by {
            assert(pre.offs@[r].as_nat() <= pre.offs@[r + 1].as_nat());
        }
        if self.starts@.len() > 0 {
            assert(pre.starts@.len() > 0);
            assert forall|f: int| 0 <= f <= n1
                implies (#[trigger] self.offs@[self.runs_used(f) as int]).as_nat()
                    == self.values_used(f) by {
                assert(pre.runs_used(f) <= pre.runs_used(n1));
                assert(pre.runs_used(n1) as int <= pre.starts@.len());
                assert(pre.offs@[pre.runs_used(f) as int].as_nat()
                    == pre.values_used(f));
            }
            // Closing: the anchor at n1 IS the last offs entry.
            assert(self.offs@[self.runs_used(n1) as int].as_nat()
                == self.values_used(n1));
            assert(self.offs@[0].as_nat() == pre.offs@[0].as_nat());
        }
    }

    /// Survivor headers' pool offsets still sit at the cursors after a pop:
    /// the popped frame is above every survivor, so cursors below `n1` are
    /// untouched. Same trimming rationale as the survivors lemma.
    pub proof fn lemma_pop_tiling(&self, pre: Self, n1: int)
        requires
            pre.wf(),
            0 <= n1 < pre.frames@.len(),
            self.frames@.len() == n1,
            forall|g: int| 0 <= g < n1 ==> #[trigger] self.frames@[g] == pre.frames@[g],
        ensures
            forall|f: int| 0 <= f < n1 ==> {
                let h = #[trigger] self.frames@[f];
                &&& h.runs_off.as_nat() == self.runs_used(f)
                &&& (h.mode is Plain ==> h.data_off.as_nat() == self.pairs_used(f))
                &&& (h.mode is Runs ==> h.data_off.as_nat() == self.values_used(f))
                &&& (h.mode is RunsDict ==> {
                        &&& h.druns_off.as_nat() == self.druns_used(f)
                        &&& h.dict_off.as_nat() == self.dicts_used(f)
                        &&& h.data_off.as_nat() == self.codes_used(f)
                    })
            },
    {
        self.lemma_cursors_prefix_all(pre, n1);
        assert forall|f: int| 0 <= f < n1 implies {
            let h = #[trigger] self.frames@[f];
            &&& h.runs_off.as_nat() == self.runs_used(f)
            &&& (h.mode is Plain ==> h.data_off.as_nat() == self.pairs_used(f))
            &&& (h.mode is Runs ==> h.data_off.as_nat() == self.values_used(f))
            &&& (h.mode is RunsDict ==> {
                    &&& h.druns_off.as_nat() == self.druns_used(f)
                    &&& h.dict_off.as_nat() == self.dicts_used(f)
                    &&& h.data_off.as_nat() == self.codes_used(f)
                })
        } by {
            assert(self.frames@[f] == pre.frames@[f]);
        }
    }

    /// Pop the top frame: truncate every pool back to the popped header's own
    /// offsets. O(1), no free, no repair — the bump-allocator property.
    #[verifier::rlimit(900)]
    #[verifier::spinoff_prover]
    pub fn pop_frame(&mut self)
        requires
            old(self).wf(),

        ensures
            final(self).wf(),
            final(self).frames@.len() == old(self).frames@.len() - 1,
    {
        // Total: popping an empty stack is the documented trap.
        if self.frames.len() == 0 {
            crate::guard::refuse("ColdStack::pop_frame: empty stack");
        }
        let ghost pre = *self;
        let h = match self.frames.pop() {
            Some(h) => h,
            None => { crate::guard::refuse("ColdStack::pop_frame: empty stack"); }
        };
        let ghost n1 = self.frames@.len() as int;
        proof {
            // The popped header's offsets ARE the cursors at n1 (tiling), and
            // the pool ends are the cursors at n1+1; truncating to the popped
            // offsets therefore lands exactly at the new stack's cursors.
            self.lemma_cursors_prefix_all(pre, n1);
            pre.lemma_cursors_monotone_all(n1);
            assert(pre.frames@[n1] == h);
            // The popped header's own wf: Plain has no runs (closes the
            // starts-length chain), Runs bounds runs_off strictly below
            // offs.len (discharges the truncate index arithmetic).
            assert(pre.hdr_wf(n1));
            assert(h.runs_off.as_nat() == pre.runs_used(n1));
            // Pool-end unfolds at n1+1, split by the popped mode.
            assert(pre.pairs_used(n1 + 1) == pre.pairs_used(n1)
                + if h.mode is Plain { h.data_len.as_nat() } else { 0 });
            assert(pre.values_used(n1 + 1) == pre.values_used(n1)
                + if h.mode is Runs { h.data_len.as_nat() } else { 0 });
            assert(pre.runs_used(n1 + 1) == pre.runs_used(n1) + h.runs_len.as_nat());
            assert(pre.druns_used(n1 + 1) == pre.druns_used(n1)
                + if h.mode is RunsDict { h.druns_len.as_nat() } else { 0 });
            assert(pre.dicts_used(n1 + 1) == pre.dicts_used(n1)
                + if h.mode is RunsDict { h.dict_len.as_nat() } else { 0 });
            assert(pre.codes_used(n1 + 1) == pre.codes_used(n1)
                + if h.mode is RunsDict { h.data_len.as_nat() } else { 0 });
        }
        match h.mode {
            ColdMode::Plain => {
                self.pairs.truncate(h.data_off.as_usize());
                proof {
                    assert(self.pairs@.len() == pre.pairs_used(n1));
                    assert(self.values@.len() == pre.values_used(n1));
                    assert(self.starts@.len() == pre.runs_used(n1));
                    assert(self.druns@.len() == pre.druns_used(n1));
                    assert(self.dicts@.len() == pre.dicts_used(n1));
                    assert(self.codes.view().len() == pre.codes_used(n1));
                }
            }
            ColdMode::Runs => {
                let voff = h.data_off.as_usize();
                self.values.truncate(voff);
                let roff = h.runs_off.as_usize();
                self.starts.truncate(roff);
                if roff == 0 {
                    self.offs.clear();
                } else {
                    // Exec witness for the arithmetic: offs.len() as usize
                    // bounds roff via the popped header's wf, so roff + 1
                    // cannot wrap.
                    let ol = self.offs.len();
                    proof {
                        assert(pre.hdr_wf(n1));
                        assert(h.runs_off.as_nat() + h.runs_len.as_nat() < pre.offs@.len());
                        assert(roff < ol);
                    }
                    self.offs.truncate(roff + 1);
                    proof {
                        // The anchor at the popped boundary recloses offs.
                        assert(pre.starts@.len() > 0);
                        assert(pre.offs@[pre.runs_used(n1) as int].as_nat()
                            == pre.values_used(n1));
                        assert(self.offs@[roff as int].as_nat()
                            == self.values@.len());
                    }
                }
                proof {
                    assert(self.values@.len() == pre.values_used(n1));
                    assert(self.starts@.len() == pre.runs_used(n1));
                    assert(self.pairs@.len() == pre.pairs_used(n1));
                    assert(self.druns@.len() == pre.druns_used(n1));
                    assert(self.dicts@.len() == pre.dicts_used(n1));
                    assert(self.codes.view().len() == pre.codes_used(n1));
                }
            }
            ColdMode::RunsDict => {
                self.druns.truncate(h.druns_off.as_usize());
                self.dicts.truncate(h.dict_off.as_usize());
                let coff = h.data_off.as_usize();
                proof {
                    // The popped header's codes extent bounds the truncation
                    // index inside the pool.
                    assert(h.data_off.as_nat() + h.data_len.as_nat()
                        <= pre.codes.view().len());
                }
                self.codes.truncate_codes(coff);
                proof {
                    assert(self.druns@.len() == pre.druns_used(n1));
                    assert(self.dicts@.len() == pre.dicts_used(n1));
                    assert(self.codes.view().len() == pre.codes_used(n1));
                    assert(self.values@.len() == pre.values_used(n1));
                    assert(self.starts@.len() == pre.runs_used(n1));
                    assert(self.pairs@.len() == pre.pairs_used(n1));
                }
            }
        }
        proof {
            // Cursor prefix equality across the pool truncations (cursors
            // read only frames, which are already popped).
            self.lemma_cursors_prefix_all(pre, n1);
            // Pointwise pool-prefix facts for the survivors lemma: every
            // truncate keeps its prefix verbatim, and untouched pools are
            // equal outright.
            assert forall|m: int| 0 <= m < self.pairs@.len()
                implies #[trigger] self.pairs@[m] == pre.pairs@[m] by {}
            assert forall|m: int| 0 <= m < self.values@.len()
                implies #[trigger] self.values@[m] == pre.values@[m] by {}
            assert forall|m: int| 0 <= m < self.druns@.len()
                implies #[trigger] self.druns@[m] == pre.druns@[m] by {}
            assert forall|m: int| 0 <= m < self.dicts@.len()
                implies #[trigger] self.dicts@[m] == pre.dicts@[m] by {}
            assert forall|m: int| 0 <= m < self.codes.view().len()
                implies #[trigger] self.codes.view()[m] == pre.codes.view()[m] by {}
            assert(self.starts@.len() > 0 ==> self.offs@.len() == self.starts@.len() + 1);
            self.lemma_pop_survivors_hdr_wf(pre, n1);
            assert forall|m: int| 0 <= m < self.offs@.len()
                implies #[trigger] self.offs@[m] == pre.offs@[m] by {}
            self.lemma_pop_offs_wf(pre, n1);
            self.lemma_pop_tiling(pre, n1);
        }
    }
}

// The dictionary build compares values, which the codebase does through
// `as_usize` lifted by `as_nat` injectivity (`assign_codes`); hence the
// stronger `T: IndexLike` bound on the dict-mode seal alone.
impl<T: IndexLike, I: IndexLike> ColdStack<T, I> {
    /// Seal one hot stratum as a `RunsDict` cold frame: sort by index, build
    /// the frame dictionary and code column, coalesce consecutive indices
    /// into frame-local CSR runs, and append to the pools. Uniqueness of the
    /// stratum's indices is a REQUIRES (deliverable 6's factoring), because
    /// runs cannot encode a duplicate index.
    #[verifier::rlimit(1800)]
    #[verifier::spinoff_prover]
    pub fn seal_runs_dict(&mut self, stratum: &Vec<(T, I)>)
        requires
            old(self).wf(),

        ensures
            final(self).wf(),
            final(self).frames@.len() == old(self).frames@.len() + 1,
    {
        // Total: every bound the sealing needs is checked here, not assumed
        // (each refusal is the documented trap); the uniqueness scan is one
        // sort of the stratum, which the sealing performs anyway.
        if stratum.len() == 0 {
            crate::guard::refuse("ColdStack::seal_runs_dict: empty stratum");
        }
        if !crate::diff_compress::is_unique_idx(stratum) {
            crate::guard::refuse("ColdStack::seal_runs_dict: stratum has duplicate indices");
        }
        if !(self.frames.len() < usize::MAX) {
            crate::guard::refuse("ColdStack::seal_runs_dict: frame stack at usize::MAX");
        }
        if !(stratum.len() <= usize::MAX - self.codes.len()) {
            crate::guard::refuse("ColdStack::seal_runs_dict: code column would overflow usize");
        }
        if !(<I as crate::index_like::IndexLike>::try_from_usize(self.codes.len() + stratum.len()).is_some()) {
            crate::guard::refuse("ColdStack::seal_runs_dict: code column at the index word");
        }
        if !(stratum.len() <= usize::MAX - self.dicts.len()) {
            crate::guard::refuse("ColdStack::seal_runs_dict: dictionary pool would overflow usize");
        }
        if !(<I as crate::index_like::IndexLike>::try_from_usize(self.dicts.len() + stratum.len()).is_some()) {
            crate::guard::refuse("ColdStack::seal_runs_dict: dictionary pool at the index word");
        }
        if !(stratum.len() <= usize::MAX - self.druns.len()) {
            crate::guard::refuse("ColdStack::seal_runs_dict: dictionary runs would overflow usize");
        }
        if !(<I as crate::index_like::IndexLike>::try_from_usize(self.druns.len() + stratum.len()).is_some()) {
            crate::guard::refuse("ColdStack::seal_runs_dict: dictionary runs at the index word");
        }
        if !(<I as crate::index_like::IndexLike>::try_from_usize(self.starts.len()).is_some()) {
            crate::guard::refuse("ColdStack::seal_runs_dict: run table at the index word");
        }
        if !(<I as crate::index_like::IndexLike>::try_from_usize(stratum.len()).is_some()) {
            crate::guard::refuse("ColdStack::seal_runs_dict: stratum at the index word");
        }
        let slen = stratum.len();
        let mut k: usize = 0;
        while k < slen
            invariant
                k <= slen,
                slen == stratum@.len(),
                forall|j: int| 0 <= j < k ==> (#[trigger] stratum@[j]).1.as_nat() + 1 < I::max_nat(),
            decreases slen - k,
        {
            let ix = stratum[k].1.as_usize();
            if !(ix < usize::MAX) || !(<I as crate::index_like::IndexLike>::try_from_usize(ix + 1).is_some()) {
                crate::guard::refuse("ColdStack::seal_runs_dict: index plus one leaves the index word");
            }
            k += 1;
        }
        let sorted = sort_frame_by_index(stratum);
        let n = sorted.len();
        // Value column of the sorted stratum, then dictionary + codes.
        let mut vals: Vec<T> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == sorted@.len(),
                vals@.len() == i as nat,
                forall|t: int| 0 <= t < i ==> #[trigger] vals@[t] == sorted@[t].0,
            decreases n - i,
        {
            vals.push(sorted[i].0);
            i += 1;
        }
        let (dict, codes_v) = crate::diff_compress::assign_codes(&vals);
        let dlen = dict.len();
        let ghost pre = *self;
        // Widen the shared code pool for this dictionary, then append the
        // frame's codes and dictionary.
        self.codes.widen_for(dlen);
        let coff = self.codes.len();
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                n == codes_v@.len(),
                dlen == dict@.len(),
                forall|t: int| 0 <= t < n ==> (#[trigger] codes_v@[t]) < dlen,
                (dlen as nat) <= self.codes.width_cap(),
                !(self.codes is Packed),
                self.codes.wf(),
                self.codes.view().len() == coff + k,
                coff == pre.codes.view().len(),
                forall|m: int| 0 <= m < coff
                    ==> #[trigger] self.codes.view()[m] == pre.codes.view()[m],
                forall|m: int| 0 <= m < k
                    ==> #[trigger] self.codes.view()[coff + m] == codes_v@[m] as nat,
                self.codes.width_cap() == old(self).codes.width_cap()
                    || self.codes.width_cap() >= dlen as nat,
                self.frames@ == pre.frames@,
                self.starts@ == pre.starts@,
                self.offs@ == pre.offs@,
                self.pairs@ == pre.pairs@,
                self.values@ == pre.values@,
                self.druns@ == pre.druns@,
                self.dicts@ == pre.dicts@,
            decreases n - k,
        {
            self.codes.push_code(codes_v[k]);
            k += 1;
        }
        let dioff = self.dicts.len();
        let mut j: usize = 0;
        while j < dlen
            invariant
                j <= dlen,
                dlen == dict@.len(),
                self.dicts@.len() == dioff + j,
                dioff == pre.dicts@.len(),
                forall|m: int| 0 <= m < dioff ==> #[trigger] self.dicts@[m] == pre.dicts@[m],
                forall|m: int| 0 <= m < j ==> #[trigger] self.dicts@[dioff + m] == dict@[m],
                self.frames@ == pre.frames@,
                self.starts@ == pre.starts@,
                self.offs@ == pre.offs@,
                self.pairs@ == pre.pairs@,
                self.values@ == pre.values@,
                self.druns@ == pre.druns@,
                self.codes.view().len() == coff + n,
                !(self.codes is Packed),
                self.codes.wf(),
                forall|m: int| 0 <= m < coff
                    ==> #[trigger] self.codes.view()[m] == pre.codes.view()[m],
                forall|m: int| 0 <= m < n
                    ==> #[trigger] self.codes.view()[coff + m] == codes_v@[m] as nat,
            decreases dlen - j,
        {
            self.dicts.push(dict[j]);
            j += 1;
        }
        // Coalesce the sorted, unique index column into frame-local CSR runs.
        let droff = self.druns.len();
        let mut k2: usize = 0;
        let mut run_count: usize = 0;
        while k2 < n
            invariant
                0 < n == sorted@.len(),
                sorted@.len() == stratum@.len(),
                droff + stratum@.len() < I::max_nat(),
                stratum@.len() < I::max_nat(),
                crate::diff_compress::unique_idx(sorted@),
                forall|a: int, b: int| 0 <= a < b < sorted@.len()
                    ==> (#[trigger] sorted@[a]).1.as_nat() <= (#[trigger] sorted@[b]).1.as_nat(),
                k2 <= n,
                self.druns@.len() == droff + run_count,
                droff == pre.druns@.len(),
                run_count <= k2,
                k2 > 0 ==> run_count > 0,
                // Frame-local CSR facts under construction: nonempty runs,
                // strictly chaining cumulative ends, closing at k2.
                forall|r: int| droff <= r < droff + run_count
                    ==> (if r == droff { 0nat } else { self.druns@[r - 1].1.as_nat() })
                        < (#[trigger] self.druns@[r]).1.as_nat(),
                run_count > 0
                    ==> self.druns@[droff + run_count - 1].1.as_nat() == k2 as nat,
                forall|m: int| 0 <= m < droff ==> #[trigger] self.druns@[m] == pre.druns@[m],
                self.frames@ == pre.frames@,
                self.starts@ == pre.starts@,
                self.offs@ == pre.offs@,
                self.pairs@ == pre.pairs@,
                self.values@ == pre.values@,
                self.dicts@.len() == dioff + dlen,
                forall|m: int| 0 <= m < dioff ==> #[trigger] self.dicts@[m] == pre.dicts@[m],
                self.codes.view().len() == coff + n,
                !(self.codes is Packed),
                self.codes.wf(),
                forall|m: int| 0 <= m < coff
                    ==> #[trigger] self.codes.view()[m] == pre.codes.view()[m],
                self.druns@.len() < I::max_nat(),
            decreases n - k2,
        {
            let (_, idx) = sorted[k2];
            let open_new_run = if k2 == 0 {
                true
            } else {
                let (_, prev_idx) = sorted[k2 - 1];
                proof {
                    assert(sorted@[(k2 - 1) as int].1.as_nat() <= sorted@[k2 as int].1.as_nat());
                    assert(sorted@[(k2 - 1) as int].1.as_nat() != sorted@[k2 as int].1.as_nat());
                }
                idx.as_usize() - 1 != prev_idx.as_usize()
            };
            let end = match I::try_from_usize(k2 + 1) {
                Some(e) => e,
                None => { crate::guard::refuse("ColdStack::seal_runs_dict: end overflow"); }
            };
            if open_new_run {
                self.druns.push((idx, end));
                run_count += 1;
            } else {
                let last = self.druns.len() - 1;
                let (s0, _) = self.druns[last];
                self.druns.set(last, (s0, end));
            }
            k2 += 1;
        }
        let hdr = ColdHdr {
            mode: ColdMode::RunsDict,
            runs_off: match I::try_from_usize(self.starts.len()) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs_dict: runs cursor overflow"); }
            },
            runs_len: match I::try_from_usize(0) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs_dict: zero unrepresentable"); }
            },
            data_off: match I::try_from_usize(coff) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs_dict: codes cursor overflow"); }
            },
            data_len: match I::try_from_usize(n) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs_dict: frame length overflow"); }
            },
            entries: match I::try_from_usize(n) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs_dict: entry count overflow"); }
            },
            druns_off: match I::try_from_usize(droff) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs_dict: druns cursor overflow"); }
            },
            druns_len: match I::try_from_usize(run_count) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs_dict: run count overflow"); }
            },
            dict_off: match I::try_from_usize(dioff) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs_dict: dict cursor overflow"); }
            },
            dict_len: match I::try_from_usize(dlen) {
                Some(x) => x,
                None => { crate::guard::refuse("ColdStack::seal_runs_dict: dict size overflow"); }
            },
        };
        let ghost mid = *self;
        self.frames.push(hdr);
        proof {
            let n0 = pre.frames@.len() as int;
            self.lemma_cursors_prefix_all(mid, n0);
            mid.lemma_cursors_prefix_all(pre, n0);
            assert(self.runs_used(n0 + 1) == self.runs_used(n0));
            assert(self.pairs_used(n0 + 1) == self.pairs_used(n0));
            assert(self.values_used(n0 + 1) == self.values_used(n0));
            assert(self.druns_used(n0 + 1) == self.druns_used(n0) + run_count as nat);
            assert(self.dicts_used(n0 + 1) == self.dicts_used(n0) + dlen as nat);
            assert(self.codes_used(n0 + 1) == self.codes_used(n0) + n as nat);
            assert forall|f: int| 0 <= f < self.frames@.len()
                implies #[trigger] self.hdr_wf(f) by {
                if f < n0 {
                    // Old frames: pools only grew and their prefixes are
                    // verbatim, so every extent and content clause carries.
                    assert(pre.hdr_wf(f));
                    let hf = pre.frames@[f];
                    if hf.mode is RunsDict {
                        self.lemma_dict_content_transfer(pre, f);
                    }
                } else {
                    // The new top: hdr_wf(RunsDict) from the construction
                    // loops' exit invariants.
                    assert(f == n0);
                    // A nonempty stratum forces a nonempty dictionary: its
                    // first code indexes it.
                    assert(codes_v@[0] < dict@.len());
                    assert(dlen > 0);
                    assert(self.dict_content_wf(n0)) by {
                        reveal(ColdStack::dict_content_wf);
                        let h = self.frames@[n0];
                        let first = h.druns_off.as_nat() as int;
                        assert(first == droff as int);
                        assert forall|r: int| first <= r < first + h.druns_len.as_nat()
                            implies self.dpos_base(first, r)
                                < (#[trigger] self.druns@[r]).1.as_nat() by {
                            assert((if r == droff as int { 0nat }
                                else { self.druns@[r - 1].1.as_nat() })
                                < self.druns@[r].1.as_nat());
                        }
                        assert(self.druns@[first + h.druns_len.as_nat() - 1].1.as_nat()
                            == n as nat);
                        assert forall|q: int| 0 <= q < h.data_len.as_nat()
                            implies #[trigger] self.codes.view()[h.data_off.as_nat() + q]
                                < h.dict_len.as_nat() by {
                            assert(self.codes.view()[coff + q] == codes_v@[q] as nat);
                            assert(codes_v@[q] < dlen);
                        }
                    }
                }
            }
            // CSR anchors for the values-runs column: starts/offs untouched
            // and the new frame adds no run and no value.
            self.lemma_cursors_prefix_all(pre, n0);
            pre.lemma_cursors_monotone_all(n0);
            if self.starts@.len() > 0 {
                assert(pre.starts@.len() > 0);
                assert forall|f: int| 0 <= f <= n0 + 1
                    implies (#[trigger] self.offs@[self.runs_used(f) as int]).as_nat()
                        == self.values_used(f) by {
                    let g = if f <= n0 { f } else { n0 };
                    assert(pre.offs@[pre.runs_used(g) as int].as_nat()
                        == pre.values_used(g));
                    assert(self.offs@ == pre.offs@);
                }
            }
        }
    }
}

} // verus!
