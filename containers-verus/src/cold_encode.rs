// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Checked construction of a Cold frame from sorted unique captures.

use vstd::prelude::*;

verus! {
use crate::frame::{ColdFrameHdr, IndexRun};
use crate::index_like::IndexLike;

/// Appended runs partition exactly the first `done` input entries. Offsets
/// name the physical value pool; no persistent copy of the input is stored.
pub(crate) open spec fn run_prefix<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, rs: int, vs: int, entries: Seq<(T, I)>, done: int, limit: nat,
) -> bool {
    &&& 0 <= rs <= runs.len()
    &&& 0 <= vs
    &&& 0 <= done <= entries.len()
    &&& runs.len() - rs <= done
    &&& (runs.len() == rs <==> done == 0)
    &&& (rs < runs.len() ==> runs[rs].start == vs)
    &&& (rs < runs.len() ==> runs[runs.len() - 1].start + runs[runs.len() - 1].len == vs + done)
    &&& forall|r: int| rs <= r < runs.len() ==> {
        &&& 0 < (#[trigger] runs[r]).len
        &&& vs <= runs[r].start
        &&& runs[r].start + runs[r].len <= vs + done
        &&& runs[r].base.as_nat() + runs[r].len <= limit
        &&& forall|q: int| 0 <= q < runs[r].len ==>
            (#[trigger] entries[runs[r].start - vs + q]).1.as_nat() == runs[r].base.as_nat() + q
        &&& (r + 1 < runs.len() ==> {
            &&& runs[r].start + runs[r].len == runs[r + 1].start
            &&& runs[r].base.as_nat() + runs[r].len < runs[r + 1].base.as_nat()
        })
    }
}

/// Layout-only accessor keeps entry-mapping quantifiers out of frame assembly.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_run_prefix_layout<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, rs: int, vs: int, entries: Seq<(T, I)>, done: int, limit: nat,
)
    requires run_prefix(runs, rs, vs, entries, done, limit),
    ensures
        0 <= rs <= runs.len(), 0 <= vs, 0 <= done <= entries.len(),
        runs.len() - rs <= done, runs.len() == rs <==> done == 0,
        rs < runs.len() ==> runs[rs].start == vs,
        rs < runs.len() ==> runs[runs.len() - 1].start + runs[runs.len() - 1].len == vs + done,
{}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_run_prefix_run_at<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, rs: int, vs: int, entries: Seq<(T, I)>, done: int, limit: nat, r: int,
)
    requires run_prefix(runs, rs, vs, entries, done, limit), rs <= r < runs.len(),
    ensures 0 < runs[r].len, vs <= runs[r].start,
        runs[r].start + runs[r].len <= vs + done,
        runs[r].base.as_nat() + runs[r].len <= limit,
        r + 1 < runs.len() ==> runs[r].start + runs[r].len == runs[r + 1].start
            && runs[r].base.as_nat() + runs[r].len < runs[r + 1].base.as_nat(),
{}

#[verifier::spinoff_prover]
proof fn append_run<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, rs: int, vs: int, entries: Seq<(T, I)>,
    first: int, end: int, limit: nat, run: IndexRun<I>,
)
    requires run_prefix(runs, rs, vs, entries, first, limit),
        first < end <= entries.len(), run.start == vs + first, run.len == end - first,
        run.base.as_nat() + run.len <= limit,
        forall|q: int| first <= q < end ==>
            (#[trigger] entries[q]).1.as_nat() == run.base.as_nat() + q - first,
        rs < runs.len() ==> runs[runs.len() - 1].base.as_nat() + runs[runs.len() - 1].len < run.base.as_nat(),
    ensures run_prefix(runs.push(run), rs, vs, entries, end, limit),
{
    let out = runs.push(run);
    assert forall|r: int| rs <= r < out.len() implies {
        &&& 0 < (#[trigger] out[r]).len
        &&& vs <= out[r].start
        &&& out[r].start + out[r].len <= vs + end
        &&& out[r].base.as_nat() + out[r].len <= limit
        &&& forall|q: int| 0 <= q < out[r].len ==>
            (#[trigger] entries[out[r].start - vs + q]).1.as_nat() == out[r].base.as_nat() + q
        &&& (r + 1 < out.len() ==> {
            &&& out[r].start + out[r].len == out[r + 1].start
            &&& out[r].base.as_nat() + out[r].len < out[r + 1].base.as_nat()
        })
    } by {
        if r < runs.len() { assert(out[r] == runs[r]); }
    }
}

/// Coalesce maximal consecutive index ranges, preserving every Copy value.
/// Empty input yields an empty frame header, with no empty index runs.
#[verifier::spinoff_prover]
pub(crate) fn append_sorted<T: Copy, I: IndexLike>(
    runs: &mut std::vec::Vec<IndexRun<I>>, values: &mut std::vec::Vec<T>,
    entries: &[(T, I)], saved_len: I,
) -> (frame: ColdFrameHdr<I>)
    requires
        forall|a: int, b: int| 0 <= a < b < entries@.len() ==>
            (#[trigger] entries@[a]).1.as_nat() < (#[trigger] entries@[b]).1.as_nat(),
        forall|q: int| 0 <= q < entries@.len() ==>
            (#[trigger] entries@[q]).1.as_nat() < saved_len.as_nat(),
    ensures
        frame.saved_len == saved_len, frame.runs_start == old(runs)@.len(),
        frame.runs_start + frame.runs_len == final(runs)@.len(),
        final(runs)@.subrange(0, old(runs)@.len() as int) == old(runs)@,
        final(values)@.subrange(0, old(values)@.len() as int) == old(values)@,
        final(values)@.len() == old(values)@.len() + entries@.len(),
        forall|q: int| 0 <= q < entries@.len() ==>
            #[trigger] final(values)@[old(values)@.len() + q] == entries@[q].0,
        run_prefix(final(runs)@, old(runs)@.len() as int, old(values)@.len() as int,
            entries@, entries@.len() as int, saved_len.as_nat()),
{
    let rs = runs.len();
    let vs = values.len();
    let n = entries.len();
    let mut q: usize = 0;
    let ghost original_runs = runs@;
    let ghost original_values = values@;
    while q < n
        invariant
            n == entries@.len(), q <= n,
            rs == original_runs.len(), vs == original_values.len(),
            runs@.subrange(0, rs as int) == original_runs,
            values@.subrange(0, vs as int) == original_values,
            values@.len() == vs + q,
            run_prefix(runs@, rs as int, vs as int, entries@, q as int, saved_len.as_nat()),
            forall|p: int| 0 <= p < q ==> #[trigger] values@[vs + p] == entries@[p].0,
            forall|a: int, b: int| 0 <= a < b < n ==>
                (#[trigger] entries@[a]).1.as_nat() < (#[trigger] entries@[b]).1.as_nat(),
            forall|p: int| 0 <= p < n ==> (#[trigger] entries@[p]).1.as_nat() < saved_len.as_nat(),
            q < n && rs < runs@.len() ==>
                runs@[runs@.len() - 1].base.as_nat() + runs@[runs@.len() - 1].len < entries@[q as int].1.as_nat(),
        decreases n - q,
    {
        let first = q;
        let base = entries[q].1;
        let base_index = base.as_usize();
        let start = values.len();
        while q < n && entries[q].1.as_usize() - base_index == q - first
            invariant
                n == entries@.len(), first < n, first <= q <= n,
                base == entries@[first as int].1, base_index == base.as_nat(),
                start == vs + first,
                rs == original_runs.len(), vs == original_values.len(),
                runs@.subrange(0, rs as int) == original_runs,
                values@.subrange(0, vs as int) == original_values,
                values@.len() == vs + q,
                run_prefix(runs@, rs as int, vs as int, entries@, first as int, saved_len.as_nat()),
                forall|p: int| 0 <= p < q ==> #[trigger] values@[vs + p] == entries@[p].0,
                forall|p: int| first <= p < q ==>
                    (#[trigger] entries@[p]).1.as_nat() == base.as_nat() + p - first,
                base.as_nat() + q - first <= saved_len.as_nat(),
                forall|a: int, b: int| 0 <= a < b < n ==>
                    (#[trigger] entries@[a]).1.as_nat() < (#[trigger] entries@[b]).1.as_nat(),
                forall|p: int| 0 <= p < n ==> (#[trigger] entries@[p]).1.as_nat() < saved_len.as_nat(),
                rs < runs@.len() ==>
                    runs@[runs@.len() - 1].base.as_nat() + runs@[runs@.len() - 1].len < base.as_nat(),
            decreases n - q,
        {
            values.push(entries[q].0);
            q += 1;
        }
        proof {
            assert(first < q);
            if q < n {
                assert(entries@[q - 1].1.as_nat() == base.as_nat() + q - first - 1);
                assert(base.as_nat() + q - first < entries@[q as int].1.as_nat());
            }
        }
        let run = IndexRun { base, start, len: q - first };
        proof { append_run(runs@, rs as int, vs as int, entries@, first as int, q as int, saved_len.as_nat(), run); }
        runs.push(run);
    }
    ColdFrameHdr { saved_len, runs_start: rs, runs_len: runs.len() - rs }
}

/// Some run in `[lo, hi)` holds value-pool offset `o`.
pub(crate) open spec fn offset_covered<I: IndexLike>(
    runs: Seq<IndexRun<I>>, lo: int, hi: int, o: int,
) -> bool {
    exists|k: int| lo <= k < hi && (#[trigger] runs[k]).start <= o
        && o < runs[k].start + runs[k].len
}

/// The appended runs tile `[runs[r].start, vs + done)`: every offset from run
/// `r` on is inside some run at or after `r`.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_run_prefix_covers<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, rs: int, vs: int, entries: Seq<(T, I)>, done: int, limit: nat, r: int,
)
    requires run_prefix(runs, rs, vs, entries, done, limit), rs <= r < runs.len(),
    ensures forall|o: int| runs[r].start <= o < vs + done ==>
        #[trigger] offset_covered(runs, r, runs.len() as int, o),
    decreases runs.len() - r,
{
    lemma_run_prefix_layout(runs, rs, vs, entries, done, limit);
    lemma_run_prefix_run_at(runs, rs, vs, entries, done, limit, r);
    if r + 1 < runs.len() {
        lemma_run_prefix_covers(runs, rs, vs, entries, done, limit, r + 1);
    }
    assert forall|o: int| runs[r].start <= o < vs + done implies
        #[trigger] offset_covered(runs, r, runs.len() as int, o) by {
        if o < runs[r].start + runs[r].len {
            assert(runs[r].start <= o && o < runs[r].start + runs[r].len);
        } else {
            assert(r + 1 < runs.len());
            assert(runs[r + 1].start <= o);
            assert(offset_covered(runs, r + 1, runs.len() as int, o));
            let k = choose|k: int| r + 1 <= k < runs.len() && (#[trigger] runs[k]).start <= o
                && o < runs[k].start + runs[k].len;
            assert(r <= k < runs.len() && runs[k].start <= o && o < runs[k].start + runs[k].len);
        }
    }
}

/// Input entry `p` is reached by a run covering its index, at the value-pool
/// offset `vs + p`.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_run_prefix_entry<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, rs: int, vs: int, entries: Seq<(T, I)>, done: int, limit: nat, p: int,
)
    requires run_prefix(runs, rs, vs, entries, done, limit), 0 <= p < done,
    ensures exists|k: int| rs <= k < runs.len()
        && (#[trigger] runs[k]).base.as_nat() <= entries[p].1.as_nat()
        && entries[p].1.as_nat() < runs[k].base.as_nat() + runs[k].len
        && runs[k].start + (entries[p].1.as_nat() - runs[k].base.as_nat()) == vs + p,
{
    lemma_run_prefix_layout(runs, rs, vs, entries, done, limit);
    lemma_run_prefix_covers(runs, rs, vs, entries, done, limit, rs);
    let o = vs + p;
    assert(offset_covered(runs, rs, runs.len() as int, o));
    let k = choose|k: int| rs <= k < runs.len() && (#[trigger] runs[k]).start <= o
        && o < runs[k].start + runs[k].len;
    lemma_run_prefix_run_at(runs, rs, vs, entries, done, limit, k);
    let q = o - runs[k].start;
    assert(entries[runs[k].start - vs + q].1.as_nat() == runs[k].base.as_nat() + q);
    assert(runs[k].start - vs + q == p);
}

/// A run's cell `q` names the input entry at its offset, which is unique in a
/// strictly sorted input, so the run's value is that entry's value.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_run_prefix_cell<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, rs: int, vs: int, entries: Seq<(T, I)>, done: int, limit: nat,
    r: int, q: int,
)
    requires run_prefix(runs, rs, vs, entries, done, limit), rs <= r < runs.len(),
        0 <= q < runs[r].len,
    ensures 0 <= runs[r].start - vs + q < done,
        entries[runs[r].start - vs + q].1.as_nat() == runs[r].base.as_nat() + q,
{
    lemma_run_prefix_run_at(runs, rs, vs, entries, done, limit, r);
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn appends_maximal_runs_near_index_limit_without_touching_prefix() {
        let mut runs = vec![IndexRun {
            base: 2u64,
            start: 0,
            len: 2,
        }];
        let mut values = vec![70u32, 71];
        let entries = [
            (100, u64::MAX - 5),
            (101, u64::MAX - 4),
            (103, u64::MAX - 2),
        ];
        let frame = append_sorted(&mut runs, &mut values, &entries, u64::MAX);
        assert_eq!(
            (frame.runs_start, frame.runs_len, frame.saved_len),
            (1, 2, u64::MAX)
        );
        assert_eq!((runs[0].base, runs[0].start, runs[0].len), (2, 0, 2));
        assert_eq!(
            (runs[1].base, runs[1].start, runs[1].len),
            (u64::MAX - 5, 2, 2)
        );
        assert_eq!(
            (runs[2].base, runs[2].start, runs[2].len),
            (u64::MAX - 2, 4, 1)
        );
        assert_eq!(values, [70, 71, 100, 101, 103]);
        let empty = append_sorted(&mut runs, &mut values, &[], 0u64);
        assert_eq!(
            (empty.runs_start, empty.runs_len, empty.saved_len),
            (3, 0, 0)
        );
        assert_eq!(runs.len(), 3);
        assert_eq!(values, [70, 71, 100, 101, 103]);
    }

    #[test]
    fn run_payloads_use_copy_without_invoking_clone() {
        #[derive(Copy, Debug, PartialEq, Eq)]
        struct CopyOnly(u32);
        impl Clone for CopyOnly {
            fn clone(&self) -> Self {
                panic!("run construction must use Copy")
            }
        }
        let entries = [
            (CopyOnly(7), 1u32),
            (CopyOnly(8), 2u32),
            (CopyOnly(9), 4u32),
        ];
        let mut runs = Vec::new();
        let mut values = Vec::new();
        let frame = append_sorted(&mut runs, &mut values, &entries, 5u32);
        assert_eq!(frame.runs_len, 2);
        assert_eq!(values, [CopyOnly(7), CopyOnly(8), CopyOnly(9)]);
    }
}
