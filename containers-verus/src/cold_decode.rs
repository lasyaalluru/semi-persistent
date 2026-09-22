// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Checked Cold survivor decoding into the store-selected writable pair pool.

use vstd::prelude::*;

verus! {
use crate::frame::IndexRun;
use crate::index_like::IndexLike;

/// Append one run directly to its destination. Values are copied, not cloned;
/// index conversion is proved successful for every saved-domain cell.
#[verifier::spinoff_prover]
#[inline(always)]
pub(crate) fn append_run<T: Copy, I: IndexLike>(
    out: &mut std::vec::Vec<(T, I)>, values: &std::vec::Vec<T>,
    run: IndexRun<I>, saved_len: I,
)
    requires
        run.start + run.len <= values@.len(),
        run.base.as_nat() + run.len <= saved_len.as_nat(),
        old(out)@.len() + run.len <= usize::MAX,
    ensures
        final(out)@.len() == old(out)@.len() + run.len,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        forall|q: int| 0 <= q < run.len ==> {
            &&& (#[trigger] final(out)@[old(out)@.len() + q]).0 == values@[run.start + q]
            &&& final(out)@[old(out)@.len() + q].1.as_nat() == run.base.as_nat() + q
        },
{
    let ghost before = out@;
    proof { saved_len.lemma_as_nat_bounded(); I::lemma_max_nat_fits_usize(); }
    let base = run.base.as_usize();
    let values_len = values.len();
    let mut q: usize = 0;
    while q < run.len
        invariant
            q <= run.len,
            run.start + run.len <= values@.len(),
            values@.len() == values_len,
            run.base.as_nat() == base,
            run.base.as_nat() + run.len <= saved_len.as_nat(),
            saved_len.as_nat() <= usize::MAX, saved_len.as_nat() < I::max_nat(),
            before.len() + run.len <= usize::MAX,
            out@.len() == before.len() + q,
            out@.subrange(0, before.len() as int) == before,
            forall|p: int| 0 <= p < q ==> {
                &&& (#[trigger] out@[before.len() + p]).0 == values@[run.start + p]
                &&& out@[before.len() + p].1.as_nat() == run.base.as_nat() + p
            },
        decreases run.len - q,
    {
        let index = match I::try_from_usize(base + q) {
            Some(index) => index,
            None => { assert(false); return; },
        };
        let ghost prior = out@;
        out.push((values[run.start + q], index));
        q += 1;
        proof {
            assert(out@.subrange(0, before.len() as int) =~= before);
            assert forall|p: int| 0 <= p < q implies {
                &&& (#[trigger] out@[before.len() + p]).0 == values@[run.start + p]
                &&& out@[before.len() + p].1.as_nat() == run.base.as_nat() + p
            } by {
                if p + 1 < q { assert(out@[before.len() + p] == prior[before.len() + p]); }
            }
        }
    }
}

pub(crate) open spec fn layout<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, values: Seq<T>, lo: int, hi: int, limit: nat,
) -> bool {
    &&& 0 <= lo <= hi <= runs.len()
    &&& forall|r: int| lo <= r < hi ==> {
        &&& 0 < (#[trigger] runs[r]).len
        &&& runs[r].start + runs[r].len <= values.len()
        &&& runs[r].base.as_nat() + runs[r].len <= limit
        &&& (r + 1 < hi ==> {
            &&& runs[r].start + runs[r].len == runs[r + 1].start
            &&& runs[r].base.as_nat() + runs[r].len <= runs[r + 1].base.as_nat()
        })
    }
}

pub(crate) open spec fn covers_position<I: IndexLike>(
    runs: Seq<IndexRun<I>>, lo: int, hi: int, vs: int, p: int,
) -> bool {
    exists|r: int| lo <= r < hi && (#[trigger] runs[r]).start - vs <= p
        < runs[r].start + runs[r].len - vs
}

pub(crate) open spec fn decoded_cell<T, I: IndexLike>(
    run: IndexRun<I>, values: Seq<T>, vs: int, out: Seq<(T, I)>, q: int,
) -> bool {
    &&& 0 <= run.start - vs + q < out.len()
    &&& out[run.start - vs + q].0 == values[run.start + q]
    &&& out[run.start - vs + q].1.as_nat() == run.base.as_nat() + q
}

pub(crate) open spec fn decoded_run<T, I: IndexLike>(
    run: IndexRun<I>, values: Seq<T>, vs: int, out: Seq<(T, I)>,
) -> bool {
    forall|q: int| 0 <= q < run.len ==> #[trigger] decoded_cell(run, values, vs, out, q)
}

/// Exact positional relation to the source payload, plus coverage of every
/// destination cell. Together these exclude both dropped and extra captures.
pub(crate) open spec fn decoded<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, values: Seq<T>, lo: int, hi: int, vs: int, out: Seq<(T, I)>,
) -> bool {
    &&& forall|r: int| lo <= r < hi ==> #[trigger] decoded_run(runs[r], values, vs, out)
    &&& forall|p: int| 0 <= p < out.len() ==>
        #[trigger] covers_position(runs, lo, hi, vs, p)
}

#[verifier::spinoff_prover]
proof fn run_cell<T, I: IndexLike>(run: IndexRun<I>, values: Seq<T>, vs: int, out: Seq<(T, I)>, q: int)
    requires decoded_run(run, values, vs, out), 0 <= q < run.len,
    ensures 0 <= run.start - vs + q < out.len(),
        out[run.start - vs + q].0 == values[run.start + q],
        out[run.start - vs + q].1.as_nat() == run.base.as_nat() + q,
{ assert(decoded_cell(run, values, vs, out, q)); }

#[verifier::spinoff_prover]
pub(crate) proof fn decoded_entry<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, values: Seq<T>, lo: int, hi: int, vs: int,
    out: Seq<(T, I)>, limit: nat, p: int,
)
    requires layout(runs, values, lo, hi, limit), decoded(runs, values, lo, hi, vs, out),
        0 <= p < out.len(),
    ensures out[p].1.as_nat() < limit,
        crate::vec::cold_range_saved_value(runs, values, lo, hi, out[p].1.as_nat()) == Some(out[p].0),
{
    assert(covers_position(runs, lo, hi, vs, p));
    let r = choose|r: int| lo <= r < hi && (#[trigger] runs[r]).start - vs <= p
        < runs[r].start + runs[r].len - vs;
    assert(decoded_run(runs[r], values, vs, out));
    let q = p - (runs[r].start - vs);
    run_cell(runs[r], values, vs, out, q);
    let j = out[p].1.as_nat();
    assert(crate::vec::cold_run_covers(runs[r], j));
    let s = choose|s: int| lo <= s < hi && crate::vec::cold_run_covers(#[trigger] runs[s], j);
    if r < s { crate::vec::lemma_cold_run_order(runs, lo, hi, r, s); }
    else if s < r { crate::vec::lemma_cold_run_order(runs, lo, hi, s, r); }
    assert(r == s);
}

/// Exact map equality, with no live-buffer or snapshot reconstruction premise.
#[verifier::spinoff_prover]
pub(crate) proof fn decoded_lookup<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, values: Seq<T>, lo: int, hi: int, vs: int,
    out: Seq<(T, I)>, limit: nat, j: nat,
)
    requires layout(runs, values, lo, hi, limit), decoded(runs, values, lo, hi, vs, out),
    ensures crate::vec::range_saved_value(out, 0, out.len() as int, j)
        == crate::vec::cold_range_saved_value(runs, values, lo, hi, j),
{
    if exists|r: int| lo <= r < hi && crate::vec::cold_run_covers(#[trigger] runs[r], j) {
        let r = choose|r: int| lo <= r < hi && crate::vec::cold_run_covers(#[trigger] runs[r], j);
        assert(decoded_run(runs[r], values, vs, out));
        let q = (j - runs[r].base.as_nat()) as int;
        let p = runs[r].start - vs + q;
        run_cell(runs[r], values, vs, out, q);
        assert(out[p].1.as_nat() == j);
        assert(0 <= p < out.len());
        assert(crate::vec::captured_in_range(out, 0, out.len() as int, j));
    }
    if crate::vec::captured_in_range(out, 0, out.len() as int, j) {
        crate::vec::lemma_lowest_hitter(out, 0, out.len() as int, j);
        let p = choose|p: int| 0 <= p < out.len() && (#[trigger] out[p]).1.as_nat() == j
            && crate::vec::first_hitter(out, 0, p, j);
        decoded_entry(runs, values, lo, hi, vs, out, limit, p);
    }
}

#[verifier::spinoff_prover]
proof fn payload_order<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, values: Seq<T>, lo: int, hi: int, limit: nat, a: int, b: int,
)
    requires layout(runs, values, lo, hi, limit), lo <= a < b < hi,
    ensures runs[a].start + runs[a].len <= runs[b].start,
    decreases b - a,
{
    if a + 1 < b { payload_order(runs, values, lo, hi, limit, a + 1, b); }
}

#[verifier::spinoff_prover]
pub(crate) proof fn decoded_sorted<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, values: Seq<T>, lo: int, hi: int, vs: int,
    out: Seq<(T, I)>, limit: nat, a: int, b: int,
)
    requires layout(runs, values, lo, hi, limit), decoded(runs, values, lo, hi, vs, out),
        0 <= a < b < out.len(),
    ensures out[a].1.as_nat() < out[b].1.as_nat(),
{
    hide(decoded_run);
    assert(covers_position(runs, lo, hi, vs, a));
    assert(covers_position(runs, lo, hi, vs, b));
    let r = choose|r: int| lo <= r < hi && (#[trigger] runs[r]).start - vs <= a
        < runs[r].start + runs[r].len - vs;
    let s = choose|r: int| lo <= r < hi && (#[trigger] runs[r]).start - vs <= b
        < runs[r].start + runs[r].len - vs;
    assert(decoded_run(runs[r], values, vs, out));
    assert(decoded_run(runs[s], values, vs, out));
    run_cell(runs[r], values, vs, out, a - (runs[r].start - vs));
    run_cell(runs[s], values, vs, out, b - (runs[s].start - vs));
    if s < r { payload_order(runs, values, lo, hi, limit, s, r); }
    assert(r <= s);
    assert(out[a].1.as_nat() == runs[r].base.as_nat() + a - (runs[r].start - vs));
    assert(out[b].1.as_nat() == runs[s].base.as_nat() + b - (runs[s].start - vs));
    if r < s { crate::vec::lemma_cold_run_order(runs, lo, hi, r, s); }
}

#[verifier::spinoff_prover]
proof fn extend_decoded<T, I: IndexLike>(
    runs: Seq<IndexRun<I>>, values: Seq<T>, lo: int, r: int, vs: int,
    before: Seq<(T, I)>, out: Seq<(T, I)>,
)
    requires 0 <= lo <= r < runs.len(),
        decoded(runs, values, lo, r, vs, before),
        before.len() == runs[r].start - vs,
        out.len() == before.len() + runs[r].len,
        out.subrange(0, before.len() as int) == before,
        forall|q: int| 0 <= q < runs[r].len ==> {
            &&& (#[trigger] out[before.len() + q]).0 == values[runs[r].start + q]
            &&& out[before.len() + q].1.as_nat() == runs[r].base.as_nat() + q
        },
    ensures decoded(runs, values, lo, r + 1, vs, out),
{
    let run = runs[r];
    assert forall|s: int| lo <= s < r + 1 implies
        #[trigger] decoded_run(runs[s], values, vs, out) by {
        reveal(decoded_run);
        if s < r { assert(decoded_run(runs[s], values, vs, before)); }
        assert forall|q: int| 0 <= q < runs[s].len implies
            #[trigger] decoded_cell(runs[s], values, vs, out, q) by {
            if s < r {
                let p = runs[s].start - vs + q;
                run_cell(runs[s], values, vs, before, q);
                assert(before[p].1.as_nat() == runs[s].base.as_nat() + q);
                assert(out[p] == before[p]);
            }
        }
    }
    assert forall|p: int| 0 <= p < out.len() implies
        #[trigger] covers_position(runs, lo, r + 1, vs, p) by {
        if p < before.len() {
            assert(covers_position(runs, lo, r, vs, p));
            let s = choose|s: int| lo <= s < r && (#[trigger] runs[s]).start - vs <= p
                < runs[s].start + runs[s].len - vs;
        } else { assert(run.start - vs <= p < run.start + run.len - vs); }
    }
}

#[verifier::spinoff_prover]
#[inline(always)]
pub(crate) fn decode_into<T: Copy, I: IndexLike>(
    out: &mut std::vec::Vec<(T, I)>, runs: &std::vec::Vec<IndexRun<I>>,
    values: &std::vec::Vec<T>, lo: usize, hi: usize, saved_len: I,
)
    requires old(out)@.len() == 0, layout(runs@, values@, lo as int, hi as int, saved_len.as_nat()),
    ensures decoded(runs@, values@, lo as int, hi as int,
            if lo < hi { runs@[lo as int].start as int } else { 0 }, final(out)@),
        final(out)@.len() == if lo < hi {
            runs@[hi - 1].start + runs@[hi - 1].len - runs@[lo as int].start
        } else { 0int },
        forall|j: nat| #[trigger] crate::vec::range_saved_value(final(out)@, 0, final(out)@.len() as int, j)
            == crate::vec::cold_range_saved_value(runs@, values@, lo as int, hi as int, j),
        forall|a: int, b: int| 0 <= a < b < final(out)@.len() ==>
            (#[trigger] final(out)@[a]).1.as_nat() < (#[trigger] final(out)@[b]).1.as_nat(),
        forall|p: int| 0 <= p < final(out)@.len() ==>
            (#[trigger] final(out)@[p]).1.as_nat() < saved_len.as_nat(),
{
    hide(decoded);
    let ghost vs = if lo < hi { runs@[lo as int].start as int } else { 0int };
    let values_len = values.len();
    proof { assert(decoded(runs@, values@, lo as int, lo as int, vs as int, out@)) by { reveal(decoded); } }
    let mut r = lo;
    while r < hi
        invariant
            lo <= r <= hi,
            values@.len() == values_len,
            layout(runs@, values@, lo as int, hi as int, saved_len.as_nat()),
            vs == if lo < hi { runs@[lo as int].start as int } else { 0 },
            decoded(runs@, values@, lo as int, r as int, vs as int, out@),
            out@.len() == if lo < r { runs@[r - 1].start + runs@[r - 1].len - vs } else { 0int },
            r < hi ==> out@.len() == runs@[r as int].start - vs,
        decreases hi - r,
    {
        let run = runs[r];
        let ghost before = out@;
        append_run(out, values, run, saved_len);
        proof { extend_decoded(runs@, values@, lo as int, r as int, vs as int, before, out@); }
        r += 1;
    }
    proof {
        assert forall|j: nat| #[trigger] crate::vec::range_saved_value(out@, 0, out@.len() as int, j)
            == crate::vec::cold_range_saved_value(runs@, values@, lo as int, hi as int, j) by {
            decoded_lookup(runs@, values@, lo as int, hi as int, vs as int, out@, saved_len.as_nat(), j);
        }
        assert forall|a: int, b: int| 0 <= a < b < out@.len() implies
            (#[trigger] out@[a]).1.as_nat() < (#[trigger] out@[b]).1.as_nat() by {
            decoded_sorted(runs@, values@, lo as int, hi as int, vs as int, out@, saved_len.as_nat(), a, b);
        }
        assert forall|p: int| 0 <= p < out@.len() implies
            (#[trigger] out@[p]).1.as_nat() < saved_len.as_nat() by {
            decoded_entry(runs@, values@, lo as int, hi as int, vs as int, out@, saved_len.as_nat(), p);
        }
    }
}

} // verus!
