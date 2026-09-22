// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! First-capture deduplication of chronological Trail frames into unique Hot payloads.
use vstd::prelude::*;

verus! {
use crate::index_like::IndexLike;

/// `out[lo..]` is exactly the earliest capture of every index in
/// `pool[start..q)`: each retained entry is a physical first hitter, and every
/// physical first hitter is retained.
pub(crate) open spec fn dedupe_prefix<T, I: IndexLike>(
    pool: Seq<(T, I)>, start: int, q: int, out: Seq<(T, I)>, lo: int,
) -> bool {
    &&& 0 <= lo <= out.len()
    &&& forall|k: int| #![trigger out[k]] lo <= k < out.len() ==> exists|p: int| #![trigger pool[p]] start <= p < q
        && out[k] == pool[p]
        && crate::vec::first_hitter::<T, I>(pool, start, p, pool[p].1.as_nat())
    &&& forall|p: int| start <= p < q
        && crate::vec::first_hitter::<T, I>(pool, start, p, (#[trigger] pool[p]).1.as_nat())
        ==> exists|k: int| lo <= k < out.len() && (#[trigger] out[k]) == pool[p]
}

/// A unique retained range with the dedupe contract has the source range's
/// earliest-capture map, including absence.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_dedupe_saved_value<T, I: IndexLike>(
    pool: Seq<(T, I)>, start: int, end: int, out: Seq<(T, I)>, lo: int, j: nat,
)
    requires 0 <= start <= end <= pool.len(), 0 <= lo <= out.len(),
        crate::vec::stratum_unique::<T, I>(out, lo, out.len() as int),
        dedupe_prefix::<T, I>(pool, start, end, out, lo),
    ensures crate::vec::range_saved_value::<T, I>(out, lo, out.len() as int, j)
        == crate::vec::range_saved_value::<T, I>(pool, start, end, j),
{
    let hi = out.len() as int;
    if crate::vec::captured_in_range::<T, I>(pool, start, end, j) {
        crate::vec::lemma_lowest_hitter::<T, I>(pool, start, end, j);
        let p = choose|p: int| start <= p < end && (#[trigger] pool[p]).1.as_nat() == j
            && crate::vec::first_hitter::<T, I>(pool, start, p, j);
        let k = choose|k: int| lo <= k < out.len() && (#[trigger] out[k]) == pool[p];
        assert(crate::vec::captured_in_range::<T, I>(out, lo, hi, j));
        crate::vec::lemma_lowest_hitter::<T, I>(out, lo, hi, j);
        let k2 = choose|k2: int| lo <= k2 < hi && (#[trigger] out[k2]).1.as_nat() == j
            && crate::vec::first_hitter::<T, I>(out, lo, k2, j);
        assert(k2 == k);
        let p2 = choose|p2: int| start <= p2 < end && (#[trigger] pool[p2]).1.as_nat() == j
            && crate::vec::first_hitter::<T, I>(pool, start, p2, j);
        assert(p2 == p);
        assert(crate::vec::range_saved_value::<T, I>(out, lo, hi, j) == Some(out[k2].0));
        assert(crate::vec::range_saved_value::<T, I>(pool, start, end, j) == Some(pool[p2].0));
    } else {
        assert(!crate::vec::captured_in_range::<T, I>(out, lo, hi, j)) by {
            if crate::vec::captured_in_range::<T, I>(out, lo, hi, j) {
                let k = choose|k: int| lo <= k < hi && 0 <= k < out.len()
                    && (#[trigger] out[k]).1.as_nat() == j;
                let p = choose|p: int| #![trigger pool[p]] start <= p < end && out[k] == pool[p]
                    && crate::vec::first_hitter::<T, I>(pool, start, p, pool[p].1.as_nat());
                assert(pool[p].1.as_nat() == j);
            }
        }
    }
}

/// The membership set holds exactly the indices of `pool[start..q)`.
pub(crate) open spec fn seen_prefix<T, I: IndexLike>(
    pool: Seq<(T, I)>, start: int, q: int, seen: Set<I>,
) -> bool {
    forall|i: I| #[trigger] seen.contains(i)
        <==> exists|p: int| start <= p < q && (#[trigger] pool[p]).1 == i
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_seen_step<T, I: IndexLike>(pool: Seq<(T, I)>, start: int, q: int, seen: Set<I>)
    requires 0 <= start <= q < pool.len(), seen_prefix::<T, I>(pool, start, q, seen),
    ensures seen_prefix::<T, I>(pool, start, q + 1, seen.insert(pool[q].1)),
{
    let next = seen.insert(pool[q].1);
    assert forall|i: I| #[trigger] next.contains(i)
        <==> exists|p: int| start <= p < q + 1 && (#[trigger] pool[p]).1 == i by {
        if next.contains(i) {
            if i == pool[q].1 { assert(pool[q].1 == i); }
        } else {
            assert(!seen.contains(i));
        }
    }
}

/// An unseen index at `q` has no earlier hit: `q` is its first hitter.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_dedupe_fresh<T, I: IndexLike>(pool: Seq<(T, I)>, start: int, q: int, seen: Set<I>)
    requires 0 <= start <= q < pool.len(), seen_prefix::<T, I>(pool, start, q, seen),
        !seen.contains(pool[q].1),
    ensures crate::vec::first_hitter::<T, I>(pool, start, q, pool[q].1.as_nat()),
{
    assert forall|p: int| start <= p < q implies
        (#[trigger] pool[p]).1.as_nat() != pool[q].1.as_nat() by {
        if pool[p].1.as_nat() == pool[q].1.as_nat() {
            I::lemma_as_nat_injective(pool[p].1, pool[q].1);
            assert(seen.contains(pool[q].1));
        }
    }
}

/// A seen index at `q` was hit earlier: `q` is not its first hitter.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_dedupe_dup<T, I: IndexLike>(pool: Seq<(T, I)>, start: int, q: int, seen: Set<I>)
    requires 0 <= start <= q < pool.len(), seen_prefix::<T, I>(pool, start, q, seen),
        seen.contains(pool[q].1),
    ensures !crate::vec::first_hitter::<T, I>(pool, start, q, pool[q].1.as_nat()),
{
    let p = choose|p: int| start <= p < q && (#[trigger] pool[p]).1 == pool[q].1;
    assert(pool[p].1.as_nat() == pool[q].1.as_nat());
}

/// Retaining a first hitter preserves uniqueness and the dedupe contract.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_dedupe_push<T, I: IndexLike>(
    pool: Seq<(T, I)>, start: int, q: int, pre: Seq<(T, I)>, lo: int,
)
    requires 0 <= start <= q < pool.len(), 0 <= lo <= pre.len(),
        crate::vec::stratum_unique::<T, I>(pre, lo, pre.len() as int),
        dedupe_prefix::<T, I>(pool, start, q, pre, lo),
        crate::vec::first_hitter::<T, I>(pool, start, q, pool[q].1.as_nat()),
    ensures
        crate::vec::stratum_unique::<T, I>(pre.push(pool[q]), lo, pre.len() as int + 1),
        dedupe_prefix::<T, I>(pool, start, q + 1, pre.push(pool[q]), lo),
{
    let out = pre.push(pool[q]);
    let n = pre.len() as int;
    assert forall|k: int| lo <= k < n implies
        (#[trigger] out[k]).1.as_nat() != pool[q].1.as_nat() by {
        let p = choose|p: int| #![trigger pool[p]] start <= p < q && pre[k] == pool[p]
            && crate::vec::first_hitter::<T, I>(pool, start, p, pool[p].1.as_nat());
        assert(pool[p].1.as_nat() != pool[q].1.as_nat());
    }
    assert forall|a: int, b: int| lo <= a < n + 1 && lo <= b < n + 1 && a != b
        implies (#[trigger] out[a]).1.as_nat() != (#[trigger] out[b]).1.as_nat() by {
        if a < n && b < n {
            assert(out[a] == pre[a]);
            assert(out[b] == pre[b]);
        }
    }
    assert forall|k: int| #![trigger out[k]] lo <= k < n + 1 implies exists|p: int| #![trigger pool[p]] start <= p < q + 1
        && out[k] == pool[p]
        && crate::vec::first_hitter::<T, I>(pool, start, p, pool[p].1.as_nat()) by {
        if k < n {
            let p = choose|p: int| #![trigger pool[p]] start <= p < q && pre[k] == pool[p]
                && crate::vec::first_hitter::<T, I>(pool, start, p, pool[p].1.as_nat());
            assert(out[k] == pool[p]);
        } else {
            assert(out[k] == pool[q]);
        }
    }
    assert forall|p: int| start <= p < q + 1
        && crate::vec::first_hitter::<T, I>(pool, start, p, (#[trigger] pool[p]).1.as_nat())
        implies exists|k: int| lo <= k < n + 1 && (#[trigger] out[k]) == pool[p] by {
        if p < q {
            let k = choose|k: int| lo <= k < n && (#[trigger] pre[k]) == pool[p];
            assert(out[k] == pool[p]);
        } else {
            assert(out[n] == pool[p]);
        }
    }
}

/// Skipping a duplicate preserves the dedupe contract.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_dedupe_skip<T, I: IndexLike>(
    pool: Seq<(T, I)>, start: int, q: int, out: Seq<(T, I)>, lo: int,
)
    requires 0 <= start <= q < pool.len(), dedupe_prefix::<T, I>(pool, start, q, out, lo),
        !crate::vec::first_hitter::<T, I>(pool, start, q, pool[q].1.as_nat()),
    ensures dedupe_prefix::<T, I>(pool, start, q + 1, out, lo),
{
    assert forall|k: int| #![trigger out[k]] lo <= k < out.len() implies exists|p: int| #![trigger pool[p]] start <= p < q + 1
        && out[k] == pool[p]
        && crate::vec::first_hitter::<T, I>(pool, start, p, pool[p].1.as_nat()) by {
        let p = choose|p: int| #![trigger pool[p]] start <= p < q && out[k] == pool[p]
            && crate::vec::first_hitter::<T, I>(pool, start, p, pool[p].1.as_nat());
    }
    assert forall|p: int| start <= p < q + 1
        && crate::vec::first_hitter::<T, I>(pool, start, p, (#[trigger] pool[p]).1.as_nat())
        implies exists|k: int| lo <= k < out.len() && (#[trigger] out[k]) == pool[p] by {
        assert(p < q);
    }
}

/// Append the earliest capture of every index in `pool[start..end)` to `out`,
/// in chronological order of first capture. One left-to-right pass with a
/// membership test per entry; `seen` is cleared first and may be reused.
#[verifier::spinoff_prover]
pub(crate) fn dedupe_trail_range<T: Copy, I: IndexLike>(
    pool: &std::vec::Vec<(T, I)>, start: usize, end: usize,
    seen: &mut std::collections::HashSet<I, crate::hasher_spec::IndexHasher>,
    out: &mut std::vec::Vec<(T, I)>,
)
    requires start <= end <= pool@.len(),
        vstd::std_specs::hash::obeys_key_model::<I>(),
    ensures
        old(out)@.len() <= final(out)@.len() <= old(out)@.len() + (end - start),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        crate::vec::stratum_unique::<T, I>(final(out)@, old(out)@.len() as int, final(out)@.len() as int),
        dedupe_prefix::<T, I>(pool@, start as int, end as int, final(out)@, old(out)@.len() as int),
        forall|j: nat| #[trigger] crate::vec::range_saved_value::<T, I>(final(out)@,
            old(out)@.len() as int, final(out)@.len() as int, j)
            == crate::vec::range_saved_value::<T, I>(pool@, start as int, end as int, j),
{
    hide(dedupe_prefix);
    hide(seen_prefix);
    hide(crate::vec::stratum_unique);
    hide(crate::vec::first_hitter);
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use crate::hasher_spec::axiom_index_hasher_builds_valid_hashers;
    let ghost base = out@;
    let ghost lo = base.len() as int;
    out.reserve(end - start);
    proof {
        assert(dedupe_prefix::<T, I>(pool@, start as int, start as int, out@, lo)) by {
            reveal(dedupe_prefix);
        }
        assert(crate::vec::stratum_unique::<T, I>(out@, lo, out@.len() as int)) by {
            reveal(crate::vec::stratum_unique);
        }
    }
    // Fast path: a strictly ascending frame (the sweep/append write pattern)
    // holds no index twice, so every entry is its own first hitter and the
    // frame copies straight through — no set, no hashing. The scan is one
    // compare per entry and stops at the first descent.
    let mut asc = true;
    let mut r = start;
    while asc && end - r > 1
        invariant
            start <= r <= end <= pool@.len(),
            r < end || start == end,
            asc ==> forall|a: int, b: int| start <= a < b <= r
                ==> (#[trigger] pool@[a]).1.as_nat() < (#[trigger] pool@[b]).1.as_nat(),
        decreases end - r + (if asc { 1int } else { 0int }),
    {
        if pool[r].1.as_usize() < pool[r + 1].1.as_usize() {
            r += 1;
        } else {
            asc = false;
        }
    }
    if asc {
        // `[start, end)` is strictly ascending: the scan reached the last
        // entry (`end - r <= 1`), or the frame has at most one entry.
        proof {
            assert forall|a: int, b: int| start <= a < b < end
                implies (#[trigger] pool@[a]).1.as_nat() < (#[trigger] pool@[b]).1.as_nat() by {
                assert(b <= r);
            }
        }
        let mut q = start;
        while q < end
            invariant
                start <= q <= end <= pool@.len(),
                lo == base.len(), lo <= out@.len(), out@.len() <= lo + (q - start),
                out@.subrange(0, lo) == base,
                forall|a: int, b: int| start <= a < b < end
                    ==> (#[trigger] pool@[a]).1.as_nat() < (#[trigger] pool@[b]).1.as_nat(),
                crate::vec::stratum_unique::<T, I>(out@, lo, out@.len() as int),
                dedupe_prefix::<T, I>(pool@, start as int, q as int, out@, lo),
            decreases end - q,
        {
            let entry = pool[q];
            let ghost pre_out = out@;
            proof {
                // Ascending ⟹ no earlier entry shares this index: q is a first hitter.
                assert(crate::vec::first_hitter::<T, I>(
                    pool@, start as int, q as int, pool@[q as int].1.as_nat())) by {
                    reveal(crate::vec::first_hitter);
                }
            }
            out.push(entry);
            proof {
                lemma_dedupe_push::<T, I>(pool@, start as int, q as int, pre_out, lo);
                assert(out@.subrange(0, lo) =~= base);
            }
            q += 1;
        }
    } else {
        seen.clear();
        // Size the set for the frame up front: it otherwise grows from empty
        // through a chain of rehashes on every pass.
        seen.reserve(end - start);
        proof {
            assert(seen_prefix::<T, I>(pool@, start as int, start as int, seen@)) by {
                reveal(seen_prefix);
            }
        }
        let mut q = start;
        while q < end
            invariant
                start <= q <= end <= pool@.len(),
                vstd::std_specs::hash::obeys_key_model::<I>(),
                vstd::std_specs::hash::builds_valid_hashers::<crate::hasher_spec::IndexHasher>(),
                lo == base.len(), lo <= out@.len(), out@.len() <= lo + (q - start),
                out@.subrange(0, lo) == base,
                seen_prefix::<T, I>(pool@, start as int, q as int, seen@),
                crate::vec::stratum_unique::<T, I>(out@, lo, out@.len() as int),
                dedupe_prefix::<T, I>(pool@, start as int, q as int, out@, lo),
            decreases end - q,
        {
            let entry = pool[q];
            let index = entry.1;
            let ghost pre_out = out@;
            let ghost pre_seen = seen@;
            let fresh = seen.insert(index);
            proof { lemma_seen_step::<T, I>(pool@, start as int, q as int, pre_seen); }
            if fresh {
                proof { lemma_dedupe_fresh::<T, I>(pool@, start as int, q as int, pre_seen); }
                out.push(entry);
                proof {
                    lemma_dedupe_push::<T, I>(pool@, start as int, q as int, pre_out, lo);
                    assert(out@.subrange(0, lo) =~= base);
                }
            } else {
                proof {
                    lemma_dedupe_dup::<T, I>(pool@, start as int, q as int, pre_seen);
                    lemma_dedupe_skip::<T, I>(pool@, start as int, q as int, out@, lo);
                }
            }
            q += 1;
        }
    }
    proof {
        assert forall|j: nat| #[trigger] crate::vec::range_saved_value::<T, I>(out@, lo, out@.len() as int, j)
            == crate::vec::range_saved_value::<T, I>(pool@, start as int, end as int, j) by {
            lemma_dedupe_saved_value::<T, I>(pool@, start as int, end as int, out@, lo, j);
        }
    }
}
} // verus!
