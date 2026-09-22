// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Trusted contract for std's in-place unstable slice sort, keyed by index.
use vstd::prelude::*;

verus! {
use crate::index_like::IndexLike;

/// TRUSTED (trust ledger group B, contract-carrying): std documents that
/// `<[T]>::sort_unstable_by_key` reorders the slice in place into
/// non-decreasing key order and touches nothing outside it. The key is the
/// index projection, which `IndexLike::as_usize` orders exactly as `as_nat`.
#[verifier::external_body]
pub(crate) fn sort_pairs_by_index<T: Copy, I: IndexLike>(
    v: &mut std::vec::Vec<(T, I)>, start: usize, end: usize,
)
    requires start <= end <= old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|q: int| 0 <= q < old(v)@.len() && !(start <= q < end) ==>
            #[trigger] final(v)@[q] == old(v)@[q],
        final(v)@.subrange(start as int, end as int).to_multiset()
            == old(v)@.subrange(start as int, end as int).to_multiset(),
        forall|a: int, b: int| start <= a < b < end ==>
            (#[trigger] final(v)@[a]).1.as_nat() <= (#[trigger] final(v)@[b]).1.as_nat(),
{
    v[start..end].sort_unstable_by_key(|(_, index)| index.as_usize());
}

} // verus!
