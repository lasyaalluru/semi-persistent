// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Local representation views and conditional transform/pool contracts.
//! These are spec values extracted from physical slices, not stored ghost fields.

use super::*;

verus! {

pub struct Pairs<T> { pub saved_len: nat, pub entries: Seq<(nat, T)> }
pub struct Run<T> { pub base: nat, pub values: Seq<T> }
pub struct Runs<T> { pub saved_len: nat, pub runs: Seq<Run<T>> }

pub open spec fn earliest<T>(entries: Seq<(nat, T)>) -> Map<nat, T>
    decreases entries.len(),
{
    if entries.len() == 0 { Map::empty() } else {
        capture_first(earliest(entries.drop_last()), entries.last().0, entries.last().1)
    }
}

pub open spec fn pairs_meaning<T>(p: Pairs<T>) -> Frame<T> {
    Frame { saved_len: p.saved_len, saved: earliest(p.entries) }
}

pub open spec fn trail_valid<T>(p: Pairs<T>) -> bool {
    forall|q: int| 0 <= q < p.entries.len() ==> (#[trigger] p.entries[q]).0 < p.saved_len
}

pub open spec fn hot_valid<T>(p: Pairs<T>) -> bool {
    trail_valid(p) && forall|a: int, b: int| 0 <= a < b < p.entries.len() ==>
        (#[trigger] p.entries[a]).0 != (#[trigger] p.entries[b]).0
}

pub open spec fn sorted_hot<T>(p: Pairs<T>) -> bool {
    hot_valid(p) && forall|a: int, b: int| 0 <= a < b < p.entries.len() ==>
        (#[trigger] p.entries[a]).0 < (#[trigger] p.entries[b]).0
}

pub open spec fn run_pairs<T>(run: Run<T>) -> Seq<(nat, T)> {
    Seq::new(run.values.len(), |q: int| ((run.base + q) as nat, run.values[q]))
}

pub open spec fn flatten<T>(runs: Seq<Run<T>>) -> Seq<(nat, T)>
    decreases runs.len(),
{
    if runs.len() == 0 { Seq::empty() } else {
        flatten(runs.drop_last()) + run_pairs(runs.last())
    }
}

pub open spec fn runs_meaning<T>(p: Runs<T>) -> Frame<T> {
    Frame { saved_len: p.saved_len, saved: earliest(flatten(p.runs)) }
}

pub open spec fn cold_valid<T>(p: Runs<T>) -> bool {
    &&& forall|r: int| 0 <= r < p.runs.len() ==>
        0 < (#[trigger] p.runs[r]).values.len()
            && p.runs[r].base + p.runs[r].values.len() <= p.saved_len
    &&& forall|r: int| 0 <= r && r + 1 < p.runs.len() ==>
        (#[trigger] p.runs[r]).base + p.runs[r].values.len() <= p.runs[r + 1].base
}

/// These relations are the local-transform obligations. Neither stable global
/// layout nor a second maintained history is required while building a frame.
pub open spec fn deduplicated<T>(source: Pairs<T>, out: Pairs<T>) -> bool {
    trail_valid(source) && hot_valid(out) && pairs_meaning(out) == pairs_meaning(source)
}

pub open spec fn sorted<T>(source: Pairs<T>, out: Pairs<T>) -> bool {
    hot_valid(source) && sorted_hot(out)
        && source.entries.to_multiset() == out.entries.to_multiset()
        && pairs_meaning(out) == pairs_meaning(source)
}

pub open spec fn encoded<T>(source: Pairs<T>, out: Runs<T>) -> bool {
    sorted_hot(source) && cold_valid(out) && runs_meaning(out) == pairs_meaning(source)
}

pub open spec fn reopened_hot<T>(source: Runs<T>, out: Pairs<T>) -> bool {
    cold_valid(source) && hot_valid(out) && pairs_meaning(out) == runs_meaning(source)
}

pub open spec fn reopened_trail<T>(source: Runs<T>, out: Pairs<T>) -> bool {
    cold_valid(source) && trail_valid(out) && pairs_meaning(out) == runs_meaning(source)
}

/// Exact pool append separates payload construction from header publication.
/// Old prefixes and source slices remain authoritative during this phase.
pub open spec fn appended<A>(old_pool: Seq<A>, out_pool: Seq<A>, piece: Seq<A>, start: nat) -> bool {
    start == old_pool.len() && out_pool == old_pool + piece
}

#[verifier::spinoff_prover]
pub proof fn append_prefix<A>(old_pool: Seq<A>, out_pool: Seq<A>, piece: Seq<A>, start: nat)
    requires appended(old_pool, out_pool, piece, start),
    ensures out_pool.len() == start + piece.len(),
        out_pool.subrange(0, start as int) == old_pool,
        out_pool.subrange(start as int, out_pool.len() as int) == piece,
{
    assert(out_pool.subrange(0, start as int) =~= old_pool);
    assert(out_pool.subrange(start as int, out_pool.len() as int) =~= piece);
}

pub struct PoolRun { pub base: nat, pub start: nat, pub len: nat }
pub struct Header { pub saved_len: nat, pub start: nat, pub len: nat }
pub struct ColdPool<T> {
    pub headers: Seq<Header>, pub runs: Seq<PoolRun>, pub values: Seq<T>,
}

pub open spec fn payload_len<T>(runs: Seq<Run<T>>) -> nat
    decreases runs.len(),
{
    if runs.len() == 0 { 0 } else { payload_len(runs.drop_last()) + runs.last().values.len() }
}

pub open spec fn pooled_frame<T>(pool: ColdPool<T>, f: int) -> Runs<T> {
    let header = pool.headers[f];
    Runs { saved_len: header.saved_len,
        runs: Seq::new(header.len, |r: int| {
            let run = pool.runs[header.start + r];
            Run { base: run.base, values: pool.values.subrange(run.start as int, (run.start + run.len) as int) }
        }) }
}

/// Appending a locally encoded frame is not yet completed migration: source
/// headers still exist. This interface specifies exact pool prefixes, offsets,
/// payload slices and the new header, including the zero-run empty-frame case.
pub open spec fn appended_cold<T>(pre: ColdPool<T>, out: ColdPool<T>, frame: Runs<T>) -> bool {
    &&& cold_valid(frame)
    &&& out.headers == pre.headers.push(Header {
        saved_len: frame.saved_len, start: pre.runs.len(), len: frame.runs.len() })
    &&& out.runs.len() == pre.runs.len() + frame.runs.len()
    &&& out.runs.subrange(0, pre.runs.len() as int) == pre.runs
    &&& out.values.len() == pre.values.len() + payload_len(frame.runs)
    &&& out.values.subrange(0, pre.values.len() as int) == pre.values
    &&& forall|r: int| 0 <= r < frame.runs.len() ==> {
        let run = #[trigger] out.runs[pre.runs.len() + r];
        &&& run.base == frame.runs[r].base
        &&& run.start == pre.values.len() + payload_len(frame.runs.subrange(0, r))
        &&& run.len == frame.runs[r].values.len()
        &&& run.start + run.len <= out.values.len()
        &&& out.values.subrange(run.start as int, (run.start + run.len) as int) == frame.runs[r].values
    }
}

#[verifier::spinoff_prover]
pub proof fn appended_cold_meaning<T>(pre: ColdPool<T>, out: ColdPool<T>, frame: Runs<T>)
    requires appended_cold(pre, out, frame),
    ensures pooled_frame(out, pre.headers.len() as int) == frame,
        runs_meaning(pooled_frame(out, pre.headers.len() as int)) == runs_meaning(frame),
        out.headers.subrange(0, pre.headers.len() as int) == pre.headers,
        out.runs.subrange(0, pre.runs.len() as int) == pre.runs,
        out.values.subrange(0, pre.values.len() as int) == pre.values,
{
    let decoded = pooled_frame(out, pre.headers.len() as int);
    assert forall|r: int| 0 <= r < frame.runs.len() implies
        #[trigger] decoded.runs[r] == frame.runs[r] by {
        let run = out.runs[pre.runs.len() + r];
        assert(run.base == frame.runs[r].base);
    }
    assert(decoded.runs =~= frame.runs);
    assert(out.headers.subrange(0, pre.headers.len() as int) =~= pre.headers);
}

#[verifier::spinoff_prover]
pub proof fn cold_transform_and_pool<T>(source: Pairs<T>, encoded_frame: Runs<T>, pre: ColdPool<T>, out: ColdPool<T>)
    requires encoded(source, encoded_frame), appended_cold(pre, out, encoded_frame),
    ensures runs_meaning(pooled_frame(out, pre.headers.len() as int)) == pairs_meaning(source),
        out.headers.len() == pre.headers.len() + 1,
        out.values.subrange(0, pre.values.len() as int) == pre.values,
{
    appended_cold_meaning(pre, out, encoded_frame);
}

/// Publishing an oldest source prefix in the adjacent older tier and retiring
/// that prefix preserves logical frame order. Empty frames count as elements.
#[verifier::spinoff_prover]
pub proof fn move_prefix_preserves<T>(older: Seq<Frame<T>>, source: Seq<Frame<T>>, moved: Seq<Frame<T>>, count: int)
    requires 0 <= count <= source.len(), moved == source.subrange(0, count),
    ensures older + source == (older + moved) + source.subrange(count, source.len() as int),
{
    assert(source =~= moved + source.subrange(count, source.len() as int));
    assert(older + source =~= (older + moved) + source.subrange(count, source.len() as int));
}

#[verifier::spinoff_prover]
pub proof fn trail_append_equation<T>(entries: Seq<(nat, T)>, i: nat, value: T)
    ensures earliest(entries.push((i, value))) == capture_first(earliest(entries), i, value),
{
    assert(entries.push((i, value)).drop_last() =~= entries);
}

/// Physical duplicates are retained; only this ghost map ignores later values.
#[verifier::spinoff_prover]
pub proof fn repeated_capture<T>(entries: Seq<(nat, T)>, i: nat, first: T, later: T)
    ensures earliest(entries.push((i, first)).push((i, later))) == earliest(entries.push((i, first))),
        !earliest(entries).dom().contains(i) ==> earliest(entries.push((i, first)).push((i, later)))[i] == first,
{
    trail_append_equation(entries, i, first);
    trail_append_equation(entries.push((i, first)), i, later);
}

/// Exact partial-map equality composes across each representation change;
/// absence and saved length survive, not just reconstructed snapshot contents.
#[verifier::spinoff_prover]
pub proof fn conversion_chain<T>(trail: Pairs<T>, hot: Pairs<T>, ordered: Pairs<T>, cold: Runs<T>, reopened: Pairs<T>)
    requires deduplicated(trail, hot), sorted(hot, ordered), encoded(ordered, cold),
        reopened_hot(cold, reopened),
    ensures hot_valid(reopened), pairs_meaning(reopened) == pairs_meaning(trail),
        forall|i: nat| #[trigger] pairs_meaning(reopened).saved.dom().contains(i)
            == pairs_meaning(trail).saved.dom().contains(i),
{}

/// Empty transforms must preserve a frame header even though every payload
/// and map is empty. Run validity forbids manufacturing zero-length runs.
#[verifier::spinoff_prover]
pub proof fn empty_frame_contracts<T>(saved_len: nat)
    ensures
        deduplicated(Pairs::<T> { saved_len, entries: Seq::empty() }, Pairs::<T> { saved_len, entries: Seq::empty() }),
        encoded(Pairs::<T> { saved_len, entries: Seq::empty() }, Runs::<T> { saved_len, runs: Seq::empty() }),
        reopened_hot(Runs::<T> { saved_len, runs: Seq::empty() }, Pairs::<T> { saved_len, entries: Seq::empty() }),
{}

/// Nonempty consistency example: a later physical Trail duplicate is ignored
/// by the map only. Hot order may differ, sorting preserves the map, and a
/// gapped Cold encoding appends to existing pools without touching their prefix.
#[verifier::spinoff_prover]
pub proof fn encoded_duplicate_example<T>(a: T, b: T, later: T, prefix: T)
{
    reveal_with_fuel(earliest, 5);
    reveal_with_fuel(flatten, 4);
    reveal_with_fuel(payload_len, 4);
    let trail = Pairs { saved_len: 3, entries: seq![(0nat, a), (2nat, b), (0nat, later)] };
    let hot = Pairs { saved_len: 3, entries: seq![(2nat, b), (0nat, a)] };
    let ordered = Pairs { saved_len: 3, entries: seq![(0nat, a), (2nat, b)] };
    let cold = Runs { saved_len: 3, runs: seq![Run { base: 0, values: seq![a] }, Run { base: 2, values: seq![b] }] };
    assert(earliest(trail.entries) =~= earliest(hot.entries));
    assert(earliest(hot.entries) =~= earliest(ordered.entries));
    hot.entries.lemma_reverse_to_multiset();
    assert(hot.entries.reverse() =~= ordered.entries);
    assert(hot.entries.to_multiset() =~= ordered.entries.to_multiset());
    assert(flatten(cold.runs) =~= ordered.entries);
    assert(deduplicated(trail, hot) && sorted(hot, ordered) && encoded(ordered, cold));
    assert(reopened_hot(cold, hot));
    conversion_chain(trail, hot, ordered, cold, hot);
    assert(!pairs_meaning(hot).saved.dom().contains(1));
    assert(pairs_meaning(hot).saved[0] == a);

    let pre = ColdPool { headers: seq![Header { saved_len: 3, start: 0, len: 1 }],
        runs: seq![PoolRun { base: 1, start: 0, len: 1 }], values: seq![prefix] };
    let out = ColdPool { headers: pre.headers.push(Header { saved_len: 3, start: 1, len: 2 }),
        runs: pre.runs + seq![PoolRun { base: 0, start: 1, len: 1 }, PoolRun { base: 2, start: 2, len: 1 }],
        values: seq![prefix, a, b] };
    assert forall|r: int| 0 <= r < cold.runs.len() implies {
        let run = #[trigger] out.runs[pre.runs.len() + r];
        &&& run.base == cold.runs[r].base
        &&& run.start == pre.values.len() + payload_len(cold.runs.subrange(0, r))
        &&& run.len == cold.runs[r].values.len()
        &&& run.start + run.len <= out.values.len()
        &&& out.values.subrange(run.start as int, (run.start + run.len) as int) == cold.runs[r].values
    } by {
        if r == 0 {
            assert(cold.runs.subrange(0, r) =~= Seq::empty());
            assert(out.values.subrange(1, 2) =~= seq![a]);
        } else {
            assert(r == 1);
            assert(cold.runs.subrange(0, r) =~= seq![cold.runs[0]]);
            assert(out.values.subrange(2, 3) =~= seq![b]);
        }
    }
    assert(out.runs.subrange(0, pre.runs.len() as int) =~= pre.runs);
    assert(out.values.subrange(0, pre.values.len() as int) =~= pre.values);
    assert(appended_cold(pre, out, cold));
    cold_transform_and_pool(ordered, cold, pre, out);
}

} // verus!
