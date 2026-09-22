// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conditional physical composition. There is no production Runtime adapter:
//! verification proves implications from these contracts, not runtime closure.
//! witness.rs checks their consistency using mathematical map storage.
//! Production code neither imports this target nor trusts these interfaces.

use vstd::prelude::*;
mod encoding;
mod model;
use model::*;
mod mutation;
mod policy;
mod public_sequence;
mod witness;

verus! {

/// Mirrors the public request-error categories. Concrete adapters must preserve
/// the existing guard order and map these variants to ContainerError exactly.
pub enum RequestError { Untracked, DepthLimit, CapacityExhausted, InvalidToken }

pub trait View<T>: Sized {
    type History;
    type Canonical;
    spec fn model(self) -> Model<T>;
    spec fn history(self) -> Self::History;
    spec fn canonical(self) -> Self::Canonical;
    spec fn canonical_prefix(self, k: int) -> Self::Canonical;
    spec fn cold(self) -> int;
    spec fn hot(self) -> int;
    spec fn trail(self) -> int;
    spec fn unique(self) -> bool;
    spec fn fused_clear(self) -> bool;
    spec fn active_saved_len(self) -> nat;
    spec fn partition_ok(self) -> bool;
    spec fn tags(self) -> Set<nat>;
    spec fn store_ok(self) -> bool;
    spec fn layout_ok(self) -> bool;
    spec fn meaning_ok(self) -> bool;
    spec fn canonical_ok(self) -> bool;

    /// The client supplies a public token predicate, not just a frame bound.
    type Token;
    spec fn token_valid(self, token: Self::Token) -> bool;
    spec fn coordinate(token: Self::Token) -> int;
    spec fn retired_prefix(out: Self, pre: Self, k: int) -> bool;
    spec fn older_storage_unchanged(out: Self, pre: Self, survivor: int) -> bool;
}

pub trait Runtime<T>: View<T> {
    proof fn token_bounds(pre: Self, token: Self::Token)
        requires stable(pre), pre.token_valid(token),
        ensures 0 <= Self::coordinate(token) < pre.model().frames.len();

    proof fn resize(pre: Self, k: int) -> (out: Self)
        requires stable(pre), 0 <= k < pre.model().frames.len(),
        ensures physical(out), same_history(out, pre),
            out.model().live.len() == pre.model().snapshots[k].len(),
            agrees(out.model().live, pre.model().live),
            out.tags().subset_of(pre.tags()),
            forall|i: nat| #[trigger] out.tags().contains(i) ==> i < out.model().live.len();

    /// Non-fused stores clear now; fused stores retain flags until the first
    /// ingress batch. Both protocols preserve the resized buffer and history.
    proof fn prepare(pre: Self, work: Self) -> (out: Self)
        requires stable(pre), physical(work), same_history(work, pre),
            work.tags().subset_of(pre.tags()),
        ensures physical(out), same_history(out, pre), out.model() == work.model(),
            out.tags().subset_of(pre.tags()), !pre.fused_clear() ==> out.tags().is_empty();

    /// One actual Trail or Hot range, with frame composition in its contract.
    /// If this is the first batch, it contains the pre-state ingress frame.
    proof fn pair_batch(pre: Self, work: Self, trail: bool, lo: int, hi: int) -> (out: Self)
        requires stable(pre), physical(work), same_history(work, pre),
            0 <= lo < hi <= pre.model().frames.len(),
            if trail { pre.cold() + pre.hot() <= lo && hi == pre.model().frames.len() }
            else { pre.cold() <= lo && hi == pre.cold() + pre.hot() },
            work.tags().is_empty() || hi == pre.model().frames.len(),
            work.tags().subset_of(pre.tags()),
            !pre.fused_clear() ==> work.tags().is_empty(),
        ensures physical(out), same_history(out, pre), out.tags().is_empty(),
            out.model().live == apply_range(pre.model().frames, lo, hi, work.model().live);

    /// Direct Cold run replay; no intermediate pair encoding is assumed.
    proof fn cold_frame(pre: Self, work: Self, f: int) -> (out: Self)
        requires stable(pre), physical(work), same_history(work, pre),
            0 <= f < pre.cold(), work.tags().is_empty(),
        ensures physical(out), same_history(out, pre), out.tags().is_empty(),
            out.model().live == apply(pre.model().frames[f].saved, work.model().live);

    /// Retire exact physical/canonical prefixes before any survivor movement.
    proof fn retire(pre: Self, work: Self, k: int) -> (out: Self)
        requires stable(pre), physical(work), same_history(work, pre),
            0 <= k < pre.model().frames.len(), work.tags().is_empty(),
            work.model().live == pre.model().snapshots[k],
        ensures physical(out), out.model() == restore(pre.model(), k),
            out.tags().is_empty(), out.unique() == pre.unique(),
            out.fused_clear() == pre.fused_clear(),
            Self::retired_prefix(out, pre, k), out.canonical() == pre.canonical_prefix(k),
            out.cold() == if k < pre.cold() { k } else { pre.cold() },
            out.hot() == if k <= pre.cold() { 0 }
                else if k < pre.cold() + pre.hot() { k - pre.cold() } else { pre.hot() },
            out.trail() == if k <= pre.cold() + pre.hot() { 0 } else { k - pre.cold() - pre.hot() };

    /// Full map equality includes membership. Reopening moves only the newest
    /// retained frame; older physical storage and canonical history survive.
    proof fn reopen_hot(work: Self) -> (out: Self)
        requires physical(work), snapshots_ok(work.model()), work.tags().is_empty(),
            !work.unique(), work.trail() == 0, work.hot() > 0,
        ensures physical(out), ingress_ready(out), out.model() == work.model(),
            out.tags().is_empty(), out.canonical() == work.canonical(), same_protocol(out, work),
            out.cold() == work.cold(), out.hot() == work.hot() - 1, out.trail() == 1,
            Self::older_storage_unchanged(out, work, work.model().frames.len() - 1);

    proof fn reopen_cold(work: Self) -> (out: Self)
        requires physical(work), snapshots_ok(work.model()), work.tags().is_empty(),
            work.cold() > 0, work.hot() == 0, work.trail() == 0,
        ensures physical(out), ingress_ready(out), out.model() == work.model(),
            out.tags().is_empty(), out.canonical() == work.canonical(), same_protocol(out, work),
            out.cold() == work.cold() - 1,
            out.hot() == if work.unique() { 1int } else { 0int },
            out.trail() == if work.unique() { 0int } else { 1int },
            Self::older_storage_unchanged(out, work, work.model().frames.len() - 1);

    proof fn finish_capture(work: Self) -> (out: Self)
        requires physical(work), snapshots_ok(work.model()), ingress_ready(work), work.tags().is_empty(),
        ensures physical(out), writable(out), out.model() == work.model(),
            capture_ok(out), out.canonical() == work.canonical(), same_protocol(out, work);

    proof fn finish_empty(work: Self) -> (out: Self)
        requires physical(work), snapshots_ok(work.model()),
            work.model().frames.len() == 0, work.tags().is_empty(),
        ensures physical(out), writable(out), out.model() == work.model(),
            capture_ok(out), out.canonical() == work.canonical(), same_protocol(out, work);

    proof fn reclaim(work: Self) -> (out: Self)
        requires stable(work),
        ensures physical(out), writable(out), capture_ok(out),
            out.model() == work.model(), out.canonical() == work.canonical(), same_protocol(out, work);
}

pub open spec fn physical<T, R: View<T>>(s: R) -> bool {
    &&& s.store_ok()
    &&& s.layout_ok()
    &&& s.partition_ok()
    &&& s.meaning_ok()
    &&& s.canonical_ok()
    &&& 0 <= s.cold() && 0 <= s.hot() && 0 <= s.trail()
    &&& s.cold() + s.hot() + s.trail() == s.model().frames.len()
    &&& s.model().frames.len() == s.model().snapshots.len()
}

pub open spec fn ingress_ready<T, R: View<T>>(s: R) -> bool {
    if s.unique() {
        s.trail() == 0 && (s.model().frames.len() > 0 ==> s.hot() > 0)
    } else { s.model().frames.len() > 0 ==> s.trail() > 0 }
}

pub open spec fn writable<T, R: View<T>>(s: R) -> bool {
    ingress_ready(s) && s.active_saved_len() == if s.model().frames.len() > 0 {
        s.model().frames[s.model().frames.len() - 1].saved_len
    } else { 0 }
}

pub open spec fn same_protocol<T, R: View<T>>(s: R, pre: R) -> bool {
    s.unique() == pre.unique() && s.fused_clear() == pre.fused_clear()
}

pub open spec fn capture_ok<T, R: View<T>>(s: R) -> bool {
    forall|i: nat| #[trigger] s.tags().contains(i) <==>
        i < s.model().live.len() && s.model().frames.len() > 0
            && s.model().frames[s.model().frames.len() - 1].saved.dom().contains(i)
}

pub open spec fn stable<T, R: View<T>>(s: R) -> bool {
    physical(s) && snapshots_ok(s.model()) && writable(s) && capture_ok(s)
}

pub open spec fn same_history<T, R: View<T>>(s: R, pre: R) -> bool {
    &&& s.model().frames == pre.model().frames
    &&& s.model().snapshots == pre.model().snapshots
    &&& s.history() == pre.history()
    &&& s.canonical() == pre.canonical()
    &&& s.cold() == pre.cold() && s.hot() == pre.hot() && s.trail() == pre.trail()
    &&& s.unique() == pre.unique() && s.fused_clear() == pre.fused_clear()
}

#[verifier::spinoff_prover]
pub proof fn cold_suffix<T, R: Runtime<T>>(pre: R, work: R, lo: int, hi: int) -> (out: R)
    requires stable(pre), physical(work), same_history(work, pre), work.tags().is_empty(),
        0 <= lo <= hi <= pre.cold(),
    ensures physical(out), same_history(out, pre), out.tags().is_empty(),
        out.model().live == apply_range(pre.model().frames, lo, hi, work.model().live),
    decreases hi - lo,
{
    if lo < hi {
        let newest = R::cold_frame(pre, work, hi - 1);
        let out = cold_suffix(pre, newest, lo, hi - 1);
        assert(apply_range(pre.model().frames, hi, hi, work.model().live) == work.model().live);
        assert(apply_range(pre.model().frames, hi - 1, hi, work.model().live) == newest.model().live);
        range_split(pre.model().frames, lo, hi - 1, hi, work.model().live);
        out
    } else { work }
}

/// Conditional composition follows actual execution: one Trail batch, one
/// Hot batch, then direct Cold frames, with absent/empty tier ranges skipped.
#[verifier::spinoff_prover]
pub proof fn reconstruct<T, R: Runtime<T>>(pre: R, k: int) -> (out: R)
    requires stable(pre), 0 <= k < pre.model().frames.len(),
    ensures physical(out), same_history(out, pre), out.tags().is_empty(),
        out.model().live == pre.model().snapshots[k],
{
    let resized = R::resize(pre, k);
    let buffer = resized.model().live;
    let mut work = R::prepare(pre, resized);
    let n = pre.model().frames.len() as int;
    let ch = pre.cold() + pre.hot();
    let mut next = n;
    if pre.trail() > 0 {
        let lo = if k > ch { k } else { ch };
        work = R::pair_batch(pre, work, true, lo, n);
        next = lo;
    }
    assert(work.model().live == apply_range(pre.model().frames, next, n, buffer));
    if pre.hot() > 0 && k < ch {
        let lo = if k > pre.cold() { k } else { pre.cold() };
        assert(next == ch);
        work = R::pair_batch(pre, work, false, lo, ch);
        range_split(pre.model().frames, lo, ch, n, buffer);
        next = lo;
    }
    assert(work.tags().is_empty());
    assert(work.model().live == apply_range(pre.model().frames, next, n, buffer));
    if k < pre.cold() {
        assert(next == pre.cold());
        work = cold_suffix(pre, work, k, pre.cold());
        range_split(pre.model().frames, k, pre.cold(), n, buffer);
        next = k;
    }
    assert(next == k);
    reconstructs_target(pre.model(), k, buffer);
    work
}

#[verifier::spinoff_prover]
pub proof fn restore_public<T, R: Runtime<T>>(pre: R, token: R::Token) -> (out: R)
    requires stable(pre), pre.token_valid(token),
    ensures stable(out), out.model() == restore(pre.model(), R::coordinate(token)), same_protocol(out, pre),
        out.canonical() == pre.canonical_prefix(R::coordinate(token)),
{
    R::token_bounds(pre, token);
    let k = R::coordinate(token);
    let reconstructed = reconstruct(pre, k);
    let retained = R::retire(pre, reconstructed, k);
    restore_preserves(pre.model(), k);
    let finished = if k == 0 { R::finish_empty(retained) } else {
        let reopened = if ingress_ready(retained) { retained }
            else if retained.hot() > 0 { R::reopen_hot(retained) }
            else { R::reopen_cold(retained) };
        R::finish_capture(reopened)
    };
    R::reclaim(finished)
}

/// Rejected fallible requests leave the state itself unchanged.
pub proof fn try_restore_public<T, R: Runtime<T>>(pre: R, token: R::Token) -> (result: (R, Result<(), RequestError>))
    requires stable(pre),
    ensures stable(result.0),
        result.1 is Ok <==> pre.token_valid(token),
        result.1 is Ok ==> result.0.model() == restore(pre.model(), R::coordinate(token)),
        result.1 is Err ==> result.0 == pre && result.1 == Err(RequestError::InvalidToken),
{
    if pre.token_valid(token) { (restore_public(pre, token), Ok(())) }
    else { (pre, Err(RequestError::InvalidToken)) }
}

} // verus!
