// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Provisional primitive contracts for mutation and marking. Logical snapshot
//! closure comes from model.rs, not from any implementation or trusted wrapper.

use super::*;

verus! {

pub trait Limits<T>: View<T> {
    spec fn can_grow(self) -> bool;
    spec fn can_mark(self) -> bool;
    spec fn initial_allowed(live: Seq<T>) -> bool;
    spec fn mark_error(self) -> Option<RequestError>;
}

pub open spec fn captured_if_needed<T, R: View<T>>(s: R, i: nat) -> bool {
    s.model().frames.len() > 0 && i < s.active_saved_len() ==>
        s.model().frames[s.model().frames.len() - 1].saved.dom().contains(i)
}

/// Raw push appends a clear flag. Regrowth may need to set only this new flag.
pub open spec fn last_tag_pending<T, R: View<T>>(s: R) -> bool {
    s.model().live.len() > 0 && forall|i: nat| #[trigger] s.tags().contains(i) <==>
        i + 1 < s.model().live.len() && s.model().frames.len() > 0
            && s.model().frames[s.model().frames.len() - 1].saved.dom().contains(i)
}

// Mutation does not require restoration capability: concrete restore needs
// T: Default, while set/push/pop/mark support every admitted Copy payload.
pub trait Mutations<T>: Limits<T> {
    proof fn mark_guard(pre: Self)
        requires stable(pre),
        ensures pre.mark_error() is None <==> pre.can_mark(),
            pre.mark_error() is Some ==> pre.mark_error()->Some_0 != RequestError::InvalidToken;

    proof fn construct(live: Seq<T>, unique: bool) -> (out: Self)
        requires Self::initial_allowed(live),
        ensures physical(out), writable(out), capture_ok(out),
            out.model() == empty(live), out.unique() == unique;

    /// Trail always appends physically; Hot consults capture membership. Both
    /// export first-capture map update, including preservation of absence.
    proof fn capture_cell(pre: Self, i: nat) -> (out: Self)
        requires stable(pre), i < pre.model().live.len(),
        ensures physical(out), writable(out), capture_ok(out), same_protocol(out, pre),
            out.model() == capture(pre.model(), i);

    proof fn raw_write(work: Self, i: nat, value: T) -> (out: Self)
        requires physical(work), writable(work), capture_ok(work),
            i < work.model().live.len(), captured_if_needed(work, i),
        ensures physical(out), writable(out), capture_ok(out), same_protocol(out, work),
            out.canonical() == work.canonical(),
            out.model() == (Model { live: work.model().live.update(i as int, value), ..work.model() });

    proof fn raw_pop(work: Self) -> (out: Self)
        requires physical(work), writable(work), capture_ok(work), work.model().live.len() > 0,
            captured_if_needed(work, (work.model().live.len() - 1) as nat),
        ensures physical(out), writable(out), capture_ok(out), same_protocol(out, work),
            out.canonical() == work.canonical(),
            out.model() == (Model { live: work.model().live.drop_last(), ..work.model() });

    proof fn raw_push(pre: Self, value: T) -> (out: Self)
        requires stable(pre), pre.can_grow(),
        ensures physical(out), writable(out), last_tag_pending(out), same_protocol(out, pre),
            out.canonical() == pre.canonical(), out.model() == push(pre.model(), value);

    proof fn finish_regrowth(work: Self) -> (out: Self)
        requires physical(work), writable(work), snapshots_ok(work.model()), last_tag_pending(work),
        ensures physical(out), writable(out), capture_ok(out), same_protocol(out, work),
            out.model() == work.model(), out.canonical() == work.canonical();

    proof fn prepare_mark(pre: Self) -> (out: Self)
        requires stable(pre), pre.can_mark(),
        ensures physical(out), writable(out), out.tags().is_empty(), same_protocol(out, pre),
            out.can_mark(), out.model() == pre.model(), out.canonical() == pre.canonical();

    /// Old top is sealed and the replacement empty writable frame is opened
    /// before rollover, matching the runtime order.
    proof fn open_mark(work: Self) -> (out: Self)
        requires physical(work), writable(work), snapshots_ok(work.model()),
            work.tags().is_empty(), work.can_mark(),
        ensures physical(out), writable(out), capture_ok(out), same_protocol(out, work),
            out.model() == mark(work.model());
}

pub proof fn new_public<T, R: Mutations<T>>(live: Seq<T>, unique: bool) -> (out: R)
    requires R::initial_allowed(live),
    ensures stable(out), out.model() == empty(live), out.unique() == unique,
{
    constructor(live);
    R::construct(live, unique)
}

#[verifier::spinoff_prover]
pub proof fn set_public<T, R: Mutations<T>>(pre: R, i: nat, value: T) -> (out: R)
    requires stable(pre), i < pre.model().live.len(),
    ensures stable(out), out.model() == write(pre.model(), i, value), same_protocol(out, pre),
{
    let captured = R::capture_cell(pre, i);
    capture_preserves(pre.model(), i);
    let out = R::raw_write(captured, i, value);
    write_preserves(pre.model(), i, value);
    out
}

#[verifier::spinoff_prover]
pub proof fn pop_public<T, R: Mutations<T>>(pre: R) -> (result: (R, Option<T>))
    requires stable(pre),
    ensures stable(result.0), result.0.model() == pop(pre.model()), same_protocol(result.0, pre),
        result.1 == if pre.model().live.len() == 0 { None } else { Some(pre.model().live.last()) },
{
    if pre.model().live.len() == 0 { (pre, None) } else {
        let captured = R::capture_cell(pre, (pre.model().live.len() - 1) as nat);
        capture_preserves(pre.model(), (pre.model().live.len() - 1) as nat);
        let out = R::raw_pop(captured);
        pop_preserves(pre.model());
        (out, Some(pre.model().live.last()))
    }
}

#[verifier::spinoff_prover]
pub proof fn push_public<T, R: Mutations<T>>(pre: R, value: T) -> (out: R)
    requires stable(pre), pre.can_grow(),
    ensures stable(out), out.model() == push(pre.model(), value), same_protocol(out, pre),
{
    let pushed = R::raw_push(pre, value);
    push_preserves(pre.model(), value);
    R::finish_regrowth(pushed)
}

pub proof fn try_push_public<T, R: Mutations<T>>(pre: R, value: T) -> (result: (R, Result<(), RequestError>))
    requires stable(pre),
    ensures stable(result.0), result.1 is Ok <==> pre.can_grow(),
        result.1 is Ok ==> result.0.model() == push(pre.model(), value),
        result.1 is Err ==> result.0 == pre && result.1 == Err(RequestError::CapacityExhausted),
{
    if pre.can_grow() { (push_public(pre, value), Ok(())) }
    else { (pre, Err(RequestError::CapacityExhausted)) }
}

/// Token construction and configured/forced/adaptive rollover compose after
/// this mark core; their contracts are inventoried separately.
#[verifier::spinoff_prover]
pub proof fn mark_core<T, R: Mutations<T>>(pre: R) -> (out: R)
    requires stable(pre), pre.can_mark(),
    ensures stable(out), out.model() == mark(pre.model()), same_protocol(out, pre),
{
    let prepared = R::prepare_mark(pre);
    let out = R::open_mark(prepared);
    mark_preserves(pre.model());
    out
}

/// The second token is checked against the post-mutation state by the public
/// wrapper. No new genealogy or token-survival rule is assumed here.
#[verifier::spinoff_prover]
pub proof fn restore_write_restore<T, R: Mutations<T> + Runtime<T>>(
    pre: R, first: R::Token, second: R::Token, i: nat, value: T,
) -> (result: (R, bool))
    requires stable(pre), pre.token_valid(first),
        forall|k: int| k == R::coordinate(first) && 0 <= k < pre.model().snapshots.len() ==>
            i < (#[trigger] pre.model().snapshots[k]).len(),
    ensures stable(result.0),
        result.1 ==> 0 <= R::coordinate(second) < pre.model().snapshots.len(),
        result.1 ==> result.0.model().live == pre.model().snapshots[R::coordinate(second)],
        result.1 ==> result.0.model().snapshots == pre.model().snapshots.subrange(0, R::coordinate(second)),
        !result.1 ==> result.0.model() == write(restore(pre.model(), R::coordinate(first)), i, value)
            && !result.0.token_valid(second),
{
    R::token_bounds(pre, first);
    let restored = restore_public(pre, first);
    let written = set_public(restored, i, value);
    if written.token_valid(second) {
        R::token_bounds(written, second);
        let out = restore_public(written, second);
        assert(out.model().snapshots =~= pre.model().snapshots.subrange(0, R::coordinate(second)));
        (out, true)
    } else { (written, false) }
}

} // verus!
