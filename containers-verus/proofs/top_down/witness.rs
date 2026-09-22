// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! A mathematical consistency witness, not an adapter for production storage.
//! Frame maps are its storage, so it validates realizability of the conditional
//! interfaces without discharging physical Trail/Hot/Cold encoding obligations.

use super::mutation::*;
use super::policy::*;
use super::*;

verus! {

pub struct Witness<T> {
    pub m: Model<T>,
    pub c: int,
    pub h: int,
    pub t: int,
    pub unique: bool,
    pub fused: bool,
    pub flags: Set<nat>,
    pub active: nat,
}

pub open spec fn expected<T>(m: Model<T>) -> Set<nat> {
    if m.frames.len() > 0 {
        m.frames[m.frames.len() - 1].saved.dom().filter(|i: nat| i < m.live.len())
    } else { Set::empty() }
}

impl<T> View<T> for Witness<T> {
    type History = Seq<Frame<T>>;
    type Canonical = Seq<Seq<T>>;
    type Token = int;
    open spec fn model(self) -> Model<T> { self.m }
    open spec fn history(self) -> Self::History { self.m.frames }
    open spec fn canonical(self) -> Self::Canonical { self.m.snapshots }
    open spec fn canonical_prefix(self, k: int) -> Self::Canonical { self.m.snapshots.subrange(0, k) }
    open spec fn cold(self) -> int { self.c }
    open spec fn hot(self) -> int { self.h }
    open spec fn trail(self) -> int { self.t }
    open spec fn unique(self) -> bool { self.unique }
    open spec fn fused_clear(self) -> bool { self.fused }
    open spec fn active_saved_len(self) -> nat { self.active }
    open spec fn tags(self) -> Set<nat> { self.flags }
    open spec fn store_ok(self) -> bool {
        forall|i: nat| #[trigger] self.flags.contains(i) ==> i < self.m.live.len()
    }
    open spec fn layout_ok(self) -> bool {
        forall|f: int, i: nat| 0 <= f < self.m.frames.len()
            && (#[trigger] self.m.frames[f].saved.dom().contains(i)) ==>
                i < self.m.frames[f].saved_len
    }
    open spec fn partition_ok(self) -> bool {
        0 <= self.c && 0 <= self.h && 0 <= self.t
            && self.c + self.h + self.t == self.m.frames.len()
    }
    // In this witness the storage is already the map interpretation.
    open spec fn meaning_ok(self) -> bool { true }
    open spec fn canonical_ok(self) -> bool { self.m.snapshots.len() == self.m.frames.len() }
    open spec fn token_valid(self, token: int) -> bool { 0 <= token < self.m.frames.len() }
    open spec fn coordinate(token: int) -> int { token }
    open spec fn retired_prefix(out: Self, pre: Self, k: int) -> bool {
        out.m.frames == pre.m.frames.subrange(0, k)
            && out.m.snapshots == pre.m.snapshots.subrange(0, k)
    }
    open spec fn older_storage_unchanged(out: Self, pre: Self, survivor: int) -> bool {
        out.m.frames.subrange(0, survivor) == pre.m.frames.subrange(0, survivor)
    }
}

impl<T> Runtime<T> for Witness<T> {
    proof fn token_bounds(pre: Self, token: int) {}

    proof fn resize(pre: Self, k: int) -> (out: Self) {
        // Any filler is permitted by the interface; choosing target cells is
        // convenient for a proof witness and is not a runtime implementation.
        let live = Seq::new(pre.m.snapshots[k].len(), |i: int|
            if i < pre.m.live.len() { pre.m.live[i] } else { pre.m.snapshots[k][i] });
        Witness { m: Model { live, ..pre.m },
            flags: pre.flags.filter(|i: nat| i < live.len()), ..pre }
    }

    proof fn prepare(pre: Self, work: Self) -> (out: Self) {
        if pre.fused { work } else { Witness { flags: Set::empty(), ..work } }
    }

    proof fn pair_batch(pre: Self, work: Self, trail: bool, lo: int, hi: int) -> (out: Self) {
        range_len(pre.m.frames, lo, hi, work.m.live);
        Witness { m: Model { live: apply_range(pre.m.frames, lo, hi, work.m.live), ..work.m },
            flags: Set::empty(), ..work }
    }

    proof fn cold_frame(pre: Self, work: Self, f: int) -> (out: Self) {
        Witness { m: Model { live: apply(pre.m.frames[f].saved, work.m.live), ..work.m }, ..work }
    }

    proof fn retire(pre: Self, work: Self, k: int) -> (out: Self) {
        let out = Witness { m: restore(pre.m, k),
            c: if k < pre.c { k } else { pre.c },
            h: if k <= pre.c { 0 } else if k < pre.c + pre.h { k - pre.c } else { pre.h },
            t: if k <= pre.c + pre.h { 0 } else { k - pre.c - pre.h }, ..work };
        assert forall|f: int, i: nat| 0 <= f < out.m.frames.len()
            && (#[trigger] out.m.frames[f].saved.dom().contains(i)) implies
                i < out.m.frames[f].saved_len by {
            assert(out.m.frames[f] == pre.m.frames[f]);
        }
        out
    }

    proof fn reopen_hot(work: Self) -> (out: Self) {
        Witness { h: work.h - 1, t: 1, ..work }
    }

    proof fn reopen_cold(work: Self) -> (out: Self) {
        Witness { c: work.c - 1, h: if work.unique { 1 } else { 0 },
            t: if work.unique { 0 } else { 1 }, ..work }
    }

    proof fn finish_capture(work: Self) -> (out: Self) {
        Witness { active: if work.m.frames.len() > 0 {
            work.m.frames[work.m.frames.len() - 1].saved_len
        } else { 0 }, flags: expected(work.m), ..work }
    }

    proof fn finish_empty(work: Self) -> (out: Self) {
        Witness { active: 0, ..work }
    }

    proof fn reclaim(work: Self) -> (out: Self) { work }
}

#[verifier::spinoff_prover]
proof fn tags_expected<T>(s: Witness<T>)
    requires capture_ok(s),
    ensures s.flags == expected(s.m),
{
    assert forall|i: nat| #[trigger] s.flags.contains(i) <==> expected(s.m).contains(i) by {
        assert(s.tags().contains(i) <==> i < s.model().live.len() && s.model().frames.len() > 0
            && s.model().frames[s.model().frames.len() - 1].saved.dom().contains(i));
    }
    assert(s.flags =~= expected(s.m));
}

// The mathematical witness has unbounded finite sequence capacity. Concrete
// adapters must instantiate these guards with their actual representable limits.
impl<T> Limits<T> for Witness<T> {
    open spec fn can_grow(self) -> bool { true }
    open spec fn can_mark(self) -> bool { true }
    open spec fn initial_allowed(live: Seq<T>) -> bool { true }
    open spec fn mark_error(self) -> Option<RequestError> { None }
}

impl<T> Mutations<T> for Witness<T> {
    proof fn mark_guard(pre: Self) {}

    proof fn construct(live: Seq<T>, unique: bool) -> (out: Self) {
        Witness { m: empty(live), c: 0, h: 0, t: 0, unique, fused: false,
            flags: Set::empty(), active: 0 }
    }

    proof fn capture_cell(pre: Self, i: nat) -> (out: Self) {
        capture_preserves(pre.m, i);
        let m = capture(pre.m, i);
        let out = Witness { m, flags: expected(m), ..pre };
        assert forall|f: int, j: nat| 0 <= f < m.frames.len()
            && (#[trigger] m.frames[f].saved.dom().contains(j)) implies
                j < m.frames[f].saved_len by {
            assert(frame_ok(m.frames[f], m.snapshots[f], above(m, f)));
        }
        out
    }

    proof fn raw_write(work: Self, i: nat, value: T) -> (out: Self) {
        tags_expected(work);
        Witness { m: Model { live: work.m.live.update(i as int, value), ..work.m }, ..work }
    }

    proof fn raw_pop(work: Self) -> (out: Self) {
        tags_expected(work);
        let m = Model { live: work.m.live.drop_last(), ..work.m };
        Witness { m, flags: work.flags.remove((work.m.live.len() - 1) as nat), ..work }
    }

    proof fn raw_push(pre: Self, value: T) -> (out: Self) {
        tags_expected(pre);
        Witness { m: push(pre.m, value), ..pre }
    }

    proof fn finish_regrowth(work: Self) -> (out: Self) {
        Witness { flags: expected(work.m), ..work }
    }

    proof fn prepare_mark(pre: Self) -> (out: Self) {
        Witness { flags: Set::empty(), ..pre }
    }

    proof fn open_mark(work: Self) -> (out: Self) {
        let m = mark(work.m);
        let out = Witness { m, h: work.h + if work.unique { 1int } else { 0int },
            t: work.t + if work.unique { 0int } else { 1int }, active: work.m.live.len(), ..work };
        assert forall|f: int, i: nat| 0 <= f < m.frames.len()
            && (#[trigger] m.frames[f].saved.dom().contains(i)) implies
                i < m.frames[f].saved_len by {
            if f < work.m.frames.len() { assert(m.frames[f] == work.m.frames[f]); }
        }
        out
    }
}

impl<T> Policies<T> for Witness<T> {
    proof fn select_plan(pre: Self, policy: Policy, source: Source) -> (plan: Plan<T>) {
        let count = if policy is Defer
            || (policy is ForceTrail && source is Hot)
            || (policy is ForceHot && source is Trail) { 0nat } else { eligible(pre, source) as nat };
        let offset = if source is Trail { pre.c + pre.h } else { pre.c };
        Plan { source, count, frames: pre.m.frames.subrange(offset, offset + count) }
    }

    proof fn migrate(pre: Self, plan: Plan<T>) -> (out: Self) {
        tags_expected(pre);
        if plan.source is Trail {
            Witness { h: pre.h + plan.count, t: pre.t - plan.count, ..pre }
        } else {
            Witness { c: pre.c + plan.count, h: pre.h - plan.count, ..pre }
        }
    }

    proof fn make_token(pre: Self, coordinate: int) -> (token: int) { coordinate }
}

/// Any semantically valid history has a stable witness in either discipline,
/// with arbitrary eligible tier boundaries and either flag-clearing protocol.
#[verifier::spinoff_prover]
pub proof fn place<T>(m: Model<T>, c: int, h: int, t: int, unique: bool, fused: bool) -> (out: Witness<T>)
    requires snapshots_ok(m), 0 <= c, 0 <= h, 0 <= t, c + h + t == m.frames.len(),
        unique ==> t == 0 && (m.frames.len() > 0 ==> h > 0),
        !unique && m.frames.len() > 0 ==> t > 0,
    ensures stable(out), out.model() == m, out.c == c, out.h == h, out.t == t,
        out.unique == unique, out.fused == fused,
{
    let out = Witness { m, c, h, t, unique, fused, flags: expected(m),
        active: if m.frames.len() > 0 { m.frames[m.frames.len() - 1].saved_len } else { 0 } };
    assert forall|f: int, i: nat| 0 <= f < m.frames.len()
        && (#[trigger] m.frames[f].saved.dom().contains(i)) implies i < m.frames[f].saved_len by {
        assert(frame_ok(m.frames[f], m.snapshots[f], above(m, f)));
    }
    out
}

/// Saved lengths are 3,1,3,2,2; the live length is 2. Frame 3 is empty,
/// and two writes to index zero of frame 4 keep its first saved value.
#[verifier::spinoff_prover]
pub proof fn zigzag_model<T>(a: T, b: T, c: T, d: T, e: T) -> (out: Model<T>)
    ensures snapshots_ok(out), out.live.len() == 2, out.frames.len() == 5,
        out.snapshots[0] == seq![a, b, c],
        out.snapshots[1] == seq![a], out.snapshots[2] == seq![a, d, e],
        out.snapshots[3] == seq![a, d], out.snapshots[4] == seq![a, d],
        out.frames[3].saved == Map::<nat, T>::empty(),
        out.frames[4].saved.dom().contains(0), out.frames[4].saved[0] == a,
{
    let s0 = empty(seq![a, b, c]);
    constructor(seq![a, b, c]);
    mark_preserves(s0); let s1 = mark(s0);
    pop_preserves(s1); let s2 = pop(s1);
    pop_preserves(s2); let s3 = pop(s2);
    mark_preserves(s3); let s4 = mark(s3);
    push_preserves(s4, d); let s5 = push(s4, d);
    push_preserves(s5, e); let s6 = push(s5, e);
    mark_preserves(s6); let s7 = mark(s6);
    pop_preserves(s7); let s8 = pop(s7);
    mark_preserves(s8); let s9 = mark(s8);
    mark_preserves(s9); let s10 = mark(s9);
    write_preserves(s10, 0, b); let s11 = write(s10, 0, b);
    write_preserves(s11, 0, c); let out = write(s11, 0, c);
    assert(out.snapshots[0] =~= seq![a, b, c]);
    assert(out.snapshots[1] =~= seq![a]);
    assert(out.snapshots[2] =~= seq![a, d, e]);
    assert(out.snapshots[3] =~= seq![a, d]);
    assert(out.snapshots[4] =~= seq![a, d]);
    out
}

/// All survivor locations occur under one shared model. The boolean covers
/// both fused and non-fused clearing. No leaf implementation is used.
#[verifier::spinoff_prover]
pub proof fn mixed_restore_cases<T>(a: T, b: T, c: T, d: T, e: T, fused: bool)
{
    let m = zigzag_model(a, b, c, d, e);
    let trail = place(m, 2, 1, 2, false, fused);
    let zero = restore_public(trail, 0);
    let cold = restore_public(trail, 2);
    let hot = restore_public(trail, 3);
    let kept_trail = restore_public(trail, 4);
    assert(stable(zero) && stable(cold) && stable(hot) && stable(kept_trail));
    assert(zero.m.live == seq![a, b, c]);
    assert(cold.m.live == seq![a, d, e]);
    assert(hot.m.live == seq![a, d]);
    let unique = place(m, 2, 3, 0, true, fused);
    let cold_to_hot = restore_public(unique, 2);
    let kept_hot = restore_public(unique, 4);
    assert(stable(cold_to_hot) && stable(kept_hot));
    assert(cold_to_hot.m.live == seq![a, d, e]);
    let result = restore_write_restore(trail, 4, 1, 0, e);
    assert(result.1 && result.0.m.live == seq![a]);
}

/// Explicitly migrate an empty sealed Trail frame through Hot into Cold;
/// its delimiter and empty map survive both completed migration contracts.
#[verifier::spinoff_prover]
pub proof fn empty_frame_migration<T>(a: T, b: T, c: T, d: T, e: T)
{
    let m = zigzag_model(a, b, c, d, e);
    let initial = place(m, 2, 1, 2, false, false);
    let trail_plan = Plan { source: Source::Trail, count: 1, frames: m.frames.subrange(3, 4) };
    let hot = Witness::migrate(initial, trail_plan);
    assert(stable(hot) && hot.h == 2 && hot.t == 1);
    let hot_plan = Plan { source: Source::Hot, count: 2, frames: m.frames.subrange(2, 4) };
    let cold = Witness::migrate(hot, hot_plan);
    assert(stable(cold) && cold.c == 4 && cold.h == 0 && cold.t == 1);
    assert(cold.m.frames[3].saved == Map::<nat, T>::empty());
    let reopened = restore_public(cold, 4);
    assert(stable(reopened) && reopened.m.frames[3].saved == Map::<nat, T>::empty());
}

#[verifier::spinoff_prover]
pub proof fn regrowth_and_policy_cases<T>(a: T, b: T, c: T, replacement: T, unique: bool)
{
    let initial: Witness<T> = new_public(seq![a, b, c], unique);
    let (marked, token) = mark_public(initial, Policy::Defer);
    let (popped, value) = pop_public(marked);
    assert(value == Some(c));
    let regrown = push_public(popped, replacement);
    assert(regrown.m.frames[0].saved.dom().contains(2));
    assert(regrown.tags().contains(2));
    let restored = restore_public(regrown, token);
    assert(restored.m.live == seq![a, b, c]);
    let configured = apply_policy(regrown, Policy::Configured);
    let adaptive = apply_policy(regrown, Policy::Adaptive);
    let trail = apply_policy(regrown, Policy::ForceTrail);
    let hot = apply_policy(regrown, Policy::ForceHot);
    assert(configured.m == regrown.m && adaptive.m == regrown.m
        && trail.m == regrown.m && hot.m == regrown.m);
    let sequence = apply_policy_sequence(regrown,
        seq![Policy::Adaptive, Policy::ForceHot, Policy::Configured, Policy::ForceTrail, Policy::Defer]);
    assert(sequence.m == regrown.m && stable(sequence));
}

/// A legal Hot-then-Trail trace is also covered, independently of the usual
/// configured wrapper's Trail-then-Hot execution order.
#[verifier::spinoff_prover]
pub proof fn alternative_rollover_order<T>(a: T, b: T, c: T, d: T, e: T)
{
    let m = zigzag_model(a, b, c, d, e);
    let initial = place(m, 2, 1, 2, false, false);
    let hot_plan = Plan { source: Source::Hot, count: 1, frames: m.frames.subrange(2, 3) };
    let after_hot = Witness::migrate(initial, hot_plan);
    let trail_plan = Plan { source: Source::Trail, count: 1, frames: m.frames.subrange(3, 4) };
    let after_trail = Witness::migrate(after_hot, trail_plan);
    let states = seq![initial, after_hot, after_trail];
    let plans = seq![hot_plan, trail_plan];
    assert forall|n: int| 0 <= n < plans.len() implies
        plan_ok(states[n], #[trigger] plans[n])
            && migration_effect(states[n], states[n + 1], plans[n]) by {
        if n == 0 {} else { assert(n == 1); }
    }
    legal_rollover_sequence(states, plans, 2);
    assert(after_trail.m == initial.m && stable(after_trail));
}

} // verus!
