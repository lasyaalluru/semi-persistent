// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conditional preservation by eligible oldest-prefix migration plans. Policy
//! cost and threshold accuracy is separate from this semantic theorem.

use super::mutation::*;
use super::*;

verus! {

pub enum Source { Trail, Hot }
pub enum Policy { Configured, ForceTrail, ForceHot, Adaptive, Defer }
pub struct Plan<T> {
    pub source: Source,
    pub count: nat,
    pub frames: Seq<Frame<T>>,
}

pub open spec fn eligible<T, R: View<T>>(s: R, source: Source) -> int {
    match source {
        Source::Trail => if s.trail() > 0 { s.trail() - 1 } else { 0 },
        Source::Hot => if s.unique() && s.hot() > 0 { s.hot() - 1 } else { s.hot() },
    }
}

/// A precomputed plan must name exactly the selected source frames, not just
/// fit a count bound. Empty frame meanings remain in this sequence.
pub open spec fn plan_ok<T, R: View<T>>(s: R, p: Plan<T>) -> bool {
    let offset = if p.source is Trail { s.cold() + s.hot() } else { s.cold() };
    p.count <= eligible(s, p.source)
        && p.frames == s.model().frames.subrange(offset, offset + p.count)
}

/// Effect of one completed migration, independent of policy selection. The
/// order may vary, but each source prefix must be legal in its current state.
pub open spec fn migration_effect<T, R: View<T>>(pre: R, out: R, plan: Plan<T>) -> bool {
    &&& physical(out) && writable(out) && capture_ok(out)
    &&& same_protocol(out, pre)
    &&& out.model() == pre.model()
    &&& out.canonical() == pre.canonical()
    &&& if plan.source is Trail {
        out.cold() == pre.cold() && out.hot() == pre.hot() + plan.count
            && out.trail() == pre.trail() - plan.count
    } else {
        out.cold() == pre.cold() + plan.count && out.hot() == pre.hot() - plan.count
            && out.trail() == pre.trail()
    }
}

pub trait Policies<T>: Mutations<T> {
    /// Thresholds choose a count; the semantic contract requires the complete
    /// source frame meanings and excludes the active writable frame.
    proof fn select_plan(pre: Self, policy: Policy, source: Source) -> (plan: Plan<T>)
        requires stable(pre),
        ensures plan_ok(pre, plan), plan.source == source,
            policy is Defer ==> plan.count == 0,
            policy is ForceTrail ==> if source is Trail {
                plan.count == eligible(pre, source)
            } else { plan.count == 0 },
            policy is ForceHot ==> if source is Hot {
                plan.count == eligible(pre, source)
            } else { plan.count == 0 };

    /// Completed migration composes local transform, append, retirement, and
    /// rebasing. It exports exact map equality and physical frame-count effects.
    proof fn migrate(pre: Self, plan: Plan<T>) -> (out: Self)
        requires stable(pre), plan_ok(pre, plan),
        ensures migration_effect(pre, out, plan),
            physical(out), writable(out), capture_ok(out), same_protocol(out, pre),
            out.model() == pre.model(), out.canonical() == pre.canonical(),
            if plan.source is Trail {
                out.cold() == pre.cold() && out.hot() == pre.hot() + plan.count
                    && out.trail() == pre.trail() - plan.count
            } else {
                out.cold() == pre.cold() + plan.count && out.hot() == pre.hot() - plan.count
                    && out.trail() == pre.trail()
            };

    /// Preserve the existing mark token coordinate contract. Token validity
    /// is still tested by the independent public restore predicate.
    proof fn make_token(pre: Self, coordinate: int) -> (token: Self::Token)
        requires stable(pre), 0 <= coordinate < pre.model().frames.len(),
        ensures Self::coordinate(token) == coordinate;
}

#[verifier::spinoff_prover]
pub proof fn apply_policy<T, R: Policies<T>>(pre: R, policy: Policy) -> (out: R)
    requires stable(pre),
    ensures stable(out), out.model() == pre.model(), same_protocol(out, pre),
        out.canonical() == pre.canonical(),
{
    let trail_plan = R::select_plan(pre, policy, Source::Trail);
    let after_trail = R::migrate(pre, trail_plan);
    let hot_plan = R::select_plan(after_trail, policy, Source::Hot);
    R::migrate(after_trail, hot_plan)
}

/// A trace records conditional interface effects, not a persistent ghost log.
/// Stable is required only at its beginning and is established inductively.
pub open spec fn legal_rollovers<T, R: View<T>>(states: Seq<R>, plans: Seq<Plan<T>>) -> bool {
    &&& states.len() == plans.len() + 1
    &&& forall|n: int| 0 <= n < plans.len() ==>
        plan_ok(states[n], #[trigger] plans[n])
            && migration_effect(states[n], states[n + 1], plans[n])
}

#[verifier::spinoff_prover]
pub proof fn legal_rollover_sequence<T, R: View<T>>(states: Seq<R>, plans: Seq<Plan<T>>, n: int)
    requires legal_rollovers(states, plans), stable(states[0]), 0 <= n < states.len(),
    ensures stable(states[n]), states[n].model() == states[0].model(),
        states[n].canonical() == states[0].canonical(), same_protocol(states[n], states[0]),
    decreases n,
{
    if n > 0 {
        legal_rollover_sequence(states, plans, n - 1);
        assert(plan_ok(states[n - 1], plans[n - 1]));
        assert(migration_effect(states[n - 1], states[n], plans[n - 1]));
    }
}

/// Configured, forced, adaptive and deferred policies may be interleaved.
/// Their selectors establish legality; the common preservation result then
/// makes each next call well-formed, without any commutativity assumption.
#[verifier::spinoff_prover]
pub proof fn apply_policy_sequence<T, R: Policies<T>>(pre: R, policies: Seq<Policy>) -> (out: R)
    requires stable(pre),
    ensures stable(out), out.model() == pre.model(), same_protocol(out, pre),
        out.canonical() == pre.canonical(),
    decreases policies.len(),
{
    if policies.len() == 0 { pre } else {
        let prefix = apply_policy_sequence(pre, policies.drop_last());
        apply_policy(prefix, policies.last())
    }
}

#[verifier::spinoff_prover]
pub proof fn mark_public<T, R: Policies<T>>(pre: R, policy: Policy) -> (result: (R, R::Token))
    requires stable(pre), pre.can_mark(),
    ensures stable(result.0), result.0.model() == mark(pre.model()), same_protocol(result.0, pre),
        R::coordinate(result.1) == pre.model().frames.len(),
{
    let opened = mark_core(pre);
    let out = apply_policy(opened, policy);
    let token = R::make_token(out, pre.model().frames.len() as int);
    (out, token)
}

/// Every rejected request preserves the state, not merely its current values.
/// The error projection must preserve the concrete mark guard order.
#[verifier::spinoff_prover]
pub proof fn try_mark_public<T, R: Policies<T>>(pre: R, policy: Policy) -> (result: (R, Result<R::Token, RequestError>))
    requires stable(pre),
    ensures stable(result.0),
        result.1 is Ok <==> pre.can_mark(),
        result.1 is Ok ==> result.0.model() == mark(pre.model())
            && R::coordinate(result.1->Ok_0) == pre.model().frames.len(),
        result.1 is Err ==> result.0 == pre && pre.mark_error() == Some(result.1->Err_0),
{
    R::mark_guard(pre);
    if pre.can_mark() {
        let (out, token) = mark_public(pre, policy);
        (out, Ok(token))
    } else { (pre, Err(pre.mark_error()->Some_0)) }
}

} // verus!
