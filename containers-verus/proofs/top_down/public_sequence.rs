// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Closure of the complete conditional public operation family under arbitrary
//! legal interleaving. The trace is a proof parameter, not runtime bookkeeping.

use super::mutation::*;
use super::policy::*;
use super::*;

verus! {

pub enum Operation<T, Token> {
    Set(nat, T), Push(T), Pop, Mark(Policy), Restore(Token), Rollover(Policy),
}

pub open spec fn legal<T, R: Limits<T>>(pre: R, op: Operation<T, R::Token>) -> bool {
    match op {
        Operation::Set(i, _) => i < pre.model().live.len(),
        Operation::Push(_) => pre.can_grow(),
        Operation::Pop => true,
        Operation::Mark(_) => pre.can_mark(),
        Operation::Restore(token) => pre.token_valid(token),
        Operation::Rollover(_) => true,
    }
}

pub open spec fn logical_result<T, R: View<T>>(pre: R, op: Operation<T, R::Token>) -> Model<T> {
    match op {
        Operation::Set(i, v) => write(pre.model(), i, v),
        Operation::Push(v) => push(pre.model(), v),
        Operation::Pop => pop(pre.model()),
        Operation::Mark(_) => mark(pre.model()),
        Operation::Restore(token) => restore(pre.model(), R::coordinate(token)),
        Operation::Rollover(_) => pre.model(),
    }
}

/// Do not assume snapshot correctness at the output: derive it from the
/// logical result of each operation and the correctness of its input.
pub open spec fn effect<T, R: View<T>>(pre: R, out: R, op: Operation<T, R::Token>) -> bool {
    physical(out) && writable(out) && capture_ok(out) && same_protocol(out, pre)
        && out.model() == logical_result(pre, op)
}

#[verifier::spinoff_prover]
pub proof fn execute_one<T, R: Policies<T> + Runtime<T>>(pre: R, op: Operation<T, R::Token>) -> (out: R)
    requires stable(pre), legal(pre, op),
    ensures stable(out), effect(pre, out, op),
{
    match op {
        Operation::Set(i, v) => set_public(pre, i, v),
        Operation::Push(v) => push_public(pre, v),
        Operation::Pop => pop_public(pre).0,
        Operation::Mark(policy) => mark_public(pre, policy).0,
        Operation::Restore(token) => restore_public(pre, token),
        Operation::Rollover(policy) => apply_policy(pre, policy),
    }
}

#[verifier::spinoff_prover]
pub proof fn effect_preserves<T, R: Policies<T> + Runtime<T>>(pre: R, out: R, op: Operation<T, R::Token>)
    requires stable(pre), legal(pre, op), effect(pre, out, op),
    ensures stable(out),
{
    match op {
        Operation::Set(i, v) => write_preserves(pre.model(), i, v),
        Operation::Push(v) => push_preserves(pre.model(), v),
        Operation::Pop => pop_preserves(pre.model()),
        Operation::Mark(_) => mark_preserves(pre.model()),
        Operation::Restore(token) => {
            R::token_bounds(pre, token);
            restore_preserves(pre.model(), R::coordinate(token));
        },
        Operation::Rollover(_) => {},
    }
}

pub open spec fn legal_execution<T, R: Limits<T>>(states: Seq<R>, ops: Seq<Operation<T, R::Token>>) -> bool {
    &&& states.len() == ops.len() + 1
    &&& forall|n: int| 0 <= n < ops.len() ==>
        legal(states[n], #[trigger] ops[n]) && effect(states[n], states[n + 1], ops[n])
}

#[verifier::spinoff_prover]
pub proof fn complete_sequence<T, R: Policies<T> + Runtime<T>>(states: Seq<R>, ops: Seq<Operation<T, R::Token>>, n: int)
    requires legal_execution(states, ops), stable(states[0]), 0 <= n < states.len(),
    ensures stable(states[n]), same_protocol(states[n], states[0]),
        n < ops.len() && ops[n] is Restore ==>
            states[n + 1].model().live == states[n].model().snapshots[R::coordinate(ops[n]->Restore_0)]
            && states[n + 1].model().frames
                == states[n].model().frames.subrange(0, R::coordinate(ops[n]->Restore_0))
            && states[n + 1].model().snapshots
                == states[n].model().snapshots.subrange(0, R::coordinate(ops[n]->Restore_0)),
    decreases n,
{
    if n > 0 {
        complete_sequence(states, ops, n - 1);
        assert(legal(states[n - 1], ops[n - 1]) && effect(states[n - 1], states[n], ops[n - 1]));
        effect_preserves(states[n - 1], states[n], ops[n - 1]);
    }
    if n < ops.len() && ops[n] is Restore {
        assert(effect(states[n], states[n + 1], ops[n]));
        R::token_bounds(states[n], ops[n]->Restore_0);
    }
}

} // verus!
