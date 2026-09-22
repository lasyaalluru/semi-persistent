// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Logical closure for the conditional top-down proof. These are mathematical
//! values, not fields added to the runtime container or maintained ghost state.

use vstd::prelude::*;

verus! {

pub struct Frame<T> {
    pub saved_len: nat,
    pub saved: Map<nat, T>,
}

pub struct Model<T> {
    pub live: Seq<T>,
    pub snapshots: Seq<Seq<T>>,
    pub frames: Seq<Frame<T>>,
}

/// Finite-map view of a bounded physical lookup. Adapters must separately
/// establish that the physical lookup has no captures outside this domain.
pub open spec fn bounded_saved_map<T>(len: nat, lookup: spec_fn(nat) -> Option<T>) -> Map<nat, T> {
    let indices = Seq::new(len, |i: int| i as nat).to_set();
    Map::new(indices.filter(|i: nat| lookup(i) is Some), |i: nat| lookup(i)->Some_0)
}

#[verifier::spinoff_prover]
pub proof fn bounded_saved_map_at<T>(len: nat, lookup: spec_fn(nat) -> Option<T>, i: nat)
    ensures bounded_saved_map(len, lookup).dom().contains(i) <==> i < len && lookup(i) is Some,
        bounded_saved_map(len, lookup).dom().contains(i) ==>
            bounded_saved_map(len, lookup)[i] == lookup(i)->Some_0,
{
    let indices = Seq::new(len, |j: int| j as nat);
    indices.to_set_ensures();
    if i < len {
        assert(indices[i as int] == i);
        assert(indices.to_set().contains(i));
    } else if indices.to_set().contains(i) {
        let j = choose|j: int| 0 <= j < indices.len() && indices[j] == i;
        assert(indices[j] == j as nat);
    }
}

pub open spec fn above<T>(s: Model<T>, f: int) -> Seq<T> {
    if f + 1 < s.frames.len() { s.snapshots[f + 1] } else { s.live }
}

pub open spec fn frame_ok<T>(frame: Frame<T>, snap: Seq<T>, newer: Seq<T>) -> bool {
    &&& frame.saved_len == snap.len()
    &&& forall|i: nat| #[trigger] frame.saved.dom().contains(i) ==> i < frame.saved_len
    &&& forall|i: nat| i < frame.saved_len ==> {
        if #[trigger] frame.saved.dom().contains(i) {
            frame.saved[i] == snap[i as int]
        } else {
            i < newer.len() && newer[i as int] == snap[i as int]
        }
    }
}

pub open spec fn snapshots_ok<T>(s: Model<T>) -> bool {
    &&& s.frames.len() == s.snapshots.len()
    &&& forall|f: int| 0 <= f < s.frames.len() ==>
        #[trigger] frame_ok(s.frames[f], s.snapshots[f], above(s, f))
}

pub open spec fn capture_first<T>(m: Map<nat, T>, i: nat, v: T) -> Map<nat, T> {
    if m.dom().contains(i) { m } else { m.insert(i, v) }
}

pub open spec fn capture<T>(s: Model<T>, i: nat) -> Model<T> {
    let f = s.frames.len() - 1;
    if s.frames.len() > 0 && i < s.frames[f].saved_len {
        Model { frames: s.frames.update(f, Frame {
            saved: capture_first(s.frames[f].saved, i, s.live[i as int]),
            ..s.frames[f]
        }), ..s }
    } else { s }
}

pub open spec fn write<T>(s: Model<T>, i: nat, v: T) -> Model<T> {
    Model { live: s.live.update(i as int, v), ..capture(s, i) }
}

pub open spec fn push<T>(s: Model<T>, v: T) -> Model<T> {
    Model { live: s.live.push(v), ..s }
}

pub open spec fn pop<T>(s: Model<T>) -> Model<T> {
    if s.live.len() == 0 { s } else {
        Model { live: s.live.drop_last(), ..capture(s, (s.live.len() - 1) as nat) }
    }
}

pub open spec fn mark<T>(s: Model<T>) -> Model<T> {
    Model { live: s.live,
        snapshots: s.snapshots.push(s.live),
        frames: s.frames.push(Frame { saved_len: s.live.len(), saved: Map::empty() }) }
}

pub open spec fn restore<T>(s: Model<T>, k: int) -> Model<T> {
    Model { live: s.snapshots[k], snapshots: s.snapshots.subrange(0, k),
        frames: s.frames.subrange(0, k) }
}

pub open spec fn empty<T>(live: Seq<T>) -> Model<T> {
    Model { live, snapshots: Seq::empty(), frames: Seq::empty() }
}

pub proof fn constructor<T>(live: Seq<T>)
    ensures snapshots_ok(empty(live)),
{}

#[verifier::spinoff_prover]
pub proof fn capture_preserves<T>(s: Model<T>, i: nat)
    requires snapshots_ok(s), i < s.live.len(),
    ensures snapshots_ok(capture(s, i)),
        capture(s, i).live == s.live,
        capture(s, i).snapshots == s.snapshots,
        capture(s, i).frames.len() == s.frames.len(),
        s.frames.len() > 0 && i < s.frames[s.frames.len() - 1].saved_len ==>
            capture(s, i).frames[s.frames.len() - 1].saved.dom().contains(i),
{
    let out = capture(s, i);
    let top = s.frames.len() - 1;
    assert forall|f: int| 0 <= f < out.frames.len() implies
        #[trigger] frame_ok(out.frames[f], out.snapshots[f], above(out, f)) by {
        assert(frame_ok(s.frames[f], s.snapshots[f], above(s, f)));
        if f == top && i < s.frames[f].saved_len {
            assert forall|j: nat| j < out.frames[f].saved_len implies
                if #[trigger] out.frames[f].saved.dom().contains(j) {
                    out.frames[f].saved[j] == out.snapshots[f][j as int]
                } else {
                    j < above(out, f).len()
                        && above(out, f)[j as int] == out.snapshots[f][j as int]
                } by {
                assert(s.frames[f].saved.dom().contains(j) ||
                    j < above(s, f).len() && above(s, f)[j as int] == s.snapshots[f][j as int]);
            }
        }
    }
}

/// Only the active layer changes. Every changed or removed saved-domain cell
/// must already be in its capture map; arbitrary regrowth values are allowed.
#[verifier::spinoff_prover]
pub proof fn change_live_preserves<T>(s: Model<T>, live: Seq<T>)
    requires snapshots_ok(s),
        s.frames.len() > 0 ==> forall|i: nat|
            i < s.frames[s.frames.len() - 1].saved_len
                && !(#[trigger] s.frames[s.frames.len() - 1].saved.dom().contains(i)) ==>
            i < s.live.len() && i < live.len() && live[i as int] == s.live[i as int],
    ensures snapshots_ok(Model { live, ..s }),
{
    let out = Model { live, ..s };
    assert forall|f: int| 0 <= f < out.frames.len() implies
        #[trigger] frame_ok(out.frames[f], out.snapshots[f], above(out, f)) by {
        assert(frame_ok(s.frames[f], s.snapshots[f], above(s, f)));
        assert forall|i: nat| i < out.frames[f].saved_len implies
            if #[trigger] out.frames[f].saved.dom().contains(i) {
                out.frames[f].saved[i] == out.snapshots[f][i as int]
            } else {
                i < above(out, f).len() && above(out, f)[i as int] == out.snapshots[f][i as int]
            } by {
            assert(s.frames[f].saved.dom().contains(i) ||
                i < above(s, f).len() && above(s, f)[i as int] == s.snapshots[f][i as int]);
            if f + 1 == s.frames.len() && !s.frames[f].saved.dom().contains(i) {
                assert(f == s.frames.len() - 1);
                assert(i < s.frames[s.frames.len() - 1].saved_len);
                assert(!s.frames[s.frames.len() - 1].saved.dom().contains(i));
                assert(i < live.len() && live[i as int] == s.live[i as int]);
            }
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn write_preserves<T>(s: Model<T>, i: nat, v: T)
    requires snapshots_ok(s), i < s.live.len(),
    ensures snapshots_ok(write(s, i, v)), write(s, i, v).snapshots == s.snapshots,
{
    capture_preserves(s, i);
    let out = capture(s, i);
    if s.frames.len() > 0 {
        let f = s.frames.len() - 1;
        assert(frame_ok(out.frames[f], out.snapshots[f], above(out, f)));
        assert forall|j: nat| j < out.frames[f].saved_len && !out.frames[f].saved.dom().contains(j)
            implies j < out.live.len() && j < s.live.update(i as int, v).len()
                && #[trigger] s.live.update(i as int, v)[j as int] == out.live[j as int] by {
            assert(j != i);
        }
    }
    change_live_preserves(capture(s, i), s.live.update(i as int, v));
}

#[verifier::spinoff_prover]
pub proof fn push_preserves<T>(s: Model<T>, v: T)
    requires snapshots_ok(s),
    ensures snapshots_ok(push(s, v)), push(s, v).frames == s.frames,
        push(s, v).snapshots == s.snapshots,
        s.frames.len() > 0 && s.live.len() < s.frames[s.frames.len() - 1].saved_len ==>
            s.frames[s.frames.len() - 1].saved.dom().contains(s.live.len()),
{
    if s.frames.len() > 0 {
        assert(frame_ok(s.frames[s.frames.len() - 1], s.snapshots[s.frames.len() - 1], above(s, s.frames.len() - 1)));
        assert(frame_ok(s.frames[s.frames.len() - 1], s.snapshots[s.frames.len() - 1], s.live));
    }
    change_live_preserves(s, s.live.push(v));
}

#[verifier::spinoff_prover]
pub proof fn pop_preserves<T>(s: Model<T>)
    requires snapshots_ok(s),
    ensures snapshots_ok(pop(s)), pop(s).snapshots == s.snapshots,
{
    if s.live.len() > 0 {
        capture_preserves(s, (s.live.len() - 1) as nat);
        let out = capture(s, (s.live.len() - 1) as nat);
        if s.frames.len() > 0 {
            let f = s.frames.len() - 1;
            assert(frame_ok(out.frames[f], out.snapshots[f], above(out, f)));
            assert forall|j: nat| j < out.frames[f].saved_len && !out.frames[f].saved.dom().contains(j)
                implies j < out.live.len() && j < s.live.drop_last().len()
                    && #[trigger] s.live.drop_last()[j as int] == out.live[j as int] by {
                assert(j != s.live.len() - 1);
            }
        }
        change_live_preserves(capture(s, (s.live.len() - 1) as nat), s.live.drop_last());
    }
}

#[verifier::spinoff_prover]
pub proof fn mark_preserves<T>(s: Model<T>)
    requires snapshots_ok(s),
    ensures snapshots_ok(mark(s)),
{
    let out = mark(s);
    assert forall|f: int| 0 <= f < out.frames.len() implies
        #[trigger] frame_ok(out.frames[f], out.snapshots[f], above(out, f)) by {
        if f < s.frames.len() {
            assert(frame_ok(s.frames[f], s.snapshots[f], above(s, f)));
            assert(above(out, f) == above(s, f));
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn restore_preserves<T>(s: Model<T>, k: int)
    requires snapshots_ok(s), 0 <= k < s.frames.len(),
    ensures snapshots_ok(restore(s, k)),
{
    let out = restore(s, k);
    assert forall|f: int| 0 <= f < out.frames.len() implies
        #[trigger] frame_ok(out.frames[f], out.snapshots[f], above(out, f)) by {
        assert(frame_ok(s.frames[f], s.snapshots[f], above(s, f)));
        assert(above(out, f) == above(s, f));
    }
}

pub open spec fn agrees<T>(buffer: Seq<T>, layer: Seq<T>) -> bool {
    forall|i: int| 0 <= i < buffer.len() && i < layer.len() ==>
        #[trigger] buffer[i] == layer[i]
}

pub open spec fn apply<T>(m: Map<nat, T>, buffer: Seq<T>) -> Seq<T> {
    Seq::new(buffer.len(), |i: int| if m.dom().contains(i as nat) { m[i as nat] } else { buffer[i] })
}

/// Oldest frame applies last. This specification describes composition only;
/// it does not require a runtime per-frame loop for batched pair replay.
pub open spec fn apply_range<T>(frames: Seq<Frame<T>>, lo: int, hi: int, buffer: Seq<T>) -> Seq<T>
    recommends 0 <= lo <= hi <= frames.len(),
    decreases hi - lo,
{
    if lo < hi {
        apply(frames[lo].saved, apply_range(frames, lo + 1, hi, buffer))
    } else { buffer }
}

#[verifier::spinoff_prover]
pub proof fn frame_step<T>(frame: Frame<T>, snap: Seq<T>, newer: Seq<T>, buffer: Seq<T>)
    requires frame_ok(frame, snap, newer), agrees(buffer, newer),
    ensures agrees(apply(frame.saved, buffer), snap),
        apply(frame.saved, buffer).len() == buffer.len(),
{
    let out = apply(frame.saved, buffer);
    assert forall|i: int| 0 <= i < out.len() && i < snap.len() implies
        #[trigger] out[i] == snap[i] by {
        assert(frame.saved.dom().contains(i as nat) ||
            i < newer.len() && newer[i] == snap[i]);
    }
}

#[verifier::spinoff_prover]
pub proof fn range_len<T>(frames: Seq<Frame<T>>, lo: int, hi: int, buffer: Seq<T>)
    requires 0 <= lo <= hi <= frames.len(),
    ensures apply_range(frames, lo, hi, buffer).len() == buffer.len(),
    decreases hi - lo,
{
    if lo < hi { range_len(frames, lo + 1, hi, buffer); }
}

#[verifier::spinoff_prover]
pub proof fn range_split<T>(frames: Seq<Frame<T>>, lo: int, mid: int, hi: int, buffer: Seq<T>)
    requires 0 <= lo <= mid <= hi <= frames.len(),
    ensures apply_range(frames, lo, mid, apply_range(frames, mid, hi, buffer))
        == apply_range(frames, lo, hi, buffer),
    decreases mid - lo,
{
    if lo < mid { range_split(frames, lo + 1, mid, hi, buffer); }
}

#[verifier::spinoff_prover]
pub proof fn range_reconstructs<T>(s: Model<T>, lo: int, hi: int, buffer: Seq<T>)
    requires snapshots_ok(s), 0 <= lo < hi <= s.frames.len(),
        agrees(buffer, above(s, hi - 1)),
    ensures agrees(apply_range(s.frames, lo, hi, buffer), s.snapshots[lo]),
        apply_range(s.frames, lo, hi, buffer).len() == buffer.len(),
    decreases hi - lo,
{
    if lo + 1 < hi { range_reconstructs(s, lo + 1, hi, buffer); }
    assert(frame_ok(s.frames[lo], s.snapshots[lo], above(s, lo)));
    frame_step(s.frames[lo], s.snapshots[lo], above(s, lo),
        apply_range(s.frames, lo + 1, hi, buffer));
    range_len(s.frames, lo, hi, buffer);
}

/// A resized buffer can contain arbitrary new cells; shared-prefix agreement
/// with the original live data is the only value premise.
#[verifier::spinoff_prover]
pub proof fn reconstructs_target<T>(s: Model<T>, k: int, buffer: Seq<T>)
    requires snapshots_ok(s), 0 <= k < s.frames.len(),
        buffer.len() == s.snapshots[k].len(), agrees(buffer, s.live),
    ensures apply_range(s.frames, k, s.frames.len() as int, buffer) == s.snapshots[k],
{
    range_reconstructs(s, k, s.frames.len() as int, buffer);
    assert(apply_range(s.frames, k, s.frames.len() as int, buffer) =~= s.snapshots[k]);
}

/// Internal coordinates only. The physical/public composition must also check
/// the existing token-validity predicate; this model does not replace it.
pub enum Action<T> {
    Set(nat, T), Push(T), Pop, Mark, Restore(int), Migrate,
}

pub open spec fn enabled<T>(s: Model<T>, action: Action<T>) -> bool {
    match action {
        Action::Set(i, _) => i < s.live.len(),
        Action::Restore(k) => 0 <= k < s.frames.len(),
        _ => true,
    }
}

pub open spec fn step<T>(s: Model<T>, action: Action<T>) -> Model<T> {
    match action {
        Action::Set(i, v) => write(s, i, v),
        Action::Push(v) => push(s, v),
        Action::Pop => pop(s),
        Action::Mark => mark(s),
        Action::Restore(k) => restore(s, k),
        Action::Migrate => s,
    }
}

#[verifier::spinoff_prover]
pub proof fn step_preserves<T>(s: Model<T>, action: Action<T>)
    requires snapshots_ok(s), enabled(s, action),
    ensures snapshots_ok(step(s, action)),
{
    match action {
        Action::Set(i, v) => write_preserves(s, i, v),
        Action::Push(v) => push_preserves(s, v),
        Action::Pop => pop_preserves(s),
        Action::Mark => mark_preserves(s),
        Action::Restore(k) => restore_preserves(s, k),
        Action::Migrate => {},
    }
}

pub open spec fn executes<T>(states: Seq<Model<T>>, actions: Seq<Action<T>>) -> bool {
    &&& states.len() == actions.len() + 1
    &&& forall|n: int| 0 <= n < actions.len() ==>
        enabled(states[n], #[trigger] actions[n]) && states[n + 1] == step(states[n], actions[n])
}

#[verifier::spinoff_prover]
pub proof fn sequence_preserves<T>(states: Seq<Model<T>>, actions: Seq<Action<T>>, n: int)
    requires executes(states, actions), snapshots_ok(states[0]), 0 <= n < states.len(),
    ensures snapshots_ok(states[n]),
    decreases n,
{
    if n > 0 {
        sequence_preserves(states, actions, n - 1);
        assert(states[n] == step(states[n - 1], actions[n - 1]));
        step_preserves(states[n - 1], actions[n - 1]);
    }
}

#[verifier::spinoff_prover]
pub proof fn mutate_then_restore_older<T>(s: Model<T>, k: int, j: int, i: nat, value: T)
    requires snapshots_ok(s), 0 <= j < k < s.frames.len(), i < s.snapshots[k].len(),
    ensures
        snapshots_ok(restore(write(restore(s, k), i, value), j)),
        restore(write(restore(s, k), i, value), j).live == s.snapshots[j],
        restore(write(restore(s, k), i, value), j).snapshots == s.snapshots.subrange(0, j),
        restore(write(restore(s, k), i, value), j).frames == s.frames.subrange(0, j),
{
    restore_preserves(s, k);
    write_preserves(restore(s, k), i, value);
    restore_preserves(write(restore(s, k), i, value), j);
    assert(restore(write(restore(s, k), i, value), j).snapshots =~= s.snapshots.subrange(0, j));
    assert(restore(write(restore(s, k), i, value), j).frames =~= s.frames.subrange(0, j));
}

#[verifier::spinoff_prover]
pub proof fn pop_regrow_restore<T>(s: Model<T>, value: T)
    requires snapshots_ok(s), s.live.len() > 0,
    ensures snapshots_ok(restore(push(pop(mark(s)), value), s.frames.len() as int)),
        restore(push(pop(mark(s)), value), s.frames.len() as int).live == s.live,
{
    mark_preserves(s);
    pop_preserves(mark(s));
    push_preserves(pop(mark(s)), value);
    restore_preserves(push(pop(mark(s)), value), s.frames.len() as int);
}

} // verus!
