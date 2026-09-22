# Token reuse, restore semantics, and the capture-tag recompute

What `restore` does to the frame stack, why reusing a token is caught, how the
capture-tag bits are reconstructed, and how a reusable-checkpoint variant would
differ. Grounded in production (`vec.rs`, `diff_store.rs`, `token.rs`) and the
verified port.

## 1. What `restore(t)` does to the frame stack

The token manager is a `history::Genealogy`: a `ContainerId` naming the manager
plus one generation stamp per live depth (`GenStamps`: a live length and a
counter that hands out each stamp once). A `History` pairs it with the group
depth, and it is **always provided from outside** the containers (doc 10): a
standalone `Vec` or `AppendOnlyVec` is a group of one,
`group::ForkHistory::new(Vec::new())`, and a synchronized member set is one
history over one forwarding member. Containers themselves have neither a manager
nor a token API — that changed on 2026-09-18, and this chapter's operations are
the group's. The token type is the same on both paths:

```rust
pub struct GroupToken { history: ContainerId, generation: u64, depth: u32 }
pub type VecToken = GroupToken;
```

`mark()` at frame-stack depth `d` pushes frame `d` and then mints
`GroupToken { history: <this manager>, generation: <fresh stamp>, depth: d }`.
With no outstanding mark, the first token therefore has depth 0.

**`restore(t)` is a reset to the checkpoint** (semantics B, the user's
ruling of 2026-09-17):

1. **provenance**: `genealogy.is_valid(&t)` — `t.history` names this
   manager and the live stamp at `t.depth` is `t.generation`; otherwise
   refuse (`"token is foreign, stale or consumed"`) without mutating;
2. assert `t.depth < frames.len()` (the frame is still live) and depth
   headroom;
3. resize the store to `frames[t.depth].saved_len`, then replay the diff
   strata `t.depth..` (undoing them);
4. drop frames `t.depth..` and **reopen frame `t.depth` empty**: the
   writable frame is the token's own again (the tiered `Vec` does this as
   its pop core followed by a structural frame push with a *deferred*
   rollover — a header push that converts no history, so the parent
   stratum the pop core just made writable is not re-migrated on every
   restore; the next `mark` applies the tier policy once, as it always
   did. The snapshot at `t.depth` is unchanged, so the snapshot stack is
   the old prefix of length `t.depth + 1`);
5. `finish_restore(…)` recomputes the capture tags (§2);
6. **the cut**: `genealogy.cut_from(t.depth + 1)` sets the live length to
   `t.depth + 1`, so `t` stays valid and every token minted after it is dead
   for good.

Afterwards the depth is `t.depth + 1`, the view equals `snapshots[t.depth]`,
later writes accumulate in frame `t.depth`'s stratum again, and `restore(t)`
can be repeated: each time it undoes exactly what happened since the
checkpoint.

**`pop_scope()` drops the open top frame**: undo its stratum, remove it,
make the parent writable again, and cut the genealogy at the popped depth
(that frame's token dies). `try_pop_scope` reports `Untracked` or
`NoOpenFrame` instead of refusing.

**`restore_and_pop(t)` is `restore(t)` then `pop_scope()`, fused**: the
contents are the snapshot at `t`, the depth is `t.depth`, `t` and every
later token die. This is the SMT-LIB `pop` to the level below `t`, what the
interpreter's `(pop)` does, and exactly what the legacy `containers/`
restore always was — and it runs on the one pop core the legacy restore
used, so it costs the same. Spelled as two calls it costs more: the
restore's pop core promotes the parent stratum and recomputes its capture
tags, the reopen seals it again (clearing the tags over it), and the pop
reopens it once more — two extra walks over the parent stratum per pop,
which the benchmarks of 2026-09-18 showed as 1.4–2.1× on one-frame cases
and 1.5× on the SMT store traces. Every group operation is total, so
`restore_and_pop` returns `false` on a dead or foreign token rather than
trapping.
The SAT core's backjump is the bare `restore(t)`: it stays in the
checkpoint's scope and asserts there.

## 2. How the capture tags are reconstructed (not stored)

The diff log stores **clean values**: `from_repr` strips the tag at capture
time. `restore_entry` writes them back via `into_repr`, which sets the tag
clear. The tag is never recovered from the diff, and must not be, because the
tag is **frame-relative bookkeeping**: "has slot `i` been captured in the
*currently active* frame yet" (first-write-wins; `capture` only logs if the tag
is clear).

Restore recomputes the tags for the frame it lands in, in three steps:

- `restore_entry` clears every tag it touches (via `into_repr`);
- **`finish_restore`** walks the surviving parent stratum's diff indices and
  sets exactly those tags (`for (_, idx) in current_frame_diffs { set_tag(idx) }`),
  re-establishing "captured-in-the-now-top(parent)-frame ⟺ appears in the
  parent's diff slice";
- (symmetric: `prepare_mark` clears the parent's tags when a child is marked,
  so the child starts fresh, which is why they must be put back on restore).

This `finish_restore` rescan is O(parent stratum) on top of the O(replayed
diff) of the rollback. The `+p` term is not intrinsic to semi-persistence: the
per-cell capture-depth alternative restores old depths during replay and
avoids the rescan. It is a consequence of this crate's one-bit flag protocol,
which derives parent flags from the surviving diff. The architectural trade,
including what remains unbenchmarked, is in
[Design Alternatives, Part 2](06-restore-regrow-alternatives.md#e-per-cell-capture-depth-alternative).

The parent's tags must be *set*, not left at zero. You land in the parent
mid-stratum; the parent already captured some slots before `t` was marked;
those slots are genuinely captured-in-parent, so a later `set` to one of them
must not re-log. `prepare_mark` had cleared them to 0 while the child was
alive, so the correct value (1) must be restored; leaving them at 0 would
double-capture. `finish_restore` does exactly this.

The one case where "all tags zero" is correct is `t.depth == 0`
(restoring to the very first frame pops the whole stack): there is no parent,
the diff log truncates to empty, `finish_restore([])` sets nothing, and the
bridge invariant is vacuous (gated on `frames.len() > 0`). This is the
degenerate end of the general rule.

## 3. Which tokens a container accepts

`group.is_valid(t)` means "restorable now": provenance and generation (the
manager's answer), then frame liveness. It is the group's question, not a
container's — since 2026-09-18 no container has a token API of its own, and the
history a group owns is the only authority. Under semantics B:

- **the restored checkpoint stays valid**: `restore(t)` leaves the stamp at
  `t.depth` live, so `t` restores again and again;
- **everything above it dies**: a restore to `t` sets the live length to
  `t.depth + 1`, so a token minted after `t` (deeper, or later at the same
  depth after a pop) fails the liveness half or holds a stamp the table no
  longer shows;
- **a popped frame's token dies**: `pop_scope` cuts at the popped depth;
- **a re-mark never revives a dead token**: stamps come from a counter that
  only grows, so a token's stamp is forever below the counter and any later
  stamp at its depth is at or above it (`GenStamps::mint_at`'s
  postcondition);
- **a foreign token is refused** whatever its numbers: it names another
  manager.

```rust
// A standalone column is a group of one: the history comes from outside.
let mut g = ForkHistory::new(VecI::<Id, u32, true>::new());
g.member.push(10); g.member.push(20);
let parent = g.mark(Never).expect("headroom");  // frame 0
g.member.set(1, 21);                            // parent-frame diff
let child = g.mark(Never).expect("headroom");   // frame 1
g.member.set(0, 99);                            // child-frame diff
assert!(g.restore(child));      // → [10,21], frame 1 open again, depth 2
assert!(g.is_valid(child));
g.member.set(0, 7);
assert!(g.restore(child));      // → [10,21] again
assert!(g.pop_scope());         // drop frame 1: depth 1, back in frame 0
assert!(!g.is_valid(child));
assert!(g.is_valid(parent));
```

Element operations read as before because `ForkHistory` derefs to its member;
`g.member` is the explicit spelling. Every group operation is total: `mark`
returns `None` and the rest return `false` rather than trapping, so a refusal is
a value to check.

**The retained unverified reference** (legacy `containers/`) validates on a
branch model with the same inclusive rule (a token at the fork depth stays
valid) but its restore pops the frame, so a later mark at that depth
aliases the old token. The verified crate's restore keeps the frame, so
there is nothing to alias. The conformance harnesses pair the two by
asserting, after every verified restore, that the checkpoint is still valid
and then popping the verified side, which is exactly the legacy operation.

## 4. Tokens are values, not capabilities

`GroupToken: Copy`. Under semantics B a token is valid for exactly as long
as its frame exists, which the stamp table tracks, so there is nothing an
affine (by-move) token would add: reusing a token is the intended way to
retry from a checkpoint, and a token whose frame was popped is refused at
runtime — `restore` returns `false` and moves nothing.

## 5. What the real consumers do

The e-graph interpreter is strict LIFO: `(push)` marks and stacks the
token, `(pop)` is `restore(t)` followed by `pop_scope()` — back to the
checkpoint, then the scope is dropped and the token dies. The SAT core's
backjump is `restore(t)` alone: the level's frame stays open and the solver
continues in it, minting the next level with a fresh `mark`. A retry loop
(try, fail, go back) restores the same token each time and never re-marks.
Nothing in the consumers re-marks after a restore, and nothing pops without
restoring first.

## 6. The two semantics, and why B is the primitive

Two coherent readings of "restore to `t`" exist. **A, pop**: reconstruct the
state at `t` and remove frame `t.depth`; the writable frame becomes the
parent and `t` is dead (the legacy structure, and the verified crate until
2026-09-17). **B, reset to checkpoint**: reconstruct the state at `t`, keep
frame `t.depth` open and empty, cut everything above; `t` stays valid (what
ships). B is the primitive because A is B followed by dropping an empty top
frame (`pop_scope`), and because B's restore never touches the parent
frame: reopening a sealed parent (the `restore_hot`/`restore_cold`
survivor re-materialisation) is paid only by `pop_scope`. Consumers spell
SMT-LIB `pop` as `restore(t); pop_scope()`, a backjump as `restore(t)`
alone, and retry loops reuse one token.

The original sketch of this alternative, kept for the record:


`restore(t)` could instead keep frame `t` live with an empty stratum and all its
capture bits zero (re-enter the marked frame fresh), so the *same* `t` can be
restored to repeatedly. After such a `restore(t)` the active frame is `t` itself
(not the parent), its stratum is empty, and `view() == snapshots[t]`; subsequent
mutations log into frame `t`'s fresh stratum, and `restore(t)` again rolls them
back. This is a "reset to checkpoint" / reusable savepoint semantics, versus the
current "pop the scope" semantics.

It would take:

1. `restore` truncates to `t.depth + 1` (keep frame `t`), not
   `t.depth`; its stratum becomes empty — and the genealogy cut starts at
   `t.depth + 1` too, so `t` stays valid (under the shipped rule the cut
   starts *at* `t.depth` and `t` is consumed; see §1 step 6).
2. A `prepare_mark`-style tag clear over `[0, saved_len)` so frame `t` starts
   with zero capture bits (the bridge then holds with an empty top stratum,
   `captured()[j] ⟺ false`).
3. `finish_restore` then sets no tags. So this is actually *simpler* on the tag
   front: "all zero" is exactly right for this semantics, because here the top
   frame really is freshly marked.
4. Fork-history must not pop `t`'s branch: reusability means `t` survives, so
   either no `fork()` cut or a cut that still admits `t`. This needs the
   branch-cut model rethought (currently `fork` plus the frame-index pop is
   what invalidates `t`).

Under the current pop semantics, mutations after `restore(t)` record into the
parent's stratum. That is correct for LIFO scoping: you popped scope `t`, you
are back in the enclosing scope, and edits belong there. Under the reusable
semantics they would record into the re-entered frame `t`, which is what a
"retry from checkpoint" loop (speculative execution) wants.

The recommendation is to keep the pop semantics as the default (it matches the
LIFO consumer and is verified) and, if a reusable checkpoint is ever wanted, add
it as a separate `reset_to(&t)` (by-ref, non-consuming) distinct from
`restore(t)` (by-move, consuming), rather than changing `restore`'s meaning.
`reset_to` is arguably easier to verify (empty top stratum ⇒ trivial bridge) but
needs the fork-history model extended to keep `t` valid across repeated resets.

## 7. Verus tie-in

The tag-recompute mechanism (§2) is exactly the **capture-flag bridge** clause
of `wf`: `store.captured()[j] ⟺ captured_in_range(diffs, top.diff_start, n, j)`.
`finish_restore`'s verified postcondition re-derives the tags from the parent
stratum's diff slice; `restore`'s proof re-establishes the bridge via
`lemma_captured_subrange`. The reusable-checkpoint variant (§6) would make the
top stratum empty, so the bridge degenerates to `captured()[j] ⟺ false` over
`[0, saved_len)`, a strictly simpler obligation, but the fork-history validity
theorem (`lemma_fork_valid_characterization`) would need an analogue for "t
survives its own restore".

---
[← Table of Contents](00-table-of-contents.md)
