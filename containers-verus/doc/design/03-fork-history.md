# Fork History / Branch-Cut Safety

> **Status (2026-09-18):** historical design. The shipped token is
> `history::GroupToken { history: ContainerId, generation: u64, depth: u32 }`
> (`VecToken` survives only as an alias), minted and validated by exactly one
> `History`, which is **provided from outside** the container: a group of one for
> a standalone column, one for a whole synchronized member set. No container owns
> a manager or has a token API of its own any more (§6, and doc 10 for the
> shipped shape). `frame_idx` below is today's `depth`; the branch model
> described here was replaced by generation stamps (doc 10, "Shipped design").
> The restore rule is doc 08 §1: semantics B — a restored token stays valid and
> the tokens above it die.


Branch-cut safety is the second correctness property of the semi-persistent
containers (the first is the reconstruction theorem of Chapter 1). It governs
*which tokens `restore` will accept*: a token naming a state that has been
discarded by an intervening `restore` must be rejected. Fork history is the
data structure that decides this. It is orthogonal to the reconstruction
mechanism: it adds a precondition to `restore`, it does not change how `restore`
rebuilds the contents.

## 1. The data structure

A verified token carries four fields:

```
VecToken { frame_idx: usize, branch_id: u32, depth: u32, container_id: ContainerId }
```

`mark` stamps `branch_id == forks.current_branch()`, and
`depth as usize == frame_idx == frames.len()`. `depth` and `frame_idx` are numerically
equal at creation but feed two different parts of the contract (§5).
The unverified reference implementation instead stores the corresponding
reconstruction coordinate as `frame_index: u32`; this is an API-layout
difference, not a semantic one.

`ContainerId` carries a hidden `u64` runtime payload drawn from a process-global
atomic counter; `restore` asserts `token.container_id == self.id` so ordinary
cross-container token misuse is rejected. The verified model proves equality
reflection, not global freshness. In default release builds the counter can
wrap after 2^64 allocations; `strict-id-exhaustion` makes that boundary fatal
and debug builds assert it.

Fork history itself is a forest stored as an append-only origin list:

```
ForkHistory { current_branch_id: u32, origins: Vec<ForkOrigin> }
ForkOrigin  { parent_branch_id: u32, fork_depth: u32 }
```

Branch `0` is the root. For `b >= 1`, `origins[b-1]` defines branch `b`'s parent
edge: `parent(b) := origins[b-1].parent_branch_id`, labeled with
`fork_depth(b) := origins[b-1].fork_depth`.

`mark` does not touch `forks`; it only reads `current_branch()` and the depth
into the token. A cut is recorded by `restore`, at its end, via `fork(p, d)`,
which performs exactly:

```
origins.push({ parent_branch_id: p, fork_depth: d });
current_branch_id := origins.len();   // the new branch id
```

So restoring branch `p` at depth `d` appends one origin entry and moves onto a
fresh child branch. The entry records the fact *branch `p` was restored at depth
`d` and a new branch diverged from it there*: along any path through the new
branch, `p` is retained only up to depth `d`.

## 2. Validity: the `is_valid` walk

```
is_valid(token, current_depth):
    if token.branch_id == current_branch_id { return token.depth <= current_depth }
    branch = current_branch_id
    while branch != token.branch_id {
        if branch == 0 { return false }
        origin = origins[branch - 1]
        if origin.parent_branch_id == token.branch_id {
            return token.depth <= origin.fork_depth
        }
        branch = origin.parent_branch_id
    }
    return token.depth <= current_depth
```

**Termination.** Each step sets `branch = origin.parent_branch_id`. The walk
terminates because `parent(b) < b` for every `b >= 1`: after a fork the new
branch id is `origins.len()` and its parent was a branch valid at the time,
hence strictly smaller. So the parent id strictly decreases toward `0`. This is
the well-formedness invariant `fh_wf` carried on `ForkHistory`; it gives the
spec walk its `decreases`.

## 3. The branch-safety theorem

Define the **current path** as the node sequence `current_branch_id`,
`parent(current_branch_id)`, `parent²(…)`, …, `0` (finite by `parent(b) < b`). A
branch `q` *is on the current path* iff it occurs in this sequence. For `q` on
the path, its **depth bound** is:

- `bound(q) := current_depth` if `q == current_branch_id` (the live frontier);
- `bound(q) := fork_depth(c)` if `q` is a strict ancestor, where `c` is `q`'s
  unique on-path child (the depth at which `q` was cut on the way to the current
  branch). The path is linear, so `c` is unique.

> **Theorem.** `is_valid(token, current_depth) = true` iff `token.branch_id` is
> on the current path and `token.depth <= bound(token.branch_id)`.

Contrapositive (when a token is rejected): a token is invalid iff either
(i) its branch is not on the current path (it lies in a subtree diverged away
from; the walk reaches branch `0`); or (ii) its branch is on the path but
`token.depth > bound(token.branch_id)` (it names a position past where that
branch was cut, or beyond the live frontier).

Note the asymmetry: a token on a *cut* branch `p` is not automatically invalid.
It is valid iff `token.depth <= fork_depth(c)` for `p`'s on-path child `c`. Cut
branches retain their at-or-below-the-cut tokens, which name genuine ancestors
of the current state.

## 4. Two layers and what is proved

- **Exec `ForkHistory`** is a faithful port of production:
  `current_branch_id: u32`, `origins: Vec<ForkOrigin>`, with the production
  bodies for `new`/`current_branch`/`fork`/`is_valid`. Ids and depths are
  concrete `u32` (§5), no ghost-`nat` projection.
- **Spec `fork_valid`** is a pure recursive `spec fn` over `(origins,
  current_branch, current_depth, token_branch, token_depth)` defining the walk
  declaratively, `decreases branch` (kept total with an explicit `parent >=
  branch` guard that `fh_wf` makes unreachable).

Proved in `fork_history.rs`:

1. **Refinement.** The exec `is_valid` while-loop computes exactly
   `fork_valid(...)`.
2. **Branch-safety theorem (§3).** `lemma_fork_valid_characterization` proves
   `fork_valid == reaches(current, tb) && td <= walk_bound(current, cd, tb)`
   for all cases (current branch, strict ancestors at any depth, off-path
   rejection), by induction on `branch` under `fh_wf` (which discharges the
   `parent >= branch` dead guards so the three recursions align). `reaches` and
   `walk_bound` are the spec fns realizing "on the current path" and "the
   branch's depth bound". `lemma_branch_cut` and
   `lemma_fork_valid_current_branch` remain as convenient specializations.
3. **`fh_wf` maintenance.** `new` establishes it; `fork` maintains it.

How this was wired into `Vec` while the container owned its own history: a
`forks: ForkHistory` field and an `id: ContainerId`, a token carrying the four
fields, `mark` stamping them, `restore` validating the restorable predicate and
recording the branch cut, and `wf` carrying `fh_wf`. Since the cut mutated only
the history field, Chapter 1's reconstruction proof was untouched.

**That wiring is gone (2026-09-18).** The history is external: a container has
no token type, no `mark`/`restore`, no validity query and no embedded
genealogy, and its whole versioning surface is the structural frame protocol.
One `History`, held by a `group::ForkHistory<M>` or by a consumer directly,
mints and validates tokens for the whole member set. The model in this chapter
is still the model — `GenStamps`, the depth, the branch cut — but it lives in
exactly one place. Read [doc 10](10-shared-fork-history.md) for the shipped
shape and its contracts.

## 5. Design decisions

**Ids and depths are concrete `u32`, not ghost `nat`.** Production uses `u32`,
and the bit-stealing id types are u31-effective (`define_id31!`: `u32` word, MSB
is the capture tag, `MAX_RAW = 0x7FFF_FFFF`). The model reasons on machine
integers directly; the walk arithmetic is simple `<` comparisons, so `nat`
would buy nothing for the SMT solver. A `u32` branch-id overflow at 4 G forks is
bounded in `fork`'s precondition (`origins.len() + 1 <= u32::MAX`) rather than
ghosted away, mirroring the `saved_len` treatment elsewhere.

That `origins` vector is history: the shipped `GenStamps` truncates (see §"Shipped
design" in [doc 10](10-shared-fork-history.md)), so a cut is one write and memory
is O(deepest depth ever reached) rather than one entry per restore for the
process's lifetime. The generation counter only grows, and it is the binding
mark/restore limit; `depth` falls back on restore and so caps concurrent nesting
only. A verified caller proves the bound; for an unverified one the runtime guard
(`check_precondition`, [Ch. 2 §2.5](02-trust-boundary.md)) traps rather than
letting a cast silently wrap.

**`depth` and `frame_idx` stay separate, with no equating wf clause.** They
are numerically equal at `mark` time but feed different axes of the contract:
`frame_idx` is the frame-stack slot the reconstruction mechanism rolls back
to; `depth` is what `is_valid` compares against `current_depth`/`fork_depth`.
Merging them would couple the reconstruction-index requirement to the validity
predicate. Keeping `frame_idx < frames.len()` (a structural precondition) and
validity (a separate precondition) independent is what keeps the reconstruction
theorem orthogonal to fork history.

**`ContainerId` is modeled minimally.** It is a `u64` payload with a
`spec id(): nat` that reads it, and an exec `eq` reflecting id equality —
transparent inside the crate and opaque to consumers, so both the projection and
the equality are proved (2026-09-18); only the atomic mint stays trusted. The
container check is not on the correctness-critical path (it only rejects
cross-container misuse, a caller error), so genuine end-to-end distinctness is
not proved. It
*could* be: a `tracked` monotone ghost counter threaded as the "next id" source
(advanced on each `new`, ensuring `fresh_id` exceeds all prior) expresses a
static integer generator in Verus without a global mutable static. That upgrade
is available if cross-container distinctness is ever wanted as a proved rather
than trusted property. See [Chapter 2](02-trust-boundary.md) for the trust
boundary `ContainerId` sits in.

## 6. Ownership inversion: the history is provided from outside (shipped 2026-09-18)

The layered design above left each `Vec` owning its own `GenStamps` and
`ContainerId`, with a synchronized group adding a shared `History` on top — so
genealogy state was duplicated per member and two authorities could advance a
depth. The inversion decided on 2026-09-08 fixed that by having the history own
its members. What shipped inverts it once more, and further: the history is
**provided from outside**, and a container is never its own authority.

`group::ForkHistory<M: Member>` owns one `History` and exactly one typed member.
A container implements `Member` — a structural protocol with no tokens in it
(`push_frame`, `reset_frame`, `restore_frame`, `pop_frame`, `depth_exec`, plus
the spec side `wf`/`depth_spec`/`can_push`/`model`/`archive`) — and the group
owns every token operation: `mark`, `restore`, `restore_and_pop`, `pop_scope`,
`mint_pushed`, `is_valid`, `depth`. A standalone container is a group of one,
`ForkHistory::new(Vec::new())`. `Pair<A, B>` composes two members and nests, so
a consumer with several columns either nests pairs or writes one borrowed
forwarding view and implements `Member` on it.

What the decided-but-superseded design got right, and what changed:

- **Typed, not `dyn`.** The 2026-09-08 plan used `Vec<Box<dyn SyncMember>>`, and
  that version shipped first and worked. It is deleted: a `dyn` group cannot
  state a member's model in its contract, so the lockstep theorem could only be
  stated per member rather than once. The typed group states it once, on
  `History::{mark,restore,restore_and_pop,pop}_member` over a borrowed `&mut M`,
  and every member type discharges it through `Member`'s contract.
- **`mark` and `restore` are still one write plus a fan-out.** The genealogy is
  touched only outside the fan-out, exactly as planned: `mark` mints once and
  pushes a frame on the member, `restore` validates once, resets the member and
  records the cut once.
- **Disjoint borrows still license the parallel path.** Each member owns its
  store, diff log and frame stack, so a wide member's fan-out can run on a
  `rayon::scope`; the e-graph's forwarding view does exactly that above a
  threshold, and it is glue in an unverified crate rather than a trusted twin of
  a verified function.

Misuse is refused rather than undefined: a frame pushed or popped on a member
behind the group's back drifts its depth away from the history's, and the next
group operation returns `None`/`false` and changes nothing.

Contracts, the member list and the acceptance suite:
[doc 10](10-shared-fork-history.md) and `tests/typed_group.rs`.

---
[← Table of Contents](00-table-of-contents.md)
