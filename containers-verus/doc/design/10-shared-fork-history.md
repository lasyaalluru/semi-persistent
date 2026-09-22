# Shared fork history

Lets a group of hard-synced semi-persistent vectors share one branch history and
one restore token instead of each carrying its own. This is a **wall-clock and
memory** optimization aimed at the e-graph, which runs ~10 vectors in permanent
lockstep. It is a design doc; CI gates are the source of truth.

## Purpose

When `N` vectors always `mark` and `restore` together — at the same decision
levels, on the same branches, forever — their branch genealogies are *identical*
and their restore tokens agree on everything but `container_id`. Yet each vector
maintains its own `ForkHistory`, its own depth bookkeeping, and validates its
own token on every restore. That is `N` copies of one tree and `N` genealogy
walks per backjump. This removes the redundancy: one shared history, one token,
per-vector work only where the data actually differs.

The e-graph's hard-synced set: two union-find columns (`parent`, `rank`), the
three sparse-set vectors (`dense`, `sparse`, `indices`), the class ring, the
use-list arena's two vectors, the min-pool, and the per-kind node caches. All
mark/restore in lockstep with the decision level.

## Current representation and where the redundancy is

Each `Vec<T, I, S, TRACK>` owns:

- `diff_log: Vec<(T, I)>` — **per-vector** (different values). Not shareable.
- `frames: Vec<Frame<I>>` where `Frame = { saved_len, diff_start }` —
  **per-vector** contents (each vector's length and stratum differ), but the
  **stack depth is shared** (all synced vectors are at the same level).
- capture state (bits/counter) — **per-vector** (different cells).
- `forks: ForkHistory` + depth + token counters — **fully redundant**: identical
  across the group, because forks/restores happen in lockstep.

Composition today is struct-of-tokens: a container holding several vectors
hand-writes `mark`/`restore` that fan out to each field and bundles their tokens.
Correctness relies on the caller marking and restoring all fields together — the
"hard-sync" is a convention, not an enforced structure, and the `ForkHistory`
duplication is its cost.

`ForkHistory` is the sharpest waste: per the container docs it grows one
`origin` entry per restore and is never reclaimed, so its size scales with total
backtracks over the session — multiplied by `N`.

## Design: unbundle the history

Move `ForkHistory` + depth + token counters out of `Vec` into a standalone
`History`. `Vec` keeps only its own diff state. `mark`/`restore` take the history
by reference:

```
pub struct History { forks: ForkHistory, depth: usize, /* token counters */ }

pub struct GroupToken { branch_id: u32, depth: u32, frame_idx: usize }

impl History {
    pub fn mark(&mut self) -> GroupToken;          // one genealogy write, O(1)
    pub fn is_valid(&self, t: GroupToken) -> bool; // one validation
    pub fn restore_to(&mut self, t: GroupToken);   // pop genealogy once
}

impl<T, I, S, const TRACK: bool> Vec<T, I, S, TRACK> {
    // push local (saved_len, diff_start) frame; no genealogy work
    fn push_frame(&mut self, shrink: ShrinkPolicy);
    // reverse-replay + truncate this vector's diff to the token's frame
    fn restore_frame(&mut self, t: GroupToken);
}
```

`GroupToken` drops the per-vector `container_id`: one token names the whole
group's version. Validity and genealogy live in `History` and are checked once.

## Two modes, no aliasing, no const generic

Because `History` is a parameter, not a stored field, there is nothing to alias
— which keeps the whole thing inside Verus's reach.

- **Solo** — a thin wrapper bundling one `Vec` with one `History`, reproducing
  the container-level `mark()`/`restore(token)` API exactly: the migration safety
  net, since deleted (2026-09-18). Its successor is `ForkHistory<M>` with a group
  of one, which is the same shape without a second API to keep in step.
- **Synced group** — one `History`, many `Vec`s:

  ```
  fn mark(&mut self) -> GroupToken {
      let tok = self.history.mark();              // the only genealogy write
      for v in &mut self.members { v.push_frame(shrink); }
      tok
  }
  fn restore(&mut self, tok: GroupToken) {
      assert!(self.history.is_valid(tok));        // one validation
      for v in &mut self.members { v.restore_frame(tok); }
      self.history.restore_to(tok);
  }
  ```

Const-generic mode selection was rejected: the modes differ in method
*signature* (`mark()` vs a history-taking form), which a const generic cannot
switch. Unbundling gives both modes for free and avoids stored references.

## What it saves

- **Memory:** `ForkHistory` (unbounded-growth, never reclaimed) collapses from
  `×N` to `×1`. Depth/token counters likewise. For the e-graph's ~10 synced
  vectors, that is close to an order of magnitude on the *history* component.
- **Runtime:** per backjump, token validation and genealogy pop run **once**
  instead of `N` times; per `mark`, the fork bookkeeping runs once. The
  per-vector frame push and diff replay remain (`O(N)` small ops) — those are
  irreducible, since each vector really does have its own diff. So the win is
  concentrated on the redundant genealogy/validation work, which is exactly the
  part that scales with `N` and with backtrack frequency.

**Honest bound.** This does not touch the per-vector diff replay, the per-assert
`rebuild`, or the adapter's id indirection. Its share of the wall-clock gap is
whatever fraction the fork-history/validation work occupies — to be measured
(the differential profile) before committing the refactor, not assumed.

## Ownership model and verification

`History` is owned by the group (or by the solo wrapper) and passed to members
as `&mut` per call — never stored inside a member — so there is no shared
mutable aliasing for Verus to fight. Proof structure:

- **`History` invariants standalone:** genealogy well-formedness (the existing
  `ForkHistory` theorems, lifted to the extracted type).
- **Group invariant:** for every member, `member.frames.len() == history.depth`.
  This single cross-cutting fact ties the shared depth to each per-vector frame
  stack and is maintained by `mark` (push everywhere) and `restore` (pop
  everywhere).
- **Refinement theorem:** a synced group behaves exactly as `N` vectors each
  carrying an identical private `History` — i.e., sharing changes performance,
  not semantics. This lets the per-vector proofs be reused against the shared
  depth/token supplied by `History`.

## Interaction with other work

Independent of diff-stack compression (`09-diff-stack-compression.md`):
compression changes the *frame representation*, sharing changes *who owns the
history*. They compose — a group of `COMPRESS = true` vectors is well
defined — but ship and measure them separately so each effect is attributable.

## Size and savings estimate (which workload this is for)

`ForkOrigin` is 8 bytes (two `u32`), and `origins` grows by one per restore and is
never reclaimed (`vec.rs`: "origins.len() is the lifetime restore count"). Marks
do not add to it. So per vector `fork_history_heap ≈ 8 · R` bytes for `R` lifetime
restores, and with the e-graph's ~`N`=10 hard-synced vectors each holding an
identical `origins`, sharing collapses `×N → ×1`:

```
space saved ≈ 8 · R · (N − 1) ≈ 72 · R  bytes   (N = 10)
```

| R (restores) | ×N today | shared | saved |
|---|---|---|---|
| 10³ | 80 KB | 8 KB | 72 KB |
| 10⁴ | 800 KB | 80 KB | 720 KB |
| 10⁵ | 8 MB | 0.8 MB | 7.2 MB |
| 10⁶ | 80 MB | 8 MB | 72 MB |

**This is an SMT memory optimization, not an eq-sat one.** The cost scales with
restores: SMT (CDCL) backjumps constantly (`R` = 10⁴–10⁷ on hard problems), so its
fork history reaches tens of MB of 90%-redundant genealogy; equality saturation
leans on rewrites with little backtracking (`R` small), so its fork history is
negligible and compression is its memory lever instead. This corrects the earlier
framing that lumped both memory optimizations together.

**Time saving is negligible either way.** The per-restore genealogy work (an
`is_valid` parent-chain walk plus one `fork` push, done `N` times today vs once
shared) was measured at ~0.4% of eq_diamond wall-clock; sharing removes ~90% of
that, ~0.36%. Sharing is a memory optimization, not a speed one.

**Complementary, not covered by sharing:** sharing dedups `×N→×1`, but `origins`
still grows unboundedly with `R` in the one shared copy. Reclaiming it (below)
bounds the size to the live spine depth, which for SMT (large `R`, bounded depth)
is a larger space win than sharing and removes the unbounded-growth-per-session
problem.

## Shipped design: GenStamps reclamation

The branch-model fork history (`fork_history.rs`: the append-only `origins` walk,
`fork_valid`/`fork_walk`/`reaches`) is replaced by depth-indexed generation stamps.
`GenStamps` holds `levels: Vec<u64>`, one generation per depth; a token minted at
depth `d` carries `levels[d]`; `mark` mints via `stamp_at`; a restore diverging at
`d` calls `bump_from(d+1)`, and validity is the O(1) read `levels[depth] ==
generation`. `lemma_bump_invalidates` proves the branch-cut safety: after
`bump_from(cut)`, every token at `depth >= cut` is rejected and every token at
`depth < cut` stays valid. Live size is O(max depth), not O(R lifetime restores), on
every container fork path (`Vec`, `AppendOnlyVec`, and the delegators).

`bump_from` is total via `wrapping_add`: invalidation needs only that a bumped level
becomes distinct from a stale token's stored generation, and `x.wrapping_add(1) != x`
for every `u64`, so it invalidates with no overflow precondition. It is `external_body`
(trust group B) with the `!=` ensures read off `wrapping_add`; `lemma_bump_invalidates`
is stated on `!=`.

Rejected alternative: a `< u64::MAX` headroom precondition (`gen_headroom_spec`, the
u64 analogue of the old u32 `origins.len()+1 <= u32::MAX`). It does not compose:
`restore` is reached through the delegators, and a `forall` over private `levels`
cannot be discharged O(1) at each boundary, so threading it broke preconditions across
six files. `wrapping_add` removes the obligation instead of propagating it. The only
residue is ABA after 2^64 restores at one depth, physically unreachable and backstopped
by frame-liveness.

Measured (`gen_stamps_reclamation`): live size is independent of restore count (500 vs
50000 restore cycles at depth 1000 give identical `heap_bytes`), 9 KB at depth 1000.
The deleted branch model was 8 bytes per restore, 80 MB at 10^7 restores; the test
asserts >=1000x reduction (measured 9765x). Only the AFTER runs (the branch model is
deleted).

Scope: the shared x1 `History` (one genealogy for a synced group) is a verified
primitive in `containers-verus`, but the e-graph does NOT yet route through it;
`EGraph31::mark/restore` still marks each member independently. Wiring it in is future
integration, tracked in the transient task docs, not here.

## Reclaiming abandoned branches (bounds size to O(spine depth))

`origins` grows one entry per restore and is never reclaimed because `branch_id`
is the entry's index in an append-only `Vec`: dropping an interior entry would
renumber the branch ids in tokens the client still holds. But most entries are
permanently dead, and the live ones are few.

**Every origin is already a guard.** `origins[b-1] = (parent_branch_id,
fork_depth)` states "on branch `parent_branch_id`, any mark deeper than
`fork_depth` is dead", and `fork_valid` already rejects a token by that comparison
(`token_depth <= origin.fork_depth` along the walk). So the rejection mechanism
exists; what is missing is discarding the guards no longer needed.

**What is permanently unreachable.** An entry matters only if its branch is on the
current branch's ancestor spine: the validity walk starts at `current_branch_id`
and climbs parent edges, and `fork` attaches every new branch to an ancestor of
current (`parent = token_branch <= current`). A branch off the spine is an
abandoned future whose tokens already fail `fork_valid`, and nothing created later
can reference it. Those entries are dead the moment the search diverges from them.

**Two reclamation rules.** On the backjump that cuts branch `p` at depth `d`:

- **Shallowest cut dominates.** If `p` is later cut at `d' < d`, the shallower
  guard rejects a superset, so keep only the minimum cut depth per branch and drop
  the rest.
- **Dead subtrees collapse.** Guards for branches strictly below a cut are
  subsumed by the guard at the cut, so drop the whole abandoned subtree and keep
  the single guard at its root.

The live guard set is then one shallowest cut per spine branch, so its size is
O(current spine depth), not O(total restores `R`).

**The rejection rule that makes dropping sound.** A token `(branch, depth)` is
valid iff `branch` is still live and `depth` is above every guard on its path. The
corollary that lets entries be dropped: a token whose `branch` is absent reads as
reject, "unknown branch is dead". That is sound only if branch ids are never
silently reused, so mint them from a monotonic counter, or recycle slots with a
generation tag that a stale token's old generation fails (defeating ABA: a
recycled id carrying the previous generation is rejected on the mismatch). Without
the tag a recycled id could wrongly accept a dead token.

**Dense alternative that also makes checking O(1).** Replace the parent-chain walk
with a depth-indexed generation array `gen: [u64]` of size the maximum depth,
reused across restores. A token carries `(depth, gen[depth])` at mark; a diverging
restore bumps `gen` for the levels it cuts; validity is the single read
`token.gen == gen[token.depth]`. This is the trail-solver level-stamp trick: it
bounds size to O(max depth) and turns validity from an O(spine depth) walk into an
O(1) array read, and `u64` generations do not realistically overflow. The sparse
guard set above and this dense stamp array are the same idea at different
densities; pick the stamp array when depth is small and dense, the guard set when
depth is large and sparsely cut.

**Arena allocation does not help the walk.** `origins` is already a single
contiguous `Vec<ForkOrigin>` (8-byte records), not a pointer-chased tree of
heap nodes, so there is nothing for an arena to flatten: the validity walk indexes
within one allocation already. The walk's cost is the number of parent hops (its
length is the spine depth) with a non-sequential index per hop, so the lever is
algorithmic, not allocational: shorten the chain by reclaiming (above), or remove
the walk entirely with the O(1) generation stamp. An arena would matter only if
the redesign moved to individually heap-allocated nodes, which it should not.

**The live spine is a stack, though `origins` is not.** `origins` as it stands
cannot be a LIFO pop-stack: it is indexed by restore-creation order, so an
abandoned branch is an interior entry, not the top, and the top entry is the live
branch you must keep. The genealogy is a tree, and a tree is not a stack. But the
*live* information is the current ancestor spine, and that is a stack: a
restore-to-ancestor pops the levels above the target, and a divergence pushes one.
Representing the spine explicitly as a depth-indexed level stack (the generation
array above is exactly this) gives pop-based reclamation and matches the
mark/restore discipline, where the shared `History.depth` already moves as a
stack. So the move is not "pop `origins`" but "store the spine stack instead of
the genealogy".

**The level index becomes a shared handle.** Once the spine is a dense
depth-indexed stack, a level's index is a compact `u32` key into parallel arrays,
the same dense-id-into-columns pattern the e-graph already uses. In the shared
design this is the natural join key: one shared level stack, and each synced
member's per-level frame addressed by the same level index, so the shared
`History` owns the level identity and each member owns only its frame column.
Reclaiming a level then reclaims everything keyed by its index in one step, a
clean ownership model. The caveat is the same generation tag as for tokens: if
level slots are recycled, an index alone is ambiguous (ABA), so a reference must
carry `(index, generation)` and a stale reference is rejected on the generation
mismatch. An index used purely within one non-recycled lifetime needs no tag.

Reclamation is a redesign of the validity mechanism (the token gains a generation
or the guard set replaces `origins`, and branch-id allocation changes), not a GC
pass bolted onto today's `origins`. It composes with sharing on the space axis and
supersedes it when `R` is large; the ~0.4% time share is unchanged either way,
except the generation-stamp form which also removes the walk.

### Reclamation savings estimate

Reclamation bounds the structure from O(total restores `R`) to O(live decision
depth `D`). For SMT, `R` is 10⁴–10⁷ but `D` (the CDCL decision-stack depth) stays
in the hundreds–low thousands, because backjumping keeps the stack shallow.
Per vector the fork history goes `8·R → 8·D` bytes; the whole e-graph, combined
with sharing, `8·N·R → 8·D`:

| `R`, `D` | ×N today (N=10) | reclaimed + shared | saved | factor |
|---|---|---|---|---|
| R=10⁴, D=10² | 800 KB | ~0.8 KB | ~800 KB | ~1000× |
| R=10⁵, D=10³ | 8 MB | ~8 KB | ~8 MB | ~1000× |
| R=10⁶, D=10³ | 80 MB | ~8 KB | ~80 MB | ~10000× |
| R=10⁷, D=10⁴ | 800 MB | ~80 KB | ~800 MB | ~10000× |

The reduction is ~`R/D` (100×–1000×) from reclamation times ~`N` (10×) from
sharing, but the qualitative point dominates: today the structure grows unbounded
with session length; reclamation makes it O(depth), so it **stops growing**. Once
it is a few KB, duplicating it ×N is trivial — so **reclamation largely obviates
sharing on the space axis**; do reclamation and you barely need sharing for memory.

CPU is a fraction of 0.4% either way (nil): the validity walk is already short (a
valid token validates against a recent ancestor, a few hops), so the O(1)
generation read removes a walk that was never the bottleneck, and reclamation's
per-backjump bookkeeping roughly offsets it. Wall-clock stays dominated by diff
replay and rebuild. Estimate, `D` unmeasured; measure decision depth on a real
SMT run to confirm.

## Shipped: token provenance and the group of one (2026-09-17)

The token authority is one verified type, `history::Genealogy`: a
`ContainerId` naming the manager plus the `GenStamps` levels. It has three
operations — `mint(depth)`, `is_valid(&token)`, `cut_from(depth)` — and one
token type, `GroupToken { history, generation, depth }` (`VecToken` is an
alias). `History` for a synced group is a `Genealogy` plus the group depth;
`ForkHistory` owns it and its members.

Every standalone `Vec` and `AppendOnlyVec` embeds its own `Genealogy`: a
group of one. `mark` pushes the frame and mints last (so the postcondition
states the token's validity without re-framing the frame push); `restore`
checks provenance first (`is_valid`: same manager, live stamp), resets to
the checkpoint — the state at the mark, with the mark's frame reopened
empty (semantics B, design doc 08 §1) — and cuts at `t.depth + 1`: the
checkpoint's token stays valid and reusable, every token minted after it is
dead for good, and `pop_scope` (the SMT-LIB `pop`) drops the open top frame
and kills its token. A token minted by another manager is refused whatever
its numbers.

The stamp table is O(1) per operation (commit `683dbef`): stamps come from
a counter that only grows (each handed out once), the table keeps a live
length, validity is `depth < len && levels[depth] == stamp`, a cut is
`len := d` (one write; the stale stamps above stay in place) and a mint at
the live length is one write. The first version bumped every level from
the cut up — O(deepest depth) per restore — and cost 1.1–1.7× on every
mark/restore-dominated benchmark; the truncating table replaced it the same
evening. Memory stays O(deepest depth ever reached), 8 bytes per depth,
kept as capacity like every column's frame stack.

Proof shape. The `genealogy` field is absent from every physical, ghost-trail
and snapshot predicate of `Vec`, so a change confined to it preserves `wf`:
`lemma_genealogy_framing` (the twin of `lemma_full_trail_physical_framing`,
plus a `wf_for_snap` half) is called after the mint/cut with a ghost snapshot
of the physical state, and `mark`/`restore_frame` stay within their old
solver budgets. Two lemmas of the Hot and ingress proofs were perturbed by the
new field and are decomposed (`lemma_hot_migrating_frame_range`,
`lemma_ingress_capture_{snap,cold}`); no limit was raised.

Composite tokens (ListArena, CircularList, SparseSet, UnionFind, BPlus,
EClasses, SpMap) still bundle their columns' tokens; their lockstep invariants
are unchanged, only the field read is `depth`. Grouped members under
`ForkHistory` are driven structurally (`push_frame`/`restore_frame`), and
their own manager is inert (never minted, cut along with the frames).

## Shipped: the typed external manager (2026-09-18)

The manager is now always provided from the outside, as one type:
`group::ForkHistory<M: Member>` owns a `History` and exactly one typed member
`M`. The member protocol is structural and carries no tokens —
`push_frame(shrink)`, `restore_frame(depth)`, `reset_frame(depth)`,
`pop_frame()`, `depth_exec()`, with the spec side `wf`, `depth_spec`,
`can_push`, `model`, `archive` and one lemma `lemma_archive_depth`. Every
operation is total: a member that cannot take another frame, or whose depth has
drifted, is refused rather than trusted.

The group is the only token authority. `mark` returns `Option<GroupToken>`,
`restore`/`restore_and_pop`/`pop_scope` return `bool`, `mint_pushed` adopts a
frame the caller pushed structurally (the adaptive and explicit-rollover
paths), `is_valid` answers provenance, `depth` reports the shared depth, and
`in_lockstep` is the invariant as a runtime question. `Deref`/`DerefMut` give
typed access, so `group.field` and `group.method()` read like the container
itself while `group.member` is the explicit spelling.

Who is a member. Every container in the crate: `Vec`, `AppendOnlyVec`,
`SparseSet`, `CircularList`, `ListArena`, `UnionFind`, `SpMap`,
`BPlusTreeSet`, `EClasses`, `HintedArena`, plus `Pair<A, B>`, the verified
two-member forwarder, which nests (a group of three columns is
`Pair<Pair<A, B>, C>`). Composites got token-free cores for the work they used
to do inside their own `restore`: `push_frames`, `reset_frames(target)`,
`restore_frames(target)`. A standalone container is
`ForkHistory::new(Vec::new())`, a group of one.

The lockstep theorem is stated once, on the group, instead of once per
composite: after `mark` the member's depth is the history depth; after
`restore(t)` the member sits at `t.depth + 1` with its model equal to its
archived model at `t.depth`. `History::{mark,restore,restore_and_pop,pop,
mint_pushed}_member` carry it over a borrowed `&mut M`, which is what lets a
consumer hold its members as separate fields and still have one history.

The e-graph is the first consumer on the new shape (commit `e26623e`):
`EGraphMembers<'a, Cfg, L, TRACK, PROOFS>` is a borrowed forwarding view of
its nine synchronized members plus the parallel flag, and it implements
`Member` by fanning out (above the fan-out threshold, over a `rayon::scope`).
`EGraph::{mark_with, restore_with, restore_and_pop_with, pop_scope}` are each
one call into `History::*_member` plus their own bookkeeping. Nine
depth-indexed per-member token stacks are gone, and with them the per-column
provenance constant: the `empty20k` store trace runs at 0.79–0.80× of the
previous commit, the other store traces at 0.97–1.00×, and saturation is at
parity.

Misuse is refused, not undefined. A frame pushed or popped on a member behind
the group's back drifts the member's depth away from the history's, and the
next group `mark` returns `None` while `restore`/`restore_and_pop`/`pop_scope`
return `false` and change nothing; repairing the drift makes the group answer
again. Adopting a member that already has open frames, or pairing members at
different depths, refuses at construction. Ownership, not a shared handle, is
what keeps this verifiable: a handle would put interior mutability and a
permission token on every mark and restore.

The old surface is gone, all of it. No container in the crate has `mark`,
`try_mark`, `restore`, `try_restore`, `restore_and_pop`, `pop_scope` or
`is_valid_token` of its own, none has a token type, and the token-only
predicates (`is_token_valid_spec`, `is_restorable_spec`, `restore_pre_spec`,
`snap_at`, `frames_agree`) are gone with them. `Vec` and `AppendOnlyVec` no
longer embed a `Genealogy` either: the branch cut happens once, in the group's
`History`, where the stamps live, and the three lemmas that framed a
genealogy-only change against `wf` are no longer needed. The predecessor dyn
group (`sync_group`) and the `Solo`/`SyncPair` migration wrappers are deleted,
as is the e-graph's wrapper token layer (`CacheToken`, `PoolCacheToken`,
`NodeStoreToken`, `RoutingToken`, `LitValStoreToken` and the four registry
tokens), with the director pool switched to the frame protocol. `VecToken`
survives only as the alias for the group's `GroupToken`, which is what the
paired harnesses spell.

The crate verifies at **2688 verified, 0 errors** — about 120 proof functions
fewer than before the deletions, because removing the field removed obligations
rather than creating them — and the trust surface went from 37 `external_body`
items to 34.

Consumers followed, each keeping what it measured or asserted. The e-graph runs
its nine members on one history through `EGraphMembers`. The anti-unification
search layer runs its five layers on one history through `AuMembers`: one
`SearchSession::mark` used to mint 62 container tokens (39 across the MCGS
statistics, 14 across the space layer, 7 in the term pool, one each for the
result table and the action cache) inside a nest of eleven token structs, and
now mints one. Its action cache stopped backtracking a plain `Vec` by hand: the
action lists live in an `AppendOnlyVec`, which fits because the cache is
append-only and because that container puts no `Copy` bound on its element. The exact memo's derived hash index is an `SpMap` too since 2026-09-19, so
nothing in either consumer maintains a rollback by hand any more.

Forgery is tested where tokens now exist. A column has no token to forge, so
those tests drive a group of one and forge a `GroupToken`: an out-of-range
depth and a never-minted generation are refused without mutating, and a token
from an abandoned future stays refused after a fresh mark reoccupies its depth.

The typed-group tests (`tests/typed_group.rs`) are the acceptance evidence for
the shape: a group of one per container, a nested `Pair` of three columns under
one history driven by a randomized lockstep proptest, and the refusals above.
