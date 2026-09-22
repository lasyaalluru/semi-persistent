# Policy-driven three-tier frames: make it work, make it fast, then prove it

**Status: E1–E6 EXECUTION LOCKED at `d116f76` — DiffStore-owned three tiers, explicit rollover/adaptive inputs, runtime validation, DynStore measurements, and post-migration reclamation are complete; presets remain unchanged because no universal automatic threshold was established. The first proof milestone is VERIFIED on `d21-exec`: authoritative unique-capture Hot-only Defer projection, checked capture/set, `Defer + ShrinkPolicy::Never` mark, and Hot restore for zero and nonzero targets.**

This is the controlling goal for replacing the dual-purpose hot stack on
`d21-exec` after commit `a414090`. It supersedes the two-tier layout and proof
sequence in `mainline-shape-plus-coldstack-goal.md` wherever they conflict.
That document remains historical evidence for measurements, defects, and proof
assets; it is not the architecture target after this decision.

The order is mandatory:

1. make the policy-driven executable state machine correct;
2. validate it differentially across every DiffStore protocol, tier, and
   restore boundary;
3. measure and optimize complete workload profiles end to end;
4. lock the executable algorithm and selected defaults;
5. only then attach proofs.

No proof obligation is allowed to force the execution design back into a
representation with dual meanings. During execution and performance work,
changed Verus bodies MAY use explicit `#[verifier::external_body]` scaffolding,
but every marker MUST be listed in the temporary trust ledger in this document.

## 1. The defect being removed

`hot_stack` currently describes two physically and logically different things:

- a chronological trail frame that may contain repeated writes to one cell;
- a first-write-wins frame whose physical log contains at most one entry per
  cell.

Its meaning depends on the selected `DiffStore`. Consequently there is no one
physical invariant attached to a hot frame. Reconstruction, physical/ghost
index equality, capture flags, compression, and restore all inherit discipline
case splits. A cold-target restore also has to turn a cold frame back into this
ambiguous hot representation, and writes after such a restore create an orphan
extension that compression must fold back into the cold top.

This ambiguity has blocked the proof campaign. It is an architectural defect,
not a missing-lemma problem. The replacement MUST separate:

- **ingress protocol**: an immutable property of `DiffStore`—Inline/Parallel
  use first-capture-wins and Trail uses chronological duplicate capture;
- **storage tier**: trail, unique hot, or compressed cold;
- **retention policy**: how much history may remain at each tier.

Each stack has one physical meaning regardless of workload policy.

## 2. Ruled architecture

### 2.1 The three representations

1. **Trail frame stack** — chronological, duplicate-preserving frames. Several
   frames may be buffered; only the newest is mutable when trail capture is the
   selected ingress mode.
2. **Hot frame stack** — first-capture-wins frames with at most one entry per
   cell. Several frames may be buffered; only the newest is mutable when unique
   capture is the selected ingress mode.
3. **Cold frame stack** — immutable first-capture-wins frames encoded as
   disjoint contiguous index runs. Any number of frames may remain cold.

The physical layout is:

```rust
struct Vec<T, I, S> {
    store: S,

    // Chronological, duplicate-preserving pooled frames.
    trail_value_pool: Vec<(T, I)>,
    trail_stack: Vec<TrailFrame<I>>, // { saved_len, start, end }

    // First-capture-wins pooled frames.
    hot_value_pool: Vec<(T, I)>,
    hot_stack: Vec<HotFrame<I>>, // { saved_len, start, end }

    // Run-compressed first-capture-wins frames.
    cold_value_pool: Vec<T>,
    cold_index_runs: Vec<IndexRun<I>>, // { base, start, len }
    cold_stack: Vec<ColdFrame<I>>,     // { runs_start, runs_len, saved_len }

    tier_policy: TierPolicy,

    // Existing snapshots/tokens/genealogy fields remain authoritative.
}
```

The exact field and policy type names MAY change during implementation, but the
three representation meanings MUST NOT.

### 2.2 Formation-cost / restore-cost ladder

Each successive representation spends more work once so repeated restores do
less work:

| tier | formation work | retained work units | restore operation |
|---|---|---|---|
| Trail | none beyond closing a header | one entry per write, duplicates retained | replay every write right-to-left |
| Hot | dedupe, keeping each cell's first capture | one entry per touched cell | one scalar write per touched cell |
| Cold | sort unique entries, build runs, optionally compress values | one value per touched cell grouped into runs | one direct `restore_run` call per run; raw backends use `copy_from_slice` |

For a frame with `W` writes, `U` unique cells, and `R` contiguous runs, the
intended progression is:

```text
formation cost: Trail < Hot < Cold
restore commands: W writes -> U writes -> R direct run dispatches
W >= U and R <= U
```

This is the central policy tradeoff. There is no universally best ingress
protocol, tier, or rollover cadence: applications choose a `DiffStore` and
retention independently according to write duplication, expected backtracking,
restore frequency, index locality, and memory pressure. The implementation supplies one correct
conversion pipeline; policy profiles select different points on that cost
curve without changing representation invariants.

Trail is preferred when frames are likely to be abandoned or restored quickly,
because it pays no sealing transformation. Hot is preferred when repeated
writes make `W / U` large enough for dedupe to pay back. Cold is preferred when
index locality makes `U / R` large enough for direct run dispatch to amortize
sorting and run construction (including slice copies on raw backends), or when
memory pressure justifies compression.

A length-one run is not automatically faster than one hot scalar write.
Therefore cold rollover MUST measure or estimate run locality; singleton-heavy
frames stay hot unless an explicit memory policy accepts the restore tradeoff.
The performance campaign must validate the ladder end to end rather than assume
that a smaller representation is faster.

### 2.3 DiffStore protocols

`DiffStore` is the only capture/ingress strategy abstraction. Its protocol is
chosen when the store is constructed and is immutable for that vector:

- `InlineStore` and `ParallelStore` capture the first old value for each index
  into the open Hot frame. Restore may read Hot or Cold history.
- `TrailStore` appends every old value chronologically, including duplicates,
  into the open Trail frame. Restore may read Trail, Hot, or Cold history.
- `DynStore` selects one of those protocols at construction through
  `StoreKind::{Inline, Parallel, Trail}` and delegates the same immutable
  capability answers.

There is no Vec-owned mode field, setter, const strategy generic, or constructor
parameter that can contradict its store. `TierPolicy` controls only retained
closed-history representation and is independent of ingress. A Trail vector may
therefore migrate closed frames Trail -> Hot -> Cold under pressure while new
writes continue to use Trail ingress. Changing future ingress while history is
live is a separate, unsupported transition problem.

### 2.4 Frame order

For TrailStore ingress and nonzero depth `d`:

```text
cold frames:  [0, c)
hot frames:   [c, c + h)
trail frames: [c + h, d)
open frame:   d - 1 in trail_stack

c + h + t == d
t >= 1
```

For InlineStore or ParallelStore ingress and nonzero depth `d`:

```text
cold frames: [0, c)
hot frames:  [c, d)
open frame:  d - 1 in hot_stack

trail_stack is empty
c + h == d
h >= 1
```

At depth zero all three stacks are empty. Exactly one frame is mutable when
history is nonempty: the newest frame in the selected ingress representation.
All older frames are closed. Every logical frame belongs to exactly one stack,
and the stacks form contiguous age-ordered segments.

### 2.5 Independent retention policies

Each tier has an independent policy. A tier MAY retain as many frames as the
caller wants; unbounded retention is a first-class setting, not a very large
hard-coded threshold.

A policy may be expressed by frame count, entries, bytes, measured overhead,
memory pressure, or explicit caller action:

```rust
enum TierLimit {
    Unbounded,
    Frames(usize),
    Entries(usize),
    Bytes(usize),
    Adaptive,
}

struct TierPolicy {
    trail: TierLimit,
    hot: TierLimit,
    // Capacity retention is independent of representation selection. An
    // explicit adaptive migration may reclaim every Trail/Hot/Cold pool after
    // both stages complete; disk spill is outside this goal.
    cold_reclaim: ReclaimPolicy,
}
```

This is an illustrative API, not a locked public type. Retention limits count
closed frames and their payloads; the one open ingress frame is never eligible
for automatic migration. Required semantics:

- `Unbounded` MUST never trigger automatic rollover from that tier.
- A zero trail budget routes TrailStore closed frames immediately through the
  unique hot abstraction.
- A zero hot budget compresses each eligible unique frame immediately; an
  implementation MAY fuse unique sealing and run construction without
  retaining a persistent hot payload.
- Explicit flush/compress operations MAY override automatic retention without
  changing representation meanings.
- Budget changes MAY affect future migration at a mark or explicit policy
  application. They never change the store's ingress protocol.
- `ReclaimPolicy::RetainCapacity` preserves vacated allocations. When an
  explicit adaptive pass migrates at least one frame under `ShrinkToFit`, it
  MUST reclaim unused capacity from all Trail, Hot, and Cold payload/header/run
  pools once after both migration stages. Reclamation MUST NOT alter logical
  planning, reports, tier ownership, values, or token semantics.
- Reclamation is not a pressure signal: it MUST NOT read ambient allocator
  state, add per-write work, or merge with `ShrinkPolicy` or rollover.

### 2.6 Static ingress and per-mark rollover API

Static `VecP`/`VecI` and direct Parallel/Inline store spellings compile to
first-capture Hot ingress. Static `VecT` and direct TrailStore spellings compile
to duplicate-preserving Trail ingress. `VecD` preserves its a414090 concrete
type and uses `StoreKind` as the runtime construction-time protocol selector.
No trailing const generic or alternate configurable alias participates in this
decision. `new_with_policy(policy)` and
`VecD::new_kind_with_policy(kind, policy)` configure retention only; the
pre-existing `new`, `new_with_mode`, and `new_kind` APIs retain their types and
source behavior.

Mark-time conversion is orthogonal to capacity reclaim:

```rust
enum RolloverPolicy {
    Defer,
    ApplyConfigured,
    ForceClosed { trail_to_hot: bool, hot_to_cold: bool },
}

struct MarkOptions {
    shrink: ShrinkPolicy,
    rollover: RolloverPolicy,
}
```

`try_mark_with(options)` is additive. Existing `try_mark(shrink)` delegates to
`ApplyConfigured`, including the legacy eight-frame cadence. Every mark first
seals the old ingress frame and opens the new empty ingress frame; only then is
its rollover choice evaluated. `Defer` performs no conversion.
`ApplyConfigured` enforces the legacy cadence or current `TierPolicy`.
`ForceClosed` migrates all closed prefixes selected by its booleans; when both
are true, Trail -> Hot runs before Hot -> Cold. None of these choices changes
live values, depth, snapshot order, or token coordinates. Group/internal mark
callers continue through `try_mark`/`seal_frame` and therefore preserve
`ApplyConfigured` behavior.

### 2.7 Explicit-budget adaptive pass

The additive `AdaptiveInput` is supplied to one `apply_adaptive` or
`try_mark_adaptive` call and is never retained in `Vec`. Its thresholds are
exact integer `Ratio` values whose constructor rejects a zero denominator. The
byte budget counts deterministic logical occupancy for **closed history only**:
Trail/Hot/Cold frame headers and payload lengths multiplied by `size_of`.
Capacity, allocator counters, RSS, time, the live store, and the open ingress
frame are excluded.

Planning and execution obey these rules:

1. If logical closed history is already at or below budget, return an unchanged
   report without inspecting a frame.
2. Scan the oldest closed Trail prefix without skipping. Empty frames remain
   eligible token boundaries. A nonempty frame advances only when W/U meets the
   supplied threshold and projected Hot bytes are strictly smaller.
3. Execute exactly that prefix with first-capture semantics, then recompute
   logical pressure from resulting physical lengths.
4. While still over budget, scan the oldest closed Hot prefix without skipping.
   Empty frames remain eligible. A nonempty frame advances only when U/R meets
   the supplied threshold and projected Cold bytes are no worse than Hot.
5. Execute exactly that prefix. Report inspected and migrated counts, W/U/R,
   before/after logical bytes, and the exact remaining byte shortfall.

Trail -> Hot always precedes Hot -> Cold. Ordering blockers, ratio blockers,
singleton locality, or irreducible Cold may leave a nonzero shortfall; this is
reported rather than hidden by harmful migration. `try_mark_adaptive` first
seals the old frame and opens the replacement with the immutable existing
`DiffStore`, then applies the pass. Live `DynStore` protocol switching remains
outside this goal and is not implemented.

## 3. Representation contracts

### 3.1 Trail frame stack

Every trail frame is a chronological undo log. In trail mode, every tracked
write MUST append one `(old_value, index)` entry to the open frame, including
repeated writes to the same cell. Replaying one trail frame from right to left
MUST restore the snapshot at the start of that frame.

All headers except the newest are closed and immutable. The newest header is
open in trail mode. Its effective end is `trail_value_pool.len()`; the
implementation MAY synchronize a stored `end` or derive it. Headers partition
the pool in frame order.

Closing changes mutability, not meaning. A closed trail frame remains
chronological and duplicate-preserving until migration.

### 3.2 Hot frame stack

Every hot frame contains at most one entry per cell. In trail mode, a hot frame
is `dedupe_first` of its source trail frame. In first-capture-wins mode, the
newest hot frame is built online by capture-state checks and is already unique.
These are two construction paths to the same physical invariant, not two
meanings for the stack.

Applying a hot frame's entries to the layer above reconstructs the frame's
starting snapshot. Entry order is not semantic because indices are unique.
All headers except a first-capture-wins mode's newest header are closed.

### 3.3 Cold frame stack

Every cold frame represents the same unique index-to-old-value map as its hot
source abstraction. Runs MUST be in bounds, ordered by destination index, and
pairwise disjoint. Restoring a run writes its value slice directly to the live
store; cold restore MUST NOT decode the frame into a pair vector first.

Cold headers, run headers, and values form contiguous frame-ordered partitions
that support suffix truncation.

### 3.4 Capture state

Capture flags belong only to the one open frame:

- trail mode may use them as auxiliary first-write metadata, but they MUST NOT
  suppress chronological trail appends;
- first-capture-wins mode uses them to suppress repeated hot entries;
- closed trail, closed hot, and cold frames carry no live flags.

Restore rebuilds flags only for the promoted or retained open frame.

### 3.5 Whole-frame conversions

Frames change representation only through these semantic conversions:

```text
TrailFrame --dedupe_first--> HotFrame
HotFrame   --sort + run-build--> ColdFrame
HotFrame or ColdFrame --promotion--> selected ingress representation
```

When the hot retention budget is zero, conversion MAY be physically fused:

```text
TrailFrame --dedupe + sort + run-build--> ColdFrame
open unique HotFrame --sort + run-build--> ColdFrame at close
```

The intermediate unique hot abstraction remains part of the contract even if
no persistent hot payload is allocated.

There are no location tags, straddling frames, or orphan payloads.

## 4. State transitions

### 4.1 Write

Trail ingress:

1. read the previous value;
2. append `(old_value, index)` to the open trail frame unconditionally;
3. update auxiliary capture state if needed;
4. write the new value.

First-capture-wins ingress:

1. read the previous value;
2. append `(old_value, index)` to the open hot frame only if that index has not
   yet been captured in the frame;
3. set capture state on the first capture;
4. write the new value.

Writes MUST NOT mutate any closed frame or any older tier.

### 4.2 Mark

The first mark, at depth zero, records `snapshots[0]` and opens an empty frame in
the selected ingress stack.

Every later mark:

1. closes the current ingress header at its pool length;
2. clears active capture state;
3. records the new snapshot/token boundary;
4. opens one empty frame in the selected ingress stack;
5. applies configured retention policies to closed frames.

An empty frame remains a real header because frame count is token identity.
The new open frame is never migrated by the same mark.

### 4.3 Trail rollover

Only closed trail frames are eligible. Migration processes an eligible prefix
oldest-first:

1. read one closed chronological slice;
2. retain the first capture of each index;
3. append the unique result to hot or feed it directly to cold conversion when
   hot retention is zero;
4. remove the source trail header and reclaim its pool prefix according to the
   selected pool policy.

Correctness does not require automatic rollover. With an unbounded trail
policy, all closed trail frames remain raw until restore or an explicit flush.

The first implementation SHOULD batch-convert all eligible closed trail frames
and compact the surviving trail suffix. Partial-prefix rollover using a head
cursor, ring, or periodic compaction is deferred until measurement.

### 4.4 Hot rollover

Only closed hot frames are eligible. Migration processes an eligible prefix
oldest-first:

1. sort unique entries by index;
2. coalesce adjacent indices into runs;
3. append values, runs, and one cold header;
4. remove the source hot header and reclaim its pool prefix.

Correctness does not require compression. With an unbounded hot policy, all
closed hot frames remain unique and uncompressed until restore or an explicit
compress operation.

With a zero hot budget, every closed unique frame is compressed before another
closed hot frame is retained. The new open unique frame remains hot.

### 4.5 Restore

Restore to boundary `target`, from depth `d`, restores only frames in
`[target, d)`, always newest to oldest:

1. resize the live store to the target snapshot length under the existing
   clamped-write contract;
2. restore discarded trail frames newest-to-oldest, replaying each frame's
   entries right-to-left;
3. restore discarded hot frames newest-to-oldest, applying entries within each
   unique frame left-to-right or in any fixed order;
4. restore discarded cold frames newest-to-oldest, copying runs directly; runs
   within one frame may execute in any fixed order because they are disjoint;
5. stop with `view == snapshots[target]` and truncate frames `[target, d)`;
6. if `target > 0`, ensure surviving frame `target - 1` is the open frame in the
   selected ingress representation;
7. rebuild capture state for that frame;
8. if `target == 0`, leave all three stacks empty.

Promotion for a TrailStore protocol:

- a surviving trail frame is retained and reopened;
- a hot survivor is copied as unique chronological entries into one trail
  frame;
- a cold survivor is decoded into unique trail entries for promotion.

Promotion for an InlineStore or ParallelStore protocol:

- a hot survivor is retained and reopened;
- a cold survivor is decoded into one unique hot frame;
- a trail survivor cannot exist because ingress is an immutable store
  capability.

Promotion MUST NOT change the live view. Cold decode is permitted for promotion
because it changes representation; it MUST NOT substitute for direct run
restore.

The order distinction is mandatory:

```text
between frames: newest -> oldest
inside TrailFrame: right -> left
inside HotFrame: any fixed order
inside ColdFrame: direct disjoint runs in any fixed order
```

## 5. Workload policy profiles

These profiles are required validation configurations, not necessarily fixed
public enum variants. Defaults are selected only after measurement.

### 5.1 SMT / frequent-backtrack profile

```text
protocol: TrailStore
trail retention: Unbounded
hot retention: Unbounded but unused unless explicitly flushed
automatic compression: disabled
```

All history remains in `trail_stack`. Mark is header-only, writes append without
a first-capture branch, and restores unwind chronological entries. This profile
optimizes shallow marks and frequent backtracking rather than retained-history
memory.

### 5.2 Equality-saturation / adaptive-memory profile

```text
protocol: TrailStore
trail retention: adaptive by duplicate/byte overhead
hot retention: adaptive or large
cold conversion: triggered only by configured memory pressure or explicit call
```

Recent frames stay cheap to produce and restore as trails. Trail frames roll to
unique hot frames when duplicate or byte overhead justifies dedupe. Hot frames
compress only when retained-history memory is the dominant concern.

The rollover decision SHOULD use measured bytes and duplicate density, not only
frame count.

### 5.3 Restore-optimized / direct-unique profile

```text
protocol: InlineStore or ParallelStore
trail retention: disabled
hot retention: zero or small
cold conversion: immediate or aggressive for closed frames
```

Writes pay the first-capture check, every frame is unique from inception, and a
zero hot budget compresses each closed frame directly. This profile targets
faster restore and bounded retained-history memory.

### 5.4 Fully buffered unique profile

```text
protocol: InlineStore or ParallelStore
trail retention: disabled
hot retention: Unbounded
automatic compression: disabled
```

This validates that any number of unique frames can remain hot without forcing
cold conversion.

## 6. Execution-first implementation phases

A phase is not complete until its runnable acceptance checks pass. Partial work
is not completion.

### E0 — Baseline and policy fixture lock — COMPLETE

Branch verification baseline at `a414090`:

```text
Verus 0.2026.08.02.b677dd5
verification results:: 2198 verified, 0 errors
```

Before execution changes, record same-host Criterion baselines for the current
branch and unchanged production-container control. Define deterministic policy
fixtures for the four profiles above so comparisons do not silently change
rollover behavior.

### E1 — DiffStore protocols and three-stack layout — BUILT AND RUNTIME-VALIDATED

Introduce separate trail/hot/cold pools and stacks. Keep physical logging
selection in the immutable `DiffStore` protocol. Compression may remain
disabled.

Implement and validate:

- any number of TrailStore frames with one open top;
- any number of Hot frames with one open top for InlineStore/ParallelStore;
- mark, write, pop/truncate, token lookup, and restore within the ingress tier;
- `DynStore` selection among all three protocols;
- unbounded policies causing no automatic migration.

Acceptance:

```bash
cargo test -p semi-persistent-containers-verus
cargo test -p semi-persistent-containers-verus --features "compat-all,literal-types"
cargo test -p containers-conformance
```

The production `containers/` package MUST remain an unchanged oracle.

### E2 — Trail-to-hot conversion and promotion — BUILT AND RUNTIME-VALIDATED

Implement batch dedupe of closed trail frames, hot-frame creation, and promotion
back to the selected ingress representation. Keep cold conversion disabled until
trail/hot restore boundaries are correct.

Hard cases:

- unbounded trail history;
- several closed trail frames plus one open frame;
- duplicate-heavy, empty, and one-cell frames;
- zero, finite, byte-based, and unbounded trail policies;
- restore within trail and across trail/hot boundaries;
- write after promotion followed by another mark and restore.

### E3 — Hot-to-cold conversion and direct restore — BUILT AND RUNTIME-VALIDATED

Implement finite, zero, and unbounded hot policies; run construction; direct
cold restore; and cold promotion. Test nonmonotone saved lengths, clustered and
scattered indices, and restores crossing every enabled tier.

The mandatory regression is: create cold history, restore into it, write again,
buffer more frames in the selected ingress mode, migrate them according to
policy, and restore older history. The ownership model must make orphan payloads
impossible by construction.

E1–E3 execution record: `tests/three_tier_runtime.rs` covers all three
DiffStore protocols through `VecD`, arbitrary unbounded frame buffering,
duplicate semantics, empty and one-cell frames, clustered and scattered cold
runs, zero/frame/entry/byte/adaptive limits, explicit trail flush and hot
compression, nonmonotone saved lengths, pop/regrow capture-state rebuilding,
token liveness and pending-index diagnostics, every restore target tier, and
survivor promotion/remigration. Static aliases and a414090 direct concrete
spellings are compile-checked separately. The legacy Vec adapter's non-`None`
modes remain run-cold activation aliases with their historical whole-batch
eight-frame cadence; exact named codecs remain on `compress_frame`.

### E4 — Differential policy-matrix fuzzing — BUILT AND RUNTIME-VALIDATED

Run arbitrary push, pop, set, mark, policy application, restore, repeated
restore, and deep-unwind sequences against the independent production
container. Every operation compares live values, depth, token behavior, and
failure behavior.

Minimum acceptance:

```bash
PROPTEST_CASES=1024 cargo test -p containers-conformance
cargo test -p containers-conformance --test trail_semi_persistence
```

The campaign MUST cover:

- all four policy profiles;
- inline, parallel, trail, and dynamic stores where applicable;
- zero, finite, adaptive, and unbounded retention;
- empty frames, duplicate-heavy frames, and nonmonotone lengths;
- explicit flush/compress operations;
- restore targets in every populated tier.

If 1024 cases are impractical, record the limiting test and elapsed time; do not
silently lower the campaign. No proof implementation starts while a
differential failure remains.

E4 execution record (2026-09-13):
`tests/three_tier_policy_matrix.rs` retains a `PROPTEST_CASES`-aware generated
campaign with a mandatory compact semantic spine and deterministic outer loops.
Each generated tape runs through all policy profiles and the six valid
implementations: static Inline/Parallel/Trail plus dynamic Inline/Parallel/Trail.
There is no independent capture-mode cross-product because the store type or
DynStore variant defines that protocol. Every operation compares full values,
length, depth, and issued-token verdicts to an independent full-snapshot/branch
oracle and to production wherever contracts align. The tapes include push/pop/set/mark/restore, policy changes and
application, explicit flush/compress, duplicate bursts, empty frames,
pop/regrow, repeated invalid restore, ancestor restore, and deep unwind. A
focused deterministic matrix restores newest-to-oldest across deliberately
populated trail/hot/cold segments; a separate regression checks the intentional
production-versus-raw-Vec stale-token API distinction.

The 1,024-case release target passed 3 tests in 0.75 seconds (1.13 seconds wall).
The full minimum gate, `PROPTEST_CASES=1024 cargo test -p
containers-conformance`, passed in 36.03 seconds wall, including the existing
trail semi-persistence target; that target also passed independently at 1,024
cases in 3.24 seconds. The focused three-tier runtime target now passes all
20 tests, including per-mark defer/configured/forced edge selection, empty
forced frames, and restore through every produced tier. No production-container
source or proof implementation changed.

### E5 — End-to-end measurement and optimization — MEASURED AND OPTIMIZED

The post-runtime measurement and two evidence-led optimization passes are
recorded in
[`three-tier-e5-measurement-a414090.md`](three-tier-e5-measurement-a414090.md).
The passes removed the sparse-set superlinear scan and brought tracked Vec,
restore replay, class-ring, sparse-set, and EClasses guards into the established
noise band or faster. The remaining retained Vec formation residual is measured
and accepted as a lock-candidate tradeoff; E6 still requires a recorded revision.

Measure same-host before/after/control runs:

```bash
cargo bench -p containers-conformance --bench tracked_vec_bench
cargo bench -p containers-conformance --bench two_stack_bench
cargo bench -p containers-conformance --bench normalize_bench
cargo bench -p containers-conformance --bench retained_containers_bench
```

Add a `three_tier_bench` that reports each policy profile across:

- write throughput with low and high duplicate density;
- mark cost with no rollover and each rollover boundary;
- restore within one frame and through many frames at each tier;
- trail-to-hot dedupe cost and memory reclaimed;
- hot-to-cold run construction and direct cold restore;
- deep unwind through every enabled tier;
- promotion followed by new writes and another restore;
- peak and retained bytes for all pools and scratch buffers;
- adaptive-policy decision overhead;
- end-to-end SMT-style backtracking and equality-saturation traces.

Measurements MUST report the production control and pre-refactor branch where
relevant. Helper timings and encoded-size formulas are not substitutes for
end-to-end container measurements.

Optimize only from profiles and Criterion evidence. Candidate work includes
policy thresholds, explicit pressure signals, prefix reclamation, head cursors,
dedupe scratch reuse, fused trail-to-cold conversion, run construction, direct
run copy, and pool capacity reuse.

Deltas inside the established 5–8 percent same-code noise band are
inconclusive. An optimization is retained only when it improves a named profile
without an unexplained regression in another. Workload-specific tradeoffs MAY
be accepted because policies are explicit; they MUST be recorded rather than
hidden in one global default.

### E6 — Algorithm and default-policy lock — LOCKED at `d116f76`

Lock only when:

- E1–E4 are green across the complete policy matrix;
- E5 records before/after/control results for every required profile;
- profiles explain dominant costs and memory behavior;
- defaults are selected per named workload profile rather than forced into one
  universal policy;
- each profile default is justified by its end-to-end workload evidence;
- two successive optimization passes produce no material improvement, or a
  documented tradeoff is deliberately accepted;
- the temporary `external_body` ledger is complete;
- DiffStore protocols, retention semantics, migration cadence, pool reclamation,
  and defaults are written as final decisions.

Runtime lock `d116f76` satisfies the correctness, policy-matrix, measurement,
optimization, explicit-adaptive, and reclamation criteria. The static Vec hot
path is at baseline; DynStore protocol tradeoffs, irreducible budget floors, and
rejected automatic-threshold claims are documented in the E5 record. The lock
keeps existing presets unchanged and exposes budgets, ratios, rollover, and
reclamation explicitly rather than guessing one universal policy.

After lock, execution changes require a reproduced correctness defect or a
measured performance regression and MUST record why the lock reopened.

## 7. Deferred proof architecture

Proof design was documented before E6; implementation of the proof campaign
starts only after the executable lock recorded above.

The canonical ghost model is one unique first-write abstraction per logical
frame:

```text
frame_abs: Seq<CanonicalFrame<T, I>>
```

Each representation has one refinement theorem:

```text
dedupe_first(trail_slice(f)) == frame_abs[f]
hot_decode(hot[f])           == frame_abs[f]
cold_decode(cold[f])         == frame_abs[f]
```

Snapshot reconstruction is stated once:

```text
apply(frame_abs[f], layer_above(f)) == snapshots[f]
```

Every trail frame additionally proves chronological undo:

```text
reverse_replay(trail_slice(f), layer_above(f)) == snapshots[f]
```

The open ingress frame adds a capture-state bridge:

- TrailStore protocol: flags are auxiliary and do not affect the trail
  sequence;
- InlineStore/ParallelStore protocol: flags equal the open hot frame's
  captured-index set.

The proof sequence after lock is:

1. protocol-specific frame partition and pool bounds;
2. trail append and right-to-left replay;
3. online first-capture-wins hot construction;
4. `dedupe_first` trail-to-hot equivalence;
5. hot-to-cold decode equality and direct-run restore;
6. promotion to the selected ingress representation;
7. newest-to-oldest restore telescope for each policy shape;
8. mutator preservation and removal of execution scaffolds.

Retention limits are operational policies, not correctness assumptions. Proofs
MUST hold for zero, finite, and unbounded budgets without unrolling a fixed
number of frames.

The existing `full_trail` ghost MAY remain temporarily as a bridge, but it MUST
NOT force a physical stack to regain dual meanings. The preferred final model
is `frame_abs`; raw chronology is local to `trail_stack`.

## 8. Temporary trust ledger

Update this table in the same change that adds or removes a marker.

| body | reason during execution-first phase | executable validation | status |
|---|---|---|---|
| `diff_log_len` | compatibility diagnostic | constructor compatibility suites and protocol tests | diagnostic remains trusted; `frame_saved_len_exec` and `Vec::with_store_policy` are checked and their markers removed |
| `runtime_capture`, `runtime_set_fallback`, `runtime_push_fallback`, `runtime_pop_fallback` | immutable DiffStore capability selects Trail or Hot ingress | duplicate, pop/re-entry, three-protocol policy-matrix, and compatibility tests | discharged: all-tier capture/set/push/pop preserve the full invariant; Trail regrowth restores ghost capture membership; specialized Hot proofs remain checked |
| `runtime_apply_configured_rollover`, `runtime_rollover_on_mark`, `runtime_push_frame_fallback` | open store-selected ingress, then migrate only closed prefixes | shrink-capacity, Defer/configured/forced-edge, empty-frame, all-tier restore and SyncGroup suites | discharged (`a831cc1`): configured and forced rollover dispatch and the mark fallback are checked; mark contracts export the exact view, depth and snapshot prefix and `tiers_only_changed` frames the migrations |
| `runtime_trail_shape`, `runtime_migrate_trail_count`, `runtime_execute_trail_plan`, `runtime_migrate_trail`, `flush_trail` | oldest closed-prefix statistics, deterministic sort/dedupe first-capture execution, reusable accepted-frame plans, and pool rebasing precede refinement theorem | zero/frame/entry/byte/adaptive/unbounded boundary tests | discharged (`bbb9548`): `runtime_migrate_trail_count`, `runtime_migrate_trail` and `flush_trail` are checked over the hash-set first-capture dedupe (`trail_select::dedupe_trail_range`); `runtime_trail_shape` and `runtime_execute_trail_plan` were removed with the plan buffers |
| `runtime_hot_shape`, `runtime_migrate_hot_count`, `runtime_execute_hot_plan`, `runtime_migrate_hot`, `compress_hot` | exact U/R statistics, reusable sorted accepted-frame plans, unique-to-run conversion, and zero-budget path precede proof lock | clustered/singleton runs, zero hot budget, and legacy compression tests | discharged (`990eb08`): `runtime_migrate_hot_count`, `runtime_migrate_hot` and `compress_hot` are checked over the in-place std slice sort (the one trusted std contract, design ledger row 10b); `runtime_hot_shape` and `runtime_execute_hot_plan` were removed with the plan buffers |
| `runtime_closed_history_bytes`, `runtime_reclaim_adaptive_tier_capacities`, `runtime_apply_adaptive`, `apply_adaptive`, `try_mark_adaptive` | exact closed-only logical byte planning, two-stage execution, and post-migration capacity-only reclamation are locked by runtime evidence before refinement proof; ratios and budgets are explicit call inputs | exact boundary, duplicate/locality pass/fail, empty/blocker/cascade/unmet, retain-versus-shrink tracking, promotion, all-ingress, token, and policy-matrix tests | discharged: the byte planning, both stages, reclamation and `apply_adaptive` are checked (`a831cc1`), and `try_mark_adaptive` is checked in the final checkpoint from `mark_with_options` and `runtime_apply_adaptive` (its trusted postcondition was the last execution-first `Vec` marker) |
| `runtime_apply_tier_policy`, `apply_tier_policy` | policy dispatch and reclamation are executable-first | immediate policy tightening and legacy environment-lever tests | discharged (`a831cc1`): both are checked; the public wrapper exports unchanged view, depth and snapshots |
| `runtime_restore_frame_fallback` | Cold survivor promotion formerly trusted | all-tier targets, deep unwind, nonmonotone lengths, conformance suite | discharged and renamed `restore_cold_survivor_checked`: both DiffStore-selected destinations compose checked reconstruction, retirement, promotion, capture finalization and reclamation |
| `DiffStore::restore_run`, `set_raw_usize_scaffold` | inherited Cold run writes previously trusted | overflow/clamping and capture-tag regressions | discharged: required run contract has checked Inline, Parallel, Trail, and DynStore implementations; obsolete usize-write scaffold removed |
| `runtime_begin_restore` and mixed-tier reconstruction | capture preparation previously trusted; batched reconstruction required physical frame composition | all-tier runtime and differential target tests | discharged preparation marker; checked resize, batched Trail/Hot, Cold frame/suffix replay reconstruct the target while preserving history; final survivor obligations remain |
| `runtime_promote_survivor` | survivor must become selected ingress without changing live values | hot/cold promotion and promote-write-remigrate-restore regression | removed after checked Hot and Cold promotion replacements verified; complete saved-map equality is preserved |
| `tracking_bytes`, `pending_restore_indices` | diagnostics now enumerate all physical pools/stacks | byte-counter, duplicate-index, compatibility, and conformance tests | `tracking_bytes` remains a trusted byte reporter (design ledger group B); `pending_restore_indices` is checked (`9df28cb`): `Some` iff the token is restorable, and the returned set names exactly the indices some frame in `[token, depth)` captures |
| `compress_all_hot` | obsolete proof-era adapter | source call-site audit plus runtime suites | removed; actual migration implementations remain in the rows above |
| `restore_cold` | obsolete proof-era adapter | source call-site audit plus runtime suites | removed; actual restore dispatch and Cold promotion now use checked implementations |

Store `capture` hooks define optimized first-capture mechanics. The immutable
`DiffStore` capability chooses the destination and semantics: Inline/Parallel
open Hot, while Trail opens Trail.

Existing unrelated trusted bodies remain governed by
`doc/design/02-trust-boundary.md`; they are not silently absorbed here.

### First formal milestone — unique Hot-only Defer (2026-09-14)

The first post-lock executable prefix is verified in `src/vec.rs` against the
closed, named `Vec::hot_defer_wf` projection. Its authoritative physical state is
`hot_value_pool`/`hot_stack`; none of the new physical reconstruction proofs
reads `diff_log`. The predicate includes:

- unique-capture and Hot-only scope, with Trail and Cold stacks/pools empty;
- exact Hot/ghost-frame/snapshot counts and zero-valued retained ghost
  boundaries while the retired `full_trail` remains empty;
- closed-header extents, `hot_stack[0].start == 0`, and
  `hot_defer_end(top) == hot_value_pool.len()` for the writable top;
- per-frame `saved_len == snapshots[i].len()`, top `active_saved_len`
  alignment, per-stratum uniqueness, and `frame_inv_range` reconstruction;
- the open capture-flag bridge over the top Hot pool slice, no stray set flags,
  and explicit empty-history clauses.

Verified named functions (each reported `1 verified, 0 errors` with
`touch src/vec.rs` immediately before its function-scoped query):

1. `lemma_frame_inv_range_capture_append`
2. `lemma_frame_inv_range_set_captured`
3. `lemma_frame_inv_range_set_outside`
4. `lemma_hot_defer_start_monotone`
5. `lemma_hot_defer_cell_eq_overlay`
6. `hot_defer_capture_checked`
7. `hot_defer_set_checked`
8. `hot_defer_mark_checked`
9. `hot_defer_restore_zero_checked`
10. `hot_defer_restore_nonzero_checked`

The real unique runtime branches call these cores: unique capture calls
`hot_defer_capture_checked`; unique set calls `hot_defer_set_checked`;
`Defer + ShrinkPolicy::Never` mark calls `hot_defer_mark_checked`; and a
non-fused unique Hot-only restore (the Parallel protocol) dispatches target
zero/nonzero to the corresponding checked restore core. InlineStore keeps its
existing fused tag-clear replay path so proof wiring does not add a second scan.
The outer protocol/mixed-tier dispatch functions remain `external_body` and are
not counted as proof.

Runtime evidence: `cargo test --test three_tier_runtime` passes 30/30, including
`unique_defer_restores_surviving_prefix_and_zero`; `cargo test --test trail_vec`
passes 5/5. The new test exercises Inline and Parallel, repeated unique
capture, pop/regrow with nonmonotone saved lengths, four explicit Defer marks
including an empty frame, three surviving-prefix restores, and target-zero
retirement.

Trust delta needed to make the execution-locked branch function-queryable:
seven policy datatypes are transparent `external_type_specification`
registrations; `Ratio` alone is opaque because its fields are private. Three new
`external_body` markers are present relative to `44b8657`: `ExRatio`,
`retained_closed_prefix`, and `hot_frame_run_count`. The two functions hide
execution-only planner code that uses unsupported std APIs and carry no
postconditions. `Vec::with_store_mode` and `Vec::with_store_policy` verify,
including empty unique-state establishment of `hot_defer_wf`; the pre-existing
`with_store_policy` marker was removed. H1 additionally verifies
`frame_saved_len_exec` over the Cold|Hot|Trail partition and removes that marker.
Net source counts at H1 were 90 default and 95 with `literal-types`. H1 removes
one proved accessor marker plus five unreachable legacy scaffold markers. H2
then verifies public `push`, `pop`, and `set_index` through checked Hot-scope
dispatch and removes three more markers; H2 counts were 87 default and 92
with `literal-types`. H3 verifies explicit Hot `Defer` marks for both shrink
variants and removes two wrapper markers; current counts are 85 default and 90
with `literal-types`. No `admit` or `assume` exists in the new proof prefix.

H1 now gives general `wf` named pool-native boundaries (`frame_partition_ok`,
`hot_repr_ok`, `trail_repr_ok`, `cold_repr_ok`, and `open_ingress_ok`) and the
verified `lemma_wf_implies_hot_defer_wf` extractor for unique capture with empty
Trail/Cold tiers. Inert `diff_log` appears only in `proof_compat_ok`, which says
an empty logical history has no compatibility residue and grants no physical
reconstruction, extent, or capture fact. H1 strengthens Cold reconstruction for
non-monotone saved lengths: an uncovered saved cell must be in bounds of its
layer above. It also guards dead capture flags by `TRACK`, matching DiffStore's
untracked contract. Named Cold and ingress transfer lemmas discharge
`maybe_shrink`. Targeted queries, runtime suites, and a clean full Vec-module
query are green (`117 verified, 0 errors`).

Remaining boundary: prove shrink-enabled Defer mark and
`runtime_push`/`runtime_pop`, then remove the in-scope external dispatch wrappers.
ApplyConfigured/ForceClosed conversion and mixed Trail/Hot/Cold restore remain
later policy-refinement milestones.

## 9. Forbidden shortcuts

- Trail and hot frames MUST NOT share a payload/header stack or a
  discipline-dependent invariant, because that recreates the defect.
- `DiffStore` MUST be the only authority selecting whether the open physical
  stack permits duplicates.
- Closed trail frames MUST retain chronological duplicate-preserving semantics;
  closed hot frames MUST retain unique semantics.
- Only the newest frame in the selected ingress stack may receive writes.
- Unbounded retention MUST NOT be implemented as an arbitrary large constant or
  trigger automatic migration.
- An ingress-protocol change MUST NOT occur with live history; `DynStore` is
  immutable after construction.
- Hot or cold frames MUST NOT accept writes through orphan extensions.
- Cold restore MUST NOT decode pairs before writing live data, because the
  compressed form is the restore plan.
- A zero hot budget MAY fuse conversion but MUST NOT skip the unique hot
  abstraction contract.
- Helper benchmarks MUST NOT replace end-to-end profile measurements.
- The production container MUST NOT be changed to make differential tests pass.
- Proof convenience MUST NOT alter executable architecture before performance
  lock.
- A green test suite is not a performance result, and a microbenchmark win is
  not semantic validation.

## 10. Deliverables and definition of done

| deliverable | required evidence | status |
|---|---|---|
| ruled policy-driven architecture | this document reviewed against token semantics | DESIGNED |
| three DiffStore ingress protocols | runtime tests for static and dynamic Inline/Parallel/Trail | BUILT — focused and compatibility suites green |
| arbitrary per-tier buffering | zero/finite/unbounded policy tests | BUILT — zero/finite/adaptive/unbounded boundaries green |
| trail-only SMT profile | differential traces and end-to-end benchmark | MEASURED — see E5 record |
| adaptive equality-saturation profile | explicit closed-history budgets, memory/restore traces, and benchmark | MEASURED — deterministic W/U/R planner, serial v2 rows, retained/high-water evidence, and negative automatic-threshold decision recorded in E5 |
| direct-unique restore profile | direct-compression traces and benchmark | MEASURED — see E5 record |
| correct conversions and promotions | boundary tests + arbitrary traces | BUILT — cross-tier and promote/write/remigrate regression green |
| all-store policy-matrix campaign | retained proptest artifacts | BUILT — 1,024-case complete matrix and full conformance gate green |
| end-to-end performance record | Criterion before/after/control tables | MEASURED AND OPTIMIZED — see E5 record |
| optimized algorithm and defaults | profiles, tradeoffs, lock revision | READY TO LOCK — explicit budgets/ratios and reclaim policy retained; serial data does not justify a default automatic threshold or preset change |
| complete proof plan against locked code | invariant and theorem dependency graph | DESIGNED IN OUTLINE |
| discharged proof scaffolds | full Verus and trust-surface gates | DEFERRED |

The execution campaign is complete only when all three stacks support arbitrary
retention, all three DiffStore protocols are correct, workload profiles are
measured and optimized end to end, and the executable algorithm/defaults are
locked with a recorded revision. It then transfers to proof work with no physical stack having
dual meaning. Proof completion is a subsequent milestone, not a condition for
locking execution.
