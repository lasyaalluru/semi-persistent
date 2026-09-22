# Three-tier proof milestone: general Hot-only `Defer` semi-persistence

**Status: H0 CHECKPOINTED AT `df10134`; H1 CHECKPOINTED AT `706a305`;
H2 CHECKPOINTED AT `5a5a6d4`; H3 EXPLICIT HOT DEFER MARKS FULLY VERIFIED
(`140 verified, 0 errors`); H4 HOT RESTORE NEXT.**

This task is the first bounded formal milestone after the three-tier runtime
lock. It consults `origin/main` at
`56a06a5adb450ad41b54ad14b7f66dd0b24a4201` for the established Vec proof
shape and adapts that shape to the authoritative three-tier fields.

The task has three outcomes, in order:

1. independently validate and checkpoint the existing Hot-only `Defer` proof
   prefix;
2. replace the stale general invariant boundary that still treats inert
   `diff_log` as physical authority;
3. prove complete Hot-only semi-persistence for unique-capture DiffStores,
   including push, pop, set, marks, and every Hot restore target.

Trail replay, Trail → Hot conversion, Hot → Cold conversion, mixed-tier restore,
adaptive planning, reclamation, and History/SyncGroup genealogy are explicitly
out of scope. They begin only after this milestone is complete.

## 1. Fixed references

- Working branch: `d21-exec`.
- Runtime lock: `d116f76`.
- Final runtime documentation: `44b8657`.
- Main proof template: `origin/main` at `56a06a5`.
- Runtime architecture:
  `containers-verus/doc/tasks/three-tier-frame-architecture-goal.md`.
- Geometric proof model:
  `containers-verus/doc/design/17-three-tier-frame-grid.md`.
- Existing proof record:
  `containers-verus/doc/tasks/three-tier-proof-progress.md`.
- Trust ledger: `containers-verus/doc/design/02-trust-boundary.md` and the
  task-local ledger in the architecture goal.

H0 is committed at `df101348d1617f2ebe8c963b50f7f95a642fbd77`.
Main remains reference material only and must not be merged over the working
proof branch.

## 2. The theorem boundary

The milestone applies when:

```text
TRACK
store.unique_capture_spec()
all logical frames are represented by hot_stack/hot_value_pool
trail_stack and trail_value_pool are empty
cold_stack, cold_index_runs, and cold_value_pool are empty
rollover is RolloverPolicy::Defer
```

Under that boundary, `hot_value_pool` is main's physical `diff_log` and
`hot_stack` is main's frame stack. The inert compatibility `diff_log` MUST NOT
appear in a physical reconstruction or capture argument.

The structural semi-persistence theorem is:

```text
mark at frame t
→ perform legal push/pop/set operations
→ optionally create more Defer marks
→ restore any structurally live Hot token k

ensures:
    view_after == snapshots_before[k]
    depth_after == k
    snapshots_after == snapshots_before[..k]
    surviving older Hot frames preserve their abstractions
    the surviving top capture state is rebuilt exactly
    subsequent writes remain first-capture-wins
```

This is a raw Vec structural theorem. Abandoned-future invalidation belongs to
`History`/`GenStamps` and is not claimed here.

## 3. Authoritative Hot invariant

Maintain a named, solver-controlled predicate such as `hot_defer_wf` with:

- `TRACK`, store well-formedness, and unique-capture ingress;
- Trail and Cold stacks/pools empty;
- `hot_stack.len == snapshots.len` and the required ghost coordinate length;
- empty-depth pool/cache/flag clauses;
- first Hot start at zero;
- bounded and adjacent closed Hot extents;
- effective top end equal to `hot_value_pool.len()`;
- each Hot `saved_len` equal to its snapshot length;
- `active_saved_len` equal to the top saved length, or minimum at depth zero;
- `stratum_unique` for every Hot extent;
- `frame_inv_range` over `hot_value_pool` for every Hot frame;
- exact open-top capture-flag/index-set equality;
- no stray capture flags.

Raw nested quantifiers SHOULD remain behind named predicates and extractor
lemmas because previous direct expansion caused solver instability.

## 4. Existing executable prefix to validate

The current working tree records these functions as individually verified:

- `lemma_frame_inv_range_capture_append`;
- `lemma_frame_inv_range_set_captured`;
- `lemma_frame_inv_range_set_outside`;
- `lemma_hot_defer_start_monotone`;
- `lemma_hot_defer_cell_eq_overlay`;
- `hot_defer_capture_checked`;
- `hot_defer_set_checked`;
- `hot_defer_mark_checked`;
- `hot_defer_restore_zero_checked`;
- `hot_defer_restore_nonzero_checked`.

The implementation claims that actual runtime branches call these checked
cores. Before committing, independently confirm that:

1. every checked core is non-`external_body`;
2. each core is reachable from the locked runtime branch it claims to verify;
3. every physical range reads `hot_value_pool`, never inert `diff_log`;
4. zero-target and surviving-prefix restore both close;
5. no `admit()` or `assume()` was introduced;
6. the external-body count and ledger match the source.

If these checks pass, commit this prefix before extending the invariant.

## 5. Ordered work

### H0 — Validate and checkpoint the interrupted prefix

Run each load-bearing query with the cache workaround:

```bash
cd containers-verus
touch src/vec.rs
cargo verus verify -- --verify-only-module vec --verify-function hot_defer_mark_checked

touch src/vec.rs
cargo verus verify -- --verify-only-module vec --verify-function hot_defer_restore_zero_checked

touch src/vec.rs
cargo verus verify -- --verify-only-module vec --verify-function hot_defer_restore_nonzero_checked
```

Run the complete ten-function batch recorded in
`three-tier-proof-progress.md`, focused runtime tests, formatting, source policy,
and trust-count checks. Fix discrepancies without weakening contracts.

Commit when green.

### H1 — Bridge general state to authoritative tier invariants

The current general `wf` still describes the old `diff_log`/Hot layout. Replace
that physical layer with named predicates for:

```text
frame_partition_ok
hot_repr_ok
trail_repr_ok     // statement only; proof deferred
cold_repr_ok      // retain existing structural facts; refinement deferred
open_ingress_ok
```

For this milestone, prove extractors showing that a general state satisfying
the Hot-only boundary yields `hot_defer_wf`.

Required structural facts:

- `cold.len + hot.len + trail.len == snapshots.len`;
- DiffStore protocol determines the open ingress tier;
- only the newest ingress frame is open;
- each header addresses its own pool;
- effective open end is the corresponding pool length;
- empty frame headers remain logical token boundaries;
- saved lengths map to snapshots across all three segments.

Do not prove conversion equivalence yet. Trail and Cold semantic refinements MAY
remain named opaque obligations, but general `wf` MUST stop asserting false
relationships to inert `diff_log`.

**Current H1 outcome (2026-09-14): FULL-MODULE VERIFIED.** `wf` now
composes `frame_partition_ok`, `hot_repr_ok`, `trail_repr_ok`,
`cold_repr_ok`, and `open_ingress_ok`; only `proof_compat_ok` mentions inert
`diff_log`, and only to rule out residue at zero logical depth. The pool-native
extractor `lemma_wf_implies_hot_defer_wf` verifies from general `wf`, `TRACK`,
unique capture, and empty Trail/Cold tiers. Pointwise accessors, both
constructors, executable depth, and three-segment saved-length dispatch verify.
`frame_saved_len_exec` lost its `external_body` marker. Cold reconstruction now
handles non-monotone per-frame saved lengths explicitly: every uncovered saved
cell must be in bounds of `layer_above_at(f)`, while cells beyond that layer must
be represented by a Cold run. Capture-flag obligations are guarded by `TRACK`,
matching the `DiffStore` contract that untracked flags are dead. `maybe_shrink`
verifies through named Cold and ingress transfer lemmas. A clean
`cargo verus verify -- --verify-only-module vec` reports `117 verified, 0
errors`. Focused runtime, policy-matrix, compatibility/literal-type, formatting,
no-admit/assume, and source-count gates remain recorded green; the source count
is 90 default / 95 with `literal-types`.

Commit the invariant bridge independently when its targeted queries and runtime
suite are green.

### H2 — Complete unique Hot mutators

Adapt main's verified set/pop/push proofs to `hot_value_pool`:

- first capture appends exactly one `(old_value,index)`;
- repeated writes do not append;
- writes outside `active_saved_len` do not enter history;
- marked pop captures a removed saved slot exactly once;
- push/regrow restores capture state without scanning or changing the frame
  abstraction;
- inner Hot frames transfer through locality;
- top `stratum_unique`, reconstruction, capture bridge, and no-stray clauses
  are preserved.

Remove external markers only from real checked bodies on the execution path.
Do not count an external wrapper's postcondition as proof evidence.

### H3 — Complete Hot marks

Use main's mark proof structure:

1. validate bounds;
2. preserve state through optional capacity reclamation;
3. prove every set flag is named by the open Hot slice;
4. call `prepare_mark`;
5. seal the prior effective end;
6. push one empty Hot header and snapshot;
7. establish empty top reconstruction and clear capture state;
8. transfer the prior top and deeper frames by locality.

Prove at least:

- `RolloverPolicy::Defer` with `ShrinkPolicy::Never`;
- `RolloverPolicy::Defer` with thresholded shrink.

Configured and forced rollover remain outside this milestone.

### H4 — Complete every Hot restore target

Adapt main's restore proof to `hot_value_pool` and the current batched
`restore_overlay` contract:

1. resize to the target snapshot length;
2. satisfy `begin_restore` from the open capture bridge;
3. prove the target Hot suffix reconstructs the snapshot;
4. replay/truncate the authoritative Hot pool;
5. transfer every surviving frame invariant;
6. rebuild surviving capture state with `finish_restore`;
7. re-establish no-stray flags and general `wf`.

Cover both:

- target zero, leaving every frame/pool empty;
- nonzero target, reopening the surviving Hot top.

Saved lengths are nonmonotone; reuse main's coverage/overlay argument rather
than assuming `saved_len <= live_len` across frames.

### H5 — Close the public Hot-only theorem

Connect checked cores to the real branches of:

- `push`, `pop`, and `set_index`;
- `try_mark_with(...Defer...)` and compatible internal mark paths;
- `try_restore`/`restore_frame` for every Hot-only target.

A caller starting from general `wf` plus the Hot-only boundary must obtain the
full structural semi-persistence postcondition without assuming
`hot_defer_wf` manually.

## 6. Validation requirements

### Targeted Verus

Always touch `src/vec.rs` immediately before function-scoped queries because
Verus per-function caching is flaky.

A function is complete only when its real body is checked and reports zero
errors. Record the exact command and result in `three-tier-proof-progress.md`.

### Full Verus

At the milestone boundary:

```bash
cd containers-verus
cargo verus verify -p semi-persistent-containers-verus
```

A reduced verified count caused by new external bodies is not a success. Explain
all count changes and update the trust ledger/count gate in the same commit.

### Runtime regression

At minimum:

```bash
cargo test -p semi-persistent-containers-verus --test three_tier_runtime
PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test three_tier_policy_matrix
cargo test -p semi-persistent-containers-verus --features "compat-all,literal-types"
```

Retain the static VecP performance guard; proof refactoring must not alter the
runtime algorithm or reintroduce a hot-path branch.

### Source policy

- No `admit()` or `assume()`.
- No changes to `containers/`.
- No proof by weakening public contracts.
- No use of inert `diff_log` as physical authority.
- No Trail/Cold/adaptive theorem claimed from the Hot-only boundary.
- Preserve inclusive terminology.

## 7. Commit policy

Commit regularly because proof work is solver-sensitive:

1. validated interrupted-prefix checkpoint;
2. general invariant bridge;
3. Hot mutators and marks;
4. Hot restore/public theorem;
5. ledger and validation corrections, if separate.

Do not amend after a hook failure; fix, restage specific files, and create a new
commit.

## 8. Stop conditions

This task is complete only when:

- the authoritative general invariant no longer lies about `diff_log`;
- general `wf` can establish the Hot-only boundary;
- Hot push/pop/set and Defer marks preserve that boundary;
- zero and nonzero Hot restore prove snapshot equality and survivor validity;
- the real public execution path consumes the checked cores;
- all targeted and full Verus checks are green with an audited trust count;
- focused and policy-matrix runtime regressions are green;
- the VecP hot path remains at baseline;
- progress and trust documentation match source.

If blocked, stop with the exact first failing query, source location, solver
message, and smallest unreduced obligation. Do not broaden into downstream tier
proofs or hide the blocker behind `external_body`.

## 9. Explicit next milestone

After this task, replan before starting either:

1. Trail chronological replay and Trail → Hot `dedupe_first` refinement; or
2. Hot → Cold sorted-run refinement and direct-run restore.

Do not start both automatically.
