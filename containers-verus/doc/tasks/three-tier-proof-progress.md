# Three-tier Vec proof progress

## 2026-09-14 — Milestone 1: unique Hot-only Defer

**Result: verified executable prefix.** Starting from clean `d21-exec` HEAD
`44b8657498f004c611bdda9d886a5621165ee0f2` (`origin/main` pinned at
`56a06a5adb450ad41b54ad14b7f66dd0b24a4201`), this milestone proves the
unique-capture, Hot-only state while rollover is deferred. No commit was
created.

### Authoritative projection

`Vec::hot_defer_wf` is a closed named predicate. `Vec::hot_defer_end` gives a
closed frame its header `end` and gives the writable top the effective end
`hot_value_pool.len()`. The projection reads `hot_value_pool` and `hot_stack`,
not `diff_log`, and states:

- `TRACK`, store well-formedness, and unique-capture ingress;
- empty Trail and Cold stacks/pools;
- `hot_stack.len == trail_frames.len == snapshots.len`;
- empty-history pool/ghost/cache/flag clauses;
- first start at zero, bounded header extents, and exact adjacency of closed
  header ends to the next start;
- `saved_len`/snapshot alignment and top `active_saved_len` alignment;
- `stratum_unique` for every Hot frame;
- `frame_inv_range` reconstruction for every Hot frame over its real pool
  extent;
- exact open-top capture bridge and no stray capture flags.

The temporary retained ghost boundaries are all zero and `full_trail` is empty
inside this projection. They provide logical frame coordinates only; physical
correctness is entirely pool-native.

### Verified proof and executable functions

Every query ran from `containers-verus` with `touch src/vec.rs` immediately
before `cargo verus verify -- --verify-only-module vec --verify-function NAME`.
The final batch exited zero; every item reported `1 verified, 0 errors`:

| function | role |
|---|---|
| `lemma_frame_inv_range_capture_append` | first-capture append preserves physical reconstruction |
| `lemma_frame_inv_range_set_captured` | a write at a captured top cell preserves reconstruction |
| `lemma_frame_inv_range_set_outside` | a write beyond saved extent is local to the live view |
| `lemma_hot_defer_start_monotone` | closed extent adjacency implies start monotonicity |
| `lemma_hot_defer_cell_eq_overlay` | pool-native frame-by-frame restore telescope |
| `hot_defer_capture_checked` | first unique capture appends once; duplicate capture is a no-op |
| `hot_defer_set_checked` | checked capture followed by raw set |
| `hot_defer_mark_checked` | seal prior header and open an empty Defer frame |
| `hot_defer_restore_zero_checked` | replay all Hot frames and retire history |
| `hot_defer_restore_nonzero_checked` | replay target suffix and rebuild surviving top flags |

The actual runtime branches call these cores. `runtime_capture` and
`runtime_set` select the checked unique cores; `runtime_push_frame` selects the
checked core for `Defer + ShrinkPolicy::Never`; and `runtime_restore_frame`
selects the checked zero/nonzero cores when non-fused unique history is entirely
Hot (Parallel protocol). InlineStore remains on its existing fused replay path,
where replay itself clears tags, avoiding a proof-induced second scan. External
dispatch wrappers are not counted as verified functions.

### Runtime validation

- `cargo test --test three_tier_runtime`: **30 passed, 0 failed**.
- `cargo test --test trail_vec`: **5 passed, 0 failed**.
- Added `unique_defer_restores_surviving_prefix_and_zero`, covering Inline and
  Parallel, repeated unique capture, pop/regrow with nonmonotone saved lengths,
  four explicit Defer marks including an empty frame, three surviving-prefix
  restores, target-zero restore, and final physical-stack emptiness.
- `cargo fmt --check`: initially identified only formatting in the new test;
  `cargo fmt` corrected it.

### Trust and parsing delta

The first attempted Vec query failed before verification because the locked
execution branch used policy datatypes declared outside `verus!` and planner
helpers containing unsupported std iterator/sort/arithmetic calls. The
resolution preserves runtime code:

- transparent external type registrations for `RolloverPolicy`, `TierLimit`,
  `ReclaimPolicy`, `TierPolicy`, `TierStats`, `AdaptiveInput`, and
  `AdaptiveReport`;
- one opaque registration marker for private-field `Ratio`;
- proof-erasure markers on `retained_closed_prefix` and
  `hot_frame_run_count`, whose std planner operations are unsupported.

This is **three new `external_body` markers** relative to `a1cf1bf`: one opaque
type and two execution-only planner functions. `Vec::with_store_mode` and
`Vec::with_store_policy` now verify, including the empty unique-state
`hot_defer_wf` postcondition, so the pre-existing `with_store_policy` marker is
removed. Net source counts are 96 default and 101 with `literal-types`; axiom
counts remain 1 and 6. The checked milestone contains no `external_body`,
`admit`, or `assume`.

### Remaining work / first boundary

There is no failing obligation inside the stated Hot-only milestone: both zero
and nonzero Hot restore closed. The first unproved boundary is the transition
from general `Vec::wf` to `hot_defer_wf`: general `wf` still describes the inert
`diff_log` shadow and mixed Trail/Hot/Cold ownership. Consequently these remain
outside this milestone:

1. `runtime_push` and `runtime_pop`, including marked pop/re-entry;
2. shrink-enabled Defer marks;
3. ApplyConfigured and ForceClosed Trail-to-Hot/Hot-to-Cold conversion;
4. survivor promotion from Cold or Hot into Trail ingress;
5. mixed-tier restore and removal of the outer runtime/wrapper markers;
6. verified construction of `hot_defer_wf` from the public general invariant.

The next milestone should prove the protocol-specific partition/refinement
predicate that selects Hot-only Defer from general state, then discharge
push/pop or the first migration edge without reintroducing `diff_log` as a
physical authority.


## 2026-09-14 — Milestone H1: pool-native general invariant bridge

**Result: H1 fully verified, including the full Vec-module gate.** Work started
from clean H0 commit `df101348d1617f2ebe8c963b50f7f95a642fbd77` with
`origin/main` pinned at
`56a06a5adb450ad41b54ad14b7f66dd0b24a4201`. `containers/` was not changed.

### General invariant replacement

General `Vec::wf` no longer grants physical authority to inert `diff_log`. It
now composes these closed named predicates:

- `frame_partition_ok`: exact Cold + Hot + Trail header count against snapshots
  and ghost frame coordinates, plus saved-length mapping for all three age
  segments; zero-length extents retain their headers/token identity;
- `hot_repr_ok`: Hot header bounds/adjacency, pool-length effective newest end,
  per-frame uniqueness, and reconstruction over `hot_value_pool`;
- `trail_repr_ok`: Trail header bounds/adjacency, pool-length effective newest
  end, and the named chronological reconstruction boundary over
  `trail_value_pool`;
- `cold_repr_ok`: the pre-existing run/value pool partition, empty-pool facts,
  run disjointness, and named Cold reconstruction boundary;
- `open_ingress_ok`: `DiffStore::unique_capture_spec()` selects Hot versus Trail,
  requires only the newest selected frame to be open, and binds capture flags to
  that real pool.

`proof_compat_ok` is the only general predicate mentioning `diff_log`; it merely
rules out inert compatibility residue at zero logical depth. It supplies no
capture, extent, reconstruction, or refinement fact.

`hot_defer_wf` no longer requires compatibility ghost contents or coordinate
values to be empty/zero; it remains wholly pool-native. The pointwise accessors
avoid repeatedly exposing nested quantifiers. The bridge
`lemma_wf_implies_hot_defer_wf` requires general `wf`, `TRACK`, unique capture,
and empty Trail/Cold stacks and pools, and establishes `hot_defer_wf` without a
Trail/Cold conversion theorem.

### Exact targeted verification

Every function-scoped query ran from `containers-verus` with `touch src/vec.rs`
immediately before `cargo verus verify -- --triggers-mode silent
--verify-only-module vec --verify-function NAME`. Each listed function reported
`1 verified, 0 errors`:

- H1 accessors/bridge: `lemma_wf_named_parts`, `lemma_hot_repr_at`,
  `lemma_open_ingress_hot_at`, `lemma_wf_implies_hot_defer_wf`, and
  `lemma_index_set_transfer`;
- constructor/dispatch framing: `with_store_mode`, `with_store_policy`,
  `depth_exec`, `frame_saved_len_exec`, `lemma_hot_start_monotone`,
  `lemma_untracked_diff_log_empty`, and the retargeted
  `lemma_phys_cell_eq_overlay`;
- the complete H0 set remained green:
  `lemma_frame_inv_range_capture_append`,
  `lemma_frame_inv_range_set_captured`,
  `lemma_frame_inv_range_set_outside`,
  `lemma_hot_defer_start_monotone`,
  `lemma_hot_defer_cell_eq_overlay`,
  `hot_defer_capture_checked`, `hot_defer_set_checked`,
  `hot_defer_mark_checked`, `hot_defer_restore_zero_checked`, and
  `hot_defer_restore_nonzero_checked`.

The new partition facts make the executable body of `frame_saved_len_exec`
checkable across Cold, Hot, and Trail. Its `external_body` marker was removed.
No marker was added.

### Runtime, formatting, and source checks

- `cargo test -p semi-persistent-containers-verus --test three_tier_runtime`:
  **30 passed**.
- `cargo test -p semi-persistent-containers-verus --test trail_vec`:
  **5 passed**.
- `PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test
  three_tier_policy_matrix`: **4 passed**, including the generated matrix.
- `cargo test -p semi-persistent-containers-verus --features
  "compat-all,literal-types"`: all executed unit/integration/doc tests passed;
  only the maintained stress/measurement/child-scenario tests were ignored.
- `cargo fmt --all -- --check` and `git diff --check`: passed.
- Executable source scan found zero `admit(...)`/`assume(...)` calls.
- Source-derived marker count: **90 default**, plus **5** `literal-types`
  registrations = **95**; delta from H0 is **-6 / -6**. One proved accessor
  marker and five unreachable legacy scaffold markers were removed. Axiom
  counts remain **1 default / 6 literal-types**.
- The separate partial-API checker remains red with the same broad legacy
  allowlist drift (40 reported public partial functions); H1 changed none of
  those APIs and introduced no new public function.

### Full verification resolution

The first full-module runs exposed unreachable legacy proof bodies that encoded
the former two-stack/inert-log model. Those bodies were retired rather than
retargeted because the executable dispatch already returned through its
external runtime path and the old obligations were not conjuncts of the new
`wf`. `lemma_phys_cell_eq_overlay` was retargeted to authoritative
`hot_value_pool` and remains verified.

After that retirement, `maybe_shrink` exposed two genuine H1 framing defects.
First, Cold reconstruction had omitted the per-cell coverage needed for
non-monotone frame lengths. `cold_reconstructs(f)` now states that every
uncovered `c < saved_len(f)` is in bounds of `layer_above_at(f)` and equal to
that layer; a saved cell beyond the layer must therefore be represented by a
Cold run. Second, `open_ingress_ok` constrained capture bits while `TRACK` was
false even though `DiffStore` intentionally leaves untracked bits dead. Those
bit-content clauses are now guarded by `TRACK`.

Named pointwise/transfer lemmas keep both nested invariants solver-controlled.
The following clean queries pass:

```text
lemma_cold_reconstructs_at        1 verified, 0 errors
lemma_cold_reconstructs_transfer  1 verified, 0 errors
lemma_open_ingress_transfer       1 verified, 0 errors
maybe_shrink                      1 verified, 0 errors
full vec module                 117 verified, 0 errors
```

The full gate command was `touch src/vec.rs && cargo verus verify --
--verify-only-module vec`. No `external_body`, `admit`, or `assume` was added to
close H1.

## 2026-09-15 — H2 push/regrowth checked core

**Result: internal Hot-only push/regrowth core verified; runtime/public wiring is
not yet claimed.**

The geometric frame model is now recorded in
`doc/design/17-three-tier-frame-grid.md`. It treats indices as horizontal
columns, frame age as the vertical axis, and each frame's `saved_len` as an
independent boundary. It also records that Hot and Cold payload counts are
bounded by `saved_len`, while a Trail frame may contain arbitrarily many
chronological duplicates until `dedupe_first` establishes the unique Hot bound.
Persistent Hot is unordered; sorting is a transient, local Hot-to-Cold
translation step that preserves uniqueness and the frame abstraction.

`lemma_frame_inv_range_grow_layer` formalizes horizontal extension of the live
row. A captured column is independent of that row; an uncovered column was
already in bounds of the old row and transfers through prefix equality. It
requires no relation between adjacent frame saved lengths.

`hot_defer_push_checked` copies the locked `runtime_push` algorithm: append one
live value and a false capture bit, then restore the bit iff the appended index
is strictly below the active frame's own `saved_len`. Re-entry appends no Hot or
canonical history because the earlier pop already covered that column. The core
preserves `hot_value_pool`, `full_trail`, snapshots, frame coordinates, and
`active_saved_len`, and re-establishes `hot_defer_wf`.

Exact verification from `containers-verus`, touching `src/vec.rs` before each
query:

```text
lemma_frame_inv_range_grow_layer  1 verified, 0 errors
hot_defer_push_checked            1 verified, 0 errors
lemma_captured_in_range_dedupe    1 verified, 0 errors
full vec module                 119 verified, 0 errors
```

`lemma_captured_in_range_dedupe` received only `spinoff_prover` isolation after
the larger module context exhausted its previous shared query; its theorem and
body are unchanged. No `external_body`, `admit`, or `assume` was added.

Scope boundary: `runtime_push` and public `push` remain pre-existing trusted
wrappers, and this checked core currently proves `hot_defer_wf`, not general
`wf`. The next H2 slice must preserve canonical `wf_for_snap`, wire this core
into an in-scope checked dispatcher, and then close pop/set before removing the
public mutator markers.

## 2026-09-15 — H2 Hot mutators through public wrappers

**Result: unique-capture all-Hot push, pop, and set are checked from general
`wf` through their public wrappers.** Non-Hot Trail/Cold states remain behind
narrow fallbacks whose precondition is the exact negation of the checked
`hot_defer_scope`; those fallbacks belong to later tier milestones.

The proof now maintains two intentionally different histories:

- `hot_value_pool` is authoritative first-capture storage and grows at most once
  per `(frame,index)` column;
- canonical ghost `full_trail` appends one chronological old-value event for
  every in-frame set/pop capture, including duplicates.

`lemma_frame_inv_range_append_duplicate` proves that a later vertical Trail
event preserves the frame's first hitter. `lemma_frame_inv_range_shrink_layer`
and `lemma_frame_inv_range_pop_last` prove horizontal contraction: capture the
departing saved column, while every higher absent saved column was already
forced into the covered arm. `lemma_frame_inv_range_grow_layer` handles push
and re-entry. None assumes adjacent saved lengths are monotone.

`hot_defer_capture_canonical_checked`, `hot_defer_push_checked`,
`hot_defer_pop_checked`, and `hot_defer_set_checked` preserve both
`hot_defer_wf` and general `wf`. `hot_defer_scope_exec` proves the executable
dispatch criterion. Checked `runtime_push`, `runtime_pop`, and `runtime_set`
route the Hot scope to those cores; only `!hot_defer_scope` reaches the trusted
fallbacks. Public `push`, `pop`, and `set_index` now verify without
`external_body`, preserving their prior contracts byte-for-byte.

Exact results:

```text
all new grid/transfer/assembly lemmas       1 verified, 0 errors each
hot_defer_capture_canonical_checked         1 verified, 0 errors
hot_defer_push_checked                      1 verified, 0 errors
hot_defer_pop_checked                       1 verified, 0 errors
hot_defer_set_checked                       1 verified, 0 errors
runtime_push/runtime_pop/runtime_set        1 verified, 0 errors each
public push/public pop/public set_index     1 verified, 0 errors each
full vec module                           134 verified, 0 errors
three_tier_runtime                          30 passed, 0 failed
```

`maybe_shrink` and `lemma_captured_in_range_dedupe` received only
`spinoff_prover` isolation after the larger module context triggered the known
Verus rlimit-statistics panic; their contracts and proof bodies remain checked.
No new trusted body or assumption was added. Removing the three public mutator
markers changes the source-derived count from 90 to **87 default**, plus 5
`literal-types` registrations = **92**.

Next: H3 must connect checked `maybe_shrink` and `hot_defer_mark_checked` through
explicit `RolloverPolicy::Defer` dispatch for both `ShrinkPolicy::Never` and
thresholded shrink, then remove the in-scope mark-wrapper trust.

## 2026-09-15 — H3 explicit Hot Defer marks

**Result: explicit unique-capture all-Hot `RolloverPolicy::Defer` marks verify
through `try_mark_with` for both `ShrinkPolicy::Never` and
`IfOverallocated`.**

`hot_defer_mark_checked` now requires and preserves general `wf` in addition to
the physical Hot projection. A mark seals the prior Hot header, opens an empty
Hot frame, pushes the unchanged live view into `snapshots`, and pushes the
unchanged `full_trail.len()` as the canonical delimiter. The former top's layer
becomes an equal snapshot; the new top range is empty. Equal delimiters preserve
empty-frame token identity, and no adjacent saved-length relation is assumed.

`maybe_shrink` exposes equality of every physical tier sequence.
`hot_defer_post_mark_shrink_checked` checks the post-mark capacity-only calls,
and `hot_defer_mark_with_shrink_checked` composes pre-mark shrink, canonical/
physical mark, and post-mark shrink for both variants. The existing allocator
helpers remain in the documented capacity-only boundary and prove that element
sequences are unchanged.

`runtime_push_frame` is now a checked dispatcher. The explicit Hot+Defer branch
calls the checked composite for either shrink variant. Only the exact complement
`APPLY_CONFIGURED || !hot_defer_scope || !Defer` reaches
`runtime_push_frame_fallback`; shrink is intentionally absent from that
complement. `push_frame_with_options` and `mark_with_options` are checked, so
`try_mark_with` reaches the verified branch without an in-scope trusted wrapper.
Configured and forced rollover remain later milestones.

Exact results:

```text
hot_defer_mark_checked                    1 verified, 0 errors
lemma_wf_for_snap_transfer                1 verified, 0 errors
hot_defer_post_mark_shrink_checked        1 verified, 0 errors
hot_defer_mark_with_shrink_checked        1 verified, 0 errors
runtime_push_frame dispatcher             1 verified, 0 errors
push_frame_with_options                    1 verified, 0 errors
mark_with_options                          1 verified, 0 errors
try_mark_with                              1 verified, 0 errors
full vec module                          140 verified, 0 errors
three_tier_runtime                         30 passed, 0 failed
```

No persistent Hot sortedness is introduced; the mark opens an unordered empty
unique frame. No trust marker or assumption was added. Removing two explicit
mark-wrapper markers changes the source-derived count from 87 to **85 default**,
plus 5 `literal-types` registrations = **90**.

Next: H4 must preserve canonical/general `wf` through zero and nonzero Hot
restore, factor exact-negation restore fallback (including fused Inline replay),
and remove the in-scope `restore_frame` trust.

## 2026-09-15 — H4 canonical history prefix (work in progress)

Fresh checkout baseline at `de4b4d2`:

```text
cargo verus verify -p semi-persistent-containers-verus
containers package: 2227 verified, 0 errors
vstd dependency:    2044 verified, 0 errors (separate count)

cargo test -p semi-persistent-satcore -p semi-persistent-egraph --locked
exit 0; satcore: 10 passed, 0 failed; egraph suites passed
```

The frame-grid review found missing mandatory coverage in the illustrative
stack and a replay diagram that placed resizing after writes. Chapter 17 now
shows the saved-domain/coverage matrix, resizing before replay over a fixed
target window, and explicit preservation of the surviving canonical prefix.
The sparse-frame equivalence also states its newer-layer input.

The existing nonzero Hot restore helper discarded all `full_trail` entries
while retaining older delimiters and snapshots. This sufficed for its physical
`hot_defer_wf` postcondition, but could not preserve canonical reconstruction.
It now retains `pre.full_trail[..pre.trail_frames[target]]`.
`lemma_restore_canonical_prefix` transfers each surviving canonical frame's
range and newer layer; the new live view equals the former newer snapshot for
the surviving top. Both Hot restore helpers now export general `wf` as well as
the physical projection. Zero restore clears inert compatibility storage to
establish its zero-depth clause; that storage supplies no reconstruction fact.

Targeted checks from `containers-verus`, touching `src/vec.rs` before each:

```text
cargo verus verify -- --verify-only-module vec --verify-function lemma_restore_canonical_prefix
1 verified, 0 errors
cargo verus verify -- --verify-only-module vec --verify-function hot_defer_restore_zero_checked
1 verified, 0 errors
cargo verus verify -- --verify-only-module vec --verify-function hot_defer_restore_nonzero_checked
1 verified, 0 errors
```

This is not an H4 milestone checkpoint. Full Vec re-verification is pending.
Inline fused capture clearing, checked public restore dispatch, full-package
and runtime gates, and trust-marker removal remain. No trust marker or
assumption was added; the public contracts are unchanged.

### H4 follow-up — fused replay and checked public dispatch

The initial canonical-prefix slice passed full Vec verification:

```text
cargo verus verify -- --verify-only-module vec
142 verified, 0 errors
```

`DiffStore` now exposes `restore_entries_clear_capture_spec`, refines the
runtime accessor to it, and preserves the capability across mutations. Its
`restore_overlay` contract additionally states that, for a fused-clear store,
any still-set capture flag names no entry in the replayed range. Inline's
backward replay loop proves this by excluding every already-replayed index;
Parallel and Trail retain their existing non-fused behavior. DynStore delegates
the same capability and postcondition. No store algorithm changed.

Full store-module checks with `cargo verus verify -- --verify-only-module MODULE`:

```text
inline_store:   29 verified, 0 errors
parallel_store: 29 verified, 0 errors
trail_store:    27 verified, 0 errors
dyn_store:      26 verified, 0 errors
```

Both Hot restore helpers now use fused clearing when supported and pre-clearing
otherwise, and establish all-clear before rebuilding survivor capture state.
Each passed a function-scoped check (1 verified, 0 errors). The checked runtime
dispatcher covers all Hot states; only its exact complement reaches the renamed
`runtime_restore_frame_fallback`. The public `restore_frame` contract is
unchanged and its trust marker is removed. Cold allocation reclamation uses the
existing sequence-preserving capacity primitive and the canonical transfer
lemma. The default trust count is now 84 (plus 5 literal-type registrations).

```text
cargo verus verify -- --verify-only-module vec --verify-function '*restore*'
14 verified, 0 errors (includes runtime_restore_frame, restore_frame, restore)
cargo fmt --all -- --check
exit 0
cargo test -p semi-persistent-containers-verus --test three_tier_runtime
30 passed, 0 failed
```

The full-package Verus, feature-test, and 1024-case differential-policy gates
are running. These edits remain uncommitted until those gates pass. This
partial Hot milestone does not discharge mixed-tier fallback trust.

H4 gate update: the feature suite passed (exit 0), and
`PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test three_tier_policy_matrix`
passed all four tests. The generator reads `PROPTEST_CASES`; each generated tape
runs through every profile/backend combination.

The first package-level Verus command reused cached build output and produced
no fresh verification summary. It is NOT counted as a full-package check.
A fresh check was forced with:

```text
touch containers-verus/src/vec.rs
cargo verus verify -p semi-persistent-containers-verus -- --time-expanded
```

That fresh run remains pending; it is the remaining milestone gate before
committing H4.


### H4 checkpoint — all milestone gates passed

The forced full-package invocation above completed with **2232 verified,
0 errors** (4m 52s). This is a fresh package result, not the cached command.
Together with the 30 runtime tests, full `compat-all,literal-types` test suite,
1024-case policy matrix (four tests), formatting, and source-derived 84+5
trust-marker count, it closes H4's gates. No public theorem was weakened.

The checkpoint establishes exact snapshot restoration and surviving-prefix
validity through the real public all-Hot path, including Inline fused capture
clearing and Parallel pre-clearing. The `!hot_defer_scope()` fallback remains
trusted; this is not completion of Trail, Cold, or all-policy proofs.

Next is N2/H5 downstream composition. Inspection has identified missing public
success postconditions in `ListArena::try_restore` and `EClasses::try_restore`,
and missing archive-prefix postconditions in the Map/BPlus public surface.
These should expose already-established internal facts without changing the
runtime algorithms. The full package currently verifies their existing,
weaker contracts against the updated Vec theorem; that alone does not prove
stronger public snapshot-stack guarantees.

## 2026-09-15 — Shared physical frame meaning (in progress)

The user's updated execution plan is preserved in
`all-tier-semi-persistence-goal.md`. It places the shared physical contract and
all-tier Vec closure before the downstream public-contract pass. The H4 local
checkpoint is `740c876`; no push is authorized.

`range_saved_value` interprets a physical Trail/Hot range as the first
chronological value at an index, or `None` when absent. Its contract is derived
from `frame_cell_inv` and `first_hitter`. `frame_saved_len` reads the appropriate
physical header, and `frame_saved_value` uses Trail/Hot pools or Cold runs.
`lemma_frame_saved_value_contract` derives the same covered/inherited rule for
all three tiers from the existing invariant; it does not add an assumption or
use `diff_log` as storage authority.

`lemma_overlay_saved_value` proves length preservation and the earliest-hit
mapping for backward replay, including duplicate Trail writes. The checked,
inlined `replay_physical_range` exports that meaning alongside the unchanged
DiffStore replay/capture guarantees. The real Trail and Hot replay sites now
call it. `lemma_physical_frame_step` proves the fixed-window telescope step:
within the frame's saved domain the result equals that frame's snapshot, even
when that domain is shorter than the target buffer. The full runtime
composition and Cold replay still need to consume this shared argument.

Targeted Verus evidence (touching `src/vec.rs` before each invocation):

```text
cargo verus verify -- --verify-only-module vec --verify-function '*saved_value*'
2 verified; combined tier bridge exceeded the default resource limit
```

The bridge was then factored to expose only the selected tier, reusing
`lemma_hot_repr_at` for Hot. No resource-limit increase was needed:

```text
cargo verus verify -- --verify-only-module vec --verify-function lemma_frame_saved_value_contract
1 verified, 0 errors
cargo verus verify -- --verify-only-module vec --verify-function replay_physical_range
1 verified, 0 errors
cargo verus verify -- --verify-only-module vec --verify-function lemma_physical_frame_step
1 verified, 0 errors
cargo fmt --all -- --check
exit 0
```

A fresh full-package run (`touch containers-verus/src/vec.rs`, then
`cargo verus verify -p semi-persistent-containers-verus -- --time-expanded`) and
the runtime, feature, and 1024-case policy gates are running. This work is
uncommitted pending those results and is not an all-tier completion claim.

### Shared-frame checkpoint — milestone gates passed

The fresh full-package run completed with **2237 verified, 0 errors** (4m 48s),
five more checked facts than H4. The 30 runtime regressions, full
`compat-all,literal-types` suite, and 1024-case differential matrix (four tests)
all passed. Formatting and `git diff --check` passed. Trust remains 84 default
markers plus five literal-type registrations; no assumptions were added.

This checkpoint establishes the shared interpretation and checked Trail/Hot
range replay. It does not claim the entire mixed-tier orchestrator is checked.
Next: discharge the default Cold `DiffStore::restore_run` path used by Inline
and DynStore, then connect Cold frame replay and the fixed-window telescope.


### Cold run primitive — checked backends

Replaced the trusted default `DiffStore::restore_run` with a required contract
implemented by all four backends. Inline proves a bounded re-encoding loop that
preserves tags even with `TRACK=false`; DynStore delegates to checked Inline,
Parallel, and Trail implementations. Removed the unused trusted usize-write
scaffold. Custom DiffStore implementations must now provide `restore_run`.

A runtime regression first reproduced overflow at `base=u64::MAX` in the old
Inline and dynamic defaults. The fixed loop clamps before addition; all three
regressions now pass, including explicit capture-tag preservation. Targeted
Verus checks report Inline 2 verified and DynStore 1 verified, zero errors.
Trust falls from 84 to 82 default markers (plus five literal-type registrations).
The fresh default full-package run passed: **2240 verified, 0 errors**
(4m 51s). The `compat-all,literal-types` suite passed, including all 30
three-tier runtime tests and the three new regressions. The release differential
policy matrix passed all four tests with `PROPTEST_CASES=1024`. E-graph and
SAT consumer suites passed 1267 tests, with 45 ignored and zero failures.
Formatting, source trust counts, and `git diff --check` passed.

The mixed-tier restore orchestrator is still trusted; checked run copies alone
do not close it.

The fresh `literal-types` Verus run also passed: **2240 verified, 0 errors**
(4m 57s). Both feature configurations were checked from freshly touched source.


### Mixed-tier reconstruction — local pre-state and batched induction

The preceding Cold-run checkpoint is `d174186`. The next reconstruction phase
uses `let ghost pre = *self` and adds no persistent fields or ghost history.
`frame_saved_value` remains a projection of physical pools. Reconstruction is
separate from final well-formedness: intermediate buffers need only agree with
the relevant pre-state layer on their shared index domain.

Cold replay now proves adjacent-run disjointness implies pairwise separation,
composes the checked run copies, bridges the resulting mapping to
`frame_saved_value`, and calls `lemma_physical_frame_step`. A checked reverse
Cold frame traversal preserves the fixed target window even when saved lengths
zigzag. Empty frames need no special logical case.

Trail/Hot replay remains one batched pool overlay per tier. A per-cell induction
uses the captured-or-inherited contract and `lemma_overlay_split` to show that
the batch implements newest-to-oldest frame replay. Narrow layout accessors
supply only required bounds and mapping facts. Profiling identified automatic
unfolding of `wf` as a source of unrelated history instantiations; keeping it
opaque makes the induction verify at the default limit.

`replay_all_tiers_checked` consumes the checked tier results in runtime order.
`reconstruct_target_checked` adds the actual one-time resize and capture
preparation. It returns exactly `pre.snapshots[target]`, preserves every history
field, and preserves store protocols while only decreasing capture flags.
`runtime_begin_restore` is now checked against resized flags and the original
physical ingress pool; its trusted marker is removed. Default trust is 81
markers, plus five literal-type registrations.

The actual mixed-tier fallback calls this reconstruction phase. Its remaining
truncation, canonical-prefix retention, promotion, and capture rebuilding are
still trusted and are not covered by this milestone's completion claim.
Configured/forced/adaptive conversions and mixed-tier mutations also remain.

Targeted checks passed for Cold run composition, the physical/frame bridge,
Cold frame and suffix execution, Trail/Hot layout and cell induction, batched
execution, the mixed-tier replay helper, capture preparation, and the complete
reconstruction wrapper. Fresh default full-package verification passed:
**2259 verified, 0 errors** (3m 24s). Fresh `literal-types` verification also
passed **2259 verified, 0 errors** (3m 26s). The `compat-all,literal-types`
suite passed, including 30 three-tier runtime tests and three Cold regressions.
The release policy matrix passed all four tests with `PROPTEST_CASES=1024`.
The e-graph/SAT consumer suite passed 1267 tests (45 ignored), with zero
failures. Formatting, `git diff --check`, and the 81 + 5 source trust count
passed. All milestone gates are green; the next action is a local signed commit.


Next preservation audit: `cold_repr_ok` currently contains pooled layout,
adjacent-run disjointness, and reconstruction on the saved domain. It does not
explicitly constrain every stored Cold value to that domain or exclude empty
runs. Promotion to a Hot `frame_inv_range` needs the former; the documented
`cold_run_count <= cold_value_count` theorem needs nonempty runs. Establish these
relationships through run formation and preserve them, without adding ghost
history or assuming the relationships. Also export a precise contract for
`cold_value_cut` when verifying physical-prefix truncation.


### Restore prefixes and zero-target closure

The mixed-tier reconstruction checkpoint is `9a16936`. Reconstruction now also
ensures every capture flag is clear: pair-tier header monotonicity proves any
replayed ingress suffix contains all originally flagged indices. Fused stores
clear those indices during the existing batch; other stores retain the checked
pre-clear protocol. No extra capture-clearing pass or persistent state is added.

`restored_history_prefix` specifies exact retained Cold, Hot, Trail, snapshot,
canonical-boundary, and canonical-entry prefixes. The checked runtime
`truncate_restored_history_checked` executes the existing tier-specific cuts
and leaves the reconstructed store unchanged. It also establishes
`wf_for_snap`, using the unchanged newer layer of the surviving canonical top.
The Cold value cut now exports its exact physical selector contract.

A regression reproduced a zero-target invariant violation: an allowed nonempty
inert `diff_log` at positive depth survived a Trail zero restore. The restored
value was correct, confirming the shadow was not reconstruction authority.
Zero-target truncation now clears that compatibility vector; nonzero truncation
preserves it. `restore_zero_all_tiers_checked` composes reconstruction, exact
empty-prefix retirement, active-length reset, and existing capacity reclamation
to establish the general invariant for all tier layouts. The dispatcher routes
zero targets through checked paths, and the trusted mixed-tier fallback now
requires a strictly positive target.

Targeted checks passed for capture inclusion/clearing, prefix truncation,
partition and canonical-prefix preservation, zero-target closure, strengthened
reconstruction, and restore dispatch. The fresh default full-package run passed
**2267 verified, 0 errors** (4m 38s). Fresh `literal-types` verification also
passed **2267 verified, 0 errors** (4m 55s). The feature suite passed, including the new zero-depth regression and all
30 three-tier runtime tests. The 1024-case differential matrix passed all four
tests. E-graph/SAT consumers passed 1267 tests (45 ignored), with zero failures.
Formatting, `git diff --check`, and trust-count checks passed. All milestone
gates are green. Trust
remains 81 default markers plus five literal-type registrations: this narrows
the remaining fallback's scope without replacing it with another trusted body.
Nonzero physical-invariant restoration and survivor promotion remain unfinished.


### Retained Trail/Hot representation after truncation

The preceding prefix and zero-target checkpoint is `76c56fc`. The actual
`truncate_restored_history_checked` helper now additionally establishes
`hot_repr_ok` and `trail_repr_ok`. Each retained physical frame keeps its
original range, snapshot, and newer layer. In particular, a newly open top
ends at the same boundary that previously sealed it, and sees the restored
target snapshot as its unchanged newer layer. Unique Hot captures transfer
through equality of the retained pool range.

The proof uses a raw-header-end projection and narrow layout accessors; these
are specifications, not new stored fields. Per-frame transfer and separate
Trail/Hot quantifiers keep unrelated history predicates opaque. The combined
proof passes at the default resource limit. Runtime execution and batching
are unchanged. Cold representation preservation, survivor promotion, and the
remaining nonzero mixed-tier fallback are still unfinished.

Fresh full-package verification passed in both configurations: **2271 verified,
0 errors**, default (4m 52s) and `literal-types` (4m 54s). The
`compat-all,literal-types` suite and all four release differential policy tests
with `PROPTEST_CASES=1024` passed. E-graph/SAT consumers passed 1267 tests
(45 ignored), with zero failures. Formatting and whitespace checks passed.
Trust remains 81 default markers plus five literal-type registrations.


### Retained Cold representation after truncation

The retained pair-tier checkpoint is `f2fb8d7`. The checked truncation helper
now also establishes `cold_repr_ok`, so it exports all three physical tier
invariants alongside exact physical/canonical prefixes and `wf_for_snap`.

Frame/run offset monotonicity proves each cut retains complete Cold run slices
and payload ranges. These offset facts do not assume monotone saved lengths.
Explicit covering-run witnesses transfer coverage in both directions; pairwise
run separation makes the selected covering run unique and transfers its value
through the retained payload prefix. The unchanged snapshot/newer-layer lemma
then transfers each retained frame's reconstruction contract, including the
new top and empty frames. No fields, runtime work, or trust markers are added.

Targeted Cold layout, coverage, value, and representation checks pass at the
default resource limit. A full run exposed a resource-limit regression in the
zero-target caller; factoring its final empty-history invariant check into a
small proof resolved the targeted check without increasing limits. Fresh full
verification passed **2278 verified, 0 errors** in both default (4m 54s) and
`literal-types` (4m 53s) configurations. The feature suite passed; the release
differential policy matrix passed all four tests with `PROPTEST_CASES=1024`.
E-graph/SAT consumers passed 1267 tests (45 ignored), with zero failures.
Formatting and whitespace checks passed; trust remains 81 default markers
plus five literal-type registrations.
Survivor promotion/capture rebuilding, conversions, and the remaining public
mixed-tier paths are still unfinished.


### Capture rebuilding and retained-ingress restore

The Cold-prefix checkpoint is `389c7eb`. `finish_restore_range_checked` now
proves that flags across the whole live buffer equal membership in the retained
physical frame. It passes the current live length to the store protocol, so
saved lengths may still zigzag or exceed the restored live length.
`finish_survivor_checked` sets the surviving saved length and proves the full
container invariant once the survivor occupies the selected writable tier.
A separate transfer proof preserves all frame contracts through these flag and
cached-length changes. The existing promotion runtime now calls this checked
finalizer; its frame-moving operations remain trusted.

`restore_retained_ingress_checked` composes reconstruction, all-tier truncation,
flag rebuilding, and checked capacity reclamation. Runtime dispatch selects it
when the target leaves a frame in the selected writable tier, including mixed
histories with older immutable Cold/Hot frames. This removes those executions
from the trusted restore fallback. Cases needing Hot-to-Trail or Cold-to-ingress
survivor movement still require promotion proofs. No trust markers or fields
are added, and Trail/Hot replay remains batched.

Targeted range finalization, history transfer, survivor finalization, capacity
reclamation, and retained-ingress composition checks passed. Full default
verification passed **2284 verified, 0 errors** (5m 00s); `literal-types` also
passed **2284 verified, 0 errors** (4m 55s). The feature suite passed, and the
1024-case differential policy matrix passed all four tests. E-graph/SAT consumers
passed 1267 tests (45 ignored), with zero failures. Formatting and whitespace
checks passed. Trust remains 81 default markers plus five literal registrations.
Existing differential tests deliberately
restore through every populated tier for each backend and include shrink/grow
histories; those cover the newly dispatched path and remaining promotion path.


### Checked Hot-to-Trail survivor promotion

The capture-rebuilding checkpoint is `717873f`. Hot-to-Trail promotion now has
an exact physical postcondition: the Hot prefix is retained, its newest frame's
complete payload moves to a single Trail frame rebased to zero, and all other
fields remain unchanged. The proof preserves the first hitter under rebasing,
the retained Hot frame ranges, the logical frame partition, and all canonical
and Cold contracts. Empty frames retain their header and snapshot identity.
Header-offset ordering supplies bounds without any saved-length ordering.

`promote_hot_survivor_checked` performs the move with one reserve and direct
Copy writes into the retained Trail allocation. This eliminates the temporary
vector and second copy. A regression with a custom Copy value whose Clone
panics exposed a runtime issue with generic cloning: Rust 1.97 specializes slice
extension on TrivialClone, not all Copy types. Direct copies handle both empty
and populated frames without invoking Clone. The regression also writes after
promotion and restores the older token. Batched Trail/Hot replay is unchanged;
no new trusted specification is added.

`restore_hot_promotion_checked` composes reconstruction, exact truncation,
physical promotion, capture rebuilding, and reclamation. Runtime dispatch uses
this path for Trail-discipline restores whose survivor is Hot. The trusted
restore fallback now requires `target <= cold_stack.len()`: its remaining
physical obligation is Cold-to-ingress decoding/promotion. Conversions and
all-tier mutation closure also remain unfinished.

Targeted rebasing, retained Hot range/invariant, complete logical promotion,
executable copying, promotion readiness, and restore composition checks pass.
Final full-package verification passed **2294 verified, 0 errors** in both
default (5m 03s) and `literal-types` (5m 36s) configurations. The feature suite
passed 275 tests (10 ignored), including all 31 three-tier runtime tests and
the new Copy/Clone regression. The 1024-case release differential matrix passed
all four tests. E-graph/SAT consumers passed 1267 tests (45 ignored), with zero
failures. Formatting and whitespace checks passed. Trust remains 81 default
markers plus five literal registrations. Existing runtime tests exercise Hot
promotion, empty frame identity, and write/remigrate after promotion.


### Checked Cold run formation and saved-domain bounds

The Hot-promotion checkpoint is `4ebf531`. Cold promotion requires facts that
were absent from `cold_repr_ok`: emitted runs are nonempty, and every decoded
index lies below that frame's saved length. `cold_payload_ok` now states those
facts without adding stored fields or assuming monotone saved lengths.

The new internal `cold_encode` module checks the actual linear run-formation
loop over sorted unique captures. Its contract preserves both physical pool
prefixes, maps every appended value to its input entry, partitions the input
into maximal consecutive runs, bounds each run by the saved length, and emits
an empty header for an empty frame. The loop groups entries while using index
differences to avoid overflowing a base-plus-length probe. Values use Copy,
never a potentially different user-defined Clone.

`append_cold_sorted_checked` appends the frame header and proves pooled layout,
run disjointness, and saved-domain bounds. Configured and adaptive Hot migration
both call it, replacing their duplicated unchecked run-building loops. Sorting,
complete conversion/refinement, policy orchestration, and Cold promotion remain
unfinished; this checkpoint does not claim those trusted callers are verified.

Pointwise header/run accessors avoid repeated adjacency expansion during frame
assembly. Targeted encoder, frame-layout, payload-bound, disjointness, and
executable append checks pass at the default resource limit. Two runtime tests
pass: prefixed pools with captures near the index limit and an empty frame,
and Copy payloads whose Clone panics. Preservation checks required narrowing
Cold layout/reclamation and capture-finalization proofs: finalization now
requests just the writable top's bounds instead of unfolding every Hot frame.
No resource limits were raised and no trusted markers were added.

Full verification passed **2310 verified, 0 errors** in default (3m 48s) and
`literal-types` (3m 37s) configurations. Feature tests passed 277 tests (10
ignored), including all 31 three-tier runtime tests. The 1024-case release
policy matrix passed all four tests; e-graph/SAT consumers passed 1267 tests
(45 ignored). Formatting and whitespace checks passed. Trust remains 81
default markers plus five literal registrations.

Further leaf work is paused for the top-down conditional composition milestone
in `three-tier-top-down-proof-engineering.md`. Existing proofs will be retained
and classified against the required interfaces only after that composition
works; the top theorem will not be weakened to fit existing helpers.


### Physical storage refines the shared top-down model

The conditional composition and classification checkpoint is `7827e85`.
The production crate now imports the same mathematical model used by the
conditional proof. `persistence_frame` derives a finite map from each physical
frame's saved-value lookup; `persistence_model` uses those maps alongside the
existing live view and ghost snapshots. Neither is maintained storage.

The physical-domain theorem proves every Some lookup is below the frame's
saved length, including Cold runs. Thus the bounded finite-map construction
cannot silently drop an out-of-domain payload. The lookup theorem preserves
both membership and value. Existing captured-or-inherited lemmas then establish
`snapshots_ok` for the actual Vec view. The capture and writable lemmas connect
real ingress ownership, active saved length, and live capture flags to the same
map interpretation. Untracked mode has no logical frames.

Pair frame and suffix lemmas prove exact shared-map application for arbitrary
buffers. `replay_persistence_pair_checked` performs the original single pool
batch and exports this effect and the existing capture protocol. The old
snapshot-oriented wrapper calls it and retains its complete contract. Likewise,
`replay_persistence_cold_checked` performs direct run replay and proves the
shared map's exact application; the old Cold frame wrapper retains its snapshot
step contract. No replay loop or batching changes, extra runtime map lookups,
assumptions, or trusted bodies were introduced.

Targeted checks passed for the physical interpretation, capture/writable
bridge, pair composition/execution, and Cold execution. The conditional target
passes 80 obligations with the new finite-map accessor. Full default and
literal-types production verification each passed **2340 verified, 0 errors**.
Feature tests passed 277 tests (10 ignored), the 1024-case differential policy
matrix passed all four tests, and e-graph/SAT consumer tests passed 1267 tests
(45 ignored). Formatting and whitespace checks passed. Trust remains 86 source
markers (81 default plus five literal registrations); the differential oracle
is unchanged. This milestone does not yet instantiate every provisional
interface or complete all-tier public closure. The derived-contract audit
records the initial public wrapper gaps without changing their implementations.

### Exact shared-map retirement and Hot survivor reopening

Physical range equality and subrange rebasing now preserve the complete
earliest-capture lookup, including absence. Retained Cold cells use the existing
coverage/value transfer theorem; retained Trail/Hot cells use the existing exact
range bounds and the new local equality theorem. No intermediate `self.wf()`
premise is needed. The resulting map theorem gives the exact shared frame
sequence prefix and is exported by `truncate_restored_history_checked` alongside
all its previous canonical and physical postconditions.

Hot survivor promotion preserves the whole shared model. The newest frame's
rebased Trail range has the same earliest-capture map as its original Hot range;
older Hot ranges and all Cold storage retain their meanings. The checked
promotion exports this equality. Capture finalization also exports unchanged
shared model via a history framing lemma, while preserving its original full
well-formedness and concrete field-framing contract.

Targeted lookup, rebasing, retained-frame and Hot-promotion lemmas passed. Full
default and literal-types verification each passed **2348 verified, 0 errors**;
the conditional theorem still passes 80 obligations. Feature tests passed 277
(10 ignored), the 1024-case differential policy matrix passed four tests, and
consumer tests passed 1267 (45 ignored). Formatting and whitespace checks passed.
Trust remains 86 source markers; the differential oracle is unchanged. This
milestone adds only erased proofs and contracts, with no executable statement
changes. This remains concrete
interface-discharge work; Cold promotion and the remaining all-tier/public and
derived/parallel obligations are not complete.

### Checked Cold decoder for both writable tiers

`cold_decode::decode_into` now implements the existing nested run/cell traversal
directly into the destination pair pool. Its contract proves exact saved-value
lookup equality with the source runs for every index, strictly increasing
destination indices, saved-domain bounds, and exact output length. A positional
source/destination relation supplies coverage in both directions, including
empty frames and gaps. Index conversion is proved successful; values use Copy.

Both Cold branches in the existing survivor dispatcher call this helper: Hot
for unique-capture stores, Trail for chronological stores. The helper adds no
intermediate pair buffer, runtime map, persistent ghost field, or extra traversal.
Both executable helper boundaries are marked inline(always). Performance has
not been benchmarked; no speedup or slowdown claim is made.

The local decoder's ten obligations and two Vec interpretation/representation
bridge lemmas passed targeted verification. Narrow per-cell lemmas resolved the
initial quantifier/resource failures without raising limits. Full default and
literal-types verification each passed **2360 verified, 0 errors**; the
conditional theorem passed 80 obligations. Feature tests passed 277 (10
ignored), the 1024-case differential policy matrix passed four tests, and
consumer tests passed 1267 (45 ignored). Formatting and whitespace checks passed.
Trust remains 86 source markers and the differential oracle is unchanged.

The surrounding `runtime_promote_survivor` remains trusted. Its Cold source
truncation, destination header publication, older-frame preservation and final
invariant composition still need concrete discharge. Replacing its inner loops
with the checked decoder does not discharge that caller or reduce the trust
count. Existing checked replay, retirement, Hot promotion and capture rebuilding
remain intact.

The promotion caller must establish that the selected destination pool is empty
and that the original survivor header names valid source runs before it is
popped. The retained Cold-prefix proof should use the existing layout accessors
(which require only `repr_ok`) and preserve per-cell coverage/value facts without
assuming an intermediate full `wf`. Header publication must re-establish the
Cold/Hot/Trail frame partition for the store-selected destination before the
existing capture-finalization theorem is applied.

### Checked Cold promotion and complete Cold-survivor restore

The decoder checkpoint is signed local commit `a69572f`. The subsequent work
checks the complete promotion assembly for both DiffStore-selected destinations.
`promote_cold_storage_checked` proves the exact Cold prefixes, unchanged store
and canonical fields, decoded destination contents, and the new survivor header.
`cold_survivor_promoted` records that intermediate effect without assuming full
well-formedness. Partition, older Cold representation, destination representation
and shared-map equality are then proved separately.

The Cold prefix proofs were adapted to require physical representation rather
than full `wf`. Their original restore contracts remain as checked wrappers.
Saved-value transfer uses explicit header/run accessors to stay within existing
resource limits. The decoded destination satisfies the original pair-frame
invariant and uniqueness; no snapshot or map contract was weakened.

`restore_cold_survivor_checked` now composes reconstruction, exact retirement,
checked Cold promotion, capture finalization and reclamation. It retains the old
public-facing contents/depth/snapshot-prefix effects and additionally exports
the exact retained shared-frame prefix. Capacity reclamation now exports shared
model and canonical-history preservation. The original specialized Hot proofs
remain checked.

All 45 selected Cold obligations and the shared-view framing lemma passed. Only
then was the obsolete trusted `runtime_promote_survivor` removed. The former
`runtime_restore_frame_fallback` is now the checked Cold restore function.
This removes two markers: **79 default + 5 literal registrations**, with no new
trusted body or axiom. CI and the trust ledger are updated together. Full default
and literal-types verification each passed **2373 verified, 0 errors**; the
conditional target passed 80 obligations. Feature tests passed 277 (10 ignored),
the 1024-case differential matrix passed four tests, and consumer tests passed
1267 (45 ignored). Formatting and whitespace checks passed. The differential
oracle is unchanged.

An additional CI partial-API audit fails with 73 public partial functions,
33 allowlisted and 40 unlisted (zero unsafe-public functions). Running the
same scanner against the committed `a69572f` source produced exactly the same
output and exit status. This change adds no public partial API; the pre-existing
allowlist discrepancy remains recorded rather than being hidden by expanding
the allowlist. The trust-count CI check passes at 79 + 5.

This closes the remaining trusted Cold restore implementation boundary. It does
not discharge all-tier mutation/mark/rollover fallbacks, the complete production
interface instantiation, or derived and parallel container closure. Those remain
part of the active objective.

### General canonical capture and checked mark wrapper

The nightshift resumes from `aa01a08` under the detailed acceptance checklist in
`semi-persistence-completion-goal.md` and the execution instructions in
`nightshift-completion-goal.md`. All four completion milestones remain open.

`lemma_canonical_capture_append` separates canonical-history preservation from
Hot-only physical assumptions. It proves chronological append preservation,
including duplicate captures and all older strata, from `wf_for_snap`, unchanged
live/snapshot/boundary views and the physical caller's partition. Existing
first-capture, duplicate and unchanged-range lemmas are reused. The original
Hot canonical capture helper now calls this general lemma with its unchanged
contract; its no-append branch reuses canonical repartition framing.

The legacy `push_frame` wrapper verifies against the existing dispatcher
contract, removing one redundant `external_body`. The dispatcher still depends
on the trusted all-tier mark fallback. Trust is **78 default + 5 literal
registrations**; CI and the trust ledger agree, and axioms are unchanged.
These edits change only proof code and verification annotations, with no
executable statement changes or new resource limits.

Evidence:

- Selected capture proofs: 16 verified, zero errors
  (`/tmp/sp-d21-canonical-capture-reuse.log`). The new general lemma verified
  independently before its use replaced the specialized proof block.
- Selected mark wrapper/dispatcher proofs: 3 verified, zero errors
  (`/tmp/sp-d21-mark-wrapper.log`).
- Full default and literal-types: **2375 verified, zero errors** each
  (`/tmp/sp-d21-capture-general-default.log`,
  `/tmp/sp-d21-capture-general-literal.log`).
- Conditional composition: 80 verified, zero errors
  (`/tmp/sp-d21-capture-general-conditional.log`).
- Feature tests: 277 passed, 10 ignored
  (`/tmp/sp-d21-capture-general-features.log`). Formatting and whitespace checks
  passed; the source trust count matches 78 + 5.

Commands retain the previous milestone's form: `cargo verus verify -p
semi-persistent-containers-verus -- --time-expanded`, the same command with
`--features literal-types`, direct `verus --crate-type lib
containers-verus/proofs/top_down/composition.rs`, and `cargo test -p
semi-persistent-containers-verus --features 'compat-all,literal-types'`.
The differential oracle is unchanged. Consumer/differential suites and performance
benchmarks were not rerun for this proof-only checkpoint; final revision gates
and benchmark parity remain required, as does the recorded partial-API audit.

Next: prove the physical capture effect and membership preservation for both
ingress disciplines, then compose with the general canonical lemma. The regrowth
audit found that Trail's ghost flag is cleared by `TrailStore::push` but the
trusted Vec fallback only calls `mark_captured` for unique stores. The general
push proof must restore Trail's ghost membership when reentering a saved domain,
without weakening the invariant or adding runtime flag overhead. This obligation
is recorded in the proof classification alongside the existing capture gaps.

### Checked all-tier physical capture through DiffStore

Starting from signed checkpoint `d29bde3`, `runtime_capture` now verifies for
both store-selected ingress disciplines under the general Vec invariant. The
old trusted capture boundary is removed. Its contract exports exact physical
append/no-op behavior, unchanged nonselected pool, capture-flag update, unchanged
live contents, canonical event append and all three immutable store protocol
predicates. Outside the active saved domain, the whole state is unchanged.

`ingress_capture_effect` describes only the intermediate physical mutation.
`lemma_ingress_capture_frame` handles a single Hot or Trail frame using the
existing first-capture, duplicate and unchanged-range proofs. Separate Hot and
Trail representation lemmas expose header triggers narrowly. Capture flags,
Cold framing and canonical preservation compose to recover `wf`. The previous
checkpoint's general canonical-append lemma then supplies the chronological
event proof. A separate full-trail framing lemma proves that this ghost-only
event leaves physical predicates unchanged.

The physical frame and final flag arguments verified before integration.
Resource failures were resolved by splitting tier/header obligations, hiding
irrelevant reconstruction definitions and explicitly supplying store
well-formedness where `wf_for_snap` was hidden. No solver limits were raised.
The original specialized Hot capture proofs remain checked and intact.

Both runtime branches now call `DiffStore::capture`. The Trail implementation
continues to append duplicates unconditionally and maintains capture flags only
in ghost code. Unique capture uses the same store primitive without invoking a
Hot-only helper under a weaker premise. No persistent fields, maps, buffers or
traversals were added. The call-path change has not been benchmarked; performance
parity remains a required final gate.

Evidence on this source revision:

- Selected capture family: **23 verified, zero errors**
  (`/tmp/sp-d21-ingress-runtime-final.log`); separate full-trail physical framing:
  one verified, zero errors (`/tmp/sp-d21-ingress-framing2.log`).
- Full default and literal-types verification: **2383 verified, zero errors**
  each (`/tmp/sp-d21-ingress-default.log`, `/tmp/sp-d21-ingress-literal.log`).
- Conditional composition: **80 verified, zero errors**
  (`/tmp/sp-d21-ingress-conditional.log`).
- Feature tests: **277 passed, 10 ignored**
  (`/tmp/sp-d21-ingress-features.log`).
- Release differential policy matrix with `PROPTEST_CASES=1024`: **4 passed**
  (`/tmp/sp-d21-ingress-policy.log`).
- E-graph/SAT-core consumers: **1267 passed, 45 ignored**
  (`/tmp/sp-d21-ingress-consumers.log`).
- Formatting, whitespace and trust-count checks passed. Trust is now
  **77 default + 5 literal registrations**, with unchanged axiom counts and
  synchronized CI/trust documentation. The legacy `containers/` tree is unchanged.

Commands use the previous full-gate sequence: default and literal-types
`cargo verus verify -p semi-persistent-containers-verus -- --time-expanded`,
direct `verus --crate-type lib containers-verus/proofs/top_down/composition.rs`,
`cargo test -p semi-persistent-containers-verus --features 'compat-all,literal-types'`,
`PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test three_tier_policy_matrix`,
and `cargo test -p semi-persistent-egraph -p semi-persistent-satcore`.

The additional partial-API audit still fails with 73 public partial functions,
33 allowlisted and 40 unlisted, zero unsafe-public. Its output in
`/tmp/sp-d21-ingress-partial-api.log` is byte-for-byte identical to the recorded
baseline audit; no allowlist entries were added. This remains an open final-audit
item, not a claim that all CI gates pass.

Next: compose this checked capture with `set_raw` and the existing captured-cell
and outside-saved-domain write lemmas for general mixed-tier set. Pop and
regrowth still need their general preservation proofs, including Trail's ghost
flag restoration on regrowth. Explicit shared-map `capture_first` equality is
still required for the production interface. Mutation/mark, migration/policy,
complete interface instantiation, derived/parallel closure and benchmark parity
remain open; this checkpoint does not complete any of the four overall steps.

### Checked mixed-tier set through capture and raw write

Starting from signed checkpoint `226df51`, `runtime_set_fallback` now verifies
against its original contract. Both ingress disciplines compose the checked
general capture path with `DiffStore::set_raw`. The former unique-store branch
no longer calls a Hot-only helper under a weaker mixed-history premise. The
specialized Hot set proof and its existing fast-path dispatch remain checked.

`raw_set_effect` specifies the exact live update, field framing and immutable
store protocols. Capture-flag equality is TRACK-conditional, matching the
existing DiffStore contract: untracked inline writes are not required to retain
irrelevant tag bits. This preserves supported untracked behavior without adding
flag preservation overhead or weakening any public persistence contract.

The frame proof reuses existing captured-cell and outside-saved-domain write
lemmas. Separate Hot/Trail representation proofs retain all headers, pools and
uniqueness. Pointwise canonical access supplies the newest saved length and
frame contract; older canonical layers are unchanged. A narrow capture-domain
accessor supplies the appended canonical event's range bounds to the executable
wrapper. The final composition recovers all of `wf`, including ingress and Cold
reconstruction. Resource failures were resolved by narrow accessors, explicit
coordinate equalities and local invariant exposure, without increased limits.

`lemma_cold_reconstructs_layer_transfer` adapts the existing Cold framing proof
to require equality of the immediate newer layer rather than the whole live
vector. Older Cold frames therefore survive writes above them. The original
whole-live-equality contract is retained as a checked wrapper; no verified caller
loses its old guarantees.

Evidence on the final source for this checkpoint:

- Selected set family: **18 verified, zero errors**
  (`/tmp/sp-d21-set-runtime5.log`). Cold layer transfer and its existing wrappers
  passed three selected obligations (`/tmp/sp-d21-set-cold-layer.log`).
- Full default and literal-types: **2393 verified, zero errors** each
  (`/tmp/sp-d21-set-default.log`, `/tmp/sp-d21-set-literal.log`).
- Conditional composition: **80 verified, zero errors**
  (`/tmp/sp-d21-set-conditional.log`).
- Feature tests: **277 passed, 10 ignored** (`/tmp/sp-d21-set-features.log`).
- Release differential policy matrix with `PROPTEST_CASES=1024`: **4 passed**
  (`/tmp/sp-d21-set-policy.log`).
- E-graph/SAT-core consumers: **1267 passed, 45 ignored**
  (`/tmp/sp-d21-set-consumers.log`).
- Formatting, whitespace and source trust-count checks passed. The legacy
  `containers/` tree is unchanged. The gate commands are the same full sequence
  recorded for the preceding capture checkpoint.

The set fallback's trust marker is removed. Counts are **76 default + 5 literal
registrations**, with unchanged axioms and synchronized CI/trust documentation.
The partial-API audit remains at 73 public partial functions, 33 allowlisted,
40 unlisted and zero unsafe-public; its output is identical to the preceding
checkpoint (`/tmp/sp-d21-set-partial-api.log`). That final-audit issue remains open.

The new [performance inventory](conformance-performance-inventory.md) reviews all
13 registered Criterion targets. It distinguishes matched legacy comparisons
from tier-specific controls and local algorithm experiments, and records the
parallel-group coverage gap. No timing measurements or parity claim accompany
the inventory; the final benchmark gate remains required.

Next: general push/regrowth and pop preservation. Reuse grow/shrink frame lemmas
and the new Cold-layer transfer; preserve capture membership on saved-domain
regrowth for Trail as well as Hot. Mark, migration/policy, full shared-map
interface instantiation and derived/parallel closure remain open. None of the
four overall completion steps is declared complete by this checkpoint.

### Checked all-tier push/regrowth and pop

Starting from signed checkpoint `28e2add`, both remaining mutation fallback
bodies now verify: `runtime_push_fallback` and `runtime_pop_fallback`. Capture,
set, push/regrowth and pop therefore have checked general implementations in
addition to the retained Hot specializations. Mark/open-frame and policy
execution still require discharge, and the shared-model adapter remains incomplete.

Push preserves every history field, appends exactly one live value and preserves
all three store protocol predicates. Existing grow-layer lemmas preserve pair
and canonical reconstruction. `lemma_push_reentered_capture` proves that a
saved-domain column absent from the old live layer must already be captured.
Regrowth restores capture membership through `mark_captured` for both Hot and
Trail disciplines. This discharges the previously recorded Trail ghost-flag gap.
The Trail hook changes only ghost state; no runtime tag or persistent history
is added. The generic execution guard no longer tests unique capture before
calling that existing hook. Its performance remains subject to the final gate.

Pop captures a disappearing saved-domain value through checked `runtime_capture`
before calling the actual store pop method. The existing last-cell contraction
lemma preserves pair and canonical reconstruction. Older Cold layers are framed
through the newer-layer transfer lemma. Empty pop returns without mutation;
saved-domain index conversion is proved successful from the active-length bound.
Untracked flag behavior retains the original store contract. Neither operation
adds a buffer, map or traversal, and no public contract is weakened.

The first full verifier attempt exposed a resource failure in the existing
canonical-frame accessor (2408 verified, one error). The accessor was decomposed
into frame-contract and saved-length accessors; its original contract remains
unchanged. All three then verified independently. The final full runs below
passed with no increased resource limits, new trust or new axioms.

Final evidence:

- Selected push family: **18 verified, zero errors**
  (`/tmp/sp-d21-push-runtime.log`).
- Selected pop family: **12 verified, zero errors**
  (`/tmp/sp-d21-pop-runtime.log`).
- Decomposed canonical accessors: **3 verified, zero errors**
  (`/tmp/sp-d21-push-pop-accessor2.log`).
- Full default and literal-types verification: **2411 verified, zero errors**
  each (`/tmp/sp-d21-push-pop-final-default.log`,
  `/tmp/sp-d21-push-pop-final-literal.log`).
- Conditional composition: **80 verified, zero errors**
  (`/tmp/sp-d21-push-pop-final-conditional.log`).
- Feature tests: **277 passed, 10 ignored**
  (`/tmp/sp-d21-push-pop-final-features.log`).
- Release differential policy matrix, `PROPTEST_CASES=1024`: **4 passed**
  (`/tmp/sp-d21-push-pop-final-policy.log`).
- E-graph/SAT-core consumers: **1267 passed, 45 ignored**
  (`/tmp/sp-d21-push-pop-final-consumers.log`).
- Formatting, whitespace and trust-count checks passed. The commands are the
  same full gate sequence recorded for the capture checkpoint. `containers/`
  is unchanged both in the worktree and relative to baseline `aa01a08`.

Two trust markers are removed: **74 default + 5 literal registrations**, with
unchanged axioms and synchronized CI/trust documentation. The additional
partial-API audit still reports the same 73 public partial functions, 33 allowed,
40 unlisted and zero unsafe-public; its output is identical to the set checkpoint
(`/tmp/sp-d21-push-pop-partial-api.log`). That audit and benchmark parity remain open.

Next is general mark opening. The caller audit found an omitted TRACK premise
in the internal mark dispatcher/fallback; both actual callers already require
TRACK. Propagate that premise internally, preserve public guards, and prove
prepare/seal/open using the borrowed active range and the transfer of the old
live layer to the equal new snapshot. Replace the invalid Hot-only shortcut for
unique stores with older Cold history. Policy and reclamation calls must compose
after opening, and mark is not complete until those dependencies verify.

## General mark preparation through DiffStore

The internal `runtime_push_frame` and fallback now require TRACK, matching both
existing public-facing callers. This corrects an omitted internal premise without
changing public guards or runtime behavior.

`prepare_mark_range_checked` translates active physical-range coverage into the
borrowed-slice witness required by `DiffStore::prepare_mark`.
`prepare_mark_checked` selects Hot or Trail from the store discipline, handles
zero depth with clear flags, and proves exact framing of every field except the
store. Store data and all three protocol predicates are preserved; all live
capture flags are cleared. The fallback now calls this checked preparation
instead of constructing an unchecked slice inline. No allocation or traversal is
added. The intermediate contract intentionally does not claim container wf:
opening the new empty frame must restore capture-map agreement.

Selected verification: **2 verified, zero errors**
(`/tmp/sp-d21-mark-prepare.log`). Full gate results are recorded below when
available. This does not remove the fallback's trust marker: sealing, empty-frame
opening, the invalid mixed-history Hot shortcut, and actual policy dependencies
remain to be discharged. Existing specialized Hot proofs remain intact.

Checkpoint validation: full default **2413 verified, zero errors**
(`/tmp/sp-d21-mark-prepare-default.log`); feature regression tests completed
successfully (`/tmp/sp-d21-mark-prepare-features.log`). Formatting and whitespace
checks pass, and `containers/` remains unchanged from `aa01a08`. Trust markers
are unchanged. Literal-types verification, differential policy tests and consumer
checks will be rerun with the completed frame-opening milestone; their previous
checkpoint results are not claimed as verification of this revision. Final
benchmark parity remains open.

## Mark structural transition and canonical reconstruction

The actual fallback now uses checked `open_mark_headers_checked` after checked
preparation. The helper seals only the selected newest pair header, appends an
empty header to the DiffStore-selected tier, appends the snapshot and canonical
boundary, and updates the active saved length. Its contract states the exact
header sequences (old last header updated, then one header pushed), exact
snapshot/boundary appends, unchanged unrelated fields, and the final frame
partition. Indexed header updates replace equivalent `last_mut` sugar; no new
traversal, buffer, or runtime history is introduced.

`lemma_canonical_mark_frame` and `lemma_canonical_mark` prove reconstruction
across snapshot/boundary append independently of physical tier placement. They
require the canonical pre-invariant and the post-partition, not an all-Hot model.
After these replacements verified, the existing `hot_defer_mark_checked` was
changed to call the shared canonical theorem instead of duplicating the proof.
The specialized function retains its full contract and verifies with the reuse.

Targeted evidence:

- Canonical helpers: **2 verified, zero errors**
  (`/tmp/sp-d21-mark-canonical2.log`). The initial attempt exposed a missing
  snapshot-count/boundary-count equality; explicitly accessing that existing
  canonical fact resolved the failure without increasing solver limits.
- Existing Hot mark with shared proof: **1 verified, zero errors**
  (`/tmp/sp-d21-mark-canonical-reuse.log`).
- Actual header-opening helper: **1 verified, zero errors**
  (`/tmp/sp-d21-mark-headers.log`).

Still required: use the exact header transition to preserve physical Hot/Trail
ranges, uniqueness, Cold reconstruction, and empty active capture membership;
compose with canonical preservation to obtain general wf. Then replace the
invalid mixed-history Hot shortcut and discharge rollover/reclamation calls.
The fallback remains trusted, and this checkpoint does not close Step 1 or 2.

Structural checkpoint full evidence: default **2416 verified, zero errors**
(`/tmp/sp-d21-mark-structure-default.log`); feature regression suite **277 passed,
10 ignored** (`/tmp/sp-d21-mark-structure-features.log`). Formatting and whitespace
checks pass; the legacy `containers/` tree is unchanged from `aa01a08`. No trust
marker or solver limit changed. Literal-types verification and broader policy/
consumer gates remain due for the completed general opening milestone; final
performance acceptance is still open.

## Physical frame meaning across mark opening

`open_mark_headers_checked` now additionally exports unchanged logical offsets,
starts and effective ends for every old pair frame, plus the selected new frame's
empty range and incremented tier count. These facts are checked against the
actual indexed header updates, rather than assumed by a separate model.

`lemma_mark_pair_frame` uses those coordinate facts to preserve an older Trail
or Hot frame's reconstruction contract after snapshot append; Hot uniqueness is
preserved as well. The prior top's layer changes from live contents to an equal
snapshot, so the same proof handles both the top and older frames.

`lemma_mark_cold_repr` preserves the entire Cold representation across mark.
It uses the new `lemma_cold_reconstructs_frame_transfer`, which needs equality of
only the relevant snapshot and immediately newer layer, plus unchanged physical
Cold storage. The existing layer-transfer contract remains intact as a checked
wrapper. No existing caller loses a guarantee and no runtime body changes in
this checkpoint.

Targeted validation: mark selection **17 verified, zero errors**
(`/tmp/sp-d21-mark-ranges.log`); Cold selection **48 verified, zero errors**
(`/tmp/sp-d21-mark-cold.log`). No trust or solver limit changes.

Next: aggregate the old-frame lemmas and new empty-frame facts into Hot/Trail
representation preservation, establish cleared-flag ingress and compatibility,
and combine with canonical preservation into general wf. The trusted mark
fallback and policy dependencies remain open; these lemmas alone do not complete
mark or the production end-to-end theorem.

Full checkpoint results: default and literal-types each **2419 verified, zero
errors** (`/tmp/sp-d21-mark-physical-default.log`,
`/tmp/sp-d21-mark-physical-literal.log`); conditional composition **80 verified,
zero errors** (`/tmp/sp-d21-mark-physical-composition.log`). Formatting and
whitespace checks pass, and `containers/` is unchanged from `aa01a08`. This
checkpoint contains only proof/specification changes, so runtime regression tests
were not repeated; the preceding structural checkpoint recorded 277 passing
feature tests. Benchmark parity remains unmeasured and required.

## General mark opening and explicit Defer dispatch

`mark_open_effect` is a local specification of the exact existing header/store
transition, not stored ghost history. `lemma_mark_hot_repr` and
`lemma_mark_trail_repr` aggregate old-frame preservation and new empty-frame
reconstruction; `lemma_mark_ingress` establishes cleared-flag agreement and proof
compatibility. `lemma_mark_preserves` combines these with the existing canonical
and Cold preservation lemmas to establish full general wf.

`open_mark_checked` executes actual DiffStore preparation and header opening and
proves this effect plus the public snapshot/depth result. `mark_defer_checked`
composes pre-mark shrinking, opening and checked post-mark reclamation. The actual
dispatch now uses this path for every explicit Defer mark outside the retained
Hot specialization, including older Cold history and chronological stores.

The fallback uses the same checked opening/reclamation. Its invalid Hot-only
shortcut has been removed. A first attempt to check the entire fallback exposed
unsupported direct `shrink_to_fit` calls; these now use the existing
`shrink_vec_capacity(..., 0, 1)` capacity primitive, as restore already does.
Reclamation was separated to avoid broad invariant expansion after a resource
failure, without raising limits. The resulting dispatch attempt identified the
remaining semantic gap: `runtime_apply_configured_rollover` and
`runtime_rollover_on_mark` have no preservation contracts. No assumed contracts
were added to them. The configured/forced fallback retains its existing trust
marker until concrete policy preservation is proved.

Targeted mark checks: **25 verified, zero errors**
(`/tmp/sp-d21-mark-defer.log`). Trust counts and axioms are unchanged. Full gate
results follow below. Runtime changes preserve the pre-shrink/open/rollover/
post-shrink order and add no traversal or allocation. Final benchmark parity
remains required, including any effect from the dispatch/helper refactoring.

General opening checkpoint evidence:

- Full default and literal-types: **2426 verified, zero errors** each
  (`/tmp/sp-d21-mark-general-default.log`, `/tmp/sp-d21-mark-general-literal.log`).
- Feature regression suite: **277 passed, 10 ignored**
  (`/tmp/sp-d21-mark-general-features.log`).
- Release differential policy matrix with `PROPTEST_CASES=1024`: **4 passed**
  (`/tmp/sp-d21-mark-general-policy.log`).
- Conditional composition: **80 verified, zero errors**
  (`/tmp/sp-d21-mark-general-composition.log`).
- Formatting/whitespace pass; trust remains **74 default + 5 literal**;
  `containers/` is unchanged from `aa01a08`.

Step 1 remains open for configured/forced mark's actual policy dependencies and
shared-model interface closure. Next discharge closed-prefix Trail-to-Hot and
Hot-to-Cold migration and assembly, then their policy selectors/execution. Derived
and parallel closure, final consumer/CI audits and benchmark parity remain due.

## Trail migration: exact selected-position publication

`append_selected_hot_frame_checked` now implements the ordinary Trail migration's
existing per-position payload copy and header append. The checked contract gives
exact destination concatenation, exact header append (saved length and bounds),
and full optional saved-value equality between the appended physical range and
the selected payload for every index. Empty selections and nonempty destination
prefixes are covered. Source pools, sorting and selected-position computation
remain in the existing caller; this helper introduces no intermediate payload or
new traversal. Indexed iteration replaces the original iterator loop over the
same selected positions.

Targeted result: **2 verified, zero errors**
(`/tmp/sp-d21-migrate-selected-map.log`). The caller's selection-bounds premise
still needs discharge together with earliest-capture selection, uniqueness,
source retirement/rebasing, and the final global invariant. No migration or policy
trust marker has been removed by this partial assembly proof.

The adaptive bulk-copy path was inspected but remains unchanged. In the pinned
vstd `std_specs/vec.rs`, `Vec::extend_from_slice` guarantees exact length/prefix
but only `cloned(source, destination)` for appended cells. An attempted exact
payload equality proof failed (`/tmp/sp-d21-migrate-hot-append.log`). Generic
`T: Copy` alone does not expose the needed equality through that specification.
No stronger payload bound, assumed clone identity, trusted wrapper, or slower
replacement copy loop was introduced to conceal this gap. Resolve that library
contract/implementation connection before claiming adaptive payload assembly.

Follow-up ownership audit: `runtime_execute_trail_plan` has one caller in
`runtime_apply_adaptive`; it records the frame count before execution and drops
`trail_plan` immediately afterward. No payload is read after execution. This
supports a concrete next step: consume each owned temporary frame through the
already specified `Vec::append`, preserving bulk transfer and avoiding the weak
clone contract. Validate that change and its performance before treating adaptive
assembly as closed. This is an implementation option, not a proved result yet.

Selected publication checkpoint validation: full default **2428 verified, zero
errors** (`/tmp/sp-d21-migrate-append-default.log`); feature tests **277 passed,
10 ignored** (`/tmp/sp-d21-migrate-append-features.log`); release differential
policy matrix with `PROPTEST_CASES=1024` **4 passed**
(`/tmp/sp-d21-migrate-append-policy.log`). Formatting/whitespace pass and the legacy
reference is unchanged. Trust counts are unchanged. Literal-types verification,
consumer tests and final audits remain due with completed migration; benchmark
parity remains an open acceptance criterion.

## Adaptive Trail plan assembly with owned bulk transfer

The clone-specification gap in adaptive publication is resolved for this phase
without new trust or stronger payload bounds. The sole caller already owned the
accepted Trail payload vectors and dropped them immediately after execution.
It now passes mutable ownership to the executor, which publishes payloads through
checked `Vec::append` bulk moves. The planner's count/report is computed before
consumption and no emptied payload is read afterward. Destination behavior and
source-frame order are preserved; no intermediate buffer or per-cell replacement
loop is introduced for adaptive payloads.

`append_owned_hot_frame_checked` proves exact concatenation, emptied temporary
payload, exact header/saved length and full optional saved-value equality. Its
contract also exports executable length bounds obtained from actual Vec length
calls; these justify header-offset casts in the multi-frame proof.

`append_trail_plan_checked` checks the actual assembly loop. A local recursive
`trail_plan_prefix` spec describes concatenation of accepted payloads without
storing history. The loop proves exact destination contents, unchanged destination
header prefix, exact appended header order/saved lengths/start/end offsets,
consumed-empty payloads, and unchanged source/other Self fields. Early failed
attempts isolated missing header-preservation instantiations and length bounds;
explicit facts resolved them without raising solver limits.

Targeted evidence: owned append **1 verified, zero errors**
(`/tmp/sp-d21-migrate-owned-bounds2.log`); plan loop **2 verified, zero errors**
(`/tmp/sp-d21-migrate-plan5.log`). The caller still must prove the plan matches
source first captures and establish retirement/rebasing and final wf. Trust
counts remain unchanged; no policy or migration closure is claimed yet.

Next retirement implementation candidate: pinned vstd supplies exact overlapping
`[T]::copy_within` semantics in `std_specs/slice.rs`, whereas `Vec::drain` is not
specified there. For these Copy payloads and headers, a bulk prefix shift followed
by truncation can preserve the current linear memory movement without repeated
removal or new trust. Prove exact retained suffix and header rebasing, then connect
the assembly and retirement phases. This candidate remains to be implemented and
validated, including final performance gates.

Owned assembly checkpoint evidence: full default **2432 verified, zero errors**
(`/tmp/sp-d21-migrate-owned-default.log`); feature tests **277 passed, 10 ignored**
(`/tmp/sp-d21-migrate-owned-features.log`); release differential policy matrix,
`PROPTEST_CASES=1024`, **4 passed** (`/tmp/sp-d21-migrate-owned-policy.log`).
Formatting/whitespace checks pass; legacy `containers/` is unchanged. Trust and
axiom counts are unchanged. Literal-types verification, consumer/final audits and
benchmark parity remain required with migration closure.

## Checked pair-pool retirement and header rebasing

`discard_prefix_checked` uses the pinned, already specified overlapping
`copy_within` operation followed by truncation. It proves that the result is
exactly the old suffix after the cut. This replaces unspecified `Vec::drain`
for Copy pools and headers, preserving bulk linear memory movement rather than
introducing per-element removal or new trust.

`retire_trail_prefix_checked` and `retire_hot_prefix_checked` prove exact payload
suffixes, exact surviving header counts/order, unchanged saved lengths, offsets
reduced by the cut, and unchanged unrelated Self fields. Their concrete
preconditions expose the bounds needed to avoid subtraction underflow. Trail
retirement retains a header; Hot retirement additionally supports removing all
Hot frames. Both ordinary and adaptive Trail/Hot migration callers now use these
checked helpers. Source precondition suppliers still require proof as part of
complete migration; the existing caller trust markers remain.

`lemma_range_saved_value_retire_prefix` relates any retained physical range to its
rebased range with full optional saved-value equality, including absent captures.
It reuses the checked subrange lemma and extensional sequence equality. No
persistent history or new semantic assumption is introduced.

Targeted retirement helpers: **5 verified, zero errors**
(`/tmp/sp-d21-retire-pairs2.log`). Full verification/regression results follow.
Global partition restoration, selected-payload/source identity and policy closure
remain pending. Final benchmark parity must cover the drain-to-copy/truncate
change; equal bulk-work structure is not a timing measurement.

Selection follow-up: the existing checked `diff_compress::sort_frame_by_index`
is insertion sort with a quadratic worst case. Do not substitute it for migration's
current unstable sort merely to obtain a proof. Preserve the migration complexity
and benchmark acceptance while resolving sorting/earliest-capture selection.

Retirement checkpoint full evidence: default and literal-types each **2438
verified, zero errors** (`/tmp/sp-d21-retire-pairs-default.log`,
`/tmp/sp-d21-retire-pairs-literal.log`); feature suite **277 passed, 10 ignored**
(`/tmp/sp-d21-retire-pairs-features.log`); release differential policy matrix,
`PROPTEST_CASES=1024`, **4 passed** (`/tmp/sp-d21-retire-pairs-policy.log`).
Formatting/whitespace checks pass, trust counts are unchanged, and legacy
`containers/` remains unchanged from `aa01a08`. Full migration composition,
consumer/final audits and measured benchmark parity remain open requirements.

## Composed adaptive Trail storage transition

`execute_trail_plan_storage_checked` now composes the actual accepted-plan
assembly and source retirement. `runtime_execute_trail_plan` calls it after its
existing closed-prefix guard. Given the general pre-invariant and a plan count
strictly below the Trail frame count, the helper supplies every retirement bound
from the pre-state's checked pair layout/start-order lemmas.

The resulting contract states exact Hot concatenation, exact retained Trail
suffix, exact destination and survivor headers, emptied temporary payloads,
unchanged unrelated fields and restored global frame partition. Logical positions
are preserved: moved Trail frames occupy the appended Hot positions, while the
remaining Trail offset advances by precisely the removed count. Snapshots,
canonical boundaries and store state stay unchanged.

`lemma_trail_retirement_bounds` isolates the bound supplier;
`lemma_trail_migration_partition` handles frame identity/counts/saved lengths.
`lemma_trail_plan_frame_range` proves each payload occupies its exact range in
concatenated plan prefixes. The executable composition exports full optional
saved-value equality for every new Hot frame and its planned payload.

The initial combined proof exceeded its resource limit. Narrow bound/partition
lemmas and an explicit source-header trigger resolved the issue without changing
contracts or limits. Targeted Trail selection: **15 verified, zero errors**
(`/tmp/sp-d21-trail-compose-map2.log`). No runtime traversal or allocation was
added by this composition, and no trust marker is removed yet.

Still required: prove plan payloads equal the source frames' first-capture maps,
prove uniqueness, and transfer Hot/Trail/Cold reconstruction and active flags to
recover full wf. The present helper establishes the structural partition, not the
full semantic migration theorem. Ordinary sorting/selection and rollover policy
execution remain open, as do derived/group closure and final benchmark parity.

Storage-composition checkpoint evidence: full default **2442 verified, zero
errors** (`/tmp/sp-d21-trail-compose-default.log`); feature suite **277 passed,
10 ignored** (`/tmp/sp-d21-trail-compose-features.log`); release differential
policy matrix with `PROPTEST_CASES=1024` **4 passed**
(`/tmp/sp-d21-trail-compose-policy.log`). Formatting/whitespace pass and legacy
`containers/` is unchanged. Trust counts remain unchanged. Literal-types and
consumer/final audit gates remain due for semantic migration closure, alongside
required benchmark parity.

## Source-map meaning for moved Trail frames

`lemma_frame_inv_range_same_saved_map` proves full frame-contract transfer between
physical ranges with identical optional saved-value maps. It proves destination
capture-domain bounds as well as captured-or-inherited reconstruction; absence
outside the saved domain is essential, so equal reconstructed contents alone are
not substituted for map equality.

`trail_plan_matches` names the remaining selection contract: each planned payload
is index-unique and its full optional saved map equals the corresponding original
Trail range. This is a local specification, not stored history or an assumed
fact. `lemma_pair_tier_contract` provides a narrow accessor for the source frame's
existing physical contract.

The actual `execute_trail_plan_storage_checked` now conditionally exports
reconstruction and uniqueness of every moved Hot frame when the source plan
matches. Its executable precondition is unchanged; the semantic guarantee is
proved inside the checked body from the explicit matching condition. The exact
assembly/range proof supplies destination map identity, the new transfer lemma
supplies reconstruction/domain bounds, and per-frame payload uniqueness supplies
Hot uniqueness. An explicit uniqueness accessor resolved the initial quantifier
instantiation failure without increasing resource limits.

Targeted shared map-transfer proof **1 verified, zero errors**
(`/tmp/sp-d21-frame-map-transfer.log`); Trail selection **15 verified, zero errors**
(`/tmp/sp-d21-trail-semantics2.log`). This checkpoint changes only proofs/contracts,
not runtime execution or trust counts. Still prove the selection code establishes
`trail_plan_matches`, transfer untouched/surviving representations and ingress to
full wf, and close policy/production composition. Conditional moved-frame facts
are not claimed as complete semantic migration.

Moved-frame semantic checkpoint: full default **2444 verified, zero errors**
(`/tmp/sp-d21-trail-semantics-default.log`). Formatting/whitespace pass and legacy
`containers/` is unchanged. This is a proof/specification-only change, so runtime
tests were not repeated; the preceding storage checkpoint recorded 277 passing
feature tests and four passing release policy tests. Literal-types/final consumer
and CI gates remain due with migration closure, and benchmark parity remains open.

## Full Trail assembly/retirement preservation under the selection contract

The checked `execute_trail_plan_storage_checked` now ensures full `wf` whenever
its input plan satisfies `trail_plan_matches`. Its executable precondition is
unchanged. The predicate remains a proof obligation of actual selection; it is
not assumed, stored, or supplied by a new trusted wrapper. The existing adaptive
executor remains trusted until that producer obligation is discharged.

Concrete preservation now covers:

- `trail_retained_effect`: exact survivor/unchanged-field facts exported by the
  checked transition, including the sealed Hot boundary and zero-count case.
- `lemma_trail_retained_frame` / `lemma_trail_retained_repr`: exact rebasing
  preserves all surviving Trail reconstruction and layout, including active top.
- `lemma_trail_old_hot_frame`: old Hot ranges, values and uniqueness survive
  destination append; former last Hot headers are sealed while Trail is active.
- `lemma_trail_retained_ingress`: store state/flags remain unchanged, and rebased
  active physical membership is equivalent to the old membership.
- `lemma_trail_fixed_history`: canonical reconstruction, Cold representation and
  compatibility survive unchanged history with the restored frame partition.
- `lemma_trail_hot_header` / `lemma_trail_hot_repr`: old/new header adjacency,
  bounds, empty-prefix cases, all Hot reconstruction and uniqueness aggregate.
- `lemma_trail_plan_contract_at` / `lemma_trail_moved_frame`: source frame meaning
  transfers first into the matched planned payload and then into the exact new
  Hot range; this separates source and destination quantifiers.
- `lemma_wf_from_named_parts`: the original complete invariant is recovered,
  with no weakened conjunct or additional semantic assumption.

Proof decomposition resolved resource failures without increasing limits. The
assembly loop now explicitly exports first-new-header and sealed-last-header
facts. A pointwise header accessor avoids an expanding plan-prefix trigger;
pointwise source/destination contracts and a checked uniqueness-subrange lemma
keep map/uniqueness quantifiers narrow. Existing verified contracts are retained.
Targeted Trail checks: **26 verified, zero errors**
(`/tmp/sp-d21-trail-wf12.log`). This checkpoint changes proofs/contracts only;
execution and trust counts remain unchanged.

Remaining Step 2 work includes actual first-capture selection/sorting proving
`trail_plan_matches`, Hot-to-Cold semantic assembly/retirement, legal policy
selection/execution, and shared-model effect exports. Full producer-to-consumer
closure is not claimed by this conditional preservation result. Derived/group
scope and final benchmark parity remain required.

Full preservation checkpoint evidence: default and literal-types each **2457
verified, zero errors** (`/tmp/sp-d21-trail-wf-default.log`,
`/tmp/sp-d21-trail-wf-literal.log`); conditional composition **80 verified, zero
errors** (`/tmp/sp-d21-trail-wf-composition.log`). Formatting/whitespace pass and
legacy `containers/` is unchanged. Trust remains **74 default + 5 literal**.
Runtime execution is unchanged by this proof/specification checkpoint, so tests
were not repeated; the last runtime checkpoint recorded 277 passing feature tests
and four release policy tests. Final consumer/CI audits and measured benchmark
parity remain required. The next producer obligation is actual first-capture
selection proving `trail_plan_matches`, without quadratic fallback sorting.


## Trail selection producer: checked key construction and group scan

`trail_select.rs` now checks the executable `build_keys` shared by ordinary and
adaptive Trail migration, and the ordinary `select_positions` group scan. The
builder exports exact `(index, chronological position)` keys and complete source
coverage. The scan exports its exact recursively defined result; this is a local
mathematical sequence, not stored ghost history.

Checked supporting lemmas establish that lexicographically sorted group heads
are earliest source captures, every selected position has this property, every
input index has a retained group head, and multiset-preserving permutations
preserve key/source correspondence. Targeted verification reports **9 verified,
zero errors** (`/tmp/sp-d21-trail-select5.log`). No trusted contract for sorting
has been added: callers must still prove both sorting and permutation effects.

Executable changes replace iterator key construction with one reserved linear
loop and extract the existing ordinary group scan into a checked loop. The
original sorting calls, buffers, selection order, destination assembly and replay
batching remain. This is not a performance-parity claim; final benchmark acceptance
remains open.

Remaining producer work includes sorting with the existing performance profile,
selected-index uniqueness and complete payload map equality, chronological
reordering, adaptive in-place deduplication, and connecting these facts to
`trail_plan_matches`. The surrounding migration/planner bodies remain trusted
until their actual precondition suppliers and semantic effects verify. No Step 2
or whole-goal completion is claimed by this producer checkpoint.

Selection producer checkpoint evidence: full default and literal-types each
**2466 verified, zero errors** (`/tmp/sp-d21-select-default.log`,
`/tmp/sp-d21-select-literal.log`); conditional composition **80 verified, zero
errors** (`/tmp/sp-d21-select-composition.log`); feature suite **277 passed, 10
ignored** (`/tmp/sp-d21-select-tests.log`); release differential policy matrix
with `PROPTEST_CASES=1024` **4 passed** (`/tmp/sp-d21-select-policy.log`). The
first feature-suite run was interrupted by a session exit before `eclasses_behavior`
reported and was rerun from scratch; the recorded log is the complete rerun.
Formatting/whitespace pass, trust remains **74 default + 5 literal**, and legacy
`containers/` is unchanged from `aa01a08`. Benchmark parity remains open.


## 2026-09-16 — Trail deduplication through an index set; checked Trail migration and selectors

**Algorithm change (user-directed).** Trail-to-Hot first-capture selection no
longer sorts `(index, chronological position)` keys. A Trail frame is
chronological, so the earliest capture per index is found by one left-to-right
fold with a membership set: `trail_select::dedupe_trail_range` inserts each
index into a reusable `HashSet<I, IndexHasher>` and, on first insertion, pushes
the entry straight into the Hot pool. No `usize`-widened key buffer, no
positions buffer, no sort, no intermediate payload. The set is keyed by the
generic index type, so 16/32/64-bit indices keep their width.

**Checked producer.** `dedupe_prefix` states that the appended range holds
exactly the physical first hitters of the source range; `seen_prefix` states
the set's contents. `lemma_dedupe_saved_value` derives full optional saved-map
equality, including absence, from uniqueness plus that contract. The exec loop
verifies through four step lemmas (`lemma_seen_step`, `lemma_dedupe_fresh`,
`lemma_dedupe_dup`, `lemma_dedupe_push`, `lemma_dedupe_skip`) after the first
attempt exceeded the resource limit as one query. The set relies on vstd's
hash-table model: `IndexLike` gains `lemma_obeys_key_model`, discharged from
vstd's shipped axioms for `u8`..`usize` and stated as justified axioms for
`DenseId31`, `DenseId63`, `DenseUsize` and every `define_id*!` type (structural
`raw` equality/hashing under the clean-id invariant).

**Checked migration.** Two closed state predicates, `trail_migrating` (unique
payloads published with headers) and `trail_tentative` (next frame deduplicated
into the pool, header pending), are maintained by four checked primitives:
`trail_frame_tentative_checked` (returns `(start, writes, uniques)`),
`trail_frame_commit_checked` (publishes the header and extends the ghost plan),
`trail_frame_discard_checked` (truncates a rejected frame) and
`trail_migration_finish_checked` (one bulk prefix retirement, then
`lemma_trail_migration_frames`/`lemma_trail_migration_wf`). The plan lemmas were
generalized from `Seq<Vec<(T, I)>>` to `Seq<Seq<(T, I)>>` so a ghost plan of
pool subranges reuses them; `lemma_trail_plan_prefix_push` supplies prefix
stability. The actual executors are now checked loops over these primitives:
`runtime_migrate_trail_count`; `runtime_migrate_trail`, whose
`TierLimit::Adaptive` branch commits a frame while `writes >= 2 * uniques` and
discards the first frame that fails; the closure-free, tier-indexed
`retained_closed_prefix` (with `pair_frame_entries`); and
`adaptive_trail_stage_checked`, the byte-budget Trail stage of
`runtime_apply_adaptive`, which discards the first ineligible frame and stops.
`Ratio` is now a Verus-native struct (`denominator: usize` under a type
invariant instead of `NonZeroUsize`, whose vstd specs are feature-gated) with a
proved `accepts`; its opaque registration is gone. The `AdaptiveReport`
accounting order (inspected/W/U before eligibility) is unchanged.

Removed as dead: `runtime_trail_shape`, `runtime_execute_trail_plan`,
`execute_trail_plan_storage_checked`, `append_trail_plan_checked`,
`append_owned_hot_frame_checked`, `append_selected_hot_frame_checked`,
`plan_views`, and the sort-based `trail_select` items. Behavioral notes: the
adaptive stage guards overflow with `checked_*` and `guard::refuse` where the
external body used `expect`/plain arithmetic (same unreachable-overflow panic
semantics); `saturating_mul` is written as `checked_mul` with a `usize::MAX`
fallback because vstd carries no `saturating_mul` contract.

Targeted evidence: `trail_select` **17 verified** (`/tmp/sp-d21-dedupe4.log`,
later 8 after removing the sort items, `/tmp/sp-d21-dedupe5.log`); all `*trail*`
Vec functions **39 verified** (`/tmp/sp-d21-select-checked1.log`); `tier_policy`
**8 verified** (`/tmp/sp-d21-ratio3.log`); full Vec module **346 verified, 1
error** before the final `invariant_except_break` fix
(`/tmp/sp-d21-vec-full1.log`), then `adaptive_trail_stage_checked` **verified**
(`/tmp/sp-d21-adaptive2.log`). Trust: **68 default + 5 literal** markers
(from 74); default axioms 1 -> 4 plus one generated per consumer id type.

Remaining on this front: Hot-to-Cold (in-place slice sort of `(T, I)` by `I`
under a std `sort_unstable_by_key` contract, replacing the copying insertion
sort in `cold_stack`/`diff_compress` and the per-frame `to_vec` copies),
`hot_frame_run_count`, the adaptive Hot stage and reclamation, the configured/
forced/mark dispatch wrappers, derived/parallel closure, and benchmark parity.

Trail-dedupe checkpoint evidence (fresh, touched source before each Verus
run): full default **2503 verified, zero errors** (`/tmp/sp-d21-dedupe-default.log`);
literal-types **2503 verified, zero errors** (`/tmp/sp-d21-dedupe-literal.log`);
conditional composition **80 verified, zero errors**
(`/tmp/sp-d21-dedupe-composition.log`); `au-verus` **29 verified, zero errors**
(`/tmp/sp-d21-dedupe-au.log`); feature suite **277 passed, 10 ignored**
(`/tmp/sp-d21-dedupe-tests.log`); release differential policy matrix with
`PROPTEST_CASES=1024` **4 passed** (`/tmp/sp-d21-dedupe-policy.log`); e-graph/SAT
consumers **1267 passed, 45 ignored** (`/tmp/sp-d21-dedupe-consumers.log`);
canary **2 passed** (`/tmp/sp-d21-dedupe-canary.log`). Formatting, whitespace and
the unchanged-legacy check passed; the CI trust constant moves to 68. Benchmark
parity remains an open acceptance criterion and is measured at the end.


## 2026-09-16 — Hot-to-Cold migration through in-place std sort

**Algorithm change (user-directed).** Hot frames are unordered, so a closed
Hot frame is now sorted in place inside the Hot pool by std's unstable sort and
encoded into Cold straight from that slice. This removes the per-frame `to_vec`
copy of `runtime_migrate_hot_count`, the adaptive stage's per-frame copy plus
`Vec<Vec<(T, I)>>` plan (`runtime_hot_shape`, `runtime_execute_hot_plan`), and
the `Vec<usize>` scratch of `hot_frame_run_count`; runs are counted on the
sorted slice by `count_index_runs` with no allocation. A frame the adaptive
policies reject stays in Hot, sorted, which is meaning-preserving.

**Trusted std contract.** `std_sort::sort_pairs_by_index(v, start, end)` states
std's documented `sort_unstable_by_key` behaviour for the index key: same
length, nothing outside `[start, end)` touched, same multiset on the range,
non-decreasing `as_nat` order (trust ledger group B, contract-carrying). It is
the only new trusted item; `diff_compress::sort_frame_by_index` now uses it too,
dropping the former verified insertion sort's quadratic worst case while keeping
that function's contract.

**Checked migration.** `lemma_unique_range_permutation` proves a unique range
permuted within itself stays unique with the same earliest-capture map. The
closed state predicates `hot_migrating` (= `hot_migrating_hot` for the pool and
`hot_migrating_cold` for the appended Cold frames) and `hot_retired_from` are
maintained by `hot_frame_sort_checked`, `hot_frame_encode_checked` and
`hot_migration_finish_checked`, and read through accessor lemmas so every query
stays below the default resource limit. The encode step derives the new Cold
frame's coverage-is-capture and cell values from `cold_encode::run_prefix`
(`lemma_run_prefix_covers`/`_entry`/`_cell`), and `lemma_cold_append_keeps_*`
transfer kept frames. `lemma_hot_migration_wf` recovers the full invariant after
the bulk retirement: partition, kept and new Cold reconstruction
(`lemma_captured_cell_value` reads the frame contract through the map), rebased
Hot frames (`lemma_range_saved_value_retire_prefix`), unchanged Trail
representation, ingress (the last Hot frame's capture range rebases), canonical
history. `reclaim_after_hot_migration_checked` keeps the `ShrinkToFit`
reclamation of the three pools. `runtime_migrate_hot_count`, `runtime_migrate_hot`
(with the `TierLimit::Adaptive` run-count loop) and `adaptive_hot_stage_checked`
(the byte-budget Hot stage, called by the still-external `runtime_apply_adaptive`)
are checked loops over the primitives.

Trust: **64 default + 5 literal** markers (five removed, one trusted std sort
contract added); default axioms unchanged at 4. Targeted evidence for every new
lemma and primitive is in `/tmp/sp-d21-hot*.log`; the final whole-module run is
`/tmp/sp-d21-vec-full3.log`. Gate evidence follows.

Hot-to-Cold checkpoint evidence (fresh, touched source before each Verus run):
full default **2561 verified, zero errors** (`/tmp/sp-d21-hotcold-default.log`);
literal-types **2561 verified, zero errors** (`/tmp/sp-d21-hotcold-literal.log`);
conditional composition **80 verified, zero errors**
(`/tmp/sp-d21-hotcold-composition.log`); `au-verus` **29 verified, zero errors**
(`/tmp/sp-d21-hotcold-au.log`); feature suite **277 passed, 10 ignored**
(`/tmp/sp-d21-hotcold-tests.log`); release differential policy matrix with
`PROPTEST_CASES=1024` **4 passed** (`/tmp/sp-d21-hotcold-policy.log`);
e-graph/SAT consumers **1267 passed, 45 ignored**
(`/tmp/sp-d21-hotcold-consumers.log`); canary **2 passed**
(`/tmp/sp-d21-hotcold-canary.log`). Formatting, whitespace, the key-model axiom
discipline grep and the unchanged-legacy check passed; the CI trust constant
moves to 64. Benchmark parity remains an open acceptance criterion.


## 2026-09-16 — Checked rollover dispatch

The whole dispatch layer above the migrations is now checked, with no new
trusted item. `runtime_closed_history_bytes` folds closed Trail/Hot frame
entries through `pair_frame_entries` and combines header/payload sizes with
`checked_*` arithmetic, refusing on overflow exactly where the external body
`expect`ed. `runtime_reclaim_adaptive_tier_capacities` is the seven-pool
`shrink_vec_capacity` composition with the existing view-transfer lemmas, so its
former contract-free trust row is retired. `runtime_apply_adaptive` builds a zero
report literal (the derived `Default`), runs the two checked stages with the
original recompute between them, combines counts with checked adds, reclaims
when anything migrated and reports the budget shortfall; the public
`apply_adaptive` keeps its contract. `runtime_apply_tier_policy`,
`runtime_apply_configured_rollover` (the `hot_buffer` closure became a `match`),
`runtime_rollover_on_mark` and the `ApplyConfigured`/`ForceClosed` mark path
`runtime_push_frame_fallback` are checked compositions; `apply_tier_policy`,
`flush_trail` and `compress_hot` gain the standard `wf` contracts and are listed
in the partial-API allowlist. The shared postcondition `tiers_only_changed`
states that only the seven physical tier vectors move.

Targeted evidence: **17 verified, zero errors** across
`/tmp/sp-d21-policy1-*.log`. Trust: **53 default + 5 literal** markers (eleven
removed), default axioms unchanged at 4. Gate evidence follows.

Policy-dispatch checkpoint evidence (fresh, touched source before each Verus
run): full default **2576 verified, zero errors** (`/tmp/sp-d21-policy-default.log`);
literal-types **2576 verified, zero errors** (`/tmp/sp-d21-policy-literal.log`);
conditional composition **80 verified, zero errors**
(`/tmp/sp-d21-policy-composition.log`); `au-verus` **29 verified, zero errors**
(`/tmp/sp-d21-policy-au.log`); feature suite **277 passed, 10 ignored**
(`/tmp/sp-d21-policy-tests.log`); release differential policy matrix with
`PROPTEST_CASES=1024` **4 passed** (`/tmp/sp-d21-policy-policy.log`); e-graph/SAT
consumers **1267 passed, 45 ignored** (`/tmp/sp-d21-policy-consumers.log`); canary
**2 passed** (`/tmp/sp-d21-policy-canary.log`). The partial-API audit reports the
unchanged baseline discrepancy (73 public partial functions, 33 allowed, 40
unlisted, zero unsafe-public; `/tmp/sp-d21-policy-partial-api2.log`); the four
`wf`-only public wrappers are not partial by its rule and stay unlisted.
Formatting, whitespace, the key-model axiom discipline grep and the
unchanged-legacy check passed; the CI trust constant moves to 53. Benchmark
parity remains an open acceptance criterion.


## 2026-09-16 — Derived restore contracts and group member effects

The derived wrappers now export the effects their inner checked restores
already establish. `ListArena::try_restore` exports heads/nodes/model views at
the mark and all three archive prefixes; `EClasses::restore`/`try_restore`
export roots, size, depth and the roots archive prefix (the wrapper's check is
exactly full validity); `SpMap::restore`/`try_restore` export depth and the log
archive prefix; `UnionFind::try_restore` exports parent/rank views and the
parent archive prefix; `BPlusTreeSet::restore` exports both retained archive
prefixes. Every fallible wrapper now states `r is Err ==> state unchanged`.

`SyncMember` gains an object-safe `model`/`archive` pair (index-projected, so
`Box<dyn SyncMember>` stays usable) with a `tracked &self` archive-depth
obligation; the `Vec` member discharges them from `seal_frame`/`restore_frame`
by sequence extensionality. `ForkHistory::mark` exports unchanged member models
and one archived model per member; `restore` exports every member's model at the
token's depth and the archive prefix; rejected requests leave the group
unchanged. The parallel variants carry the same contracts over the documented
rayon boundary (trust ledger 3.6d). No runtime change and no new trust.

Targeted evidence: `list` 1, `eclasses` 3, `map` 2, `circular_list` 1,
`union_find` 1, `bplus` 1 and `sync_group` **17 verified, zero errors**
(`/tmp/sp-d21-derived*-*.log`). Trust remains **53 default + 5 literal**. Gate
evidence follows.

Derived-contract checkpoint evidence (fresh, touched source before each Verus
run): full default **2577 verified, zero errors** (`/tmp/sp-d21-derived-default.log`);
literal-types **2577 verified, zero errors** (`/tmp/sp-d21-derived-literal.log`);
conditional composition **80 verified, zero errors**
(`/tmp/sp-d21-derived-composition.log`); `au-verus` **29 verified, zero errors**
(`/tmp/sp-d21-derived-au.log`); feature suite **277 passed, 10 ignored**
(`/tmp/sp-d21-derived-tests.log`); release differential policy matrix with
`PROPTEST_CASES=1024` **4 passed** (`/tmp/sp-d21-derived-policy.log`); e-graph/SAT
consumers **1267 passed, 45 ignored** (`/tmp/sp-d21-derived-consumers.log`);
canary **2 passed** (`/tmp/sp-d21-derived-canary.log`); partial-API audit at the
unchanged baseline (73/33/40/0). Formatting, whitespace and the unchanged-legacy
check passed; trust remains 53 default + 5 literal. The Step 3 dependency map is
`proofs/top_down/interface-inventory.md`.


## 2026-09-16 — Checked pending-restore indices and the production sequence witness

`pending_restore_indices` is now checked with an exact contract: `Some` iff the
token is restorable, and `names_index(out, j)` iff some frame in
`[token, depth)` captures `j` (`frame_captures`, the physical saved-value
lookup). The `external_body` Cold scaffold is replaced by
`pending_cold_indices_checked` (frames, runs, cells) and the Hot/Trail walks by
`pending_pair_indices_checked`; `lemma_pending_union` joins the three passes and
`lemma_frame_captures_cold`/`_pair` bridge each tier's predicate to
`frame_captures`. The loops are the original ones; the exec length call bounds
the run-range addition.

`sequence_witness_checked` is the Step 3 production instantiation: from the
public contracts alone it proves that after mark, write, mark, restore, write,
`apply_tier_policy` and an older restore the live view equals the archived
snapshot, the depth the token's frame and the archive its prefix. The interface
inventory (`proofs/top_down/interface-inventory.md`) maps every provisional
`Runtime` method to its checked production function, supplier and consumer.

Targeted evidence: `pending_cold_indices_checked` 4, `pending_pair_indices_checked` 3,
`lemma_pending_union` 1, `lemma_frame_captures_*` 1 each, `pending_restore_indices` 1,
`sequence_witness_checked` 1 (`/tmp/sp-d21-pending*-*.log`). Trust: **51 default +
5 literal** (two markers removed, no new trust). Gate evidence follows.

Pending-indices/witness checkpoint evidence (fresh, touched source before each
Verus run): full default **2589 verified, zero errors**
(`/tmp/sp-d21-pending-default.log`); literal-types **2589 verified, zero errors**
(`/tmp/sp-d21-pending-literal.log`); conditional composition **80 verified, zero
errors** (`/tmp/sp-d21-pending-composition.log`); `au-verus` **29 verified, zero
errors** (`/tmp/sp-d21-pending-au.log`); feature suite **277 passed, 10 ignored**
(`/tmp/sp-d21-pending-tests.log`); release differential policy matrix with
`PROPTEST_CASES=1024` **4 passed** (`/tmp/sp-d21-pending-policy.log`); e-graph/SAT
consumers **1267 passed, 45 ignored** (`/tmp/sp-d21-pending-consumers.log`);
canary **2 passed** (`/tmp/sp-d21-pending-canary.log`); partial-API audit at the
unchanged baseline (73/33/40/0). Formatting, whitespace and the unchanged-legacy
check passed; the CI trust constant moves to 51.


## 2026-09-16 — EClasses component contents exported through restore

`EClasses::restore` and `try_restore` now state every column of an e-class
state at the token's frame and every retained archive prefix, not only the
union-find roots: entries (`CircularList` model and node views, both archives),
representatives (`SparseSet` dense/sparse/indices views and archives), uses
(`ListArena` model view and archive) and the minimum pool (`Vec` view and
archive). The new `pub open(crate)` accessors (`entries_model_view`,
`entries_archive`, `reprs_*_view`/`_archive`, `uses_model_view`/`_archive`,
`pool_view`/`_archive`) only project the components' own verified views; the
facts come from the component restores' existing contracts, so no proof body
changed and no runtime code moved. This closes the derived-contract audit
table (`proofs/top_down/derived-contract-audit.md`).

Targeted evidence: `eclasses` `*restore*` **3 verified, zero errors**
(`/tmp/sp-d21-eclasses1.log`). Trust unchanged at **51 default + 5 literal**.
Gate evidence follows.

EClasses checkpoint evidence (fresh, touched source before each Verus run):
full default **2589 verified, zero errors** (`/tmp/sp-d21-eclasses-default.log`);
literal-types **2589 verified, zero errors** (`/tmp/sp-d21-eclasses-literal.log`);
conditional composition **80 verified, zero errors**
(`/tmp/sp-d21-eclasses-composition.log`); `au-verus` **29 verified, zero
errors** (`/tmp/sp-d21-eclasses-au.log`); feature suite **277 passed, 10
ignored** (`/tmp/sp-d21-eclasses-tests.log`); release differential policy matrix
with `PROPTEST_CASES=1024` **4 passed** (`/tmp/sp-d21-eclasses-policy.log`);
e-graph/SAT consumers **1267 passed, 45 ignored**
(`/tmp/sp-d21-eclasses-consumers.log`); canary **2 passed**
(`/tmp/sp-d21-eclasses-canary.log`); partial-API audit at the unchanged
baseline (73/33/40/0). Formatting, whitespace and the unchanged-legacy check
passed; trust unchanged at 51 default + 5 literal. The same commit records the
final performance protocol (`doc/tasks/final-performance-report.md`, tolerance
and decision rule fixed before measurement) and the comparison script
`tools/bench_compare.py`.


## 2026-09-16 — Final checkpoint: last Vec marker removed, benchmark-driven fixes

`try_mark_adaptive` was the last execution-first `Vec` marker: a public entry
point with a trusted semantic postcondition (view unchanged, depth + 1,
snapshot pushed) whose body — three guards, `mark_with_options`,
`runtime_apply_adaptive` — had become fully checked in earlier checkpoints.
The marker is removed with the body unchanged (the three index-bound lemma
calls the sibling `try_mark_with_options` uses are added before the capacity
guard) and the contract follows from the callees'. Trust: **50 default + 5
literal**; CI `EXPECTED_DEFAULT=50`. No default marker carries a semantic
postcondition about container contents any more.

The first execution of the frozen benchmark protocol
(`doc/tasks/final-performance-report.md`) attributed every regressed case and
led to two constant-factor changes, neither of which alters an algorithm:
`trail_select::dedupe_trail_range` reserves its hash set and output for the
frame up front (`HashSet::reserve`/`Vec::reserve`, both vstd-specified and
view-preserving; the set was growing from empty through ~9 rehashes per
512-entry frame), and `runtime_closed_history_bytes` states its loop bounds
explicitly with the per-frame accessor forced inline. Targeted evidence:
`trail_select` **8 verified**, `pair_frame_entries` **1 verified**,
`runtime_closed_history_bytes` **3 verified**, `try_mark_adaptive` **1
verified**, zero errors (`/tmp/sp-d21-fix1-*.log`, `/tmp/sp-d21-fix2-rchb.log`,
`/tmp/sp-d21-tma.log`). Gate evidence follows.

Final checkpoint evidence (fresh, touched source before each Verus run): full
default **2590 verified, zero errors** (`/tmp/sp-d21-final-default.log`);
literal-types **2590 verified, zero errors** (`/tmp/sp-d21-final-literal.log`);
conditional composition **80 verified, zero errors**
(`/tmp/sp-d21-final-composition.log`); `au-verus` **29 verified, zero errors**
(`/tmp/sp-d21-final-au.log`); feature suite **277 passed, 10 ignored**
(`/tmp/sp-d21-final-tests.log`); release differential policy matrix with
`PROPTEST_CASES=1024` **4 passed** (`/tmp/sp-d21-final-policy.log`); e-graph/SAT
consumers **1267 passed, 45 ignored** (`/tmp/sp-d21-final-consumers.log`);
canary **2 passed** (`/tmp/sp-d21-final-canary.log`); partial-API audit at the
unchanged baseline (73/33/40/0). Formatting, whitespace and the unchanged-legacy
check passed; trust **50 default + 5 literal**, CI `EXPECTED_DEFAULT=50`.


## 2026-09-16 — User-directed performance work: B+ tree, find sweep, size sweep

At the user's direction (overriding "do not modify algorithms" for these
items) the verified B+ tree was brought above legacy speed on every measured
case: `try_from_sorted` no longer validates twice; the cursor caches the leaf
it stands on (`cursor_ok = cursor_wf ∧ leaf_cached`); leaves are filled by the
total `NodeLayout::leaf_fill_keys` with the key→word conversion fused in and
one refusal per leaf; the order checks are branch-free reductions; and
`insert` tracks the rightmost leaf incrementally (`insert_rec` returns the
fresh right leaf iff the subtree's rightmost leaf split — `last_after`,
`last_lift`, three per-arm lemmas) instead of descending from the root after
every insert (`rightmost_leaf_of` removed). Bulk load 0.53× → 1.19×, scan
0.60× → 3.7×, shuffled insert 0.89× → 1.04× against legacy
(`doc/tasks/final-performance-report.md`). The e-class find sweep was shown
to be at parity (per-process placement bimodality, not code) and the tracked
vectors at parity at 10M/100M elements. Benchmarks: `tracked_vec_bench` gains
10M/100M groups, `eclasses_bench` drops a per-element `black_box`,
`bplus_cursor_bitset_bench` gains split bulk-load/scan cases and seeks its
cursors first. No new trust; the partial-API count is unchanged.

Targeted evidence: `bplus` module **189 verified**, `bplus_layout` **323
verified**, zero errors (`/tmp/sp-d21-ll4.log`, `/tmp/sp-d21-total3.log`).

Gate evidence (fresh, touched source before each Verus run): full default
**2602 verified, zero errors** (`/tmp/sp-d21-final3-default.log`);
literal-types **2602 verified, zero errors** (`/tmp/sp-d21-final3-literal.log`);
conditional composition **80 verified, zero errors**
(`/tmp/sp-d21-final3-composition.log`); `au-verus` **29 verified, zero errors**
(`/tmp/sp-d21-final3-au.log`); feature suite **277 passed, 10 ignored**
(`/tmp/sp-d21-final3-tests.log`); release differential policy matrix with
`PROPTEST_CASES=1024` **4 passed** (`/tmp/sp-d21-final3-policy.log`); B+ tree,
oracle and reference-e-graph property tests **31 passed**
(`/tmp/sp-d21-final3-conformance.log`); e-graph/SAT consumers **1267 passed,
45 ignored** (`/tmp/sp-d21-final3-consumers.log`); canary **2 passed**
(`/tmp/sp-d21-final3-canary.log`); partial-API audit at the unchanged baseline
(73/33/40/0). Formatting, whitespace and the unchanged-legacy check passed;
trust **50 default + 5 literal**.


## 2026-09-16 — Cached Trail-to-Hot dedupe set (extended goal, item a)

The dedupe set for the Trail-to-Hot conversion is now owned by the vector
(`Vec::trail_seen: Option<HashSet<I, IndexHasher>>`): each migration pass
takes it out (`Option::take`), clears and reserves it per frame as before, and
puts it back, so its table survives across passes instead of being allocated
and freed per rollover; `ShrinkToFit` reclamation drops it. The field has no
spec content; it is named, like the tier vectors, in every framing predicate
of the Trail pass (`trail_migrating`, `trail_tentative`,
`trail_retained_effect`, `lemma_trail_migration_wf`'s framing, the
`runtime_migrate_trail*`/`adaptive_trail_stage_checked` and
`trail_migration_finish_checked` contracts, `tiers_only_changed`). One more
struct field made five proofs that were at the solver's edge exceed it; per
convention none had its limit raised: `lemma_persistence_saved_len` hides
`wf` (its named parts suffice), `lemma_push_preserves` delegates the Cold
representation to `lemma_push_cold_repr`/`lemma_push_cold_reconstructs`,
`lemma_survivor_top_bounds` is split by tier arm, `lemma_hot_migration_hot_frame`
hides its target predicate until the end, and `maybe_shrink` re-establishes
`wf` through the same named-parts transfer recipe as tier reclamation instead
of a full `wf` reveal (which had begun to hang the solver).

Targeted evidence: Trail family **41 verified** (`/tmp/sp-d21-seen4.log`),
decomposed lemmas and `maybe_shrink` **verified individually**
(`/tmp/sp-d21-rl*.log`); `vec` module **436 verified, zero errors**.

Gate evidence (fresh, run in a worktree holding exactly this commit's files,
`/tmp/sp-d21-1a-*.log`): full default **2606 verified, zero errors**
(four more functions than `31286e2`: the decomposed lemmas); literal-types
**2606 verified, zero errors**; conditional composition **80 verified**;
`au-verus` **29 verified**; feature suite **277 passed, 10 ignored**; release
differential policy matrix with `PROPTEST_CASES=1024` **4 passed**; B+ tree,
oracle and reference-e-graph property tests **31 passed**; e-graph/SAT
consumers **1267 passed, 45 ignored**; canary **2 passed**; partial-API audit
at the unchanged baseline (73/33/40/0); formatting, whitespace and the
unchanged-legacy check passed; trust **50 default + 5 literal**. Benchmarks:
`doc/tasks/final-performance-report.md`, "Extended goal 1(a)".


## 2026-09-16 — SpMap restore unwinds the discarded suffix (extended goal, item b)

`SpMap::restore` no longer rebuilds its hash index from the survivors. Each
log position now carries the position of the PREVIOUS occurrence of its key
(`prev: Vec<Option<I>>`, a column parallel to the log), filled from the value
`HashMap::insert` already returns when the entry is indexed — so `insert` does
no extra lookup and no extra clone. Restore reads the target frame's saved
length, and when the discarded suffix is no larger than the survivors it
unwinds the index BEFORE the log truncates (`unwind_index`): the discarded
entries are walked newest first, and each one's key is pointed back at its
`prev` link (`insert`, the one place restore clones a key) or removed when the
link is `None`. The cost is one hash operation per discarded entry, and zero
work for a restore straight after a mark, instead of one hash insert plus one
key clone per surviving entry. When the suffix outnumbers the survivors the
old full rebuild (`rebuild_index`, kept verified) is cheaper and is taken.

The fingerprint-bucket variant sketched earlier was dropped: vstd specifies no
`BuildHasher::hash_one`/`Hasher::finish`, so a spec-level fingerprint would
have needed a new trusted specification. The previous-occurrence chain needs
none: it is proved from the index's own last-occurrence agreement.

Proof structure. `wf` gains `prev_agrees` (every link is the last occurrence
of its key strictly before its position, or `None` when the key has no
earlier occurrence — `prev_link_ok`); `index_agrees` is restated through the
part relation `index_agrees_seq`, and `index_agrees_prefix_seq` is its
restriction to `[0, bound)`. `unwind_index`'s loop invariant is prefix
agreement at the running bound, and `lemma_unwind_step` shows one retirement
step lowers the bound by one (the retired position is the last occurrence of
its key within the bound; its link is the unique last occurrence below it).
`lemma_index_agrees_after_truncate` and `lemma_prev_agrees_after_truncate`
turn prefix agreement into full agreement once the log and the column are
cut; `lemma_insert_prev_link` proves the chain maintenance of `insert`,
using `lemma_last_occurrence_exists` (moved from `hinted_arena` to `map`,
where it belongs) for the "no earlier occurrence" case. No proof needed
decomposition for the solver's limit. The public contract of every map
operation is unchanged, so `HintedArena` and the consumers re-verify without
edits. No new trust; the partial-API count is unchanged (73/33/40/0).

Targeted evidence: `map` module **31 verified, zero errors**
(45 s, `scratchpad/map_verify3.log`); `hinted_arena` module **14 verified,
zero errors** (`scratchpad/hinted_verify1.log`).

Gate evidence (fresh, run in a worktree holding exactly this commit's files,
`/tmp/sp-d21-1b-*.log`): full default **2614 verified, zero errors** (eight
more functions than `3a41ff5`: the map's new lemmas and `unwind_index`);
literal-types **2614 verified, zero errors**; conditional composition **80
verified**; `au-verus` **29 verified**; feature suite **277 passed, 10
ignored**; release differential policy matrix with `PROPTEST_CASES=1024`
**4 passed**; B+ tree, oracle and reference-e-graph property tests **31
passed**; e-graph/SAT consumers **1267 passed, 45 ignored**; canary **2
passed**; partial-API audit at the unchanged baseline (73/33/40/0);
formatting, whitespace and the unchanged-legacy check passed; trust **50
default + 5 literal**. Benchmarks: `doc/tasks/final-performance-report.md`,
"Extended goal 1(b)".


## 2026-09-16 — Store policy for every composite (extended goal, item 2)

Every composite now takes a policy type parameter `P` that chooses the store
of each of its tracked columns, defaulting to `HotFirst` (the stores the
composites hardcoded before), so nothing observable changes unless a consumer
names the policy. `crate::store_policy` holds two plain traits — no generic
associated types, no specialization — chosen by the column's element type:
`TaggedFamily<T, I, TRACK>` for a `Tagged` element (where `HotFirst` gives
`InlineStore`) and `PlainFamily<T, I, TRACK>` for any `Copy` element (where
`HotFirst` gives `ParallelStore`); `TrailFirst` gives `TrailStore` for both.
Each family has an associated `Store: DiffStore<T, I, TRACK>` and a verified
`empty()` (ensures `wf` and an empty `data()`), and every composite builds its
columns through `Vec::with_store(P::empty())`. Parameterized, in order:
`UnionFind<T, J, TRACK, PROOFS, P>` (parent, rank, and the two proof
columns), `SparseSet<T, Idx, S, TRACK, VC, P>` (sparse and indices; `dense`
already took `S`), `CircularList<T, N, TRACK, P>`, `ListArena<T, L, N, TRACK, P>`,
`BPlusTreeSet<K, L, S, TRACK, P>`, and `EClasses<T, K, L, N, J, TRACK, PROOFS, P>`,
which threads `P` into its four composites and its min-monomial pool (a
plain-family column). Consumers that name these types with the old argument
lists are unchanged (the default supplies `P`).

Two things the concrete stores had been supplying for free had to be stated
once for the abstract store. The frame-pushing `Vec` entry points require the
column's length to fit its index word, which the composites had been reading
off `InlineStore`'s open `wf`; `DiffStore` gains the universal lemma
`lemma_wf_data_len` (`wf ==> data().len() < I::max_nat()`, discharged by each
of the four stores from its own `wf`), and the composites call it before
`push_frame`/`seal_frame` and inside the arena's row-fits lemmas. And the
arenas' total-operation guards read the store's `data` field directly; they
now go through the trait's `raw_len()`. The proofs themselves needed no other
change: they were already stated over the `Vec` contract.

No new trust; the partial-API count is unchanged.

Targeted evidence (fresh compile before each module): `store_policy` **4 verified**, `diff_store` **6**, `inline_store` **32**, `parallel_store` **30**, `trail_store` **28**, `dyn_store` **28**, `union_find` **32**, `sparse_set` **31**, `list` **78**, `circular_list` **46**, `bplus` **187**, `eclasses` **62**, all zero errors (`scratchpad/policy_verify6.log`, `policy_verify7.log`).

Gate evidence (fresh, `/tmp/sp-d21-2-*.log`, run on the tree that becomes
this commit): full default **2622 verified, zero errors** (eight more
functions than the 1(b) commit: the family `empty` constructors and the
store lemma); literal-types **2622 verified, zero errors**; conditional
composition **80 verified**; `au-verus` **29 verified**; feature suite **277
passed, 10 ignored**; release differential policy matrix with
`PROPTEST_CASES=1024` **4 passed**; B+ tree, oracle and reference-e-graph
property tests **31 passed**; e-graph/SAT consumers **1267 passed, 45
ignored** (the consumers name the composites with their old argument lists
and compile unchanged); canary **2 passed**; partial-API audit at the
unchanged baseline (73/33/40/0); formatting, whitespace and the
unchanged-legacy check passed; trust **50 default + 5 literal**. Design:
`doc/design/18-store-policy.md`. Benchmarks:
`doc/tasks/final-performance-report.md`, "Extended goal 2".

## 2026-09-16 — HintedArena::note_hint pushes into its bucket in place (extended goal, item 1(d))

`note_hint`'s existing-key arm rebuilt the fingerprint's bucket by copying
it element by element into a fresh vector, pushing, and storing the copy
back (`Vec::set`), because the code predated vstd's specifications of
`core::mem::swap` and `&mut vec[i]`. It now swaps the bucket out against an
empty vector (no allocation), pushes, and swaps it back: destination
passing, no copy. The proof is unchanged in structure — the two swaps leave
`spill@` equal to the old sequence updated at the slot with the pushed
bucket, which is what the previous copy established — and the module drops
one loop. No consumer uses `HintedArena` today, so there is no benchmark to
re-run; the change is recorded for the allocation tour's completeness.

Item 1(c) (`diff_compress::sort_frame_by_index` in place) needs no change:
its copy is reached only from the cold-stack sealing paths, whose sole
caller is the cold-stack differential test, and from the legacy compression
cadence that production does not enable.

Targeted evidence: `hinted_arena` module **13 verified, zero errors**
(`scratchpad/hinted_verify2.log`).

Gate evidence (fresh, run in a worktree holding exactly this commit's file,
`/tmp/sp-d21-1d-*.log`): full default **2621 verified, zero errors**;
literal-types **2621 verified, zero errors**; conditional composition **80
verified**; `au-verus` **29 verified**; feature suite **277 passed, 10
ignored**; release differential policy matrix with `PROPTEST_CASES=1024`
**4 passed**; B+ tree, oracle and reference-e-graph property tests **31
passed**; e-graph/SAT consumers **1267 passed, 45 ignored**; canary **2
passed**; partial-API audit at the unchanged baseline (73/33/40/0);
formatting, whitespace and the unchanged-legacy check passed; trust **50
default + 5 literal**.

## 2026-09-16 — E-graph cache stores made static (extended goal, item 3)

The e-graph's ten node-cache columns (`egraph/src/node_store.rs`) were
`VecD` columns whose store was selected once per process by the
`SEMPER_DIFF` lever. Before choosing, the three disciplines were measured
on both workload classes — equality saturation (`saturate_bench`) and
SMT-style mark/backtrack (the new in-process `egraph/benches/store_bench.rs`
over the `sp-t880` push/pop programs) — and every ratio landed within
2.2 % of one: the cache columns are not where the e-graph's time goes. A
per-config policy would buy nothing measurable and would cost the family
bound (which names `TRACK`) on `NodeStore`, the `EGraph` struct and 51
generic functions, because an abstract policy is not covered by the blanket
family implementations that make a concrete one free. The caches therefore
take the static Hot-first inline store (`VecI`), which removes the enum
dispatch and the lever (`--diff-mode` on the CLI is gone); the verified
crate is untouched, so no proof changes. Numbers, the dispatch-removal
comparison and the reasoning: `doc/tasks/final-performance-report.md`,
"Extended goal 3".

Gate evidence (fresh, run in a worktree holding exactly this commit's
files, `/tmp/sp-d21-3-*.log`): full default **2621 verified, zero errors**
(unchanged: the verified crate is untouched); literal-types **2621 verified,
zero errors**; conditional composition **80 verified**; `au-verus` **29
verified**; feature suite **277 passed, 10 ignored**; release differential
policy matrix with `PROPTEST_CASES=1024` **4 passed**; B+ tree, oracle and
reference-e-graph property tests **31 passed**; e-graph/SAT consumers
**1267 passed, 45 ignored**; canary **2 passed**; partial-API audit at the
unchanged baseline (73/33/40/0); formatting, whitespace and the
unchanged-legacy check passed; trust **50 default + 5 literal**. Static
inline against the dynamic store: AC saturation 1.06–1.08×, plain
rewriting 1.00×, push/pop 1.01–1.02×, the 20 000-empty-frame program 1.08×
(15 cases, all pass).

## 2026-09-17 — E-graph configurations for saturation and for SMT (extended goal, item 4)

The Trail-first policy was designed for the Sundance SMT integration, so the
e-graph now chooses its store discipline per configuration:
`EGraphConfig::Policy`, threaded through the class layer (`EClasses<…, P>`)
and the ten node-cache columns (`NodeStore`/`caches.rs`, built through the
verified crate's new public constructors `store_policy::{tagged_vec,
plain_vec}`, the total forms of `Vec::with_store(P::empty())`). Four
configurations: `EqSat32`/`EqSat64` (`DefaultConfig`/`Config64`, `HotFirst`)
and `Smt32`/`Smt64` (the same id families, `TrailFirst`); the SAT core's
`Euf31`/`Euf63` now wrap the SMT ones, with `EufEqSat31`/`EufEqSat63` for
the saturation stores. Because an abstract policy is not covered by the
blanket family implementations, the engine states one bound,
`Cfg::Policy: StorePolicy<Cfg, TRACK>` (a blanket-implemented alias for the
class-layer and cache families in `egraph/src/config.rs`), on its struct, on
`Interpreter`, `NodeStore` and the wrapper types that hold an e-graph
reference, and on every generic item naming them — about a hundred and
forty sites, added by a script over the item headers. The families' stores
are now declared `Send` (they always were), which the engine's threaded
mark/restore requires of the abstract store. The verified crate's change is
confined to `store_policy.rs` (`store_policy` **6 verified**); every proof
is unchanged.

Gate evidence (fresh, `/tmp/sp-d21-4-*.log`, run on the tree that becomes
this commit): full default **2623 verified, zero errors** (two more
functions than `197fb48`: the public constructors); literal-types **2623
verified, zero errors**; conditional composition **80 verified**; `au-verus`
**29 verified**; feature suite **277 passed, 10 ignored**; release
differential policy matrix with `PROPTEST_CASES=1024` **4 passed**; B+ tree,
oracle and reference-e-graph property tests **31 passed**; e-graph/SAT
consumers **1267 passed, 45 ignored** (the SAT core now runs on `Smt32`);
canary **2 passed**; partial-API audit at the unchanged baseline
(73/33/40/0); formatting, whitespace and the unchanged-legacy check passed;
trust **50 default + 5 literal**. Benchmarks:
`doc/tasks/final-performance-report.md`, "Extended goal 4".

## 2026-09-17 — Total public API (extended goal, item 5)

The user's rule: the public API must be 100 % safe — no preconditions; a
partial function becomes total through a `Result` or a panic, and the
heavily used ones panic rather than return a `Result`. The partial-API audit
(`tools/check_partial_api.py`) went from 73 public exec functions carrying a
`requires` (33 listed, 40 unlisted) to **zero**, and
`partial-api-allowlist.txt` is empty; the only precondition a public
function may still state is the receiver's own well-formedness
(`wf`/`cursor_wf`/`cursor_ok`/`cwf`), which every constructor and operation
upholds. The checker now reads module visibility from `lib.rs`, so the items
of a `pub(crate)` module are not counted as public.

What changed, by class. Fourteen internal primitives that nothing outside
the crate called (`Codes` helpers, `select_layered`, `sync_group::add_member`,
`two_stack_log::{flush_cold, truncate_hot}`, `Vec::seal_frame`,
`guard::check_precondition`, `capture_bits::set_true`, …) became
`pub(crate)`; the unused `RunCol::idx_at` was removed. Refuse-guards
(`guard::refuse`, the documented trap, on the exact runtime condition the
erased precondition named) made total `History::{mark, restore_to}`,
`GenStamps::{stamp, stamp_at}`, the cold and compressed stacks' frame
operations, every frame's `decode_at` (`ValFrame`, `RunCol`, `DeltaFrame`,
`ColdFrame`, `DictFrame`, `LayeredFrame`, the value compressors), `Codes`,
the run compressors and the sync group's seal/restore. `HintedArena`'s
`complete` predicate joined its `wf` (with a `wf_struct` form for the
mid-operation `note_hint`), so its six operations need only the invariant.
`SparseSet::restore` archives snapshot well-formedness in `wf` (the three
snapshot stacks move in lockstep and every archived triple is `snap_wf`;
`lemma_archive_after_push` carries it through `mark`/`push_frames`), so the
guard checks token validity and equal frame indices only.
`CircularList::{splice, splice_absorb}` refuse an out-of-range id or a
same-ring pair after a verified walk of the absorbed ring
(`guard_different_rings`: the cursor's `walk_seq` is `rotate(ring, p0)`, and
`lemma_rotate_props` shows a node on the ring would have been visited), with
an O(1) fast path when the absorbed ring is a singleton — `next(aid) == aid`
puts `aid` alone on its ring (`lemma_singleton_ring`), the case equality
saturation absorbs most of the time; the
e-graph's merge keeps the walk-free crate-private cores
`splice_core`/`splice_absorb_core`, where distinct rings are a theorem, and
the external_body debug-only walk is gone (trust 50 → 49 default). The
`DiffStore` protocol — thirteen operations whose preconditions are either
ghost (`prepare_mark`, `begin_restore`, `finish_restore`: "every set flag is
named by a diff entry") or bounds the vector has already established — moved
with the ghost views onto the crate-private supertrait
`diff_store_ops::DiffStoreOps`; `DiffStore` keeps the total queries and
maintenance and stays the bound consumers name, every store implements both,
and the protocol test moved in-crate. `NodeLayout`'s nine primitives and the
two free helpers, `Tagged`'s four operations, `SpMap::new`
(`obeys_key_model::<K>() ==> m.wf()`: a property of the type, nothing to
check) and `CompressedFrame::decode_at` carry requires-free conditional
contracts (`precondition ==> postcondition`); the layout impls' runtime
mirrors became refuse-guards, and a new exec twin `is_node_wf` lets the
generic helpers re-establish `node_wf` after their own guard. Verified
callers discharge the hypotheses and keep the full contracts; the proofs of
the composites are unchanged apart from the archive clauses named above.

Gate evidence (fresh, run in a worktree holding exactly this commit's
files, `/tmp/sp-d21-b7-*.log`): full default **2649 verified, zero errors**
(twenty-six more functions than `4453abc`: the guards' proof helpers,
`lemma_archive_after_push`, `guard_different_rings` with
`lemma_singleton_ring`, `is_node_wf` per layout, the split store impls and
the cold-frame lemma's five pieces —
`lemma_hot_frame_encoded_new` went over the solver budget in the new
context and is decomposed into a facts lemma, the value half and the two
directions of the coverage half, without any limit raise); literal-types
**2649 verified, zero errors**; conditional composition **80 verified**;
`au-verus` **29 verified**; feature suite **277 passed, 10 ignored** (the
cold-run store test now runs in-crate; the same-ring misuse test asserts
the refusal in every build); release differential policy matrix with
`PROPTEST_CASES=1024` **4 passed**; B+ tree, oracle and reference-e-graph
property tests **31 passed**; e-graph/SAT consumers **1267 passed, 45
ignored**; canary **2 passed**; partial-API audit **0 public partial
functions, 0 allowed, 0 new, 0 unsafe-public** (from 73/33/40/0);
formatting, whitespace and the unchanged-legacy check passed; trust **49
default + 5 literal** (the debug-only ring walk was the one marker
removed; CI's `EXPECTED_DEFAULT` follows). Benchmarks against `4453abc`:
`doc/tasks/final-performance-report.md`, "Extended goal 5".

## 2026-09-17 — Stratified reporters, literal store on SpMap, Trail fast path, token provenance, grouped-history tests

Seven signed local commits on top of `cd8b2ef`, each gated in the isolated
worktree with the full battery (logs `/tmp/sp-d21-s{1..5}-*.log`,
`/tmp/sp-d21-w5b-*.log`, `/tmp/sp-d21-semb-*.log`): `71f8358` stratified
reporters, `2425233` Trail ascending fast path, `60b34a1` literal store on
SpMap, `6c96c24` token provenance, `33b565c` grouped-history tests,
`683dbef` O(1) stamps, `2743e17` restore semantics B. No `admit`/`assume`,
no new `external_body`, no solver limit raised (two were lowered);
`containers/` unchanged.

**Stratified reporters (`71f8358`).** The byte reporters cannot alter
execution and no proof reads them, so they left the verified perimeter: a
plain-Rust `diagnostics::HeapBytes` trait carries `heap_bytes` for the
stores and columns, every `tracking_bytes`/`total_bytes`/`diff_log_len` is
an ordinary `impl` block after its container's `verus!` block, `DiffStore`
lost its `heap_bytes` method and `SyncMember`/`ForkHistory` theirs. Twelve
`external_body` markers went with them: trust **37 default + 5 literal**
(CI `EXPECTED_DEFAULT=37`; ledger §2a). Two proofs needed maintenance in the
new declaration context, both by decomposition: `lemma_survivor_top_bounds_
trail` goes through the pointwise `lemma_trail_repr_at`, and
`ListArena::splice_raw` — whose full-crate run had started dying in a Z3
worker panic ("expected rlimit-count in smt statistics": the solver ran out
of memory, 3.9 GB, before its 2000 limit) — no longer unfolds the old state's
`cache_ok` and `model_disjoint` in its own context. The `next` quantifier of
`cache_ok` is self-feeding (an instance at `(l, p)` creates `model[l][p+1]`,
which matches it again); with both predicates hidden (`hide` as the first
statements of the body), `lemma_cache_ends_at` supplies the two lists' cached
ends, `lemma_splice_disjoint_arena` and `lemma_splice_cache_ok` re-establish
the predicates for the new state in their own small contexts, and
`lemma_disjoint_entries` gives the one instance the list_seq framing needs.
The function verifies in seconds at limit 300, the value its own comment
always called for (it had been 2000 since A1). A healthy full default verify
of the crate takes ninety seconds; every hour-long run before this fix was
that one function.

**Trail ascending fast path (`2425233`).** `trail_select::dedupe_trail_range`
scans a frame for strictly ascending indices first (one compare per entry,
stops at the first descent); an ascending frame holds no index twice, so
every entry is its own first hitter and copies straight through, with no
set and no hashing — the fast path proves `first_hitter` under the ascending
invariant and reuses `lemma_dedupe_push`. Only a frame with a repeat or a
descent takes the hash-set fold, which now sizes its set inside that branch.
This is the singleton-frame trade-off measured under extended goal 5
(`three_tier_v2/adaptive/singleton_*/dyn_trail`, 1.33x). A Bloom filter was
considered and rejected: at the false-positive rates that would matter the
filter is the size of the set (birthday bound, m ≳ n²), and a sort-based
dedupe needs a stable sort to keep the write order of repeated indices.

**Literal store on SpMap (`60b34a1`).** `LitValStore` is a
`SpMap<L::Key, L, V::Index, TRACK>` (the e-graph now enables the container
crate's `literal-types`): intern, lookup, mark and restore go through the
verified map, and the hand-rolled index with its incremental-versus-rebuild
restore heuristic is gone. Keys are canonical: `LitVal::Key`/`key()` through
a `CanonicalKey` trait — `OrderedFloat<f64>` interns under `CanonicalF64`
(the fold `OrderedFloat` already applies, pinned by the container crate's
compliance tests), `BigRational` under `CanonicalRational` (gcd-reduced,
sign-normalized, so structural equality is value equality), the machine
types, strings and big integers under themselves; `define_litval!`
generates the key enums. The node caches keep their hand-rolled index by
request (`REBUILD_RATIO`/`restore_incrementally` stay for them).

**Token provenance (`6c96c24`).** A version token was a bare frame index: a
token minted by one vector was accepted by any other at the same depth, and
a consumed token came back to life as soon as the next `mark` reused its
frame index. Now `history::GroupToken { history: ContainerId, generation,
depth }` is the one token type (`VecToken` is an alias); `Genealogy { id,
stamps }` is the verified minting manager (`mint`, `is_valid`, `cut_from`),
`History` for synced groups is a `Genealogy` plus the group depth, and every
`Vec` and `AppendOnlyVec` embeds its own `Genealogy`: a standalone container
is a group of one. `mark` mints last and `restore` cuts last; `restore` and
`is_valid_token` check provenance first and refuse a foreign, consumed or
later-minted token without mutating. The cut is inclusive
(`cut_from(t.depth)`): `restore(t)` consumes `t`. Legacy keeps a token at the
fork depth on-branch, so the verified rule is strictly stricter; the policy
matrix and oracle proptests model per-depth generations with the inclusive
cut and assert verified-valid ⟹ production-valid, and `misuse.rs` pins the
abandoned-branch, consumed and foreign refusals (`standalone_vec_refuses_
abandoned_branch_token`). Composite tokens still bundle column tokens (reads
of `frame_idx` became `depth`). Proof shape: the `genealogy` field is absent
from every physical, ghost-trail and snapshot predicate of `Vec`, so
`lemma_genealogy_framing` (the twin of `lemma_full_trail_physical_framing`
plus a `wf_for_snap` half, `lemma_genealogy_snap_framing`) carries `wf` and
the observables across the mint/cut, called with a ghost snapshot of the
physical state; `lemma_hot_frame_strict` and `lemma_ingress_capture_
preserves` were perturbed by the new field and are decomposed
(`lemma_hot_migrating_frame_range`; `lemma_ingress_capture_{snap,cold}`).
The partial-API gate caught `Genealogy::mint` (`requires depth <
u32::MAX`) as a new public partial function on the first battery; it is an
internal primitive and became `pub(crate)`, and the battery was rerun on the
corrected files (no allowlist entry). Design docs 08 and 10 carry the
semantics.

**O(1) stamps (`683dbef`).** The provenance commit's benchmarks showed
every mark/restore-dominated case 1.1–1.7× slower: `GenStamps::bump_from`
rewrote every stamp level from the cut to the deepest depth ever reached
(64 writes per restore on the 64-frame retained trace, up to 128 on the SMT
traces), and `stamp_at` grew the level array on every mark. The table now
hands out stamps from a counter that only grows and keeps a live length:
validity is `depth < len && levels[depth] == g`, a cut is one write
(`len := min(len, d)`, the stale stamps above stay in place and capacity is
kept), a mint at the live length is one write (depths a group drove
structurally are filled with fresh stamps first). Totality by refuse-guards
at the counter and length ceilings; no invariant to thread — the freshness
the token rule needs is a postcondition of `mint_at` (every stamp below the
old counter keeps its validity status). `lemma_bump_invalidates` and the
eager level array are gone; nothing outside `gen_stamps.rs`, the genealogy
and three stamp tests changed. Memory is 8 bytes per depth of the deepest
nesting reached, like every column's frame stack.

**Restore semantics B (`2743e17`).** The user's ruling of 2026-09-17
(design doc 08 §1, §6): `restore(t)` resets to the checkpoint — the state at
the mark, with the mark's frame reopened empty — so the token stays valid
and can be restored to again, every token minted after it is dead (cut at
`t.depth + 1`), and a new `pop_scope` drops the open top frame (the SMT-LIB
`pop`; `try_pop_scope` with `ContainerError::NoOpenFrame`). On the tiered
`Vec` the reset is the pop core followed by a structural frame push
(`reset_frame` = `reset_frame_physical` + cut; the physical half hides `wf`
and carries it through the step contracts, with the accessors
`lemma_store_wf` and `lemma_snapshots_len`); `AppendOnlyVec` resets by
truncation. `History::restore_to` cuts at `t.depth + 1` and gains `pop`;
the member protocol gains `reset_frame`/`pop_frame` and `ForkHistory`
resets its members and gains `pop`. Every composite's `restore` keeps the
checkpoint's frame and every composite has `pop_scope` (the four with a
structural core reuse it; `SpMap` gets a pop core; `BPlusTreeSet` and
`EClasses` derive theirs from their restore proofs with the prefix cut one
frame lower); the dead group-path prototype `EClasses::restore_with_history`
is removed. The e-graph keeps the checkpoint's member tokens on its stacks,
gains `EGraph::pop_scope`, and the interpreter's `(pop)` is `restore(t)`
then `pop_scope()`; node store, caches, registries, routing column and
literal store forward `pop_scope`. Legacy `containers/` restores are pops,
so the paired harnesses assert the checkpoint is still valid after the
verified restore and then pop for parity; the in-crate suites pin the
reusable checkpoint, the cut above it and the refusal after the pop, and
`three_tier_runtime` keeps its tier-mechanics expectations under explicit
pops. The crate verifies at **2676 functions** (pops and accessors added);
the harness rule stays "verified-valid ⟹ production-valid" on the popped
path.

**Deferred-rollover reopen and bench parity (`c23eb12`).** The benchmarks
of `2743e17` against `60b34a1` (220 cases) showed ten regressions, all on
restore-dominated cases (`store/*/eqsat32` and `smt32` 1.40–1.46,
`vec/restore_replay/verified` 1.42, `three_tier_v1/restore/shallow_high_
duplicates/*` 1.15–1.62, `smt_backtracking_128/static_vecp` 1.16), read
from the code rather than bisected. `reset_frame_physical` reopened the
checkpoint's frame with `push_frame`, the configured-rollover push of
`mark`: right after the pop core made the parent stratum writable, the
push sealed it again under the tier policy and migrated it (Trail → Hot
dedupe, Hot → Cold) on every restore. The reopen is now a `Defer` push
(`push_frame_with_options`), a header push that converts no history; the
next `mark` migrates once, as before. Same contract, same proof shape. The
benches also still measured a bare `restore(t)` against the legacy
pop-restore, so a trace with `n` restores ran `n` frames deeper than its
pair; every verified restore in the benches now pops the way the paired
harnesses do (legacy restore = `restore` then `pop_scope`). Gate: lean per-commit gate in the main tree — default verify **2676 verified, 0 errors**, feature suite **279 passed, 10 ignored**, release policy matrix **4**, conformance **31**, consumers **1268 passed, 45 skipped** under cargo-nextest (110 s), canary **2**, partial-API **0/0/0/0**, fmt, whitespace, legacy unchanged, trust **37 + 5**.

**The fused SMT-LIB pop (`073e38a`).** The benchmarks of `c23eb12` fixed
`vec/restore_replay` (1.42 → 1.02) but left the store traces at 1.50–1.55
and put every one-frame restore case at 1.4–2.1: `restore(t)` then
`pop_scope()` reopens the parent stratum twice (the restore's pop core
promotes the survivor and recomputes its capture tags, the deferred push
seals it again and `prepare_mark` clears the tags over it, the pop's core
reopens it once more and recomputes them) — two extra O(stratum) walks per
`(pop)`, on nine columns in the store traces. `restore_and_pop(t)` and the
total `try_restore_and_pop` are the two fused on the one pop core the
legacy restore always used: contents at `t`, depth `t.depth`, `t` and every
later token dead. Each fused body is the pre-B restore of `683dbef` over
the fused column ops, with its proof (`Vec`, `AppendOnlyVec`, `History`,
`ForkHistory`, the seven composites, `HintedArena`); the crate verifies at
**2696 functions** (twenty added, no limit raised). The e-graph gains
`EGraph::restore_and_pop` (member tokens leave the stacks, one history
cut) with the node store, caches, registries, routing column and literal
store forwarding it, and the interpreter's `(pop)` is the one call; the SAT
core's backjump stays the bare `restore`. Every paired bench measures
`restore_and_pop`; two verified-only cases measure the bare semantics-B
restore. `tests/restore_and_pop.rs` pins the equivalence with `restore`
then `pop_scope`, the depth and token fate, and the refusal path. Gate:
lean per-commit gate in the main tree — default verify **2696 verified, 0 errors**, feature suite **283 passed, 10 ignored**, release policy matrix **4**, conformance **31**, consumers **1268 passed, 45 skipped** under cargo-nextest (108 s), canary **2**, partial-API **0/0/0/0**, fmt, whitespace, legacy unchanged, trust **37 + 5**.

**Grouped-history tests (`33b565c`).** The lockstep property the group proofs
state is exercised end to end: `grouped_history_random_sequences_land_in_
lockstep` drives three members of different widths under one `ForkHistory`
with random marks, erased writes and restores (256 cases; every member must
equal its typed oracle snapshot from that mark, the group must sit at the
token's depth, the consumed token and every later token must be refused
forever), `consumed_and_foreign_tokens_are_refused` pins the deterministic
cases, and `egraph/tests/group_history_props.rs` runs a replay oracle over
`EGraph31<NiraLitVal, true, false>` (random insertions, merges, rebuilds,
marks and restores; after each restore the class/node/literal/sort counts
and the partition must equal both the snapshot taken at the mark and a fresh
replay of the history prefix; `EGraph::mark` rebuilds first, so the oracle
records a rebuild at every mark).

Gate evidence per commit (worktree holding exactly that commit's files):
`71f8358` default **2644 verified, 0 errors**, literal **2644/0**; `2425233`
**2646/0**, **2646/0**; `60b34a1` **2646/0**, **2646/0**; `6c96c24`
**2655/0**, **2655/0**; `33b565c` **2655/0**, **2655/0**; `683dbef`
**2651/0**, **2651/0** (the bump lemma and loop gone); `2743e17`
**2676/0**, **2676/0** (pops and accessors); `c23eb12` **2676/0** (lean
per-commit gate, goal doc outcome 7: default verify in the main tree, the four test suites, consumers under nextest, the source checks); `073e38a` **2696/0** (lean gate: default verify in the main tree, the four test suites, consumers under nextest, the source checks). Full battery on the final source `073e38a` (2026-09-18 04:30): default **2696 verified, 0 errors**, literal **2696/0**, composition **80/0**, `au-verus` **29/0**, feature suite **283 passed, 10 ignored**, release policy matrix **4**, conformance **31**, consumers **1268 passed, 45 ignored**, canary **2**, partial-API **0/0/0/0**, fmt, whitespace, legacy unchanged, trust **37 + 5**. Every commit:
conditional composition **80 verified**, `au-verus` **29 verified**, feature
suite **277 passed, 10 ignored**, release differential policy matrix with
`PROPTEST_CASES=1024` **4 passed**, B+ tree, oracle and reference-e-graph
property tests **31 passed**, e-graph/SAT consumers **1267 passed, 45
ignored** (`33b565c`: **279** feature tests and **1268** consumer tests, the new ones), canary **2 passed**, partial-API audit **0/0/0/0**,
formatting, whitespace and the unchanged-legacy check passed, trust **37
default + 5 literal**. Benchmarks against each commit's predecessor:
`doc/tasks/final-performance-report.md`, "Wave after extended goal 5".

## The external-manager wave (2026-09-18): one manager, provided from outside

Ten commits put every container and the e-graph on one externally provided
history manager, `group::ForkHistory<M: Member>` (design doc 10, "Shipped: the
typed external manager"; goal doc outcome 1).

| Commit | What it adds | Feature suite |
| --- | --- | --- |
| `5fc8b29` | `group.rs`: the `Member` protocol, `ForkHistory<M>`, `Pair<A, B>`, `Vec`/`AppendOnlyVec` impls, `tests/typed_group.rs` | 289 |
| `30f0e52` | every composite a member: sparse set, ring, list arena, union-find, map, B+ tree, e-classes (token-free frame cores) | 296 |
| `006357c` | `History::*_member` over a borrowed member, and the e-graph's nine members on one `History` via `EGraphMembers` | 296 |
| `19c2ca3` | harnesses, benches and all 22 in-crate test files on groups of one; `mint_pushed`, `Deref`, `try_push_frame_with/_adaptive`; `HintedArena` a member | 296 |
| `7976be0` | delete the containers' and e-graph wrappers' token surface | 291 |
| `67900d4` | this documentation | — |

History note: the wave was built as twelve commits and rebuilt as these six
at the user's request, each on a tree one of the twelve already had (the
twelve stay on the local branch `d21-exec-wave-full`; the two heads have
identical trees). The gate evidence below is per built commit, so it maps onto
the six by tree: `3538cb0` → `5fc8b29`, `9c29a7e`/`0222bfd`/`534cced`/
`e87df23`/`4cb12a3` → `30f0e52`, `10ed6d9`/`e26623e` → `006357c`,
`ae16efe`/`0e94c16` → `19c2ca3`, `778cdcf` → `7976be0`.

Every built commit passed the lean per-commit gate (goal doc outcome 7):
verification with 0 errors, the feature suite (289 → 296 as the members
landed), release policy matrix **4**, conformance **31**, consumers **1268
passed, 45 skipped** under cargo-nextest, canary **2**, partial-API
**0/0/0/0**, fmt, whitespace, unchanged legacy, trust **37 + 5** (**34 + 5**
after the deletion). Logs:
`scratchpad/lean_{a1,a2a,a2b,a3a,a3b,a3c,b0,b1,c,d1,d2a}.log`. The member wave
verified at **2806 verified, 0 errors** and the deletion at **2726 verified, 0
errors**. One flake seen once (`egraph/tests/par_fanout.rs`, which asserts two
rayon workers under load) passed on rerun.

Benchmarks, the e-graph commit against `073e38a` (its own measurement): store
traces **0.97–1.00×**, `empty20k` **0.79–0.80×** (the per-column provenance
constant is gone), saturation at parity.

**The deletion (eleventh commit).** With the callers gone, the old surface
went: seven composites (`SparseSet`, `CircularList`, `ListArena`, `UnionFind`,
`BPlusTreeSet`, `EClasses`, `HintedArena`) lost `mark`/`restore`/`try_*`/
`pop_scope`/`is_valid_token`, their token types and the token-only predicates;
`sync_group` (the dyn group) and `history.rs`'s `Solo`/`SyncPair` wrappers were
deleted; the e-graph's wrapper token layer went too (`CacheToken`,
`PoolCacheToken`, `NodeStoreToken`, `RoutingToken`, `LitValStoreToken`, the
four registry tokens), with the director pool moved to the frame protocol and
the per-column restore profiling (`SEMPER_RESTORE_PROF`, `NODE_PROF_PARTS`)
rewired into `NodeStore::reset_frame` so the diagnostic still reports. Four
harnesses moved to groups of one on the way: the e-classes conformance trace,
the list-arena and e-graph-reference differentials, and the e-classes and
use-list proptests. About 5,500 lines deleted; verification **2726 verified, 0
errors** (80 proof functions fewer). Two surfaces stay, on purpose: `Vec` and
`AppendOnlyVec` (the columns a group of one wraps; the `Vec` half also needs
`lemma_genealogy_framing` and the `restore_frame`/`reset_frame` cuts reworked),
and `SpMap`'s `MapToken`, because the anti-unification search layer
(`egraph/src/au`, eight token structs of its own) still checkpoints maps and
columns directly. That layer is the next consumer to put on a group.

Gate for the deletion commit (lean per-commit gate, log
`scratchpad/lean_d2a.log`): literal verify **2726 verified, 0 errors**,
feature suite **291 passed, 10 ignored** (the dyn group's six tests and the
frankentoken case go, the two new typed-group tests arrive), release policy
matrix **4**, conformance **31**, consumers **1268 passed, 45 skipped**,
canary **2**, partial-API **0/0/0/0**, fmt, whitespace, unchanged legacy,
trust **34 + 5** (three `external_body` items fewer).

**The last two consumers and the last surfaces (2026-09-18, two further
commits).** `92dab5b` puts the anti-unification search on one history:
`SearchSession` owns a `History` and drives its five layers through
`History::mark_member`/`restore_member` over one borrowed view (`AuMembers`),
so a checkpoint is one stamp instead of 62 container tokens in a nest of eleven
token structs; the action cache's action lists move from a hand-truncated plain
`Vec` into an `AppendOnlyVec` (append-only, and that container needs no `Copy`
bound); the exact memo keeps its derived index by hand on per-frame lengths;
and the four per-layer provenance tests become one at the session level. Gate
(`scratchpad/lean_au.log`): literal verify **2726/0**, feature suite **291**,
policy **4**, conformance **31**, consumers **1265 passed, 45 skipped**, canary
**2**, partial-API **0/0/0/0**, trust **34 + 5**.

`34b5a92` then deletes the last token surfaces — `SpMap`'s, `Vec`'s and
`AppendOnlyVec`'s, including the embedded `Genealogy`, the three framing lemmas
it needed, the cuts inside `restore_frame`/`reset_frame` and the three
dead-code compaction marks. `sequence_witness_checked`, the production
instantiation of the sequence theorem, restates the same run on the structural
protocol. Callers migrated: the canary's union-find shape is a
`ForkHistory<Pair<..>>`, the environment-lever, trail-compression and
trail-semi-persistence harnesses and the retained benches use groups of one on
the verified side (the frozen legacy side keeps its tokens), and `vec.rs`'s own
acceptance suites do the same; the forgery tests now forge a `GroupToken`
against a group. Gate (`scratchpad/lean_cols.log`): literal verify **2688
verified, 0 errors** (about 120 proof functions fewer, since the field's
removal removed obligations), feature suite **290**, policy **4**, conformance
**31**, consumers **1265**, canary **2**, partial-API **0/0/0/0**, fmt,
whitespace, unchanged legacy, trust **34 + 5**.

Method note: the first attempt at this deletion was scripted with brace
counting and mis-cut function bodies in seven verified files (an
`ensures ... ({ ... })` clause balances early). It was reverted and redone with
a cutter that finds each item's end by the next sibling item's start, which
needs no brace matching; that pass compiled with four stale imports as the only
fallout.

## The trust surface: 34 items to 12 (2026-09-18)

The `external_body` ledger was audited item by item and cut from 34 to 12,
verification rising from 2688 to 2701 functions with 0 errors because items that
stopped being trusted became items that are proved. Design doc 02 carries the
full list of the twelve and the reason each is irreducible; the CI pin moved with
it in the same commit, as that gate insists.

Twelve were **stratified out of the perimeter** — neither proved nor trusted, the
treatment the byte reporters already had: the ten compression-statistics and
shadow-logging functions, `list::white_box_head`, and `parallel::par_sum_canary`.
None of them has a verified caller. The statistics module keeps its verified half
(`sat_add`, `sat_mul`, `FrameStats`, the calibration types) inside the `verus!`
block, because byte-size code across the crate reads it.

Ten were **proved**:

| Item | How |
|---|---|
| `bplus_layout::{arr_get, slice_get, arr_set}` | vstd's specified array and slice accessors replace `get_unchecked`; the `unsafe` goes |
| `bplus_layout::sel_usize` | an ordinary branch |
| `bplus_layout::arr_shift_up` | a verified descending loop where a trusted `memmove` was |
| `ContainerId` (struct) and `ContainerId::eq` | the field became `pub(crate)`, so the id is transparent in-crate and opaque to consumers, and equality is provable |
| `sparse_set::values_equal` | vstd's external trait specification for `PartialEq`; `obeys_eq_spec` is never established here, so the result stays unconstrained — which is what the scan wants |
| `guard::check_precondition` | diverges through `refuse` instead of panicking itself |
| `diff_compress::choose_mode` | verified end to end; its statistics pass is two linear hash-set passes (vstd supplies the `usize` key model) under a deliberately trivial contract |

Two honest caveats. The layout primitives moved trust rather than eliminating it:
this crate stops trusting its own unchecked reads and relies on vstd's
specification, which is itself `external_body` in vstd. And the bounds checks came
back, at a measured price recorded in the performance report — `from_sorted_only`
1.11–1.12 against the previous commit, the scan cases 1.06–1.10, every insertion,
split and cursor case at parity, and all of them still ahead of the unverified
implementation in the same binary. The one trusted hint that would have restored
the margin was declined in favour of the smaller ledger.

Known pre-existing flake, unrelated: `egraph/tests/au_exact_anytime.rs`
(`exact_deadline_returns_anytime_incumbent`) asserts a 5 ms deadline is hit;
in `--release` on this machine the exact solve finishes first (fails at
`4453abc` too); the gate runs the consumer suites in debug, where it passes.

## A note on the commit hashes in this document

The branch was consolidated on 2026-09-18: the 101 commits of the ghost-trail
and restore proof campaign (12 to 14 September), whose titles were `wip`,
`proof` and `doc` notes and two of whose states did not compile, became eight
milestone commits, each landing on a tree the project actually passed through.
The twenty scratch verification dumps that campaign left at the repository root
are gone from every tree, and `/*.txt` is ignored so they cannot come back. The
hashes below name the consolidated history; the original per-lemma commits, with
their own hashes, remain on the archival branch `d21-exec`.
