# Nightshift goal: restore semi-persistence proofs for every container

**Starting checkpoint:** branch `d21-exec`, H0 commit `df10134`, H1 working tree
with the pool-native general invariant and full Vec-module verification green
(`117 verified, 0 errors`).

## Overview

Complete the formal semi-persistence campaign without changing the established
public ghost snapshot-stack abstraction. First close the real Vec Hot-only
unique-capture `RolloverPolicy::Defer` path (H2-H5). Then reverify every derived
container against the unchanged Vec contracts. Finally discharge the remaining
Trail, Cold, conversion, mixed-tier, and adaptive policy refinements needed for
the same public Vec theorem to hold for every supported three-tier policy.

The central abstraction boundary MUST remain:

```text
mark:
    view/model unchanged
    depth_after == depth_before + 1
    snapshots_after == snapshots_before.push(old_view_or_model)

restore(k):
    view/model_after == snapshots_before[k]
    depth_after == k
    snapshots_after == snapshots_before[..k]
    surviving older frames remain valid
```

Higher-level proofs MUST consume this contract rather than Hot/Trail/Cold
representation details. The geometric model in
`containers-verus/doc/design/17-three-tier-frame-grid.md` is the required lemma-
discovery aid: horizontal moves correspond to live-length changes, vertical
moves to frame locality/depth, and column encoding changes to tier refinement.
Existing SparseSet, UnionFind, CircularList, ListArena, BPlusTreeSet, and
EClasses archive/refinement proofs SHOULD reverify unchanged; a downstream edit is allowed only when verification demonstrates a real
abstraction leak or an independently incorrect collection invariant.

## Fixed constraints

1. The agent MUST preserve the exact public ghost snapshot-stack theorem because
   it is the modular boundary used by every derived collection.
2. The agent MUST NOT assume frame saved lengths are monotone because every
   Trail, Hot, and Cold frame stores its own `saved_len`; restoration may grow or
   shrink relative to any adjacent frame.
3. Every per-frame reconstruction invariant MUST use pointwise coverage:
   a saved cell is either physically represented by that frame or is in bounds
   and unchanged in the layer above.
4. The agent MUST NOT use inert compatibility `diff_log` as physical authority
   because real history is owned by `trail_value_pool`, `hot_value_pool`, and
   Cold runs.
5. The agent MUST NOT add `admit()`, `assume()`, `assume_specification`, or a
   contract-bearing `external_body` to hide a proof obligation.
6. The agent MUST NOT weaken public contracts, remove supported runtime
   behavior, or change `containers/`, which remains the differential oracle.
7. Runtime algorithms and the static VecP/VecI hot path MUST remain unchanged
   unless a failing runtime test proves a source correction is necessary.
8. Every milestone MUST be independently verified and committed before the next
   representation or collection family begins because Verus proof state is
   solver-sensitive.

## Milestones

### N0 — Checkpoint the H1 pool-native invariant

MUST finish and commit the current H1 working tree only after:

- `maybe_shrink` verifies;
- `cargo verus verify -- --verify-only-module vec` is green;
- `cold_reconstructs` explicitly handles non-monotone saved lengths;
- untracked capture-bit obligations match the `DiffStore` contract;
- trust counts, workflow gates, architecture notes, and progress records match
  source;
- no generated review artifact is committed.

### N1 — Prove the real Vec Hot/Defer theorem (H2-H5)

MUST adapt the checked H0 cores into the actual runtime/public path:

1. prove marked and unmarked `push`, `pop`, and `set_index` preservation;
2. prove first-capture-wins, including pop below a frame's saved length and
   regrowth above/below non-monotone adjacent saved lengths;
3. prove `Defer` marks for `ShrinkPolicy::Never` and thresholded shrink;
4. prove zero and every nonzero Hot restore target, including exact target
   length, surviving prefix validity, and rebuilt top capture state;
5. connect general `wf` to the checked cores and remove the in-scope trusted
   dispatch/public wrappers;
6. expose the unchanged public snapshot-stack theorem without requiring callers
   to mention `hot_defer_wf`.

A checked helper behind an `external_body` dispatcher is not completion. The
real selected execution path MUST be machine checked.

### N2 — Reverify all derived container theorems

MUST run targeted and full verification for:

- SparseSet: three-column lockstep restoration, permutation/inverse invariant,
  and common archived frame;
- CircularList: vector restoration plus ring partition/cyclicity archive;
- ListArena: heads/nodes lockstep plus list-model archive;
- UnionFind: parent/rank and optional proof columns plus roots/dist partition
  archive;
- BPlusTreeSet: arena restoration plus root/header/tree archive;
- EClasses: all nested containers, common-frame protection, and W1-W7 aggregate
  archive;
- SpMap/AppendOnlyVec: independent prefix/truncation theorem and rebuilt index.

Existing collection proofs SHOULD require no semantic redesign because the leaf
contract is unchanged. If a module fails, the agent MUST first determine
whether it unfolded Vec internals, relied on a trusted Vec wrapper, or contains
an independent collection proof gap. Fix only the demonstrated cause.

### N3 — Prove Trail representation and chronological replay

MUST prove that each Trail frame, including empty frames and duplicate writes,
refines the same canonical frame abstraction. Replay MUST process entries in
reverse chronological order and restore arbitrary non-monotone saved lengths.
The open Trail capture state MUST be rebuilt exactly.

### N4 — Prove Trail-to-Hot conversion

MUST prove `dedupe_first` preserves frame identity, saved length, snapshot
reconstruction, and first old value per touched cell. Empty frame headers MUST
survive conversion. No conversion may change the ghost snapshot stack.

### N5 — Prove Hot-to-Cold conversion and Cold replay

MUST prove that a transient in-place sort of the selected unique Hot frame is a
permutation preserving `stratum_unique` and the complete frame abstraction;
sortedness MUST remain local to this translation and MUST NOT become a
persistent Hot invariant. Run formation over that order must produce sorted
disjoint runs that decode to the same Hot frame abstraction, including singleton
runs and cells beyond a shorter layer above. Direct Cold slice replay MUST
restore the frame snapshot at its own saved length.

### N6 — Prove mixed-tier restore and every policy

MUST prove survivor promotion and restoration across Cold|Hot|Trail partitions
for `Defer`, `ApplyConfigured`, `ForceClosed`, and implemented adaptive plans.
Policy decisions may change only physical ownership; they MUST preserve the
public ghost snapshot stack and collection-observable result. Capacity-only
standard-library facts MAY remain in the documented trust boundary when their
contracts expose no semantic postcondition beyond sequence preservation.

### N7 — Final package and consumer closure

MUST rerun the full containers-verus package, feature combinations, runtime
regressions, differential policy matrix, and downstream consumer suites. All
collection semi-persistence theorems MUST be machine checked against the real
Vec path. Trust documentation and CI count gates MUST match the final source.

## Validation protocol

For every Vec function-scoped query:

```bash
cd containers-verus
touch src/vec.rs
cargo verus verify -- --verify-only-module vec --verify-function FUNCTION
```

At milestone boundaries:

```bash
cargo fmt --all -- --check
cargo verus verify -p semi-persistent-containers-verus
cargo test -p semi-persistent-containers-verus --test three_tier_runtime
cargo test -p semi-persistent-containers-verus --features "compat-all,literal-types"
PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test three_tier_policy_matrix
```

The agent MUST record exact commands and verified counts in
`three-tier-proof-progress.md`. A lower verified count caused by a new trusted
body is failure, not progress.

## Commit policy

Commit specific files after each independently green milestone:

1. H1 general invariant checkpoint;
2. Hot mutators;
3. Hot marks and restore/public theorem;
4. downstream collection re-verification corrections, if any;
5. Trail replay and Trail-to-Hot refinement;
6. Hot-to-Cold and mixed-tier restore;
7. all-policy/downstream closure and trust ledger.

The agent MUST NOT amend after a hook failure. It MUST fix the failure, restage
specific files, and create a new commit.

## Failure handling

When blocked, record the exact first failing command, function, source location,
and smallest unreduced obligation. The agent SHOULD isolate nested quantified
invariants behind pointwise extractor/transfer lemmas before raising resource
limits. It MUST repair a missing semantic premise rather than classify it as a
trigger issue. It MUST NOT switch milestones, weaken the theorem, or add trust
to obtain a green count.

## Completion condition

This nightshift is complete only when:

- the real Vec public path proves the unchanged snapshot-stack theorem for every
  supported three-tier policy;
- arbitrary per-frame saved-length growth and shrinkage are covered;
- all derived collection persistence modules verify using that theorem;
- no new proof holes or hidden trusted wrappers remain on those paths;
- full Verus, feature, runtime, differential, and consumer gates are green;
- milestone commits and proof/trust records match the verified source.

## Executable goal string

```text
Execute containers-verus/doc/tasks/nightshift-semi-persistence-all-containers-goal.md from N0 through N7 in order. Preserve the exact public ghost snapshot-stack theorem and non-monotone per-frame saved_len semantics; never use inert diff_log as physical authority or add admit/assume/contract-bearing external_body. Commit every independently green milestone. Finish the real Vec theorem first, then reverify SparseSet, CircularList, ListArena, UnionFind, BPlusTreeSet, EClasses, and SpMap/AppendOnlyVec, then prove Trail/Cold/conversion/mixed-tier/adaptive policy refinements until the main semi-persistence theorems are green for all containers.
```
