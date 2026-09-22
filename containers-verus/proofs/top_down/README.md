# Conditional top-down proof target

This target implements the workflow in
[three-tier-top-down-proof-engineering.md](../../doc/tasks/three-tier-top-down-proof-engineering.md).
The conditional orchestration and witness are **not imported by the production
crate**. The shared `model.rs` is imported so concrete adapters use the same
mathematical definitions. Its `Runtime`, `Mutations`, and
`Policies` traits have only a mathematical consistency implementation in
`witness.rs`. Their methods are explicit conditional premises for production,
not trusted production wrappers. No `assume`, `admit`, or
`external_body` is used here.

## Current status

The draft composition verifies with the project's pinned Verus:

```sh
verus --crate-type lib containers-verus/proofs/top_down/composition.rs
```

Result on 2026-09-15: **80 verified, 0 errors**, Verus
`0.2026.08.02.b677dd5`, Rust 1.97.1. The target needs only the bundled vstd and
has no runtime history fields. Production now verifies the shared mathematical
model as well as its concrete adapters; those counts are reported separately.

The first conditional-composition milestone is verified. The
[interface review and proof classification](proof-classification.md) records
its requirement audit, remaining concrete obligations, and reuse/adapt decisions.
No production implementation is discharged merely by this result. The original
all-tier and derived/parallel-container objective remains active.

The review added arbitrary legal rollover/public-operation sequence induction,
local encoding and exact pool-append relations, typed rejected-request results,
and a separation between mutation capability and Default-dependent restoration.
The mathematical witnesses cover zigzag lengths, all survivor tiers, both store
protocols, empty frames, encoded duplicates, regrowth and alternate policy order.

Production code and existing proofs were preserved at signed local commit
`07b6df8`. Its complete gates passed: 2310 Verus obligations in both configurations,
277 feature tests, four 1024-case policy-matrix tests, and 1267 consumer tests.
Nothing was pushed. This target's result is separate from that runtime evidence.

## Checked layers

| File | Checked result |
|---|---|
| `model.rs` | Finite partial-map frame meaning; captured-or-inherited invariant; constructor/set/push/pop/mark/restore closure; arbitrary legal action-sequence closure; mutation after restore; pop/regrowth; frame step; range composition; reconstruction with arbitrary resized filler and saved-length zigzags |
| `composition.rs` | Conditional resize/preparation, one batch per pair tier, direct Cold-frame suffix, physical/canonical retirement, survivor-tier dispatch, capture finalization, reclamation, valid public restore, unchanged state on invalid restore |
| `mutation.rs` | Conditional capture/raw-write composition, push/tag repair, capture/pop composition with returned value, mark preparation/opening, constructor, restore–write–restore |
| `policy.rs` | Plans name exact oldest eligible frame meanings; active ingress excluded; arbitrary legal rollover induction, interleaved policy sequences, staged Trail then Hot composition; mark/token coordinate composition; unchanged state on rejected mark |
| `encoding.rs` | Explicit local map/validity contracts, duplicate append semantics, exact pooled append/publication, logical prefix relocation, empty/nonempty encoded witnesses |
| `public_sequence.rs` | Complete conditional public-operation dispatcher and arbitrary legal interleaving theorem |
| `witness.rs` | Checked mathematical implementation of every provisional method and explicit nontrivial history/promotion/regrowth/policy witnesses; not a production adapter |

`Model` and `Frame` are mathematical proof values. They add no persistent ghost
fields and perform no runtime lookup for Trail's first capture. A concrete
adapter must derive their maps from physical history. Equality of frames includes
both map membership and saved values, as well as each independent saved length.

`Stable` combines physical boundaries, snapshot semantics, writable ingress,
active saved length and exact live-tag/map membership. During replay it is
intentionally absent: frozen source history and physical/store validity suffice.
The proof never assumes monotone saved lengths.

## Provisional contract inventory

Every row below remains conditional for production; no concrete `Runtime` adapter
connects these candidates to this target yet. The reviewed classification is in
[proof-classification.md](proof-classification.md).

| Interface | Concrete candidates | Required transition / next consumer |
|---|---|---|
| View and named boundaries | `Vec::wf`, named representation predicates, `frame_saved_value`, `frame_partition_ok`, canonical fields | Derived per-frame map, saved length, exact physical/canonical projections; supplies all primitive premises |
| `token_bounds` | `is_restorable_spec`, `is_valid_token` | Full public validity implies frame bounds; supplies resize and reconstruction |
| `resize` | `DiffStore::resize_default`, `reconstruct_target_checked` | Fixed target length, shared-prefix equality, source unchanged, flags inherited only from pre-state |
| `prepare` | `runtime_begin_restore` and store capture protocols | Non-fused flags clear; fused flags retained as subset until first ingress batch |
| `pair_batch` | `replay_pair_suffix_checked` / `replay_all_tiers_checked` | Exact `apply_range`, fixed length, physical source equality, flags clear; feeds next tier |
| `cold_frame` | `replay_cold_frame_checked`, store run-replay primitives | Exact single-map application directly to live storage, clear flags preserved |
| `retire` | `truncate_restored_history_checked` | Exact physical/canonical prefixes, exact retained frame meanings, tier counts and target contents; feeds reopening |
| `reopen_hot` | `promote_hot_survivor_checked` | Only newest Hot frame moves to Trail; same map/domain/length; older storage unchanged |
| `reopen_cold` | remaining `runtime_promote_survivor` Cold branches | Only newest Cold frame decoded to selected writable tier; same map/domain/length; older storage unchanged |
| `finish_capture` | `finish_survivor_checked` | Derive active length and tags from writable map, preserving live/history/protocol |
| `finish_empty` | zero-depth restore finish | Empty history, zero active length, no flags, stable boundary |
| `reclaim` | `reclaim_cold_checked` | Preserve model, flags, protocol and canonical history under capacity changes |
| `construct` | constructors and store constructors | Empty history with specified live contents and selected capture discipline |
| `capture_cell` | `runtime_capture`, Trail append, Hot capture | Physical capture realizes `capture_first`; older maps and snapshots unchanged; live unchanged |
| `raw_write` | `DiffStore::set` family | Exact live update after necessary capture; preserve history and tags |
| `raw_pop` | `DiffStore::pop` family | Remove last value/tag after necessary capture; preserve history |
| `raw_push` | `DiffStore::push` family | Append value and clear tag; maps unchanged, including regrowth |
| `finish_regrowth` | capture-bit restoration in push helpers | Only new cell's tag may need repair; prior coverage supplies saved value |
| `prepare_mark` | store `prepare_mark` / `runtime_push_frame` | Clear tags with valid sparse input; preserve contents/history and mark guards |
| `open_mark` | mark frame opening/sealing paths | Append empty frame and live snapshot before rollover; seal preceding writable frame |
| `select_plan` | configured/forced/adaptive policy selection | Exact source frame meanings, eligible count, source tier; supplies migration |
| `migrate` | Trail/Hot migration and adaptive-plan execution | Exact logical history, physical frame-count effects, stable physical/capture boundary; local transforms and pool rebasing still need interface review |
| `mark_guard` / `mark_error` | mark guards and early error branches | Exact failure reason with existing Untracked/DepthLimit/CapacityExhausted ordering; state unchanged on rejection |
| `make_token` | `mark_with_options`, `mark` | Existing returned token coordinate; public validity remains a separate predicate |

`canonical_ok` must retain the existing canonical-history obligations, split
appropriately between structural/map correspondence and snapshot semantics.
`retired_prefix` and `older_storage_unchanged` must be instantiated as exact
physical relations. Giving these predicates vacuous definitions in a production
adapter would not meet the contract review requirements.

## Dependency graph

```mermaid
flowchart TD
  F[Shared frame meaning] --> L[Logical operation closure]
  F --> R[Frame step and batched range composition]
  P[Primitive physical contracts] --> M[Conditional mutations and marking]
  L --> M
  C[Exact eligible migration plans] --> Y[Policy composition]
  M --> K[Public mark contract]
  Y --> K
  R --> B[Trail batch / Hot batch / direct Cold suffix]
  P --> B
  B --> T[Exact history retirement]
  T --> O[Survivor reopening by tier]
  O --> G[Capture rebuild and reclamation]
  G --> U[Public restore with token guard]
  U --> S[Restore / mutation / older restore]
  M --> S
```

The completed all-tier and derived/parallel-container objective remains
unchanged. A conditional theorem is the interface-design milestone; concrete
discharge and public integration are still required.
