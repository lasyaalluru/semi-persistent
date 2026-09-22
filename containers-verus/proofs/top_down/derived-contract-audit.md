# Derived public-contract audit (initial findings)

This read-only audit accompanies the concrete Vec interpretation bridge. It
does not discharge these APIs or replace the original derived/parallel scope.
The observations below are from current source, not inferred from passing tests.

| Path | Current contract evidence | Remaining obligation |
|---|---|---|
| `ListArena::restore` in `src/list.rs` | Exports restored heads, nodes and abstract model; all three archive prefixes | Retain this theorem when connecting the all-tier Vec proof |
| `ListArena::try_restore` | Exports well-formedness; on error preserves model and identifies InvalidToken | Add success contents and archive/depth effects from the checked inner restore; retain component-mark agreement checks |
| `EClasses::restore` | Conditional restored roots and size under full validity; well-formedness and minimum width | Review all component contents and retained archives, not only roots |
| `EClasses::try_restore` | Exports well-formedness; error preserves roots and identifies InvalidToken | Export successful restore contents and retained-history effects; strengthen failure framing to relevant component state |
| `SpMap::restore` / `try_restore` | Exports restored log contents; well-formedness ties index to log; failed request preserves log/index | Review and export remaining depth/archive-prefix obligations |
| `AppendOnlyVec::try_restore` | Success contents, depth, archive prefix; failure contents/depth/archive unchanged | Candidate for composition reuse, subject to full underlying-path audit |
| `SyncMember` / sequential `SyncGroup::restore` | Member invariant and depth model; successful group restore exports depth and member count | Add a member content/archive interpretation sufficient for the public persistence theorem |
| `SyncGroup::restore_parallel` and parallel dispatch | Residual external bodies identified by source audit | Preserve parallel execution while proving the same content/prefix effect and documenting any genuine library boundary; depth-only checks are insufficient |
| `SparseSet::restore` | Restores dense/sparse/index contents and all three snapshot prefixes; requires a well-formed selected snapshot | Reuse these effects; audit the marking/archive theorem that supplies the selected-snapshot premise and shared-history variants |
| `CircularList::try_restore` | Success restores entries and abstract ring partition plus both archive prefixes; failure preserves model and next links | Reuse success effects; export complete relevant failure framing and connect depth through archive agreement |
| `UnionFind::try_restore` | Success restores roots and roots archive prefix; failure preserves roots; requires same-mark component agreement at runtime | Preserve that guard; review/export parent, rank, distance and proof-column contents/prefixes and failure framing |
| `BPlusTreeSet::restore` in `src/bplus.rs` | Exports restored tree, arena and key model; runtime truncates header/tree archives and rejects invalid tokens before mutation | Export retained archive/depth effects; preserve internally archived header recovery and panic behavior |

`DenseSpanMap` explicitly has no mark/restore API; its role in persistence is a
consumer/rebuild obligation. Layered span structures and all listed containers
still require a complete method-by-method audit, including mutation and marking.
This table is an initial set of confirmed contract observations, not a completion
checklist.

Do not weaken component token checks or accepted error behavior to strengthen
postconditions. Preserve verified work, and remove a superseded proof only after
its replacement verifies. All required runtime, differential and consumer gates
remain required for concrete changes.


## Update 2026-09-16 — derived contracts forwarded

| Path | Now exported |
|---|---|
| `ListArena::try_restore` | Success: heads/nodes/model views at the mark and all three archive prefixes (same frame for both components); failure: state unchanged |
| `EClasses::restore` / `try_restore` | Success (full validity, which the wrapper's check is): roots view and size at the mark, depth, roots archive prefix; failure: state unchanged; `min_width` preserved |
| `SpMap::restore` / `try_restore` | Success: log contents at the mark, depth and log archive prefix; failure: state unchanged |
| `CircularList::try_restore` | Failure: state unchanged (success effects were already complete) |
| `UnionFind::try_restore` | Success: roots/parent/rank views at the mark, roots and parent archive prefixes, same-mark agreement; failure: state unchanged |
| `BPlusTreeSet::restore` | Retained arena and ghost-tree archive prefixes at the token's frame |
| `SyncMember` / `ForkHistory::mark`, `restore` | Trait gains an object-safe `model`/`archive` pair with an archive-depth obligation; the `Vec` member proves them from `seal_frame`/`restore_frame`. Group mark exports unchanged member models and one archived model per member; group restore exports every member's model at the token's depth and the archive prefix; rejected requests leave the group unchanged |
| `ForkHistory::mark_parallel`, `restore_parallel` | Same contracts as the sequential paths. The bodies remain the documented rayon fan-out boundary (trust ledger 3.6d): per-member effects come from the members' checked contracts and disjoint `&mut` borrows; the trusted step is that rayon applies the closure to every member exactly once |

| `EClasses::restore` / `try_restore` (component contents) | Success: every component column at the token's frame and every retained archive prefix — entries (`CircularList` model and node views, both archives), reprs (`SparseSet` dense/sparse/indices views and archives), uses (`ListArena` model view and archive), minimum pool (`Vec` view and archive) — through `pub open(crate)` accessors that project the components' own views; nothing is stored twice |

Nothing remains from the initial table: `SparseSet` and `AppendOnlyVec` were
already complete, and the `EClasses` component contents are now exported.
