# Final verification report — `containers-verus` on `d21-exec`

Evidence package required by
[semi-persistence-completion-goal.md](semi-persistence-completion-goal.md)
("Evidence required to close the step"): per-container contract/verification
matrix, trust inventory, gate report, performance comparison (in
[final-performance-report.md](final-performance-report.md)), and the signed
local commits. Nothing on this branch has been pushed; `containers/` (the
legacy oracle) is unchanged since `d191c4a` (`git diff --quiet d191c4a --
containers`).

## 1. Commits (signed, local)

| Commit | Content |
|---|---|
| `e28ac37` | Trail migration preservation groundwork |
| `bbb9548` | Trail → Hot: checked hash-set first-capture dedupe (`trail_select::dedupe_trail_range`, keyed by the generic index `I` through `IndexHasher`), plan buffers removed |
| `990eb08` | Hot → Cold: checked migration over the in-place std slice sort (`std_sort::sort_pairs_by_index`, the one trusted std contract) |
| `a831cc1` | Rollover dispatch: configured/forced rollover, mark fallback, tier policy and adaptive passes checked; `Ratio` moved inside `verus!` |
| `328c512` | Derived restore contracts (ListArena, EClasses roots, SpMap, CircularList, UnionFind, BPlusTreeSet) and group member models/archives (`SyncMember`, `ForkHistory`) |
| `9df28cb` | `pending_restore_indices` checked with an exact contract; `sequence_witness_checked` (production instantiation of the sequence theorem); interface inventory |
| `09f00b0` | EClasses component contents (entries, reprs, uses, pool) through `restore`/`try_restore`; benchmark protocol frozen |
| `2f99644` | `try_mark_adaptive` marker removed (trust 50 + 5); benchmark-attributed constant-factor fixes (pre-sized dedupe buffers, single-bound byte fold); ledgers, CI trust constant, this report and the performance investigation |
| `f304bc7` | B+ tree above legacy speed (cursor leaf cache, single validation, fused leaf fill, incremental `last_leaf`), 10M/100M bench sweep, find-sweep bench loop fix |
| `45fc132` | final two-run benchmark results appended to the performance report; goal extended with the caching, store-policy and `VecD` work (handoff "Next actions") |
| `987a964` | Extended goal 1(a): the Trail-to-Hot dedupe set cached on the vector (`trail_seen`), five edge-of-budget proofs decomposed, per-mark small-frame rollover benchmark (1.09×) |
| `54563da` | Extended goal 1(b): `SpMap::restore` unwinds the index over the discarded suffix through a previous-occurrence column (`prev`), rebuild kept as the fallback; restore-after-small-frame 970×/206× |
| `f9ffab0` | Extended goal 2: store policy for every composite (`store_policy::{TaggedFamily, PlainFamily, HotFirst, TrailFirst}`, `P = HotFirst` on `UnionFind`, `SparseSet`, `CircularList`, `ListArena`, `BPlusTreeSet`, `EClasses`), `DiffStore::lemma_wf_data_len` |
| `08dc0d5` | Extended goal 1(d): `HintedArena::note_hint` pushes into its bucket through two `core::mem::swap`s against an empty vector instead of copying the bucket; 1(c) settled by inspection |
| `ec1dd5e` | Extended goal 3: the e-graph's ten cache columns static `VecI` after measuring the three disciplines (all within 2.2 %); `VecD` sites and the `SEMPER_DIFF`/`--diff-mode` lever removed from the e-graph; new `store_bench` (push/pop workload); verified crate untouched |
| `1a90876` | Extended goal 4: `EGraphConfig::Policy` with `EqSat32`/`EqSat64` (Hot-first) and `Smt32`/`Smt64` (Trail-first) configurations; the class layer and the node caches follow the policy; `store_policy::{tagged_vec, plain_vec}` public total constructors; family stores declared `Send` |
| (this commit) | Extended goal 5: total public API — every public exec function is total (73 → 0 public `requires` beyond the receiver's own `wf`); the store protocol sealed on the crate-private `DiffStoreOps` supertrait; `CircularList::{splice, splice_absorb}` guarded by a verified walk of the absorbed ring (crate-private walk-free cores for `EClasses`); `SparseSet::restore` total through an archived snapshot invariant; `NodeLayout` primitives, `History`, `GenStamps`, `HintedArena`, frames, compressors, `Tagged` and `SpMap::new` converted to refuse-guards or conditional contracts; 14 internal primitives `pub(crate)`; the allowlist is empty and the checker is module-aware |

## 2. Per-container contract / verification matrix

All bodies below are verified unless a trust marker is named; markers are
classified in §3. "Exact" means the postcondition is an equality over the
container's abstract model, not an approximation. `S[k]` is the archived
snapshot at frame `k`.

| Container (public type) | Mutation and mark | Restore | Trust markers in the module |
|---|---|---|---|
| `Vec` (three-tier semi-persistent vector) | constructors: `wf`, empty view and history; `set_index`/`try_push`/`pop`: view updated exactly, snapshots unchanged; `try_mark*`: view unchanged, depth + 1, snapshots pushed with the old view, rejection leaves the model unchanged; rollover in any legal order (`flush_trail`, `compress_hot`, `apply_tier_policy`, `apply_adaptive`, configured/forced rollover on mark): `tiers_only_changed` — view, depth, snapshots, canonical history, store and policy unchanged | `try_restore`/`restore`: view `= S[k]`, depth `= k`, snapshots `= S[..k]`; rejection unchanged; `pending_restore_indices`: `Some` iff restorable and the set is exactly the indices captured by frames in `[k, depth)`; `sequence_witness_checked` composes mark/write/restore/rollover end to end from these contracts alone | 5 byte reporters/diagnostics (`log_heap_bytes`, `log_shrink_capacity`, `diff_log_len`, `tracking_bytes`, `total_bytes`) |
| `AppendOnlyVec` | push appends exactly; mark exact | `try_restore`: view `= S[k]`, depth `= k`, prefix | `shrink_aov_capacity` (capacity only) |
| `SpMap` | insert appends to the log and records the key's previous occurrence; index and `prev` column agree with the log | `try_restore`/`restore`: log `= S[k]`, depth `= k`, prefix; index unwound over the discarded suffix (rebuilt from the survivors only when the suffix outnumbers them); rejection unchanged | `clone_key_exact` (key-model projection) |
| `SparseSet` | insert/remove exact over dense/sparse/indices; `wf` archives every snapshot triple as a valid sparse-set state | `restore` (total: refuses an invalid token or disagreeing frame indices): dense, sparse and indices views `= S[k]`, archives truncated | `values_equal` (unconstrained bool) |
| `CircularList` | splice/walk exact over entries and ring model; the public `splice`/`splice_absorb` refuse a same-ring pair after a verified walk of the absorbed ring (the crate-private cores keep the distinct-rings precondition, a theorem in `EClasses`) | `try_restore`: entries and model views `= S[k]`, both archives truncated; `Err` leaves the state unchanged | — |
| `ListArena` | append/iterate exact over heads, nodes and model | `try_restore`: heads, nodes and model views `= S[k]` at one shared frame, three archive prefixes; `Err` unchanged | `white_box_head` (test accessor), `tracking_bytes`, `total_bytes` |
| `UnionFind` | union/find exact over roots, parent and rank | `try_restore`: roots, parent and rank views `= S[k]`, roots and parent archive prefixes, parent and rank marks agree; `Err` unchanged | — |
| `EClasses` | merge/find exact over roots; `min_width` preserved | `restore`/`try_restore` under full validity (which `try_restore` checks): roots, size, depth, roots archive prefix, and every component column and archive prefix (entries model and nodes, reprs dense/sparse/indices, uses model, minimum pool); `Err` unchanged | — |
| `BPlusTreeSet` (+ cursors) | insert/bulk-load exact over the ghost tree (bulk load through the total `leaf_fill_keys`, order checks branch-free); branchless search verified; cursor `seek`/`seek_first`/`key`/`step` exact against the in-order model under `cursor_ok` (positioning plus the cached leaf) | `restore`: tree `= S[k]`, arena and tree archive prefixes | 5 bounds-elided array/slice primitives in `bplus_layout` |
| `HintedArena` | set/push exact; `complete()` preserved | `restore`: view `= S[k]`, prefix; `Err` unchanged | — |
| `ForkHistory` / `SyncMember` (group wrappers) | `mark`: every member model unchanged, one archived model per member | `restore`: every member model at the token's depth, archive prefix; rejection unchanged; `mark_parallel`/`restore_parallel` carry the same contracts over the rayon fan-out (trusted dispatch, ledger 3.6d) | `mark_parallel`, `restore_parallel`, `checksum` |
| `History` (group token authority) | `mark`: `wf`, depth + 1 (requires depth `< u32::MAX`) | `restore_to`: `wf`, depth `= t` (requires a valid token below the depth) — both partial public functions, see §5 | — |
| Stores and encoders (`DiffStore`: `InlineStore`, `ParallelStore`, Trail; `ColdStack`, `CompressedStack`, `TwoStackLog`, `GenStamps`, `LayeredSpanMap`, `DenseSpanMap`, `SortedCursor`, `SortedVecCursor`, `IdFactory`) | verified functional contracts on every executable body (run encoding/decoding, capture bits, span maps, cursors); they have no snapshot model of their own and are consumed by the containers above | n/a | byte reporters (`heap_bytes` ×6, `data_capacity_bits`, `shrink_vec_capacity`), diagnostics and environment levers (`compression_stats` ×10, `compression_config` ×2, `diff_compress::choose_mode`), `std_sort::sort_pairs_by_index`, `par_sum_canary` |

Migration coverage required by the goal (duplicates, empty and gapped frames,
non-empty destination prefixes, different legal migration orders) is proved in
the migration lemmas named in `three-tier-proof-progress.md` (sections "Trail
deduplication and migration primitives", "Hot-to-Cold migration primitives",
"Rollover dispatch") and exercised by the release differential policy matrix.

## 3. Trust inventory (final source)

Re-derived from `grep '#[verifier::external_body]'` on the final source:
**37 default-build markers + 5 gated by `literal-types`** (the session started
at 74 + 5; the debug-only ring walk left with the total public API, the twelve
byte reporters left the perimeter with the stratification commit `0295502`,
ledger §2a), **4 default axioms** (`axiom_index_hasher_builds_valid_hashers`;
`obeys_key_model` for `DenseId31`, `DenseId63`, `DenseUsize`, plus one generated
per `define_id*!` id type) **+ 5 gated axioms**, no `admit`/`assume` in project
sources (CI-checked). Every default marker, by ledger group:

| Group | Items (49) |
|---|---|
| A — opaque identity (3) | `struct ContainerId`, `ContainerId::new`, `ContainerId::eq` |
| B — unmodeled std behaviour: byte reporters, no `ensures` (12) | `Vec::{tracking_bytes,total_bytes,log_heap_bytes,diff_log_len}`, `ListArena::{tracking_bytes,total_bytes}`, `heap_bytes` in `CaptureBits`, `CompressedStack`, `diff_compress`, `GenStamps`, `InlineStore`, `ParallelStore` |
| B — capacity helpers, contract = contents unchanged (4) | `shrink_vec_capacity`, `shrink_aov_capacity`, `Vec::log_shrink_capacity`, `data_capacity_bits` (`capacity >= len`) |
| B — bounds-elided array/slice primitives, `bplus_layout` (5) | `arr_get`, `arr_set`, `slice_get`, `sel_usize`, `arr_shift_up` |
| B — std slice sort contract (1) | `std_sort::sort_pairs_by_index` (permutation in non-decreasing key order, nothing else touched) |
| C — runtime guards (2) | `guard::check_precondition`, `guard::refuse` |
| D — key model and hasher registrations (3) | `map::clone_key_exact`, `ExIndexHasher`, `ExFoldHasher` |
| E — glue (2) | `sparse_set::values_equal` (unconstrained bool), `list::white_box_head` |
| F — diagnostics, levers, parallel dispatch (17) | `compression_stats` ×10 (`frame_stats`, `observe`, `observe_frame`, `shadow_enabled`, `shadow_emit`, `shadow_log_copy`, `shadow_log_full`, `run_count_writeorder`, `run_count_sorted`, `mode_name`), `compression_config::{env_compress_default,env_diff_store_kind}`, `diff_compress::choose_mode`, `sync_group::{mark_parallel,restore_parallel}` (rayon fan-out over the members' checked contracts, ledger 3.6d), `sync_group::checksum`, `parallel::par_sum_canary` |

No default marker carries a postcondition about container contents; the only
contract-carrying ones restate documented std behaviour (capacity, sort,
indexing) or the hasher/key-model facts. The last execution-first `Vec`
marker, `try_mark_adaptive`, is removed in the final checkpoint.

## 4. Gate report (final source)

Run on the final source (Verus 0.2026.08.02 / vstd 2026-08-02, rustc 1.97.1,
macOS 27.0, Apple M4 Pro), each Verus run after touching `src/vec.rs` so
nothing was served from cache; logs `/tmp/sp-d21-final-*.log`:

| Gate | Command | Result |
|---|---|---|
| Full crate, default features | `cargo verus verify` | 2696 verified, 0 errors (at `f676208`; 2676 at `0b1200e`, 2590 at the final checkpoint `f304bc7`) |
| Full crate, `literal-types` | `cargo verus verify --features literal-types` | 2696 verified, 0 errors |
| Conditional composition (Step 3 theorem) | `verus --crate-type lib containers-verus/proofs/top_down/composition.rs` | 80 verified, 0 errors |
| `au-verus` | `cargo verus verify` (in `au-verus/`) | 29 verified, 0 errors |
| Feature/runtime suite | `cargo test -p semi-persistent-containers-verus --features 'compat-all,literal-types'` | 279 passed, 0 failed, 10 ignored |
| Release differential policy matrix | `PROPTEST_CASES=1024 cargo test -p containers-conformance --release --test three_tier_policy_matrix` | 4 passed |
| Consumers (e-graph, SAT core) | `cargo test -p semi-persistent-satcore -p semi-persistent-egraph` | 1268 passed, 0 failed, 45 ignored |
| Canary | `cargo test -p containers-verus-canary --features compat-all` | 2 passed |
| Partial-API audit | `tools/check_partial_api.py` | 0 partial / 0 allowed / 0 unlisted / 0 unsafe — closed by extended goal 5 (§5); 73/33/40/0 at the final checkpoint |
| Formatting, whitespace | `cargo fmt --all -- --check`, `git diff --check` | clean |
| Legacy oracle unchanged | `git diff --quiet d191c4a -- containers` | unchanged |
| Trust count (CI method) | grep of `#[verifier::external_body]` | 37 default + 5 gated (`EXPECTED_DEFAULT=37`; 49 until the byte reporters left the perimeter, 50 until the debug-only ring walk left with extended goal 5) |

The 10 ignored feature tests and 45 ignored consumer tests are the suites'
pre-existing ignores (feature-gated or long-running), unchanged by this branch.

## 5. Partial-API discrepancy (closed by extended goal 5)

**Closed on 2026-09-17** (the total-API commit): `tools/check_partial_api.py`
reports **0** public executable functions with a `requires` (beyond the
receiver's own `wf`-class predicate) and the allowlist is empty; the CI
partial-API check passes. How each class was handled is recorded in
`doc/future/total-api-plan.md` ("Status") and in the progress document
("Total public API"). The paragraphs below are the exposure review as it
stood at the final checkpoint, kept as the record of what was open.

At the final checkpoint the checker reported 73 public executable functions
with a Verus `requires`, 33 allowlisted and 40 not, 0 public `unsafe`. The
40 were present before this proof drive and were unchanged by it. Exposure
review at that time:

- All 40 live in modules declared `pub mod` in `lib.rs` (`cold_stack`,
  `compressed_stack`, `diff_compress`, `diff_store`, `gen_stamps`,
  `hinted_arena`, `history`, `layered`, `sync_group`, `two_stack_log`,
  `value_compressor`, `vec`), so they are reachable from safe external Rust.
- Two are relied on by the e-graph: `History::mark` (requires depth
  `< u32::MAX`) and `History::restore_to` (requires a valid token below the
  depth); the e-graph establishes both by its own runtime checks
  (`egraph/src/egraph.rs`, "The depth guard is History::mark's
  precondition"). These are the only offenders with a production caller
  outside the crate; the policy's preferred fix is a `Result`-returning total
  pair next to them.
- `sync_group::{seal_frame, restore_frame, add_member}` and `vec::seal_frame`
  are `SyncMember` trait methods (public by the checker's pub-trait rule),
  called only by the group wrappers, which prove their preconditions.
- The remaining 33 are component internals (`ColdStack` sealing and
  frame restore, `diff_compress`/`layered`/`value_compressor` encoders,
  `HintedArena`, `GenStamps`, `TwoStackLog`, `DiffStore::restore_overlay`)
  used by in-crate callers and by the conformance tests. They fit the policy's
  "Inaccessible Store Receivers" / "Component-Boundary Preconditions"
  classes only if their modules stop being `pub mod` or their receivers stop
  being constructible externally, neither of which is true today.

The goal document forbids bulk-allowlisting. No entries were ever added; the
item stayed open (CI's partial-API check failing, exactly as at `d191c4a`)
until extended goal 5 drained every entry through contract or exposure
changes — `History::{mark, restore_to}` and the other production-reachable
functions became total with refuse-guards, the `SyncMember` and store
protocol methods moved behind crate-private surfaces, and the component
internals took guards or conditional contracts.

## 6. Performance gate

See [final-performance-report.md](final-performance-report.md).
