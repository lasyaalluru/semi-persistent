# Conditional interface review and existing-proof classification

## Evidence and scope

The complete conditional operation family, legal public-operation traces, and
arbitrary legal rollover traces verify in `composition.rs`: **79 verified,
0 errors** with pinned Verus `0.2026.08.02.b677dd5`. There are no imported leaf
implementations or trusted proof stubs. The mathematical witness implements all
provisional method contracts; additional encoded examples exercise duplicates,
sorting, gapped runs, preserved pool prefixes, and empty frames.

This completes the first **conditional composition** milestone. It does not
complete the thread goal or discharge any missing production implementation.
The interface predicates below remain concrete-adapter obligations. Their
definitions may be strengthened or decomposed as implementation evidence
requires; every interface revision must reverify the complete composition.

Production verification at `07b6df8` remains separate evidence: both configurations
verified 2310 obligations; feature, differential and consumer gates passed.
No production source was changed during the conditional milestone.

## Requirement audit

| Requirement | Conditional evidence |
|---|---|
| One saved length and earliest-capture map per frame | `model::Frame`, `frame_ok`; `encoding::earliest`, `trail_append_equation`, `repeated_capture` |
| Constructor, writes, push/pop, regrowth, mark, restore | `model` closure lemmas and `mutation`/`policy`/`composition` public wrappers |
| All legal public-operation interleavings | `public_sequence::execute_one`, `effect_preserves`, `complete_sequence` |
| Any legal rollover order, independent of selector | `policy::legal_rollover_sequence`; `apply_policy_sequence`; Hot-then-Trail witness |
| Batched pair replay and direct Cold replay | `composition::reconstruct`, `cold_suffix`; `model::range_split` |
| Arbitrary saved-length zigzags and arbitrary resize filler | `model::range_reconstructs`, `reconstructs_target`; witness lengths 3,1,3,2,2 |
| Precise logical and canonical retirement | `Runtime::retire`, `restore_public`; required exact physical prefix projection |
| Every survivor tier and both disciplines | Separate `reopen_hot`/`reopen_cold` interfaces and dispatch; `mixed_restore_cases` |
| Capture rebuilding and fused/non-fused protocols | `prepare`, `pair_batch`, `finish_capture`; witnesses parameterized over clearing protocol |
| Mutation followed by another older restore | `restore_write_restore`, `mutate_then_restore_older`; definite successful witness |
| Empty frames, duplicate captures, local transforms | `empty_frame_migration`, `empty_frame_contracts`, `encoded_duplicate_example`, `conversion_chain` |
| Exact pool append followed by frame publication | `appended`, `appended_cold`, `appended_cold_meaning`, `cold_transform_and_pool` |
| Completed prefix relocation preserves frame order | `move_prefix_preserves`; completed migration count/map contracts |
| Public tokens and rejected requests | Separate token predicate and bounds interface; typed errors and exact unchanged-state rejection effects |
| No extra runtime history or changed replay batching | Isolated proof target; all traces/maps are mathematical parameters or derived views |

## Boundary review against current source

### Canonical history

`Vec::wf_for_snap` combines store/partition facts, canonical boundary shape and
canonical frame reconstruction. The whole predicate cannot serve as
`canonical_ok` during resize/replay: changing live contents temporarily breaks
the newest canonical frame's layer relation.

The adapter must separate canonical boundary/storage correspondence from
`SnapshotsOK`. It must recover **all** of `wf_for_snap` at public boundaries,
including the old `full_trail` frame contracts. This is not permission to drop
canonical contracts or use the inert `diff_log` as replay authority.

Current physical and canonical invariants each reconstruct snapshots, but this
alone does not prove equality of their capture domains. If the adapter uses
canonical-to-physical map equality, that relationship needs its own proof or
stronger preserved invariant. It cannot be inferred from equal reconstructed
contents. The physical map remains the shared reconstruction authority.

`Vec::restored_history_prefix` already specifies exact retained headers, runs,
payloads, snapshot boundaries and chronological ghost prefix. It is the candidate
for `retired_prefix`. `hot_survivor_promoted` specifies the subsequent movement
separately, which is correct: exact pre-state physical-prefix equality is not
required after moving the survivor.

### DiffStore implementation connection

The writable tier comes from the `DiffStore` implementation's immutable capture
discipline. `Vec` consults it for capture, mark, and survivor reopening. The
rollover selector is a separate configuration input; its eligibility proof must
respect that writable tier and protect the active frame.

| Implementation | Writable tier | Reads replay indices for pre-clear | Replay clears named capture flags |
|---|---|---|---|
| `TrailStore` | Trail | No | No (capture flags are ghost state) |
| `ParallelStore` | Hot | No (bitmap reset) | No |
| `InlineStore` | Hot | Yes (sparse tag reset) | Yes |
| `DynStore` | Selected variant's tier | Selected variant's protocol | Selected variant's protocol |

`DiffStore` mutation contracts preserve all three protocol predicates. This is
essential for `DynStore`: the proofs use an instance property that remains
constant across operations, not a hard-coded generic type test.

The concrete dependency chain is:

- `capture` supplies the store-level append/no-op contract. Both selected ingress
  branches of the checked `runtime_capture`
  now consume it. Its contract exports exact append/no-op effects, protocol
  preservation, capture flags and the canonical chronological event. Trail keeps
  physical duplicates. The shared-map `capture_first` interpretation remains an
  adapter obligation; it is not inferred merely from snapshot reconstruction.
- `set_raw`, `push`, and `pop` supply exact live effects and flag framing.
  `Vec` must preserve older maps and handle active-domain capture/regrowth.
- `prepare_mark` clears capture state under its coverage premise. `Vec` seals
  and opens the tier selected by the store, then applies legal rollover.
- `resize_default`, `begin_restore`, `restore_overlay`, and `restore_run`
  supply resize, clearing, batched pair replay, and direct Cold replay effects.
  The checked shared-map replay bridge consumes these existing contracts.
- `finish_restore` supplies capture membership for the reopened frame's entries.
  The checked finalization and map-membership bridges connect it to `CaptureOK`.

These methods have checked implementations in the four store modules and are
included in full production verification. Capacity diagnostics/reclamation have
separate recorded trust boundaries; this is not a claim that every store module
is trust-free. Nor does checking these methods discharge the remaining all-tier
`Vec` mutation, conversion, policy, and Cold reopening composition obligations.

The former trusted `runtime_set_fallback` used a Hot-only helper under the weaker
runtime test `unique_capture()`. That gap is now discharged: the checked body
calls general `runtime_capture`, then `set_raw`, and proves pair, canonical,
Cold and capture-state preservation. Existing specialized Hot proofs remain.
Push/regrowth and pop now also have checked general implementations. The
regrowth path restores capture membership for both store disciplines. Mark
still needs its general implementation proof; none of these mutation results
discharges the policy or complete shared-model adapter obligations.

### Public guards and payload capabilities

The standalone Vec token predicate is `TRACK && frame_idx < depth && depth <
u32::MAX`. Keep it intact. Group genealogy belongs to the group/history layer;
do not add it to the standalone token or replace public validity with only a
frame-coordinate bound.

Mark checks Untracked, then DepthLimit, then CapacityExhausted. The adapter's
`mark_error` projection and `mark_guard` proof must retain that ordering.
`try_push` rejects with CapacityExhausted; `try_restore` rejects with InvalidToken.
The conditional wrappers retain those result categories and leave the full
state unchanged when rejected.

Mark's existing contract promises the returned coordinate, not unconditional
future token validity. In particular its depth guard and restore's depth guard
must not silently be treated as the same post-mark assertion. The conditional
theorem preserves the existing distinction.

Mutation and marking interfaces do not inherit restoration capability. Concrete
restore requires `T: Default`, whereas the mutation family supports its broader
Copy payload domain. Concrete index limits, tracking/depth guards and settings
framing must be instantiated from existing fields/contracts, not weakened to
match the mathematical witness's unbounded finite-sequence capacity.

### Assumption inventory boundaries

The `README.md` inventory names every provisional method, concrete candidate,
caller premise and next consumer. Local transform relations in `encoding.rs`
name full map equality and validity; completed migration additionally requires
source retirement/rebasing and stable physical ownership. The local pool-builder
contract deliberately does not assert global partition validity while source
and destination coexist.

The consistency witness interprets physical storage directly as frame maps and
canonical storage as snapshot sequences. That interpretation demonstrates that
the contracts are jointly realizable; **it is not the production interpretation**.
The production projections must include the actual pooled storage and canonical
chronological history described above. Opaque predicates must not be defined as
vacuous truths merely to instantiate the interface.

## Existing-proof classification

“Reuse” means retain the checked theorem/body and add the required interpretation
bridge. It does not mean its production adapter is already verified. “Adapt”
means keep existing work while strengthening exported facts or separating a
physical effect from snapshot-specific premises. No verified proof is currently
scheduled for deletion or replacement solely because a new model exists.

| Existing work | Classification | Required work against the conditional contract |
|---|---|---|
| `frame_saved_value`, `lemma_frame_saved_value_contract`, `lemma_physical_frame_step` | Reuse | Derive the finite map and its bounded domain from physical tiers; connect Option lookup to map membership/value |
| `replay_physical_range` | Reuse | Its exact overlay/lookup result already describes arbitrary-buffer application; add map interpretation and batch-composition bridge |
| `replay_cold_range` | Reuse | Exact covered/uncovered per-cell effect and unchanged flags match direct replay; add Cold-map interpretation |
| `replay_pair_suffix_checked`, `replay_cold_frame_checked` | Adapt | Existing wrappers require layer agreement and export snapshot-prefix reconstruction; expose the underlying arbitrary-buffer map effect without discarding reconstruction lemmas |
| `reconstruct_target_checked`, mixed-tier replay orchestrator | Reuse/adapt boundary | Preserve batching and local frozen state; export exact history/protocol framing required by the adapter |
| `restored_history_prefix`, truncation bounds and canonical/physical retention lemmas | Reuse | Translate exact physical prefixes to retained shared-map sequence and instantiate canonical prefix projection |
| `promote_hot_survivor_checked`, `hot_survivor_promoted` | Reuse | Exact rebased payload equality supplies map/domain equality and older-storage framing |
| `finish_survivor_checked`, zero finish, capture rebuilding | Reuse | Relate current captured-in-range predicates to shared-map membership; retain active length and no-stray-flag obligations |
| Capacity-only reclamation proofs | Reuse | Instantiate unchanged relevant sequences, protocol and canonical projection |
| `cold_encode::append_sorted`, `append_cold_sorted_checked` | Adapt | Existing run/input mapping and prefix contracts are useful; expose complete map equality, including absence and source coverage, in the local/pool interface |
| Hot-only capture/set/push/pop/mark proofs | Reuse for their scope; adapt for general case | Retain their checked scope; derive shared-map effects and all-tier preservation rather than claiming Hot-only preconditions cover mixed histories |
| All-tier mutation/mark fallbacks | Mutation bodies discharged; mark pending | Capture/set/push/pop now preserve the general invariant through actual store methods. Mark/open-frame execution and shared-model operation effects still need concrete discharge; no trust was transferred into new wrappers |
| Trusted Trail dedup/sort/migrations and configured/adaptive execution | Unproved implementation to discharge | Exact local map transforms, pool append, source-plan identity, retirement/rebasing and eligibility; compose through sequence theorem |
| Cold survivor promotion / former restore fallback | Discharged | Checked decoder, exact source prefixes, both destination representations, shared-map equality and finalization compose in `restore_cold_survivor_checked`; obsolete trusted dispatcher removed; full verification and regression gates passed |
| Old specialized Hot-defer reconstruction proofs | Preserve | Useful verified specialization; no need to remove it to establish the all-tier theorem |
| Derived/container and group/parallel paths | Pending concrete public audit | Retain original scope, review content/prefix/error contracts and fan-out trust after Vec adapters are checked |

## Next concrete work

The first concrete bridge now derives `persistence_frame` and
`persistence_model` from actual physical storage and verifies bounded domains,
exact lookup membership/value, snapshot meaning, writable ownership, and the
active capture relation. Pair suffix composition and direct Cold replay export
arbitrary-buffer shared-map application through checked executable helpers.
The original snapshot-oriented wrappers retain their contracts and use those
helpers; their existing reconstruction lemmas remain checked. The shared model
is imported by production, while the provisional interface target stays isolated.

Interpretation, replay, retirement, Hot promotion and capture finalization
bridges are verified milestones. Cold decoding at `25ecbcf` passed full default
and literal-types verification (2360 obligations), feature, differential and
consumer gates. Its local theorem alone did not discharge promotion assembly.

The next step now checks that assembly: exact older Cold prefixes, unchanged
canonical history, store-selected destination header and representation, full
shared-map equality, and capture rebuilding. `restore_cold_survivor_checked`
exports restored contents, depth, snapshot prefix and exact shared-frame prefix.
All 45 selected Cold obligations passed together. The former trusted fallback
and unused trusted survivor dispatcher are discharged/removed, reducing counts
to 79 default plus five literal registrations. Full default and literal-types
verification each passed 2373 obligations; feature, differential and consumer
tests passed. The conditional target remains at 80 verified obligations. An
additional partial-API CI audit reports the same 40 unlisted functions as the
committed baseline; no entries were added by this change or to the allowlist.

1. Complete the production interface instantiation using the checked physical
   interpretation, replay, retirement, promotion and finalization contracts.
2. Discharge remaining capture/mutation/conversion and policy implementations,
   rechecking conditional composition after any interface change.
3. Finish derived/parallel public closure and the full trust/gate audit.

No existing proof is superseded until a concrete replacement verifies. No push
to origin is authorized.

### General canonical capture preservation

`lemma_canonical_capture_append` now proves chronological ghost-history
preservation from `wf_for_snap`, a valid saved-domain capture, unchanged live
contents/snapshots/boundaries, and the caller's new physical partition. It makes
no Hot-only assumption. The proof retains the existing duplicate/first-capture
and unchanged-range lemmas; the original checked Hot canonical-capture helper
now consumes it without changing its executable statements or public contract.
The selected capture family verifies (16 obligations).

The `push_frame` wrapper also verifies directly against the existing
`runtime_push_frame` contract (three selected wrapper/dispatcher obligations).
Its redundant trust marker is removed. The all-tier mark fallback remains
trusted, so this is wrapper discharge rather than complete mark discharge.

At that checkpoint, the next capture work was to establish the general physical
pool effect and capture-membership relation for each store-selected ingress, then compose that
effect with the canonical lemma. The new canonical lemma alone does not prove
the trusted `runtime_capture`, mutation or mark fallbacks.

The regrowth audit at that checkpoint exposed a concrete ghost-state obligation
(now discharged by the push/pop checkpoint below):
`TrailStore::push` appends a clear ghost capture flag, whereas
`runtime_push_fallback` calls `mark_captured` only for unique stores. Regrowth
below the saved length already has a physical capture, so the Trail branch must
restore its ghost membership too before claiming `open_ingress_ok`. The checked
`TrailStore::mark_captured` body is ghost-only; any generic dispatch change must
still be reviewed for runtime/codegen effects. Do not weaken Trail's capture
membership invariant to conceal this missing preservation step.

### Checked physical capture for both ingress disciplines

`runtime_capture` is now checked against the general `wf` precondition for
Trail-only, Hot-only and mixed histories. Both branches call the actual
`DiffStore::capture` method. The contract exposes the exact selected-pool
append/no-op, unchanged other pool, capture-flag update, immutable protocol
predicates, live contents and canonical chronological event. Outside the saved
domain, the whole state is unchanged. No new persistent field is introduced.

`ingress_capture_effect` describes the intermediate physical effect. A common
per-frame proof reuses the existing first-capture/duplicate lemmas. Separate
Hot and Trail header proofs preserve each representation; flag preservation and
Cold/canonical framing complete the invariant. Canonical append then uses the
previous checkpoint's general lemma. Solver decomposition and explicit store
well-formedness access resolved resource failures without increasing limits.

The selected capture family passes 23 obligations; the separate physical framing
lemma passes independently. Full verification/regression evidence is recorded in
the progress log when complete. The runtime helper's trust marker is removed;
the set/pop/push and mark fallbacks remain unproved. General set must now compose
this checked capture with `set_raw` and frame-local captured/outside write lemmas,
preserving older layers and canonical reconstruction. Shared-map `capture_first`
equality remains an explicit production-interface obligation.

Trail execution now enters its store capture method rather than directly calling
`get` and appending in Vec. The method retains unconditional duplicate append
and performs its flag update in ghost code. Unique capture calls the same store
primitive without passing through the Hot-only proof helper. Existing specialized
Hot helpers remain checked. There are no new maps, buffers or traversals, but
performance parity still requires the final benchmark gate.

### Checked mixed-tier set composition

The next checkpoint discharges `runtime_set_fallback` against its original
public-facing contract. It calls the checked general capture helper followed by
the actual `DiffStore::set_raw`. `raw_set_effect` describes exact live update,
unchanged container fields and immutable store protocols. Flag preservation is
TRACK-conditional, matching the existing store contract; no tag preservation
work is added for untracked writes.

`lemma_raw_set_pair_frame` reuses the captured-cell and outside-domain write
lemmas. Separate Hot and Trail representation proofs preserve headers, pools
and uniqueness. Canonical proof access is pointwise: the newest frame uses the
same write lemmas and all older layers are unchanged. The common invariant
composition also retains capture ownership and Cold reconstruction.

`lemma_cold_reconstructs_layer_transfer` generalizes the existing transfer proof
to equality of the immediate newer layer. This frames older Cold history even
when live data changes. The original whole-live-equality contract remains a
checked wrapper, so existing callers retain their guarantees.

Selected set-family verification passes 18 obligations, including the actual
runtime wrapper. Full-gate evidence belongs in the progress log once completed.
One trust marker is removed; no public contract or solver limit is weakened.
The original specialized Hot set helper remains checked and available.

Next, the push/regrowth proof can reuse the existing grow-layer lemma for both
physical pair frames and canonical history. It must restore capture membership
when regrowing into the active saved domain for Trail as well as Hot, while
retaining dead-flag behavior in untracked stores. Pop requires checked capture
before contraction. Mark, migration and the production shared-map interface
remain separate obligations.

### Checked mixed-tier push/regrowth and pop

`runtime_push_fallback` and `runtime_pop_fallback` now have checked bodies.
Push preserves every history field and grows live contents by one cell. The
existing grow-layer lemma preserves each physical and canonical frame. The
reentered-cell lemma proves that a saved-domain index absent from the old live
layer must already be captured. Regrowth restores that membership through the
existing `mark_captured` hook for both disciplines; Trail's hook is ghost-only.
Untracked flags retain their existing dead-state contract.

Pop captures a disappearing saved-domain cell through the checked general
capture helper, then consumes `DiffStore::pop`. The last-cell contraction lemma
preserves physical and canonical reconstruction, and the newer-layer transfer
preserves older Cold history. Empty pop returns without mutation. Saved-domain
index conversion is proved successful from the existing active-length bound.

Selected push and pop families verify 18 and 12 obligations respectively.
Full-gate evidence is recorded in the progress log when complete. Neither
implementation adds a persistent history, buffer or traversal. The push runtime
guard no longer restricts membership restoration to unique stores; performance
parity for that dispatch change remains part of the final benchmark gate.

Next mark obligations:

- Completed: `runtime_push_frame` and its trusted fallback now require TRACK,
  supplied by both existing callers. Public guards and error behavior are unchanged.
- Completed: `prepare_mark_checked` and `prepare_mark_range_checked` prove the
  borrowed active-range coverage required by the actual DiffStore method, all
  live flags cleared, and exact non-store framing. Full default verification:
  2413 verified, zero errors (`/tmp/sp-d21-mark-prepare-default.log`).
- Completed: the invalid mixed-history Hot shortcut is removed; explicit Defer
  dispatch now uses the checked general opening/reclamation path outside the
  retained Hot specialization.
- Completed: `open_mark_headers_checked` proves exact sealing/opening header
  sequences, snapshot/boundary append and frame partition. Shared canonical mark
  lemmas transfer the former live layer to the equal new snapshot; the existing
  Hot mark proof now reuses them after their independent verification.
- Completed: the header helper exports unchanged old pair-frame coordinates;
  `lemma_mark_pair_frame` preserves their reconstruction and Hot uniqueness.
  `lemma_mark_cold_repr` preserves the full Cold representation across snapshot
  append through a narrower per-frame transfer lemma. Existing transfer contracts
  remain checked wrappers.
- Completed: aggregate Hot/Trail preservation, cleared-flag ingress, compatibility,
  Cold and canonical proofs establish full general wf in `open_mark_checked`.
  `mark_defer_checked` composes shrinking and opening for explicit Defer marks.
- Compose actual rollover and reclamation afterward. Mark remains incomplete
  until its policy dependencies and shared-model effects are discharged.

### Concrete migration assembly checkpoint

Reuse `append_selected_hot_frame_checked` for ordinary Trail-to-Hot publication:
exact destination concatenation/header bounds and full saved-value map equality
verify. Its actual caller now uses it. Still prove the caller's selected positions
are in bounds and are precisely the first captures, then source retirement and
representation preservation. The adaptive `extend_from_slice` path remains open:
the pinned vstd specification exposes `cloned`, not generic payload equality;
preserve the existing bulk copy and payload capabilities while resolving it.

Adaptive publication now uses checked owned `Vec::append` through
`append_owned_hot_frame_checked` and `append_trail_plan_checked`. This resolves
the previously recorded clone-contract gap for payload assembly while retaining
bulk transfer and generic Copy payloads. The loop proves exact pool concatenation,
header ordering/offsets, unchanged source fields and emptied temporaries. Plan
selection semantics and source retirement/global invariants remain pending.

Retirement implementation is now checked separately:
`discard_prefix_checked` proves bulk shift/truncate retains the exact suffix;
Trail/Hot retirement helpers prove survivor header order, saved lengths and exact
rebasing. All four ordinary/adaptive migration paths call them. Reuse
`lemma_range_saved_value_retire_prefix` to transfer full physical saved maps.
Still discharge caller-supplied bounds, source/destination frame correspondence,
final global invariants and configured/forced/adaptive policy execution.

The adaptive Trail executor now calls `execute_trail_plan_storage_checked`, which
composes actual publication and retirement, proves retirement bounds, restores
the global frame partition, and exports exact moved/survivor header and pool
relations. Every new Hot frame's saved-value map equals its planned payload.
The remaining semantic precondition supplier is first-capture plan/source
correspondence and uniqueness; reconstruction/ingress preservation must then
establish full wf. The executor remains trusted until those proofs compose.

Use `lemma_frame_inv_range_same_saved_map` for encoding-independent physical
frame-contract transfer, including destination saved-domain bounds. The actual
Trail storage helper now proves moved Hot reconstruction/uniqueness conditionally
on `trail_plan_matches` (source first-capture map equality plus unique payloads).
No caller is allowed to assume that predicate; sorting/selection must establish
it. Untouched/surviving tier and capture-state preservation remain to compose.

Trail storage execution now proves full wf under `trail_plan_matches`: existing
Hot frames, moved Hot frames, rebased Trail survivors, unchanged Cold/canonical
history and active capture membership all compose through checked lemmas. No
runtime or trusted-contract change supplies the matching predicate. Next prove
that actual selection produces it, then remove the executor trust only after the
producer/consumer chain verifies. Hot-to-Cold and policy closure remain separate.


### Trail deduplication and migration primitives

The Trail-to-Hot producer is `trail_select::dedupe_trail_range`: one
left-to-right pass with a `HashSet<I, IndexHasher>` membership test, first
capture wins, unique payload appended to the destination pool in chronological
order of first capture. Its contract (`dedupe_prefix`, uniqueness and full
optional saved-map equality with the source range) is the matching predicate the
storage theorem needed; no sort or permutation obligation remains on this path.
Migration is composed from checked per-frame primitives over the closed state
predicates `trail_migrating`/`trail_tentative`: `trail_frame_tentative_checked`
(dedupe into the pool, no header), `trail_frame_commit_checked` (publish the
header), `trail_frame_discard_checked` (truncate a rejected frame) and
`trail_migration_finish_checked` (bulk retirement plus
`lemma_trail_migration_wf`). `runtime_migrate_trail_count`,
`runtime_migrate_trail` (including the `TierLimit::Adaptive` shape loop) and
`adaptive_trail_stage_checked` (byte-budget planner stage) are checked loops
over these primitives; policy selection stays separate from the shared
preservation lemma. The planned-payload executors were removed with the plan
vectors they consumed.


### Hot-to-Cold migration primitives

Hot frames are unordered, so `hot_frame_sort_checked` sorts a closed frame in
place in the Hot pool (std's unstable sort under the trusted
`std_sort::sort_pairs_by_index` contract) and proves through
`lemma_unique_range_permutation` that a unique range permuted within itself
keeps its earliest-capture map. `hot_frame_encode_checked` appends the frame as
Cold runs straight from the pool slice via `cold_encode::append_sorted`;
`lemma_hot_frame_encoded_new` derives coverage-is-capture and cell values from
the `run_prefix` partition (`cold_encode::lemma_run_prefix_entry`/`_cell`).
`hot_migration_finish_checked` retires the encoded prefix in one bulk move and
recovers `wf` through `lemma_hot_migration_wf` (partition, kept and new Cold
frames, rebased Hot frames, unchanged Trail, ingress, canonical history). The
state predicates `hot_migrating`, `hot_migrating_hot`, `hot_migrating_cold` and
`hot_retired_from` are closed and read through accessor lemmas to keep every
query below the default resource limit. `runtime_migrate_hot_count`,
`runtime_migrate_hot` (including the `TierLimit::Adaptive` run-count loop over
`count_index_runs`) and `adaptive_hot_stage_checked` are checked loops over
these primitives; rejected frames stay in Hot, sorted.


### Rollover dispatch

Every rollover entry point is now a checked composition of the checked
migrations: `runtime_apply_tier_policy` (`apply_tier_policy`),
`runtime_apply_configured_rollover` (legacy Hot-buffer batch or configured
limits), `runtime_rollover_on_mark` (Defer / ApplyConfigured / ForceClosed),
`runtime_push_frame_fallback` (open the new frame, then roll over, then reclaim),
`flush_trail`, `compress_hot`, and `runtime_apply_adaptive` (`apply_adaptive`)
with checked byte accounting and all-tier reclamation. The shared postcondition
`tiers_only_changed(pre)` states that only the seven physical tier vectors move:
live contents, snapshots, canonical history, store and policy are untouched,
which is the Step 2 rollover-composition invariant in concrete form. Policy
legality (eligible source frames, active frame excluded) is enforced by the
primitives' preconditions rather than assumed.


### Production sequence witness and read-only consumers

`sequence_witness_checked` composes the public API on one representative
interleaving (mark, write, mark, restore, write, tier policy, older restore) and
asserts, from the public contracts alone, that the live view is always the
archived snapshot, the depth the token's frame and the archive its prefix. It is
the concrete counterpart of `composition.rs`'s conditional theorem; the
dependency map is `interface-inventory.md`. `pending_restore_indices` is checked
with `names_index(out, j) <==> exists f in [token, depth): frame_captures(f, j)`,
built from the per-tier passes and `lemma_pending_union`; consumers that repair
content-keyed indexes around a restore can rely on that set exactly.
