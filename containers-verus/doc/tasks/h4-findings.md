# H4 findings: parallel mark/restore and the one-history adoption

Closes phase H4 of `h4-f2-f5-correctness-goal.md`, both stages. Every number
names the test that regenerates it.

## H4a: the member fan-out, measured

`EGraph::restore_with` fans the seven member composites out over a
`rayon::scope` on disjoint `&mut` field borrows; the shared bookkeeping
(outcome, worklists, repair watermark) runs strictly after the join. The
differential test (`par_fanout::par_fanout_matches_sequential_and_spawns`)
drives the same grow/mark/restore workload through both paths and asserts
identical observables at every checkpoint: every node's canonical
representative, class count, node count, and re-add probe ids, including
restores past unrestored inner marks. It also asserts the spawn witness: all
seven member closures observed on at least two rayon workers
(`take_fanout_witness`).

Synthetic wall-clock (`par_fanout_bench::par_fanout_wall_clock`, release, 24
rounds per configuration):

| live nodes/frame scale | mark seq -> par | restore seq -> par |
|---|---|---|
| ~12k nodes (256 leaves/round) | 0.10ms -> 2.84ms (**0.03x**) | 3.41ms -> 4.68ms (**0.73x**) |
| ~200k nodes (4096) | 1.33ms -> 4.40ms (**0.30x**) | 116.7ms -> 72.3ms (**1.62x**) |
| ~1.6M nodes (32768) | 7.80ms -> 11.54ms (**0.68x**) | 5205ms -> 4707ms (**1.11x**) |

Decisions taken from the numbers: the public `mark` is always sequential (a
mark is a per-member frame push; the scope dispatch dominates at every
measured size), and the public `restore` gates the fan-out at
`PAR_NODE_MIN = 16384` live nodes with a `SEMPER_PAR` on/off override. The
1.11x at 1.6M nodes against 1.62x at 200k is the member skew: one member
(classes) dominates the restore critical path at large scale, so the
member-level fan-out's ceiling is set by the largest member, not the member
count.

## H4a.5: the corpus profile, and why the corpus wall stays neutral

`SEMPER_PROF` accumulates mark/restore wall in the engine
(`take_markrestore_profile`); the Sundance adapter prints it on teardown. On
the five most backtrack-heavy corpus instances (selected by a full-corpus
sweep of restore time under a 12s cap; CaDiCaL's trajectory is deterministic,
so call counts match across configurations exactly):

| instance | restore (seq) | restore (forced par) | mark | restore share of wall |
|---|---|---|---|---|
| QF_UF_cyclic_scheduler.3 | 919.3ms / 80 calls | 910.9ms (1.01x) | 7.7ms / 2056 calls | 7.7% |
| QF_UF_reader_writer.3 | 745.8ms / 99 | 730.7ms (1.02x) | 14.5ms / 4595 | 6.2% |
| QF_UF_reader_writer.2 | 264.3ms / 68 | 254.3ms (1.04x) | 9.8ms / 4242 | 2.2% |
| QF_UF_cyclic_scheduler.4 | 201.9ms / 40 | 199.2ms (1.01x) | 2.7ms / 745 | 1.7% |
| QF_UF_reader_writer.1 | 133.4ms / 52 | 130.4ms (1.02x) | 4.3ms / 1285 | 1.1% |

The corpus wall is neutral under the fan-out and the profile says why:
restore is at most 7.7% of solve wall even on the most backtrack-heavy
instances (under 1% corpus-wide), mark at most 0.12%, and at corpus graph
sizes the fan-out moves restore only 1.01x to 1.04x. The projected corpus
ceiling is about 3% even if instances reached the 200k-node regime where the
fan-out wins 1.62x. Parallel corpus gains are therefore bounded by Amdahl at
the profile, not by the fan-out implementation; revisit only if a workload is
measured to spend a large fraction of wall in restore at large node counts
(the EqSat regime is the candidate).

## H4b: one History, the token tree collapse, H2

`EGraphToken` is one `GroupToken` plus the completion outcome; the member
token structs moved into depth-indexed stacks inside the e-graph. `restore`
validates the group token once against the e-graph's `History` and records
the branch cut once. **Design decision:** the e-graph pairs its typed members
with a `History` directly instead of moving them into the owning
`ForkHistory` container, because `ForkHistory` owns its members as
`Box<dyn SyncMember>` and the e-graph's hot paths need typed member access;
the genealogy semantics are the same verified `History` in both shapes, and
`Solo`/`SyncPair` are the verified proofs that the pairing composes.

H2 landed with it: `struct Vec` and `struct AppendOnlyVec` carry no `forks`
and no `id` (grep-checked), `VecToken` is a structural `frame_idx` handle,
and branch validity plus forgery rejection live once on the `History`. The
containers' forgery and abandoned-future tests moved to the paired form, and
`structural_vec_restore_is_frame_liveness_only` pins the complementary
semantics of a raw frame handle. Every reconstruction theorem survived
untouched: the genealogy never carried proof weight in `wf`.

## H4b.3: peak fork-history bytes, shared vs duplicated

`sync_group::shared_history_bytes_vs_per_member_duplication` (ten members,
mark to depth, branch cut, re-climb):

| depth | shared History | per-member duplication (10 members) |
|---|---|---|
| 128 | 1,024 B | 10,240 B (10.0x) |
| 1024 | 8,192 B | 81,920 B (10.0x) |
| 4096 | 32,768 B | 327,680 B (10.0x) |

The real e-graph (`par_fanout_bench::shared_fork_history_bytes`): 512 B
shared at depth 64, 8,192 B at depth 1024. The pre-H2 counterfactual is 46
copies (the semi-persistent column census from the member token structure: 9
in EClasses, 29 in the node store, 8 across registries and maps): 23,552 B
and 376,832 B respectively. The duplication factor is exactly the column
count because every column's stamp array grew in lockstep under
`EGraph::mark`.

## Gates at close

`cargo verus verify`: 1964 verified, 0 errors. Containers suite 180 tests,
e-graph suite 1256 tests, 0 failures. Sundance corpus 438 total / 427
correct / 0 incorrect / 11 timeout, identical with and without
`SEMPER_COMPRESS=auto`, unchanged through the collapse and H2.

## CORRECTION (2026-09-08, post-close): restore share was understated

The 7.7% figure above divides by the 12-second CAP, not by the solve wall of
instances that complete. Symmetric trait-boundary probes (`TRAIL_PROF`,
sundance commit `e1ca8b8`) on uncapped runs of the two most backtrack-heavy
instances, semper vs the stock backend:

| instance | stock backtrack total | semper backtrack total | per call | wall |
|---|---|---|---|---|
| QF_UF_cyclic_scheduler.3 | 6.1ms / 95 calls | 904ms / 94 | 64us vs 9.6ms (~150x) | 0.16s vs 3.19s |
| QF_UF_reader_writer.3 | 15.8ms / 101 | 724ms / 101 | 156us vs 7.2ms (~46x) | 0.19s vs 3.13s |

Restore is 28% of semper's uncapped wall on the first instance: a real
co-culprit on backtrack-heavy SMT, not noise. The adapter is exonerated
(trait-boundary time minus the engine's own restore is ~0.2ms: replay and
node_to_driver rebuild cost nothing); the expense is inside the engine's
restore, whose per-column frame machinery and dirty-id repair carry costs
that do not shrink with the undo delta, against the stock backend's O(delta)
undo trail. The remaining ~2.1s of the gap is search-side as stated above.
Next lever: profile inside one 9.6ms restore call to split the ~46-column
fixed fan cost from delta-insensitive repair work. Reproduce:
`TRAIL_PROF=1 SEMPER_PROF=1 sundance-smt --infer-triggers <file>`.

### The inside-one-restore profile (the named next lever, answered)

Per-member and per-cache probes (`SEMPER_RESTORE_PROF`, sequential path) on
the uncapped cyclic_scheduler.3 run:

- 98% of restore is ONE member: the node store (885.3ms of 911.7ms; classes
  6.2ms, ops 12.3ms, everything else microseconds). The 46-column fan and the
  Vec columns are not the cost; a dirty-member skip would recover about 2%.
- Inside the node store, two hashcons caches hold it all: plain2 787.6ms and
  plain1 96.5ms (the binary and unary node caches; every other part is
  microseconds).
- Inside the caches: the arena suffix is EMPTY on every restore (suffix = 0:
  EUF search interns terms at level 0 and only merges afterwards). The whole
  cost is RE-KEY repair: 312,903 dirty re-keys summed, 147 of 206 index
  rebuilds forced by the dirty-list budget overflowing, and the rebuild path
  re-reads and re-hashes the entire live arena (1,020,417 inserts summed,
  about 800ns each with the arena read).

So the undo-trail gap is, concretely, the hashcons index repair strategy on
re-key-heavy backtracks. The direction chosen (additive, per the repo
doctrine): a new `DiffStore` (`TrailStore`, exact-event tracking, `VecT`
alias) rather than converting the existing cache repair in place; the cache
index's own adoption of exact-event undo is a follow-up decision once the
container-level mode exists.

### The hint index: what the re-key cost actually was, and its removal

Two intermediate designs fell to measurement before the fix landed; both are
recorded because their numbers redirect the diagnosis.

**Arena-derived pending set (superseded, numbers kept).** The first rewrite
deleted the caches' dirty list, budget and overflow flag and read the re-key
set from the node arena's own diff log at restore
(`VecI::pending_restore_indices`, containers commit `dfd7e85`): first-write-
wins capture already records, deduplicated per frame, exactly the slots a
restore rolls back. Per-phase timing on the cyclic_scheduler.3 run then
isolated the remaining 872ms: the arena rollback itself is 76 microseconds at
11,678 nodes (the verified Vec was never the cost), the pending materialization
1.6ms, and 703ms sat in the re-insert/rebuild phase of one cache (plain2,
K=2). The pending counts also corrected the earlier dirty-list picture: about
7,900 to 10,900 distinct re-keyed slots per restore against saved_len 11,678,
so on this workload the re-key delta IS a large fraction of live and no
incremental-vs-rebuild policy can save the fingerprint pass.

**The measured pathology is neither hashing nor rebuild size.** An isolated
rebuild of the same shape (11,678 binary nodes, all-distinct content) costs
3ns per insert; the in-situ rebuild costs 1.5 microseconds per insert and a
warm back-to-back second rebuild still 9ms. The difference is content: after
EUF merge waves the live arena degenerates to 14 DISTINCT fingerprints across
11,678 nodes (largest cluster 3,773 nodes of byte-identical op+children;
regenerated by the since-removed SEMPER_CACHE_DIAG probes). Congruent
duplicates all hash to the same slot, hashbrown insertion into a same-hash
cluster of size m walks O(m) control bytes, and a rebuild over clusters is
O(sum of m squared): 14 to 18ms per rebuild, 98 rebuilds, 703ms. The old
dirty-walk paid the same cluster scans per entry, which is where the earlier
"about 800ns each" figure came from.

**The fix: the index is now a hint cache, and restore does no index work.**
`egraph::caches` replaced the exact one-entry-per-node table with
`fingerprint -> bucket of local ids` where an entry is a HINT: a probe
validates each candidate against the arena's current content (the content
compare it always did), so a stale hint is skipped, never wrong. Interning
and recanonize push one hint in O(1) with no duplicate scan; nothing ever
removes a hint on re-key. Restore rolls back the arena and child pool and
touches the index NOT AT ALL: the rollback itself revalidates every pre-mark
hint and invalidates every post-mark one, and truncated ids fail the probe's
bounds check. Completeness (every live node's content findable) holds because
a node's current content always had a hint pushed when it was written, and
hints are never removed; the restore-time debug oracle asserts exactly that
(`index_is_complete`, replacing `index_matches_rebuild`, whose one-entry-per-
node invariant no longer exists). Compaction (amortized, on bucket growth)
may only drop bounds-dead and duplicate ids: a content-stale hint must
survive because a later restore revives it. The recanonize collision probe
excludes the node's own id, because a node that oscillates back to earlier
content has a valid self-hint that is not a collision. The insert cluster
walk disappears with the same stroke: a congruent cluster is one bucket
pushed in O(1), which also removes the O(cluster) forward-path probe chains.

Measured on the two backtrack-heavy instances (TRAIL_PROF/SEMPER_PROF,
release, --infer-triggers):

| instance | restore before | restore after | per backtrack after | stock per backtrack | wall before | wall after | stock wall |
|---|---|---|---|---|---|---|---|
| QF_UF_cyclic_scheduler.3 | 949ms / 80 calls | 25.4ms (37x) | 271us | 64us | 3.19s | 0.75s | 0.16s |
| QF_UF_reader_writer.3 | 724ms / 99 | 35.9ms (20x) | 362us | 156us | 3.13s | 1.18s | 0.20s |

The per-backtrack gap against the stock undo trail closed from about 150x
and 46x to 4.2x and 2.3x, and restore fell from 28% of semper's wall to
about 3%; the remaining wall gap is search-side. Both regimes get the same
code path: SMT backtracking pays no re-key repair, and EqSat pays no per-map
capture discipline at all, because the map is no longer semi-persistent
state, it is a derived cache over the verified semi-persistent arena.
`pending_restore_indices` stays in the containers as a general map-repair
enabler for exact indexes; the caches no longer call it.

**A latent explanation defect surfaced by the partner change (fixed,
`4819d7d`).** The hint probe returns a different congruent partner than the
exact table's probe-chain order did, and on
`edge_cases/boolean_backtracking.smt2` (a Boolean child oscillating across
backtracks) that exposed unbounded growth in `explain_deep`: a congruence
edge's premises are the two nodes' ORIGINAL children, whose present equality
can route through the very edge the collision produced, and the expansion
loop had no record of pairs already expanded, so it re-emitted the same
steps forever (measured past 2 million steps and 16 GB before the kill). The
fix memoizes congruence expansion per (node_a, node_b) pair; the step
closure is unchanged because a repeated premise pair contributes nothing.
Nothing in the pre-hint design excluded this cycle; the partner order just
never produced it on this corpus.

**EqSat scale forced the entry back to 8 bytes (the packed `HintSlot`).**
The first hint representation stored an inline SmallVec bucket per
fingerprint: a 32-byte map entry against the retired exact table's 8. On the
Criterion corpus against `main` (shared baseline `mainbase`,
`cargo bench -p semi-persistent-egraph --bench corpus`), that regressed
math-microbenchmark +9 to +12% in every configuration while the saturation
trajectory stayed bit-identical (equal node totals 1,233,013/1,248,629 and
equal recanonize/collision counts 23,860/18,483 across both trees), and no
cache function exceeded ~5% of samples: the cost was the table's 4x cache
footprint taxing every probe, invisible on the 11k-node SMT tables that fit
in L2. Compaction thresholds (64 vs 8) and frameless content-validating
compaction moved nothing, which is what pointed away from stale-hint scans.
The fix packs the map value to 4 bytes: MSB clear IS the single hinted id
(ids are 31-bit by the define_id31 doctrine), MSB set indexes a spill table
of buckets for fingerprints with two or more hinted ids. After it,
math-microbenchmark reads "no change detected" against main (three of four
configurations p > 0.05, the fourth +0.46%), herbie is about +1%, and the
corpus median sits near +1% with the sub-millisecond micro-rows oscillating
plus or minus a few percent between runs (the bench doc's own host-state
caveat; math-add-ac semi measured -3.3% and +5.9% in successive runs).

Gates at the change: e-graph suite 1257 tests, 0 failures, plain and
SEMPER_COMPRESS=auto, with the completeness oracle active on every restore
in debug; sundance's own regression suite (semper backend) 2 of 2; and the
full 438-file corpus swept stock vs semper (35s hard cap per run):
ZERO sat/unsat disagreements outside the `--arithmetic none` configuration
difference (39 arithmetic instances legitimately flip unsat to sat with the
theory disabled), and every instance semper leaves unanswered is unanswered
or unknown under stock too. Regenerate: `sweep3c.sh` against
`tests/regression/smt_files`. The SMT restore numbers are unchanged by the
packed slot (cyclic_scheduler.3 restore 25.4ms, boolean_backtracking
unsat).

### The forward path, and the VecT-in-sundance experiment (closed, negative)

After the hint index, the residual SMT wall gap was forward-path. Leaf
sampling found 60% of CPU in two per-event O(#ops) registry scans of the
group-completion machinery, on instances that declare no group operators:
`inverse_cancel_repair`'s `:inverse` precheck once per repair round, and the
completion loop's `merged_is_unit` scan once per merge. Replacing both with
map-population reads (commit `074113f`) took cyclic_scheduler.3 from 0.75s
to 0.36s wall (stock 0.16s) and reader_writer.3 from 1.18s to 0.31s (stock
0.20s); the profile is flat afterwards, no function above 10% of leaf
samples. The per-backtrack gap against the stock undo trail stands at about
2.3x and 1.6x total wall.

**VecT columns in the SMT backend: measured, no effect.** The trail
hypothesis (chronological capture on the hot columns closes the remaining
gap) was tested by switching every cache arena column (fixed and variable
node arenas, the child pool, the literal arena) from `VecI` to `VecT` and
rerunning the two profile instances idle: restore 24.1ms vs 25.4ms and wall
0.36s vs 0.36s on cyclic_scheduler.3, wall 0.31s vs 0.31s on
reader_writer.3. Flat within noise, consistent with capture branches never
appearing in any profile round. The experiment is reverted; `VecT` remains
the verified chronological-capture store with this revisit trigger: a
profile that shows capture-branch or frame-finalization cost, or a workload
whose write set per frame is large enough that the unique discipline's flag
maintenance measures. The store-selection interface (frame vs trail diffs
from the command line) remains motivated by the EqSat/SMT trade-off, not by
this instance family.

### Runtime store selection: one interface over frame diffs and the trail

The discipline moved from the type level to the instance level so it can be
a command-line choice. `DiffStore::unique_capture_spec` and
`needs_replayed_indices_spec` are now instance spec functions, and every
mutating trait method carries a constancy ensures (the discipline is chosen
at construction and immutable); definitional broadcast lemmas pin each base
store's constant answers, so the three existing stores prove the new
contract without body changes. `DynStore` is the verified dispatching enum
over Inline/Parallel/Trail (per-arm delegation; ghost-bridge proofs connect
the enum's spec views to the inner store's for the quantified-precondition
methods), `VecD` the runtime-selected column
(`VecD::new_kind(StoreKind)`), and the levers are `SEMPER_DIFF` plus
`--diff-mode inline|parallel|trail` on both the egraph CLI and
`sundance-smt`. The e-graph's cache arena columns construct through the
lever; history columns stay `VecI`.

Gates: `cargo verus verify` 2083 verified 0 errors; containers suite 206
tests 0 failures including a three-kind `VecD` differential (4000 random
ops in lockstep against an oracle across marks, deep restores and duplicate
writes); e-graph suite 1257 tests 0 failures in each of inline, trail, and
trail with SEMPER_COMPRESS=auto. Cost of the indirection: one predicted
discriminant branch per store operation; the three modes measure
statistically identical on cyclic_scheduler.3 (0.37 to 0.38s wall, trail
restore 22.9ms vs inline 23.7ms), consistent with the closed VecT
experiment above: on this corpus the discipline choice is not the
bottleneck, and the selectable interface exists for the workloads where it
will be (the EqSat deep-state trade vs the write-hot trade), not because
this instance family demanded it.

**Trail-mode corpus gate, and a pre-existing semper-arithmetic defect
surfaced by gating.** The full 438-file corpus swept stock vs semper with
`--diff-mode trail`: zero non-arithmetic sat/unsat disagreements and no
instance where trail-mode semper goes unanswered while stock answers
(`sweep-trail.sh`). Separately, running sundance's own `regression_test`
under the `semper-egraph` feature with DEFAULT (Z3) arithmetic fails 40
arithmetic instances (`expected unsat, got sat`), deterministically, at
every commit of this campaign INCLUDING the pre-campaign goal-close state
(bisected to `ba1a908^` and beyond on `define_fun/arithmetic.smt2`): the
semper backend's Nelson-Oppen arithmetic integration is broken
independently of this campaign's changes, which is consistent with every
measurement protocol here having disabled arithmetic (`--arithmetic none`)
from the first sweep onward. One earlier 2-of-2 pass of that harness ran
against a never-committed intermediate cache variant and is attributed to
ordering sensitivity of these fragile instances, not correctness. The
maintained gate (default features, basic backend) passes 2 of 2. Filed as
its own follow-up: the semper-arithmetic seam, out of scope for the store
selection work.

### The profile after the campaign: where the time actually goes

Leaf profiling (`sample`, release) on the two regimes, after the hint index,
the O(1) prechecks and the store-selection work.

**EqSat** (math-microbenchmark, 1.23M nodes; our code is about 95% of the
process):

| self | function |
|---|---|
| 16.7% | `UnionFind::find` |
| 9.4% | `FixedArityCache::probe_hints` |
| 9.1% | `LeapfrogJoin::search` |
| 6.2% | `ListArena::try_prepend` |
| 5.8% | `child_at` |
| 5.4% | `ematch::leapfrog_join` |

Inclusive: rule application 47%, e-matching 30%, evaluation 26%. `find` is
the top cost because path compression writes go through the TRACKED
`parent.set_index`: every compressed edge pays a capture. That is inherent
(an uncaptured compression write would corrupt the partition after a restore
crossing the union that justified it), so the lever is fewer writes, not
cheaper writes: PATH HALVING is the recorded candidate.

`probe_hints` was measured before being optimized, and the measurement
killed the obvious idea: over 2,004,019 probes the bucket scan averages
**1.19 entries** with 5,456 buckets longer than 8. Stale-hint accumulation is
therefore NOT the cost and move-to-front would buy nothing; the 9.4% is
fingerprint computation plus the map lookup plus one content compare, so the
only real lever is caching fingerprints rather than recomputing them.

**SMT, backtrack-heavy** (`eq_diamond18`, 133,961 marks and 133,403
restores - two orders of magnitude more version churn than the
cyclic_scheduler instances, and the right benchmark for this engine):

| self | function |
|---|---|
| 36.0% | `CaDiCaL::Internal::propagate` (the SAT solver, common to both backends) |
| ~10% | allocator (`xzm_free`, `xzm_realloc`, `malloc_zone_realloc`, `memmove`) |
| 3.4% | `probe_hints` (+ its closure) |
| 2.8% | `assert_equal` |
| 1.0% | `merge_with` |

`UnionFind::find` does NOT appear in the top fourteen here. So the two EqSat
levers do not transfer: path halving is an EqSat optimization, and
fingerprint caching is worth about 3% on this SMT profile. What the profile
does surface is mark+restore at 1.75s of 8.35s wall (21%) and allocator
churn at about 10%: those are the SMT levers, and neither was visible on the
cyclic_scheduler instances whose restores number in the dozens.

### The trail store's first measured win

`--diff-mode trail` against the default frame-diff discipline on
`eq_diamond18` (two runs each, idle):

| | restore total | wall |
|---|---|---|
| inline (frame diffs) | 1.400s / 133,403 calls | 8.35s |
| trail (chronological) | 1.243s (**11% faster**) | 8.17s (2% faster) |

This is the first workload where `VecT` pays, and it is exactly the shape the
store was built for: version churn so high that the per-write flag check and
the per-frame flag maintenance outweigh the bounded-log benefit. Mark is
unchanged (0.350s vs 0.356s): at 46 columns the mark cost is per-column frame
push, not flag clearing. Stock on the same instance is 5.70s, so semper is
1.47x there (against 2.3x and 1.6x on the low-restore instances), and
mark+restore is where the difference lives. The earlier VecT-is-flat result
stands for the cyclic_scheduler/reader_writer family and is now qualified
rather than retracted: the discipline choice is measurable exactly when
restores are frequent, which is what the runtime `--diff-mode` selector is
for.
