# Goal: complete the remaining semi-persistence proofs

## Objective and baseline

Verify that the actual supported public execution paths preserve semi-persistence
through arbitrary legal sequences of mutation, mark, rollover and restore, for
every supported DiffStore discipline and the derived and parallel containers.
Completion requires concrete implementations satisfying the end-to-end theorem;
a conditional theorem, isolated helper proofs or passing tests alone is insufficient.

This is the acceptance checklist for the remaining work. Follow the architecture
in [three-tier-top-down-proof-engineering.md](three-tier-top-down-proof-engineering.md)
and retain the full scope of
[all-tier-semi-persistence-goal.md](all-tier-semi-persistence-goal.md).

Baseline: local commit `d191c4a`. Conditional composition and concrete all-tier
restore, including Cold survivor promotion to either writable tier, verify.
Default and literal-types runs each report 2373 verified obligations and zero
errors. Mutation/mark, migration/policy, complete production interface
instantiation, and derived/parallel closure remain incomplete.

## Constraints applying to every step

- Preserve existing code and verified proofs. Reuse matching contracts, adapt
  insufficient contracts, and replace incompatible proofs only after their
  replacements verify. Do not weaken the top-level theorem to fit a leaf proof.
- Use saved length plus an earliest-capture map derived from physical storage
  as the shared frame meaning. Preserve existing snapshots and canonical
  `full_trail`/`trail_frames` contracts; add no persistent ghost history.
- Add no assumptions, admits, axioms or trusted wrappers to discharge obligations.
  Do not raise solver limits to bypass proof decomposition.
- Preserve runtime batching, direct Cold replay, Trail duplicate appends, public
  behavior and payload capabilities. Add no runtime map lookup, extra buffer or
  slower traversal solely to simplify verification.
- Keep `containers/` unchanged as the differential oracle. Record any executable
  changes and their performance implications; do not claim performance parity
  without evidence.
- Reverify conditional composition whenever an interface changes. Commit verified
  milestones locally; do not push to origin.

## 1. General mixed-tier mutation and mark

### Goal

Prove constructors, capture, set, push, pop, regrowth and mark against the shared
invariants for Trail-only, Hot-only and mixed histories, using the actual
DiffStore methods and instance-selected discipline.

### Acceptance criteria

- [ ] Constructors establish the public invariant, specified live contents and
  empty logical history, including supported untracked configurations.
- [ ] Actual capture paths establish first-capture semantics. Trail retains
  physical duplicates while the earliest capture wins; Hot remains unique and
  capture flags agree with active-map membership for live indices.
- [ ] Set and pop capture an active saved-domain cell before overwriting or
  removing it when required. Their return values and live-state effects are
  exact; snapshots, older frame meanings and canonical history remain valid.
- [ ] Push and regrowth preserve saved maps. Reentering a saved domain restores
  capture membership from the existing saved value, without capturing the newly
  pushed value. Empty pop and zero-depth behavior satisfy their public contracts.
- [ ] Mark preserves live contents, appends exactly one snapshot and empty frame,
  seals the former active frame and opens the correct writable tier. Its actual
  rollover calls are connected to Step 2's checked contracts.
- [ ] All supported stores (`TrailStore`, `ParallelStore`, `InlineStore` and each
  `DynStore` variant) preserve their capture discipline and clearing protocol
  through the methods used by these paths. A caller bypassing `DiffStore::capture`
  proves its own effect rather than borrowing that method's contract.
- [ ] Mixed-history proofs require the general public invariant, not a hidden
  Hot-only premise. Existing specialized Hot proofs remain available.
- [ ] Bounds, tracking/depth guards, error precedence and unchanged-state rejection
  effects are preserved. Mutation and mark retain their existing payload bounds;
  restoration's `Default` requirement is not imposed on them.
- [ ] The relevant trusted mutation/mark bodies are replaced by checked bodies,
  with no equivalent trust moved into a callee or wrapper.

### Evidence required to close the step

Record the concrete method-to-contract mapping, checked all-tier preservation
lemmas, targeted verifier results and full default/literal-types verification.
Include proof coverage of repeated writes, pop below saved length, regrowth,
empty frames and mutation after restore. Mark remains pending until its actual
policy dependencies are discharged in Step 2.

## 2. Conversions and rollover policies

### Goal

Prove that every supported representation conversion and every legal configured,
forced or adaptive rollover sequence preserves logical history and live contents.

### Acceptance criteria

- [ ] Trail deduplication retains the earliest value per index; Hot sorting
  preserves the unique map; Hot-to-Cold encoding preserves that map and saved
  length. Equality includes both values and absence of captures.
- [ ] Existing checked Hot-to-Trail and Cold-to-Hot/Trail reopening proofs are
  reused and connected to the same contracts. Cold reopening selects its
  destination from the DiffStore discipline.
- [ ] Empty frames survive each applicable conversion. Cold runs have positive
  lengths, disjoint saved-domain extents, valid payload ranges and safe arithmetic.
  Persistent Hot frames need not be sorted.
- [ ] Pool builders prove exact appended segments, unchanged destination prefixes,
  source framing and exact offsets. Completed migrations prove source retirement,
  rebasing, frame identity/order and the restored global partition.
- [ ] Every actual policy selector supplies legal source frames and counts, excludes
  the active writable frame and respects chronological order. Adaptive plan
  entries correspond exactly to the source frames they claim to represent.
- [ ] An induction over arbitrary legal migration sequences applies to actual
  policy execution and preserves every frame's saved length/map, snapshots, live
  contents, canonical history and the invariants required by the next step.
  Different physical layouts need not be equal.
- [ ] Configured, forced, adaptive and mark-triggered paths use checked migration
  implementations. No semantic conversion or policy-execution obligation remains
  hidden in a trusted fallback. Capacity-only helpers have explicit unchanged-
  meaning contracts and separately documented trust, if any.

### Evidence required to close the step

Provide a conversion/policy coverage table naming concrete functions and proofs,
targeted and full verifier results, and the differential policy matrix results.
Proof coverage includes duplicates, empty and gapped frames, nonempty destination
prefixes and different legal migration orders. Tests supplement the general
sequence theorem; they do not replace it.

## 3. Complete concrete end-to-end composition

### Goal

Instantiate every provisional interface with the production implementation and
connect the full public-operation theorem to actual runtime dispatch.

### Acceptance criteria

- [ ] Every provisional method has a concrete implementation, checked precondition
  supplier, checked postcondition and identified next consumer. The inventory
  has no pending semantic obligations or circular assumptions.
- [ ] Production projections describe actual physical pools, snapshot history,
  capture state and canonical history. Equal reconstructed contents are never
  used as an unproved substitute for equal capture domains.
- [ ] Public boundaries recover the complete existing invariant, including
  canonical reconstruction. Resize/replay and conversion intermediates use
  explicit phase predicates rather than assuming full well-formedness.
- [ ] The checked production composition covers constructor, set, push/pop,
  regrowth, mark, any legal rollover sequence and restore, with arbitrary legal
  interleavings, both capture disciplines and every survivor tier.
- [ ] For a publicly valid target `k`, restore yields exactly the old snapshot
  `S[k]`, depth `k`, snapshot prefix `S[..k]` and logical-frame prefix `H[..k]`.
  Canonical retirement retains its required exact prefix; survivor movement
  preserves frame meaning and capture rebuilding enables subsequent mutation.
- [ ] Actual batched pair replay and direct Cold replay satisfy the theorem for
  arbitrary saved-length zigzags and resize filler values. The induction uses
  a local frozen pre-state, without new persistent history or changed batching.
- [ ] Public token validity, guard ordering, returned errors and rejection framing
  remain intact. Structural frame bounds do not replace public token validity,
  and mark does not promise stronger token validity than its existing contract.
- [ ] Verified sequence consequences include restore followed by mutation and
  another older restore, repeated writes, shrink/regrowth, empty frames and
  zero-depth restore. Supported untracked public paths retain their behavior.
- [ ] Both the complete conditional theorem and its production instantiation
  verify. The mathematical witness is retained as consistency evidence, not
  presented as the concrete implementation.

### Evidence required to close the step

Publish a completed interface inventory and a traceable public API-to-proof
dependency map, together with full verifier results. No supported Vec dispatch
branch may rely on an unresolved provisional persistence contract.

## 4. Derived containers, parallel paths and final audit

### Goal

Establish the corresponding public persistence contracts for all containers in
the original scope, then produce reproducible verification, regression and trust
evidence for the final source revision.

### Acceptance criteria

- [ ] Audit and verify SparseSet, CircularList, ListArena, UnionFind, BPlusTreeSet,
  EClasses, SpMap and AppendOnlyVec, plus relevant shared-history/group wrappers.
  Document any supporting structure with no independent mark/restore API and
  verify the obligations of its actual consumers rather than silently omitting it.
- [ ] Each applicable constructor, mutation, mark and restore path preserves its
  container invariant and exact logical contents. Restore exports depth and
  retained archive-prefix effects for all component columns, not only a selected
  root or primary vector.
- [ ] Component marks remain synchronized. Fallible success and rejection branches
  have sufficient contents/history contracts; existing token and error semantics
  are preserved.
- [ ] Sequential and parallel group restore establish member contents and archive
  effects as well as depth/count agreement. Actual fan-out implementations and
  their ordering/ownership obligations are discharged, without a trusted semantic
  parallel-restore boundary.
- [ ] Read-only persistence consumers, including pending-restore-index helpers,
  have the guarantees their callers require and those guarantees are checked.
- [ ] Every remaining trusted body or axiom is inventoried with its purpose and
  callers. No unresolved persistence obligation is labeled allocator or diagnostic
  trust. Source counts, feature-gated counts, CI expectations and trust documents
  agree; no new semantic trust was introduced.
- [ ] On the final source revision, full default and literal-types Verus runs,
  conditional composition, required feature/runtime tests, differential policy
  tests, consumer tests, formatting and whitespace checks all pass. Record commands,
  toolchain, results and revision, including ignored tests.
- [ ] Run the conformance benchmarks on the final revision and validate that the
  verified implementation is not slower than the legacy `containers/`
  implementation on comparable workloads, within a documented measurement-noise
  tolerance. This is a required completion gate, not an optional observation.
  Follow the performance protocol below; investigate and fix reproducible
  regressions before declaring completion.
- [x] Reconcile the known partial-API CI discrepancy (40 unlisted functions at the
  baseline) through an explicit contract/exposure review and justified corrections.
  Do not bulk-allowlist entries to hide it. If it remains, report it as an open
  final-audit item and do not claim all CI checks pass. (Done 2026-09-17,
  extended goal 5: 0 partial public functions, allowlist empty, no entry ever
  added — `doc/future/total-api-plan.md` "Status".)
- [ ] Documentation reflects the completed proofs and any justified foundational
  trust. Verify `containers/` is unchanged, commit the final verified milestone
  locally and leave all work unpushed.

### Evidence required to close the step

Provide a per-container contract/verification matrix, final trust inventory and
gate report, performance comparison report with raw benchmark artifacts, and the
signed local commit identifying the verified result.

### Final performance validation protocol

Use [conformance-performance-inventory.md](conformance-performance-inventory.md)
as the initial target inventory, and recheck it against the final source. Its
coverage review does not replace measurement or establish parity.

1. Inventory all Criterion targets in `containers-conformance/Cargo.toml` and run
   the applicable legacy-versus-verified comparisons. Include tracked-vector,
   retained-container, nested-mark, eager-write, EClasses and parallel-frame
   workloads where paired comparisons exist. Cover mutation, mark, shallow/deep
   restore and representative end-to-end operation sequences. Record all
   exclusions and coverage gaps; do not select only favorable benchmarks.
2. Use the unchanged legacy implementation as the primary comparison. Match
   logical workload, inputs/seeds, payload/index types and comparable settings.
   Record implementation/configuration differences that affect interpretation.
   Where legacy lacks an equivalent tier operation, report that explicitly and
   compare the final verified code with checkpoint `d191c4a` on the corresponding
   three-tier workload, including rollover and Cold-survivor promotion. This
   supplementary comparison does not establish legacy parity for that operation.
3. Run optimized benchmarks on the same machine with the same toolchain, build
   flags and features, under comparable system load. Use warmup and repeated
   measurements, retain Criterion estimates/confidence intervals, and repeat
   suspicious or inconclusive results. Record hardware, software, commands,
   revisions and benchmark parameters so the comparison is reproducible.
4. Before evaluating results, document the noise tolerance and statistical
   decision rule, based on repeatability measurements or the project's existing
   benchmark policy. Do not widen the tolerance after seeing a regression.
   For each paired case report verified/legacy time ratio, uncertainty and
   pass/regression/inconclusive status. Insufficient precision or merely failing
   to detect a slowdown is not evidence of parity; collect enough measurements
   to bound the slowdown within the declared tolerance.
5. Require every applicable paired case to pass. Aggregate speedups cannot hide
   an individual regression. Investigate and fix reproducible slowdowns without
   weakening proofs or altering the legacy oracle, then rerun affected correctness
   gates and benchmarks. Unresolved regressions or inconclusive required cases
   keep this criterion open; report them explicitly rather than claiming the
   verified code is not slower.

## Completion rule and progress reporting

All four steps must meet their acceptance criteria. Steps 1 and 2 may develop
incrementally against explicit contracts, but neither is closed while one of its
runtime dependencies remains unproved. Step 3 integrates their concrete results;
Step 4 closes the original broader scope.

For each criterion, record the source theorem or implementation, verification
evidence and any remaining dependency before marking it complete. Report progress
by discharged obligations and open dependencies, not by raw verifier counts or
an unsupported percentage. Existing baseline proofs count when their contracts
meet the criterion; they do not need to be rewritten.
