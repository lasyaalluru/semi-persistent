# Three-tier semi-persistence: top-down proof engineering

## Main-agent goal

> Change the proof workflow to top-down. Read `containers-verus/doc/tasks/three-tier-top-down-proof-engineering.md`. First verify a conditional end-to-end semi-persistence theorem over explicit contracts for Trail/Hot/Cold conversion, direct replay, resizing, history retirement, survivor reopening, and capture rebuilding. Include set, push/pop with shrink/regrowth, mark, restore, and mutation followed by another restore. Derive and revise helper contracts from this composition before resuming leaf implementation proofs. Use one shared per-frame meaning `(saved_len, earliest-capture map)`; Trail duplicates are ignored only by the ghost abstraction, Hot tags correspond to map membership, and Cold preserves that map through run encoding. Preserve actual batched replay and public token/content/prefix contracts. Keep provisional assumptions isolated and visibly conditional, then discharge every concrete implementation against the resulting interfaces. Retain the complete all-tier and derived/parallel-container goal; a conditional theorem is the first milestone, not completion. Preserve existing work, add no runtime ghost bookkeeping, and do not push to origin.

## 1. Decision and scope

This document records the user's direction from the side conversation: prove
the top of the call graph first. The previous bottom-up workflow produced
contracts fitted to individual implementations without first demonstrating
that they compose into the complete public theorem.

The next milestone is a verifier-checked, conditional end-to-end theorem and
its contract inventory. Freeze those interfaces only after their composition
works. Then prove the concrete implementations against them. Existing proofs
are reusable evidence, not constraints on the shape of the interfaces.

This document is a proposed proof architecture, not a report that its
interfaces are implemented or discharged. Source in the shared workspace may
be changing concurrently; inspect it before implementation. Preserve the
original completion objective in [all-tier-semi-persistence-goal.md](all-tier-semi-persistence-goal.md).

The scope includes all supported store disciplines, all three physical tiers,
configured/forced/adaptive migrations, empty frames, arbitrary saved-length
zigzags, mutation after restore, and eventual derived/parallel-container
composition. Preserve the `containers/` differential oracle and runtime
batching. No push to origin is authorized.

## 2. One logical frame meaning

Use the following mathematical notation; it is not a requirement to add fields:

```text
V       : Seq<T>                         live contents
S       : Seq<Seq<T>>                    marked snapshots
H       : Seq<FrameMeaning>              retained logical frames
H[f]    = (L[f], M[f])
L[f]    : nat                           saved length
M[f]    : finite Map<nat, T>             saved captures
Above(f)= S[f+1], or V for the newest frame
```

A `Set<(T, I)>` is equivalent if it is functional in its index coordinate.
Numeric spec indices simplify the common model; connect runtime `I` through
`as_nat()` and its representability/injectivity lemmas.

Every frame satisfies:

```text
L[f] = S[f].len()
dom(M[f]) is contained in [0, L[f])

for every i < L[f]:
    i in dom(M[f])  ==> M[f][i] = S[f][i]
    i not in dom(M[f]) ==> i < Above(f).len()
                           and Above(f)[i] = S[f][i]
```

Consequently, every saved-domain cell missing from the newer layer is captured.
Saved lengths need not be monotone. Physical pool offsets have separate
monotonicity properties; never confuse these two kinds of coordinate.

### Representation abstraction

```text
abstract_trail(f) = earliest chronological entry per index in frame f
abstract_hot(f)   = unique entries in frame f
abstract_cold(f)  = values covered by frame f's runs

abstract_tier(f) = M[f]
```

This is equality of partial maps, including their domains. Merely proving that
two encodings reconstruct the same snapshot is weaker: it does not establish
capture membership or justify reopening the frame for future writes.

Trail physically appends duplicates. Its first-write-wins map update occurs
entirely in ghost/spec code; no runtime lookup or deduplication is introduced.
The replay proof establishes that the earliest physical entry is written last.

Use one logical map per frame, not one maintained copy per representation.
A derived map view and local ghost pre-states can supply this interface without
new persistent ghost fields. If explicit ghost witnesses are useful, prove
their correspondence to physical storage on every operation; they cannot be
an independently assumed source of truth.

Existing `snapshots`, `full_trail`, and `trail_frames` may remain. Record their
relationship to the common frame meaning and their preservation obligations.
Do not discard existing public or canonical-history contracts to simplify the
new theorem. Inert `diff_log` is not reconstruction authority.

## 3. Top-level theorems to establish first

Define `Stable` as the conjunction of the boundaries in section 4. Prove these
theorems using only declared interfaces, with concrete leaf bodies unavailable
to the proof:

| Operation | Abstract postcondition, in addition to `Stable` |
|---|---|
| Constructor | Specified live contents; empty `H` and `S` |
| Set at valid i | `V' = V.update(i,v)`; `S' = S`; only active map may gain a first capture |
| Push | `V' = V.push(v)`; `S' = S`; maps unchanged |
| Pop | Empty case unchanged; otherwise return last value and remove it; preserve snapshots with any necessary first capture |
| Mark | `S' = S.push(V)`; `H' = H.push((V.len(), empty))`; live unchanged |
| Sealed-frame migration | `H' = H`, `S' = S`, `V' = V` |
| Restore valid k | `V' = old(S[k])`, `S' = old(S[..k])`, `H' = old(H[..k])`, `depth' = k` |
| Invalid fallible request | No observable content/history mutation; retain the public error contract |

Restore's history equality concerns frame meaning. Survivor reopening may
change physical storage while preserving that equality.

Prove closure under legal operation sequences, not just a single restore.
At minimum, instantiate the composition with:

1. Mark, repeated writes to one index, mark, more writes, restore, write again,
   restore an older retained token.
2. Pop below a saved length, push back into that domain, then restore.
3. Multiple frames with zigzag saved lengths, forcing restore to grow live.
4. Empty frames passing through conversions and reopening.
5. Both capture disciplines and every possible survivor tier.
6. Sealed migrations selected by each policy family.

These are proof-composition obligations; runtime tests supplement them.
Carry existing token validity rules separately from structural frame bounds.
Do not replace valid-token preconditions with merely `k < depth` at the public
boundary or invent new genealogy semantics.

## 4. Invariant boundaries

| Boundary | Facts it exposes |
|---|---|
| `StoreOK` | Valid data/tag representation, lengths and index limits, stable store discipline/protocol |
| `LayoutOK` | Valid frame/pool ranges, adjacency, Cold payload bounds, Hot uniqueness, Cold disjointness |
| `PartitionOK` | Headers correspond exactly once to frames; oldest-to-newest order Cold, Hot, Trail; lengths match snapshots; empty headers survive |
| `MeaningOK` | Each physical frame abstracts to its shared map |
| `SnapshotsOK` | Captured-or-inherited contract of section 2 |
| `WritableOK` | Newest frame is in the selected ingress tier; correct active saved length; all other frames sealed |
| `CaptureOK` | For present active-domain indices, captured iff map membership; no stray flags; correct zero-depth state |
| `CanonicalOK` | Existing ghost history/boundaries and compatibility obligations remain valid |

For unique capture, the capture bridge is a runtime tag/bitmap relation. For
TrailStore, the uniform captured interface is ghost state, not runtime flags.
An index absent from live can remain in the map without a corresponding live
tag. Restoring or pushing that index requires the appropriate flag treatment.

`Stable` holds at public boundaries. It need not hold after clearing tags,
resizing, during replay, or halfway through a representation move. Give each
such intermediate state an explicit predicate instead of repeatedly attempting
to re-establish `Stable`.

## 5. Contract inventory for mutation and marking

Every row also preserves snapshots, older frame meanings, and unrelated state
unless its stated effect says otherwise.

Define `capture_first(M,i,v)` to return `M` when i is present, and insert i->v
otherwise.

| Helper family | Requires | Ensures |
|---|---|---|
| Trail append | Valid writable Trail range; i present and below active saved length | Physical append `(V[i],i)`; new abstraction `capture_first(M,i,V[i])`; live unchanged |
| Hot capture | Valid unique range and capture bridge; i present in saved domain | Append only if tag clear; same `capture_first` update; tag set; uniqueness and live preserved |
| Raw write | `StoreOK`, valid index | Exact live update; valid store; tracked tag preservation required by caller |
| Composed set | `Stable`, valid index | Capture when needed, then write; exact public set effect and `Stable` |
| Raw pop | Valid nonempty store | Remove last live cell and its flag; return old value |
| Composed pop | `Stable` | Capture disappearing active-domain cell first; exact public pop effect and `Stable` |
| Raw push | Valid store and representable new length | Append value; new flag clear; preserve prefix |
| Composed push/regrowth | `Stable`, representable new length | Maps unchanged; if reentering active saved domain, coverage supplies prior capture and Hot flag is restored; `Stable` |
| Prepare mark | Valid store; sparse-clear input covers every set flag | All flags clear; live/history unchanged |
| Seal old/open new frame | Valid history, clear flags, capacity/count bounds | Old top sealed; append empty frame and snapshot of live; active length/ownership established; `Stable` |
| Mark wrapper | `Stable`, public guards | Compose preparation/opening, then eligible rollover/reclamation; exact mark theorem |

Trail append must prove the local equation:

```text
abstract_trail(d.push((v,i))) = capture_first(abstract_trail(d), i, v)
```

Do not insert the newly pushed value into the map on regrowth. If the new index
lies below the active saved length, coverage already proves it has a saved
value from before its removal.

When marking, the old top's newer layer changes from live to the newly appended
snapshot, which equals that same live value. This is the semantic transfer
lemma. The current runtime opens the replacement writable frame before rollover;
the interface must accommodate that actual sequence.

## 6. Conversion and policy contracts

All conversions preserve `(saved_len, saved_map)` exactly, including absence.

| Local helper | Requires | Ensures |
|---|---|---|
| Trail deduplication | Valid chronological frame | Unique output representing earliest captures |
| Hot sorting | Valid unique entries | Same multiset and map; sorted result |
| Sorted Hot -> Cold | Strictly increasing indices below saved length | Valid disjoint runs and payloads; identical map/length |
| Hot -> Trail reopening | Valid unique source | Valid chronological destination; identical map/length |
| Cold -> Hot reopening | Valid runs, payload bounds/domain, representable indices | Unique destination entries; identical map/length |
| Cold -> Trail reopening | Same Cold preconditions | Valid Trail entries; identical map/length |

Cold run obligations include positive run length, index extent within saved
length, valid payload extent, and safe arithmetic. Empty frames have zero runs,
not fabricated empty runs. Persistent Hot frames need not be sorted.

Separate three levels of interface:

1. **Local transform:** source entries/runs to destination entries/runs, proving
   the map equation and destination validity.
2. **Pool builder:** exact appended segment, unchanged old destination prefix,
   unchanged source, and exact offsets/lengths. It need not preserve the global
   header partition while source and destination coexist temporarily.
3. **Completed migration:** retire source headers/payloads, rebase remaining
   offsets, preserve chronological identity, and re-establish the container
   boundaries. For sealed migrations, preserve `Stable`, live and logical history.

For oldest-prefix migration counts, require `0 <= count <= eligible_closed`.
For adaptive precomputed plans, require each plan entry to represent the
specified source frame exactly. A length/count bound alone is insufficient.
Policy selection must exclude the active writable frame and preserve order.
Separate cost/threshold correctness from semantic preservation.

**Rollover policy composition theorem:** any legal sequence of completed
rollover operations preserves the logical ghost state `(H, S)` and live
contents `V`. Prove this by induction over the policy's execution: each step
preserves frame order, saved lengths, saved maps, snapshots, and live contents,
and establishes the representation, writable-ownership, and capture invariants
needed by the next step. Thus `G0 = G1 = ... = Gn` for `G = (H, S, V)`, regardless
of which configured, forced, or adaptive policy selected the legal sequence.
“Any order” means an order satisfying each operation's preconditions: the source
tier must exist, selected prefixes must be eligible, and the active writable
frame must remain protected. Different sequences may produce different physical
layouts; the theorem requires equal logical meaning, not commuting physical
operations. Keep the policy's legality proof separate from this shared
preservation induction.

Survivor reopening is a separate context: it starts with valid retained history
but possibly no writable ingress frame. Its postcondition establishes ownership,
with flags still clear, so capture rebuilding can follow.

## 7. Replay interfaces and the shared induction

For a fixed-length buffer B, define:

```text
Apply(M,B)[i] = if i in dom(M) then M[i] else B[i]
len(Apply(M,B)) = len(B)
```

Direct Trail/Hot/Cold replay requires a valid source representing M and a valid
destination store. It ensures exact `Apply`, unchanged buffer length, unchanged
source history, valid store, and an explicit capture-flag effect.

* Trail backward replay: the earliest entry is written last.
* Hot replay: unique entries implement M.
* Cold replay: disjoint bounded run copies implement M directly in live storage.

Replay is an application theorem, not an invertible encoding into live.
Cold replay does not first decode into Hot or Trail.

The shared frame-step theorem assumes the frame contract and agreement of B
with `Above(f)` on their shared index domain. It concludes that `Apply(M[f],B)`
agrees with `S[f]` below `min(B.len(), L[f])`.

The batched pair-range interface must expose the composition of those steps:
newest frame first, oldest frame last. Prove concatenated-range composition in
spec code; preserve the actual one-batch-per-tier runtime. Cold keeps direct run
copies. The top-level proof must call interfaces shaped like these operations,
not substitute a different runtime algorithm that is easier to prove.

## 8. Restore phase contracts

Freeze `let ghost pre = *self` before resizing. Let k be valid and
`L = pre.S[k].len()`. No persistent replay history is added.

| Phase / current helper family | Requires | Ensures needed by the next phase |
|---|---|---|
| Resize / `resize_default` | Valid store; representable L | Length L; unchanged shared prefix; grown flags clear and retained flags preserved; history unchanged; no constraint on filler values |
| Capture preparation / `runtime_begin_restore` | Resized flags come from pre-state; selected range covers every flag to clear | All-clear for non-fused protocol; live/history unchanged |
| Replay / pair batches, Cold suffix, `replay_all_tiers_checked` | Frozen valid pre-history; source still matches pre; initial shared-prefix agreement; protocol-specific flag premises | Exact `pre.S[k]`; store valid; history unchanged; all flags clear after complete replay |
| Reconstruction wrapper / `reconstruct_target_checked` | Stable pre-state, valid target | Compose resize/preparation/replay and export the preceding postcondition |
| Retirement / `truncate_restored_history_checked` | Reconstructed target; history equals pre | Exact physical/canonical prefixes; `H = pre.H[..k]`, `S = pre.S[..k]`; valid retained meaning/layout/partition; store and flags unchanged |
| Reopening / representation-specific survivor helpers | Positive retained depth; valid history; clear flags; source-tier case known | Same H/S/live; valid layout/partition; writable survivor in selected tier; flags still clear |
| Capture rebuild / `finish_survivor_checked` | Writable survivor; valid history; clear flags | Correct active length and capture bridge; no stray flags; unchanged live/history; `Stable` |
| Zero-depth finish | Empty retained history and clear flags | No active frame; empty compatibility state as required; `Stable` |
| Capacity reclamation | Valid state and allocator preconditions | All relevant sequences, maps, flags and protocols unchanged; preserve `Stable` |

For fused capture clearing, do not require a separate clearing pass. Instead,
carry the original-flag subset/coverage premise until the ingress batch clears
all flags; later replay cannot set them. Every backend's flag contract must
supply the premise of the next phase.

Replay loop/induction facts:

```text
target length L stays fixed
next-frame cursor identifies the pre-state layer
buffer agrees with that layer on their intersection
all physical source ranges still match pre
capture flags satisfy the current protocol phase
```

At target k, agreement covers the full buffer. Newly default-filled cells
cannot remain arbitrary: following the uncaptured arm cannot terminate at an
original live cell that did not exist. Some replayed frame supplies a capture.

After retirement, retained frame k-1 sees `pre.S[k]` as its newer layer both
before and after restore. Earlier frames retain their newer snapshots. This
proves snapshot preservation independently of reopening.

Exact physical-prefix equality is a retirement postcondition. Reopening may
move the newest retained frame; its map/length and all other retained meanings
remain unchanged. Do not demand unchanged survivor storage after that move.

## 9. Provisional assumptions: explicit and isolated

Prefer a generic/parametric Verus interface whose methods declare the above
contracts. Check the top-level proof for any implementation satisfying that
interface, without selecting an unproved concrete implementation. Put this
composition proof in an isolated proof module/target using the pinned toolchain.

If language/tool limitations require provisional stubs, keep them in a clearly
separate scaffold target with an explicit assumption inventory. Do not add
scattered `assume` statements or trusted production wrappers, weaken public
contracts, or describe a scaffold verification result as runtime verification.

For each provisional operation record:

```text
interface and concrete function(s)
requires / ensures / fields it may change
caller supplying each precondition
next consumer of each postcondition
implementation status and verification evidence
```

Check that assumptions are mutually satisfiable and not circular. Conversion
contracts must describe genuine local effects, not simply assume the entire
public theorem. The abstract model must admit empty frames, duplicates, sparse
captures, zigzag lengths, and both capture disciplines. Concrete discharge is
ultimately required for every provisional operation.

## 10. Workflow and acceptance gates

### Milestone A: conditional composition

1. Inspect current source and preserve active work. Inventory relevant concrete
   functions against this document; group wrappers and helpers by contract role.
2. Define the common model, invariant boundaries, and phase predicates.
3. Verify abstract mutation/mark/restore closure and the complete physical-phase
   orchestration using only the provisional interfaces.
4. Verify mutation after restore and a subsequent older restore. Include the
   cases in section 3 and batched mixed-tier execution.
5. Resolve composition failures by revising interfaces at the caller boundary.
   Do not resume leaf proof work merely to make a narrow helper pass.
6. Record the conditional theorem, verifier command/result, assumption inventory,
   and contract dependency graph. Review this as the first milestone.

### Milestone B: concrete discharge

For each interface, prove the corresponding actual runtime implementation.
Reuse existing bottom-up lemmas where they fit. Re-run top-level composition
whenever a contract changes; document why the caller needs the change.

Use pointwise accessors, explicit range/map equations, and narrow invariant
unfolding. Resource-limit failures should first trigger decomposition, not
larger limits or extra maintained ghost state. Do not change batching, introduce
runtime first-capture map lookups for Trail, or substitute a slower algorithm
solely to simplify proof structure.

### Milestone C: actual public closure

Connect all concrete implementations to public APIs and audit derived/parallel
containers. Preserve contents, depth, retained-history and token contracts,
including observable no-mutation on rejected requests. Audit read-only consumer
helpers such as pending-restore indices for the guarantees their consumers need.

Final evidence must include full Verus runs (default and literal-types), feature
tests, runtime regressions, the differential policy matrix, consumer tests,
formatting, and reconciled trust documentation/counts. The existing project gate
commands and original objective remain authoritative. Commit verified milestones
locally when appropriate; do not push.

Completion means every provisional contract is concretely discharged and the
actual supported public execution paths satisfy the end-to-end theorem. A green
conditional proof is the prerequisite for that work, not a replacement for it.
