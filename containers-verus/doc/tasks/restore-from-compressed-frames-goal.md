# Restoring directly from compressed frames

This is a design goal, not a status page. It records the defect that motivates
the work, the layout it proposes, and the restore contract each representation
must meet. What the code currently does is in §1; what CI asserts about the
current code is the authority on the present state.

## 1. The defect

Restoring a compressed frame decompresses it back into pairs first, then walks
those pairs writing one cell at a time. `ColdFrame::decode_exec_cold` returns
`Vec<(T, I)>` with `ensures r@ == self.decode()`, and `subrange_vec_adaptive`
calls it for every cold frame in range, pushing the results into another
`Vec`. The run structure is reconstructed and then immediately discarded.

The consequence is that compression buys nothing at restore time. A `Runs`
frame costs strictly more to restore than a `Plain` one, despite run encoding
existing precisely so that a run is one memcpy.

The uncompressed path has a second, independent instance of the same mistake.
`DiffLog::Cols { idxs, vals }` stores indices and values in separately encoded
structures, so there is no pair to index and `restore_overlay` obtains its
range through `subrange_vec`, which allocates a `Vec` and pushes the range one
element at a time on every restore. Production keeps `diff_log: Vec<(T, I)>`
and restores by indexing backward into it, with no allocation at all.

**Measured.** Against `main` at `56a06a5`, with the production container as an
unchanged control (`containers/` has zero changed files, and `/legacy`
benchmarks confirm it at 312 to 319 microseconds on both sides):

| benchmark | main | branch | |
|---|---|---|---|
| `vec/restore_replay/verified` | 312 us | 1773 us | 5.7x slower |
| `tracked_veci/mark_churn/verus/1000` | | | +287% |
| `tracked_veci/mark_churn/verus/100000` | | | +257% |
| `tracked_veci/mark_churn/verus/1000000` | | | +114% |
| `tracked_vecp/mark_churn/verus/1000` | | | +97% |

`restore_replay` restores 8 fixtures of 50,000 touched cells each, so 400,000
cell restores: 0.78 ns per cell on `main` against 4.43 ns on the branch.
`mark_churn` is 200 marks of 8 writes each, every one restored immediately,
which is why the regression is largest at the smallest size: the per-restore
allocation is most of the work at n=1000 and amortises by n=1,000,000.

Run-to-run noise on identical code measures at 5 to 8 percent, established by
re-running one build against itself, so deltas below that are not evidence.

## 2. The principle

Split representations by tier, not by column. Pairs where restore happens,
columns and runs where compression happens. A frame changes shape once, when it
goes cold, never on the path that runs on every pop.

Stated as an invariant the implementation must satisfy: **the compressed form
is the restore plan.** `decode_exec_cold` is an oracle for tests and
differential checks. It must not appear on the restore path.

## 3. Layout

### Hot tier

Production's shape, verbatim:

```rust
hot:    Vec<(T, I)>       // interleaved, indexable, truncate to pop
frames: Vec<Frame<I>>     // { saved_len: I, loc: FrameLoc<I> }
```

Interleaved because restore indexes it directly. Truncation pops a frame.

### Cold tier

Fully pooled. The stack is LIFO, so every pool is a bump allocator: push
appends, pop truncates, fragmentation cannot occur, and a frame costs zero
allocations.

```rust
struct ColdStack<T: Copy, I: IndexLike, VC: ValueCompressor<T>> {
    frames: Vec<ColdHdr<I>>,   // one per cold frame, stack order
    starts: Vec<I>,            // target index of each run
    offs:   Vec<I>,            // runs + 1 entries, monotone non-decreasing
    pairs:  Vec<(T, I)>,       // Plain cold frames
    values: Vec<T>,            // Runs cold frames, concatenated in index order
    dicts:  Vec<T>,            // per-frame dictionaries, pooled
    codes:  Codes,             // flattened
}
```

**Runs are CSR.** Run `i` occupies `values[offs[i] .. offs[i+1]]` and lands at
`target[starts[i] ..]`. This gives the end as `offs[i+1]` and the length as the
difference, so neither has to be stored: 8 bytes per run rather than 12 with
`I = u32`, which matters because restore walks the runs array linearly. The
invariant is monotonicity of `offs` plus `offs.last() == values.len()`, which is
ordinary sequence reasoning, and the `start + len <= saved_len` obligation the
memcpy needs follows from it.

**Offsets, not slices.** A `&[T]` into a sibling `Vec` is self-referential and
unsound here regardless of the borrow checker, because appending to a pool may
reallocate and invalidate every outstanding slice. Integer offsets are also
half the size of a fat pointer, keep the structure relocatable, and stay inside
the verifiable subset.

**Dictionaries are per-frame logically, pooled physically.** Per-frame because a
shared dictionary cannot be truncated on pop: later frames' entries interleave
with earlier ones, so popping would either leak or require refcounting. Pooled
because that preserves the zero-allocation property. The header carries
`(dict_off, dict_len)`.

## 4. The restore contract

Restore resizes the target to the frame's `saved_len` first, then applies the
frame. `apply_all` never changes length and drops entries at or beyond the
current length, so a run overrunning `saved_len` is **clamped**, not grown.

**Hot frame.** Walk `hot[diff_start..]` backward, writing each `(T, I)` pair.
No allocation, no decode.

**Cold frame, RLE only.** For each run, one `copy_from_slice` from
`values[offs[i]..offs[i+1]]` into `target[starts[i] ..][.. len]`. Straight out
of the pool. No pair is ever formed.

**Cold frame, RLE with dictionary values.** Codes cannot be memcpy'd, so a
decode is unavoidable. Decode each run once into a reusable scratch buffer
(destination-passing, so the allocation persists across runs and across
frames), then copy the whole decoded slice to the target as one memcpy. One
sequential decode pass plus one block copy per run, and no allocation after the
first frame.

The scratch is unconditional rather than an optimisation for the clamped case.
Decoding straight into the target slice would save the copy for fully in-range
runs, and is rejected deliberately: routing both cold modes through the same
`copy_from_slice` keeps the write to the target uniform, which is simpler to
verify and to reason about for aliasing, and isolates the decode from the
target's borrow. The scratch belongs on the container rather than on
`ColdStack`, sized to the longest run seen, so a restore spanning several cold
frames reuses one buffer for all of them.

## 5. Mode selection must weigh restore, not only size

| mode | restore | chosen when |
|---|---|---|
| `Plain` | sequential pass over pooled pairs | singleton-heavy frames |
| `Runs` | one memcpy per run | indices cluster |
| `RunsDict` | decode to scratch, then memcpy per run | clustered and memory-pressured |

`Runs` dominates `Plain` on both axes when clustering pays, so it needs no
trade-off argument. `RunsDict` is the only mode that adds a decode pass, making
it a deliberate memory-for-restore-speed trade rather than a default.

A frame of mostly singletons encodes as length-1 runs, and restoring it chases
the runs array and the values pool once per element, which is strictly worse
than one sequential pass over pairs. The current selector (`choose_mode` over
`FrameStats`) picks on encoded size alone and can therefore choose a
representation that is smaller and slower. The objective needs a restore term.

## 6. Hot buffering, and the policy on `mark()`

Compressing on every mark is waste when the frame is restored immediately,
which is the dominant push/pop pattern and exactly what `mark_churn` measures.

```
on mark():
    push frame as Hot
    if hot_frames > HOT_BUFFER:  evict oldest hot -> compress -> cold, retag
    if pools over-committed:     reclaim
```

A `Plain` eviction is a memcpy of a contiguous range from the hot pair array
into the cold pair pool, since both are `Vec<(T, I)>`. No transformation.

## 7. Trail compatibility

The trail discipline appends every write unconditionally and permits duplicate
indices within a frame, which is why a trail column currently never compresses:
run encoding needs unique indices.

The bridge is that `overlay` is first-entry-wins. It applies a stratum
backward, so the chronologically first capture of a cell survives. Compressing
a trail frame is therefore **dedupe keeping the first occurrence, sort by
index, then RLE**, and the result restores identically, because
dedupe-keep-first selects exactly the entries `overlay` would have let win. One
sort with ties broken by original position, then a linear pass taking the first
of each index group, so the sort RLE needs anyway does double duty.

This puts the conversion at frame eviction, off the write path entirely, so
trail keeps its branch-free flag-free write. Trail's log is already
`Vec<(T, I)>`, so trail and the unique discipline share the hot tier verbatim
and differ only in whether a write checks a flag before appending.

**Trail gains more from compression than the unique discipline does.** The
unique discipline bounds a frame at one entry per cell by paying a flag check
on every write. Trail pays nothing per write and accepts a frame that grows
with total writes, so dedupe at eviction recovers exactly what trail gave up: a
frame of 1000 writes across 10 cells collapses to 10 entries. The cost moves
from the write path, which is hot, to the eviction path, which `HOT_BUFFER`
skips entirely for shallow push/pop.

## 8. Uniqueness is an algorithm contract, not a structural invariant

`stratum_unique` is currently a `Vec::wf` clause conditioned on
`store.unique_capture_spec()`, so the structural invariant asks the store which
discipline it is, and every proof that touches `wf` inherits that case split.

This is the wrong home for it. The hot frame is `Vec<(T, I)>` under both
disciplines, and nothing about the representation makes duplicates invalid:
`overlay` is total and first-entry-wins handles them. Uniqueness is a property
that some algorithms establish and others require.

It becomes a contract stated where it is used:

- **Established by** the unique-capture `set` (the flag check is exactly what
  makes it hold) and by `dedupe_first` at eviction.
- **Required by** `seal`, reordering, and RLE construction, which cannot encode
  duplicate indices into runs.
- **Irrelevant to** `overlay`, hot restore, `apply_all`, and cold restore, all
  of which are correct with or without it.

Concretely: drop the conditional clause from `Vec::wf`; add
`requires stratum_unique(..)` to the sealing and run-encoding entry points; add
the matching `ensures` to the unique-capture write and to dedupe.

Three consequences. Every `wf` lemma stops case-splitting on discipline, which
should simplify more proofs than it complicates, because that conditional is
load-bearing wherever `wf` is. Trail and capture stop differing structurally,
which is what lets them share both tiers with no discipline-conditional
anywhere in the data path. And a cold frame's uniqueness becomes a
postcondition of eviction rather than an inherited property, which is the
honest statement: it is unique because dedupe made it so.

The obligation this creates is the lemma that licenses eviction to change the
entry set at all:

    overlay(base, d) == overlay(base, dedupe_first(d))

proved once by induction on `d`, rather than case-split at every use of `wf`.

## 9. What this must not change

`History { stamps, depth }` and `GroupToken { generation, depth }` are
untouched. Compression moves a frame's diffs, never its identity.

`frames.len()` remains the depth, so a cold frame keeps its slot and
`VecToken { frame_idx }` stays a valid coordinate.

`saved_len` stays in the frame header for both tiers. It is the resize target
and is independent of how the frame's diffs are stored.

## 10. Open parameters

`HOT_BUFFER`'s home: a constant, a per-column constructor argument, or the
existing `SEMPER_*` environment lever. The lever has the advantage that the
SMT and saturation profiles already select different diff stores that way.

Whether the mode selector's restore term is tuned against the benchmarks or
derived from run count and entry count directly.

## 11. Campaign record (2026-09-12)

All seven deliverables are BUILT and their checks pass. This section records
the measurements, the deviations from the sections above, and the negative
results, so the next person does not re-run a closed experiment. The current
state of the code is what `cargo verus verify` (2239 verified, 0 errors) and
the conformance suite (26 binaries) assert; this section records what was
decided and measured on the way.

### Measurements

All Criterion comparisons run against the saved `mainline` baseline with the
`prod`/`legacy` configurations as unchanged controls; the acceptance noise
floor is ±8%.

| condition | final tree vs mainline | verdict |
|---|---|---|
| `vec/restore_replay/verified` | **−32.9%** | the 5.7x regression this campaign opened with is gone; the verified container now restores 33% faster than mainline (`retained_containers_bench`) |
| `vec/restore_replay/legacy` (control) | −0.17% | unchanged, as required |
| `tracked_veci/mark_churn/verus/1000` | +5.9% | in band (`tracked_vec_bench`) |
| `tracked_veci/mark_churn/verus/100000` | +5.1% | in band |
| `tracked_veci/mark_churn/verus/1000000` | −6.4% | in band |

The mark_churn numbers are from the finished tree, with the dedupe-first fold
live on every mark path; an interim measurement mid-campaign had read
+43%/+58%, caused by an accidental seal-on-every-mark and a non-inlined
per-element `index()` on the scatter-restore path, both fixed by the
`auto_seal` policy split and the `hot_slice` fast path.

### Decisions and deviations from §3–§8

**`Frame.loc` is derived, not stored.** §3 sketched `loc: FrameLoc<I>`; the
implementation derives tier membership as `diff_start < idx_cold_len`.
Eviction retags by advancing the cold length past the stratum, which removes
the invariant that a stored tag would have to keep consistent.

**The codes pool is byte-width, not bit-packed.** A bit-packed pool cannot
truncate at an arbitrary code boundary without read-modify-write word
surgery, and pop must stay a truncate. The pool widens monotonically
(U8→U16→U32→Usize, at most three whole-pool rewrites ever); per-frame
sub-byte packing remains available to the per-frame `ColdFrame::Dict` tier.

**Dict-frame runs live in their own `druns` column.** Their boundaries index
the codes pool, not `values`, and one shared `offs` column cannot stay
monotone across two independent cursors. `druns` holds (target start,
cumulative end) pairs, frame-local CSR, so no cross-frame anchor invariant is
needed for it.

**The RunsDict content clauses are opaque.** Inlining their nested
quantifiers into every `wf` context wedged the solver in `pop_frame` (the
worker died without statistics); `dict_content_wf` is `#[verifier::opaque]`
with an explicit transfer lemma, and `pop_frame`'s survivor, offs and tiling
arguments moved into three trimmed-context lemmas for the same reason.

**Eviction is the trail discipline's compression path.** `evict_cold_frame`
returns early for unique-capture stores: those columns compress at seal
(`auto_seal` or the explicit compaction entries), and running both policies
would leave the buffer dead weight because seal-on-mark never accumulates a
second hot stratum. The gate also keeps a mode-None unique column an honest
plain baseline, which the size-comparison unit tests and the mainline
benchmark controls read; the first cut evicted every adaptive column and
inflated the plain control until it compressed itself, failing
`indexruns_restore_matches_plain_and_compresses` and its two siblings.

**Both disciplines fold through one dedupe-first construction.** `dedupe_first`'s
`unique_idx` ensures discharges the run encoders' requires, so no fold reads
uniqueness from the container invariant; the
`unique_capture_spec()`-conditional `stratum_unique` clause left `Vec::wf`
(deliverable 6) together with its nine re-establishment blocks. For
unique-capture columns the dedupe is the identity
(`lemma_dedupe_identity_on_unique`), which is how `mark_and_compact_sorted`
rides the shrink-tolerant frame rule with no executable change.

**The dedupe scan is O(n * U) and the pipeline was already quadratic.** The
shipped `dedupe_first` is a first-hitter scan, not the min-fold-per-index it
logically is. Two facts scope that honestly: the verified subset has no
modeled hash map (the same constraint that makes `assign_codes` a linear
dict scan), and the verified sort the fold runs afterwards
(`sort_frame_by_index`) is an insertion sort - O(n^2) adversarial,
near-linear on the nearly-sorted strata capture order tends to produce - so
fusing dedupe into that sort changes a constant, not the asymptotics. The
end-to-end upgrade is a verified mergesort over position-decorated entries
with the keep-first group pass fused into its output scan (dedupe rides the
sort for free, as §7 specified), which is a proof project of its own.
Revisit when an eviction is measured to dominate a mark; the contract
boundary makes the swap local - every consumer is phrased against
`dedupe_first_spec`, so a faster exec re-proves one ensures and touches
nothing else.

### Negative results

**Loop-invariant quantifiers carrying `first_hitter` witnesses do not
re-derive.** The first `dedupe_first` carried its characterization as loop
invariants (an exists form, then a ground witness-column form); the solver
failed even the identity re-derivation across an inner loop, minimal-probe
confirmed, while structurally simpler invariants in the same probes passed.
The committed form gives the exec loop one sequence-equality invariant
against a recursive spec (`dedupe_prefix`) and proves every property by
induction on that definition; the same quantifier shapes instantiate without
trouble as lemma requires. Do not move them back into invariants.

**An LCG's low bits are not a duplicate generator.** The first trail
compression test drew indices as `seed % 64` from a 64-bit LCG; the low six
bits of such a generator have full period 64, so all 32 draws per frame were
distinct and nothing could compress. The committed test uses deterministic
duplicates. Cite this before trusting modulo-reduced LCG streams in any
future collision-dependent test.

**`decode_exec_cold` is oracle-only.** Its last production caller was the
whole-frame branch of `subrange_vec_adaptive`, which the general per-element
loop already covered; the branch is deleted and the function's doc says
oracle-only. The restore path reaches pools through `restore_to` /
`restore_range_into` block writes exclusively, with no `external_body`
anywhere on it.

### Still open

The ColdStack module is the §3 pooled layout, verified and differentially
tested against the hot-restore oracle (including RunsDict with clamp and
pop-reseal coverage), but the live cold tier remains the per-frame
`ColdFrame` vector inside `DiffLog::Adaptive`. Swapping the live tier onto
the pooled stack is postponed, not closed: revisit when a workload is
measured where per-frame allocation at seal time shows in a profile, which
shallow push/pop workloads never reach because the HOT_BUFFER keeps them
uncompressed.
