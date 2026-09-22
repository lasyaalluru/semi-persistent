# Diff-stack compression

Compresses the finalized frames of a semi-persistent vector so the rollback
history occupies close to its information-theoretic minimum. This is a **space**
optimization: it trades finalization time (a per-frame compression pass) for a
smaller history. It is a design doc; CI gates are the source of truth for what
is implemented.

## Purpose and non-goals

**Goal.** Reduce the memory held by the diff history of `VecI`/`VecP` so that
backtracking search over the e-graph stays memory-bounded on long, deep sessions.

**The baseline is the deep copy, not our own uncompressed trail.** Most e-graphs
back up by copying the whole structure, so a search holding `d` checkpoints on
its current path holds up to `d · N` for an e-graph of size `N` — memory scales
*multiplicatively* with search depth. This is why rewrite-intensive equality
saturation and ruleset-search-by-backtracking either deep-copy and exhaust
memory or re-run from scratch and exhaust time. Semi-persistence already replaces
`d · N` with `N + Σ diffs` (*additive*: a checkpoint costs only the delta written
since the previous one). Compression shrinks the `Σ diffs` term, which is the
term that grows with search depth — so it keeps deep searches bounded rather than
saving a constant factor.

Application-class split: for SMT the backtracking is bounded and the workload is
speed-dominated, so compression is not the lever (relevancy/`matchable` is); for
equality saturation and ruleset search the memory scaling above *is* the binding
constraint, so compression is first-order there. The two workload classes want
opposite priorities from the same engine.

Read the doc's "second-order win" language against the right baseline: structure
compression is second-order relative to *our own uncompressed trail on short SMT
sessions*, and first-order relative to the *deep-copy world* on eq-sat sessions.

**Non-goal — wall-clock.** Compression *costs* time at `mark` (finalization) and
adds decode work at `restore`. It does not close a wall-clock gap; if anything
it widens it slightly on backtrack-heavy workloads. Enable it only when memory
is the binding constraint. See `10-shared-fork-history.md` for the wall-clock
lever.

## Current representation

`Vec<T, I, S, TRACK>` keeps a single `diff_log: Vec<(T, I)>` partitioned into
per-frame strata by `frames[k].diff_start`. On `set`, the first write to a cell
below the frame's `saved_len` pushes `(old_value, index)` (first-write-wins, via
the capture bit). `restore` reverse-replays a stratum and truncates. Every
entry costs `sizeof(T) + sizeof(I)`, regardless of structure — a frame that
captured a contiguous range `[i, i+k)` stores `k` redundant indices.

## Design: a layered stack

Split the history into two tiers:

- **Current frame — uncompressed.** A `Vec<(T, I)>` recording diffs as they
  happen, exactly as today. The active frame must stay uncompressed because
  writes arrive one at a time and first-write-wins needs cheap append + the
  capture check.
- **History `[0, current)` — compressed.** On `mark`, the closing frame is
  *finalized*: its diff set is compressed once and appended to a compressed
  store. Finalized frames are read-only until popped by `restore`.

This matches the invariant that only the top frame is ever mutated.

## Finalization

A frame's diffs are a **set** (first-write-wins ⇒ at most one entry per cell),
so they may be freely reordered. Finalize:

1. **Sort by index.** Radix sort on the integer indices — `O(p)` for `p`
   captures (a few byte-passes, 256 counters; no `N`-sized buckets, no log
   factor).
2. **Coalesce runs.** One linear pass merges adjacent indices (`idx[t+1] ==
   idx[t] + 1`) into maximal runs. Because the set was sorted, this captures
   *all* contiguity, not just write-order contiguity.
3. **Encode** (below) and append to the compressed store.
4. **Clear capture state** for the frame's cells during the same pass (fused
   with step 2), so finalization stays a single `O(p)` sweep plus the sort.

Cost added versus today's finalize: the radix sort (`O(p)`, larger constant).
Everything else fuses with the clear pass already performed.

## Encoding: irreducible values, compressed structure

Separate what cannot shrink from what can.

**Values — irreducible per cell, but not per frame (RETRACTED as stated).** An
earlier version of this doc claimed the value pool is irreducible: "every
captured cell's old value must be stored, `P · sizeof(T)`, no encoding beats
this." That is true only cell-by-cell. It is false across a frame or a column
whenever the *multiset* of old values has low cardinality, because a dictionary
collapses repeats using only `Eq` on `T` — it assumes no structure in `T`'s
bits, so the original out-of-scope argument does not apply. The union-find
`parent` column is the case that breaks the claim: path compression re-points
whole paths at one representative, so one id recurs as the old value across many
captured cells, scattered across the array rather than confined to one
contiguous index run. See "Value axis" below; the pool term drops from
`P · sizeof(T)` to `D · sizeof(T)` for `D` distinct values.

The uncompressible residue is only the *distinct* values `D · sizeof(T)` plus
the encoding that says which cell held which value. When `D ≈ P` (all values
distinct) this reduces to the old pool and the index structure below is the only
lever; when `D ≪ P` the value axis is the larger win.

**Structure — a monotone index sequence.** Per frame the touched indices, once
sorted, are a strictly increasing integer sequence; the maximal runs are
determined by adjacency. Its entropy is `~log2(C(N, P_f))`, lower when runs
exist. Two encoders, selected per frame:

### Encoder 1 — singleton-bitmap pooled (simple, near-minimum)

Pools shared across all compressed frames (one allocation each, cache-friendly,
no per-frame `Vec` headers):

- `values: [T]` — `P · sizeof(T)` (the irreducible pool).
- `run_start: [I]` — one cell index per run; `R · sizeof(I)`.
- `run_is_singleton: bitset` — `R` bits.
- `run_len_long: [varint]` — lengths only for non-singleton runs.
- `frame_run_ofs: [u32; F+1]` — where each frame's runs begin (run count and
  value slice implicit by difference).

Length is genuinely independent information (maximal runs have unknown gaps), so
it must be carried; the singleton bitmap carries it at ~1 bit for the common
length-1 case and a varint otherwise. Worst case (all singletons) is
`P · sizeof(I) + P/8 bytes` — uncompressed plus one bit per entry. A run of
length `L` saves `(L-1) · sizeof(I)` for one bit plus a small varint.

### Encoder 2 — Elias-Fano (maximum ratio)

Encode the sorted index sequence with Elias-Fano: `P · (2 + ceil(log2(N/P)))`
bits, within a constant of the `log2 C(N,P)` entropy bound, with O(1) access.
Runs are exploited implicitly (consecutive indices share high bits and step the
low bits, so a run is nearly free) and there is **no singleton penalty** — the
encoding is uniform, spending bits proportional to the actual gaps. Values stay
in the same irreducible pool; frame boundaries as above. This is the
max-compression target; it is heavier to implement and to verify, so it lands
after Encoder 1.

### Encoder 3 — delta + varint (byte-aligned, sequential)

Store the gaps between consecutive sorted indices as varints: a contiguous or
near-contiguous frame becomes a string of 1-byte gaps. An alternative to
Elias-Fano for the index structure, chosen by the per-frame selector.

The reason it earns a place despite Elias-Fano's better asymptotics: the only
read of a compressed frame is whole-frame **sequential reverse-replay** on
restore — no cell is ever random-accessed. Elias-Fano's `O(1)` select/rank is
therefore spent capability. Delta+varint decodes front-to-back, exactly restore's
pattern, is byte-aligned (no bit extraction on the hot path), and its
encode/decode bijection is materially simpler to verify.

The catch is a floor: varint costs `>= 8` bits per index. Elias-Fano spends
`2 + ⌈log₂(N/P)⌉` bits, which drops below 8 when the frame is dense
(`N/P < 64`), and a plain bitmap beats both as `P → N`. Union-find frames are
expected dense (path compression sweeps a near-contiguous range), so on the
dominant column EF or bitmap can still win on ratio while varint wins on decode
cost and proof simplicity. Which one fires is the density measurement below, not
a fixed choice.

Varint also encodes the value axis where it helps: the sorted dictionary values
(delta+varint) and the `group_ofs`/`frame_run_ofs` offset arrays (monotone), both
minor next to the pool and index terms.

### Never-worse guarantee

A per-frame selector picks the smallest of the index-structure candidates
{plain indices, singleton-bitmap, Elias-Fano, delta-varint} at finalize (a few
selector bits per frame name the winner), bounding the structure by
`min(candidates) + O(F) bits`. So enabling compression can never enlarge the
history beyond today's plus a few bits per frame.

## Value axis: dictionary and value-major encoding

Orthogonal to the index axis above. A frame's captured old values are a multiset
of `D` distinct values over `P` cells; when `D ≪ P` the pool is compressible with
`Eq` alone. Two encoders, selected per frame by the never-worse rule:

### Value encoder A — dictionary + codes (keeps index-major structure)

- `dict: [T]` — the `D` distinct values, `D · sizeof(T)`.
- `codes: [u?]` — one dictionary index per captured cell, `P · ⌈log₂ D⌉` bits,
  in the same order as the index structure so a cell's index and code align.

Composes with the index encoders unchanged (they encode *which* cells; codes
encode *what*). Pool cost `D · sizeof(T) + P · ⌈log₂ D⌉ / 8` bytes versus the old
`P · sizeof(T)`. Wins when `⌈log₂ D⌉ < sizeof(T) · 8` minus the dict overhead —
i.e. whenever values repeat at all.

### Value encoder B — value-major / inverted (subsumes index RLE)

Invert the primary axis: store each distinct value once, then the *set* of cell
indices that held it.

- `dict: [T]` — `D · sizeof(T)`.
- per value `v`: its index set `S_v` (a monotone integer set) encoded with the
  same Elias-Fano/singleton-bitmap machinery as the index axis.
- `group_ofs: [u32; D+1]` — where each value's index set begins.

Contiguous cells sharing a value cost nearly nothing (Elias-Fano over a run),
so this captures index contiguity *and* value repetition in one structure. It is
the right shape for the union-find `parent`/`rank` columns, where both hold: a
compressed path is a near-contiguous index range that all took the same old
root. Value-major also makes restore value-major — one `dict[v]` broadcast over
`S_v` — which is a cheaper write pattern than one value read per cell.

### Selecting the encoder: exact-size costing, not thresholds

The per-frame choice is made by computing the exact encoded size of every
candidate and taking the minimum. Finalize already pays a radix sort over the
frame; the sizing rides on the same sweep and is cheaper than the sort, so the
selector is optimal by construction — because the candidate set includes plain,
the winner can never be larger than today. No tuned thresholds.

The sweep gathers, in one pass over the sorted diff set:

- `P` — captures (frame size).
- `R` — maximal contiguous index runs (from coalescing).
- `D` — distinct old values (a scratch hashset over the `P` entries; one frame,
  so cheap — the one cost beyond the index sort).
- `N` — the current vector length (the index universe).
- `Σ varint(gap)` and `Σ varint(runlen)` — accumulated during the walk (varint
  byte counts are additive, so exact and free here).

Each candidate's size is then closed-form in those counts:

| candidate | size (bytes) |
|---|---|
| plain | `P·(sizeof(I)+sizeof(T))` |
| singleton-bitmap | `R·sizeof(I) + R/8 + Σ varint(runlen) + P·sizeof(T)` |
| Elias-Fano + pool | `P·(2+⌈log₂(N/P)⌉)/8 + P·sizeof(T)` |
| delta-varint + pool | `Σ varint(gap) + P·sizeof(T)` |
| dictionary + codes | `[best index structure] + D·sizeof(T) + P·⌈log₂D⌉/8` |
| value-major | `D·sizeof(T) + Σ_v EF(S_v) + D·offset` |

**The eligible candidate set is a per-column property, decided statically.** The
value axis (dictionary, value-major) can only pay when the column's value domain
is small or highly repetitive. That is a fact about what the column stores, known
at construction, not something to rediscover each frame:

- **Distinct-payload columns** — the irreducible `values` pool, unique-id
  columns, arbitrary structs — are **index-major only**. They never cost the
  value-axis candidates and never pay the `O(P)` distinct-value pass; `D` is not
  computed for them.
- **Value-repetitive columns** opt into the value axis. The union-find `parent`
  column is the motivating case: path compression makes whole near-contiguous
  index ranges share one old representative, so `D ≪ P` structurally. `rank`
  (tiny integer domain) and any small-domain flag/enum column qualify too; today
  the union-find columns are the only ones worth enabling.

So the per-instance `CompressionMode` is chosen per column, and for a
value-eligible column it names a scheme *family* (index axis plus value axis)
rather than a bool. Within the eligible set the per-frame winner is still the
argmin below, so never-worse holds per column.

Within the eligible set the decision **factorizes**, since the index axis (which
cells) and the value axis (what values) are independent — the exception is
value-major, which fuses them and is costed as its own joint candidate:

1. best index-major = `min(plain, bitmap, EF, varint)` for structure, plus
   `min(plain-pool, dictionary+codes)` for values.
2. value-major, costed on its own.
3. selector = `argmin` of {index-major, value-major}, a few bits per frame.

Equivalently the winner is governed by three ratios read off the counts — `D/P`
(does the value axis pay), `R/P` (do runs pay), `N/P` (dense enough for EF or a
bitmap to beat varint's `>= 8` bits/index floor) — plus per-value contiguity for
value-major versus dictionary+codes. The code does not branch on these; it costs
all candidates and takes the min. The union-find columns are the reason the
value-major and dictionary candidates exist at all (`D ≪ P` there); the sizing
just confirms it per frame.

## Per-column analysis (e-graph)

Which scheme fits which column, predicted from what each column stores and how a
diff captures it. Every entry is a prediction to confirm with the finalize-pass
counts (`D/P`, `R/P`, `N/P`); the selector self-corrects per frame, so a wrong
prediction costs a pruned candidate, not correctness.

A first-write-wins diff stores the **pre-frame (old)** value to invert a write,
not the new one. This is the pivot: a column whose *new* values repeat (a
union-find pointing everything at one root) does not thereby have repeating
*captured* values.

| column | type | what a frame captures | index dist. | value `D/P` | scheme |
|---|---|---|---|---|---|
| `parent` (UF) | node id | old parent of each re-rooted / path-compressed node | scattered | low when a big class is re-rooted (members shared an old root), else high | **dictionary+codes** if `D/P` low, else plain index-major |
| `rank` (UF) | `u8` | old rank of the few roots whose rank bumped | tiny `P` | low domain, but `P` tiny | **plain** (frame too small for any header to pay) |
| repr `dense` = `ClassData` | 16-byte struct | old struct of touched class slots | scattered, small `P` | `D≈P` (distinct `use_list`) | **index-major** (value axis useless at struct granularity) |
| repr `sparse`, `indices` | index | old position / id on swap-remove | scattered, small `P` | `D≈P` | **index-major / plain** |
| class ring `next` + key | node id / `Opt<key>` | pointers touched by ring splice | few per merge | distinct | **index-major / plain** |
| use-list arena (heads, nodes) | list / node id | head/next pointers; appends are growth, not diffed | few per op | distinct | **index-major / plain** |
| min-pool | `Opt<T>` | AC completion rows | empty under plain EUF | n/a | irrelevant (EUF); index-major with completion |
| per-kind node caches | node id | hash-cons slots touched/invalidated | scattered | distinct | **index-major** |

Two conclusions worth stating plainly:

**No e-graph column has the contiguous-per-value structure that makes value-major
strictly win.** `parent` is value-*repetitive* but not value-*contiguous* (its
touched node ids are scattered), and for a scattered partition value-major's
per-group Elias-Fano costs `≈ EF(all) + P·log₂D` — exactly the code bits
dictionary+codes pays — so the two are equivalent there, and dictionary+codes is
the simpler form. Value-major would win only if node ids were allocated
per-class so a re-rooted class occupied a contiguous index range; they are not.
So enable **dictionary+codes** on `parent`, not value-major. (This narrows the
earlier "union-find is the value-major case" claim: it is the value-*dictionary*
case.)

**The value-repetitive fields in `ClassData` are buried by array-of-structs.**
`atomic`, `matchable` (bools) and `min_row` (mostly `None`) repeat heavily, but
they are packed inside the 16-byte struct, whose whole-struct value is distinct
per class, so the struct column sees `D≈P` and gains nothing. Splitting
`ClassData` into per-field columns (struct-of-arrays) would expose bool/`Option`
columns that a bitmap compresses to bits — a separate structural lever
(SoA vs AoS), out of scope here but the only way the class-payload column gets a
value-axis win. Recorded so it is not confused with the `parent` case.

## Restore and clear over compressed frames

- **Restore** to frame `d`: reverse-replay compressed frames `current-1 … d+1`,
  then the uncompressed current frame; truncate. A compressed frame replays run
  by run — `values[run] → cells[start .. start+len]` as a slice `memcpy`
  (vectorizable, cache-linear), versus `len` individual `restore_entry` calls.
  Intra-frame run order is irrelevant (disjoint indices under first-write-wins);
  only reverse *frame* order matters.
- **Clear** (fused into finalize, above): a run clears a contiguous stamp range.
  For `VecP` this is whole `u64` bitmap words over `[start, start+len)` — the
  largest single win, since `VecP` otherwise zeroes the whole materialized
  bitmap. For `VecI` the tag bits are interleaved in the value words, so it is
  still per-cell but sequential (cache-friendly).

## Complexity

| | uncompressed (today) | compressed |
|---|---|---|
| finalize (`mark`) | `O(p)` clear | `O(p)` radix sort + coalesce + clear |
| restore | `O(diff)` per-cell | `O(diff)` slice `memcpy` per run |
| history memory | `P·(T+I) + F·usize` | `P·T` + near-entropy structure |
| VecP mark clear | `O(N/64)` whole bitmap | `O(runs + touched/64)` |

## The ValueCompressor strategy (decided 2026-09-08, supersedes mode-only selection)

**The value bound lives on the codec, not on the column.** The dictionary encoder
calls `T::as_usize` and the delta encoder does value arithmetic, so both need
`T: IndexLike`; the node caches and the class-data `dense` column hold structs where
only verbatim storage or equality-RLE applies. Bounding `Vec`/`DiffLog` methods by
`T: IndexLike` would either exclude struct columns from index compression or force a
silent fallback. Instead the value layer is a strategy parameter:

```
pub trait ValueCompressor<T: Copy> {
    type Compressed;
    spec fn decode(c: &Self::Compressed) -> Seq<T>;
    fn compress(vals: &Vec<T>) -> (c: Self::Compressed)
        ensures Self::decode(&c) == vals@;
    fn decode_at(c: &Self::Compressed, i: usize) -> (v: T);
    fn byte_len(c: &Self::Compressed) -> usize;
}
```

Impl ladder, each carrying its own bound: `NoValueCompression` (any `T: Copy`,
identity), `ValueRle` (`T: Copy + PartialEq`, equality runs; structs included),
`ValueDictC` (`T: IndexLike`, dictionary + bit-packed codes), `ValueDelta`
(`T: IndexLike`, value minus cell index, arithmetic verified in range). The column
type is `Vec<T, I, S, VC: ValueCompressor<T>, TRACK>` with `NoValueCompression` the
default; the parameter sits on `Vec`/`DiffLog`, not on `DiffStore`, because the store
is the live column plus capture flags and never holds compressed bytes.

What this buys, stated as properties: an illegal column/codec pairing fails to
typecheck, so there is no runtime fallback to forbid; the index layers (runs, sorted
runs) stay a closed enum available to every column because `I` is always `IndexLike`;
per-frame adaptivity ranges over index layer x { apply VC, plain } within the
column's fixed value family; and a new codec is one new impl with no change to
`Vec`, `DiffLog` or the frame types. The earlier alternative — two member impls
split by bound (`Vec` / `OpaqueVec`) — was rejected because it duplicated the member
surface and moved the capability decision from the type to every call site.

Index and value layers compose on one frame (an index-run frame whose run values are
dict-coded), replacing the previous mutually-exclusive mode set; the seven composed
modes and their measured comparison are the F2/F5 items of
`doc/tasks/forkhistory-and-frame-compression-goal.md`.

## Runtime selection (per-instance mode, not a const generic)

Compression mode is a **per-instance runtime field**, chosen at construction, not
a compile-time const generic. The requirement it serves: one binary runs both
regimes without recompilation — SMT with compression off (speed), equality
saturation with compression on and each data structure configured to its best
mode — so the choice must be a value, not a type parameter.

```
pub enum CompressionMode { None, ValueDict, IndexRuns /* extensible */ }

pub struct Vec<T, I, S, const TRACK: bool = true> {
    // ... existing fields ...
    mode: CompressionMode,           // set at construction, consulted at mark/restore
    compressed: CompressedStore<T, I>, // empty and unused when mode == None
}
```

`mode == None` keeps today's single uncompressed `diff_log`; the only cost is one
branch at `mark`/`restore`, and the compressed store stays empty. Other modes
finalize the closing frame with the corresponding encoder. Each aggregate
(`EClasses`, `NodeStore`) sets a per-column mode: `None` everywhere for the SMT
profile; for the eq-sat profile, `ValueDict` on the union-find `parent`/`rank`
columns and `IndexRuns` (or `None`) on the rest, per the per-column analysis.

Const-generic `COMPRESS` was rejected: it bakes the choice into the type, forcing
two builds and preventing a single library from serving SMT and eq-sat callers at
runtime. The runtime field costs one predictable branch when off (measured against
the const-generic's compile-out only if that branch ever shows up in a profile),
which is the right trade for one-binary flexibility.

The choice is orthogonal to `VecI`/`VecP` (compression lives in the frame
representation, not where the capture stamp lives), so both gain it.

## Configuration object and when to compress

The per-instance `mode` generalizes to a small **configuration object** so an
aggregate names, per column, both the encoder and the policy in one value:

```
pub struct ColumnConfig {
    scheme: CompressionMode,   // None | ValueDict | IndexRuns
    // Compress the uncompressed top only when it grows past this fraction of the
    // live payload (0 == compress every mark; None-scheme ignores it).
    compress_at_fraction: f32, // e.g. 0.25 of the base vector length
    // Keep this many most-recent frames uncompressed regardless (LRU floor), so
    // an imminent backtrack pays no decode.
    keep_hot_frames: usize,
}
```

The whole e-graph's compression regime is then a table of `ColumnConfig`, one per
column, passed at construction: all-`None` for the SMT profile, and per the
per-column analysis for the eq-sat profile. The object is a value, not a type, for
the same one-binary reason as the mode field.

**Compress periodically, not every mark.** Finalizing on every `mark` (the
step-3 plan above) pays the encoder cost on the critical path at every branch,
and the measured `compress` cost makes that the wrong default. Instead the top
stack accumulates uncompressed finalized frames and is flushed only when its
footprint crosses `compress_at_fraction` of the live payload (the base vector
length times `sizeof(T)`): the diff trail is worth compressing exactly when it is
becoming a material fraction of what it shadows. This bounds the amortized
finalize cost (one encode pass per flush, over many marks) and keeps the common
mark free of encoder work. The trigger reads two sizes already cheap to track:
the uncompressed diff byte count (running sum) and the base length.

**Keep hot frames uncompressed (LRU).** A restore usually lands near the top of
the stack (backtrack one or a few levels), and decoding a frame just to
immediately restore through it is wasted work. So a flush compresses only frames
older than the `keep_hot_frames` most recent: the hot suffix stays plain and
restore-cheap, and only the cold prefix — unlikely to be a backtrack target soon
— is compressed. This is an eviction policy on the frame stack, not on cells;
"least recently marked" approximates "least likely to be restored to next".

**Monitoring.** The two-stack exposes diagnostics (no spec content, capacity/time
measurements only), which the policy consults and the benchmark records:
uncompressed byte count, compressed byte count, cumulative encode and decode time
(and counts). These are what let the size-fraction trigger fire and what the
benchmark suite reports as the space saved and the time paid.

## Verification

Two structural theorems, orthogonal to the existing mark/restore proofs:

- **Encode/decode bijection.** The compressed frame decodes to exactly the set
  of `(index, old_value)` it was built from — proved for each encoder
  (singleton-bitmap, then Elias-Fano) as a pure data-representation refinement.
- **Restore equivalence.** Restoring from a compressed frame yields the same
  `view()` as restoring from the uncompressed diff — reduces to the bijection
  plus the existing disjoint-index replay argument.

Because these are representation refinements over the *same* abstract model, the
mark/restore logic and its proofs are reused unchanged; `COMPRESS` selects the
frame representation behind the abstraction.

A future SIMD encoder, if added, is not verified: the scalar verified encoder is
its reference specification, and the SIMD path is conformance-tested for
decode-equivalence against it, not proved.

## Alternatives considered

- **Per-run `(start, length)` or `(start, value_offset)`**: wastes a field per
  singleton (`R = P`), strictly worse than uncompressed on scattered frames.
  Rejected in favor of the singleton bitmap / Elias-Fano, which have no
  singleton penalty.
- **No sort, write-order runs only**: `O(p)` with no radix pass, but misses
  contiguity written out of order. Since reordering is sound (the frame is a
  set) and radix keeps it `O(p)`, full sort is preferred for maximum ratio.
- **Compressing the value pool via `T`'s bit-structure**: impossible without
  assuming structure in `T`; out of scope. (This is the only value-compression
  claim that holds. The earlier blanket "the value pool is irreducible" was
  wrong: dictionary and value-major encoding compress the pool using `Eq` alone,
  needing no bit-structure — see "Value axis". Kept here as a retracted claim so
  it is not re-proposed.)

## Shipped encoders, per-column decision, and measured space

The value and index axes above are realized and verified. The numbers here are the
design rationale (which scheme a column gets and why), not a build log.

**Value-major (dictionary + codes).** `DictFrame` stores `dict: [T]` (the `D`
distinct values), a `codes` column, and the index column verbatim. `Codes` is
width-adaptive behind a `view: Seq<nat>` contract, so the storage width is invisible
to the frame bijection: byte-granular `U8`/`U16`/`U32` by `D`, and bit-packed
`Packed { words, bits, len }` at 1/2/4 bits for `D <= 16`, `64/bits` codes per `u64`
word with no cross-word straddle. `compress` builds the dictionary with O(N) hashmap
dedup and narrows codes with `Codes::from_usize`. The bijection `decode() == diffs@`
is proven and `Codes::get` is proven against the `packed_code_at` extraction formula;
the two bit-twiddling primitives `pack_codes`/`packed_get` are `external_body` against
that formula (variable-width shifts/masks are not a tractable proof surface, trust
ledger group B, no `unsafe`), checked by the `packed_codes_roundtrip` proptest.
Value-major does not reorder, so it keeps the exact-sequence contract.

**Index-major.** `compress_runs_writeorder` coalesces capture-order runs and
preserves the exact sequence; `compress_runs_sorted` sorts by index first, capturing
all contiguity but reordering. Both drop the index column, reconstructing it from
`start + offset` via `IndexFromNat::from_nat`; `decode_exec_i` is `external_body`
against that spec, checked by `run_frame_roundtrip`.

**Index-major with a verified decode (`RunCol`), for opaque id index types.** The
`from_nat` reconstruction above needs `IndexFromNat`, which the primitive index types
implement structurally but the opaque id types (`DenseId31`/`DenseId63`) cannot: their
range bound is a `type_invariant`, and `from_nat` would have to re-establish it from a
receiver-free spec-mode value, where the invariant is not assumed. Attempting the impl
failed at exactly that point (empty-body postcondition unproven, `use_type_invariant`
rejects a spec-mode argument): recorded negative result. `RunCol<T, I>` sidesteps it. It
stores the same write-order runs but carries a ghost `pairs: Seq<(T, I)>` tied to the
runs by `as_nat` (`run_seq(runs)[j] == (pairs[j].1.as_nat(), pairs[j].0)`), and its
`decode_exec` reconstructs each index with `IndexLike::checked_add(start, offset)`,
which is opaque-id safe. `decode_exec() == decode()` is proved (not `external_body`),
so `RunCol` removes one trusted leaf relative to `RunFrame::decode_exec_i`. `compress`
is the general write-order coalescing builder (`decode() == diffs@` via `run_seq ==
nat_pairs`); `single_run` is its one-run special case for a contiguous frame.

`restore_runs_into` is the fast restore the index-major layout exists for: a run's
values sit at consecutive indices, so restoring a run is one `copy_from_slice` (a
memcpy) into `dst[start..start+len]`, run by run in order, replacing the pair-by-pair
overlay. The slice copy is `external_body` (raw-memory primitive, trust ledger group B);
its contract, that the resulting column equals `dst` with the `decode()` pairs applied
in order, is conformance-checked against the verified `decode_exec` by
`run_col_index_major` (2000 cases). `byte_len` measures the real encoded footprint (one
`start` per run plus the value column); the same proptest asserts it is below plain
`len * (size_of::<T>() + size_of::<I>())` for coalescing frames.

**Shipped on the live path.** `DiffIdxs<I>` = `Plain(Vec<I>)` | `Runs { cold:
Vec<RunCol<(), I>>, tail }` is the index-major dual of `DiffVals`: `cold_idxs`
concatenates each cold frame's `idx_seq` (a `RunCol<(), I>` stores only run starts,
so the index column drops to one start per run), with four lemmas mirroring
`cold_vals` (snoc/at/at_prefix/split). `DiffLog.idxs` is a `DiffIdxs<I>`;
`compact_tail` folds the closed frame's index tail into a cold frame, `index` and
`index_range` reconstruct via `RunCol::idx_at`, and the `Vec` restore path
materializes index ranges through `index_range` (the whole-slice `indices()` is
gone). At most one column compresses at a time (index-major keeps values plain), so
`len` reads the plain column in O(1). `index_major_compaction_tests` drives a live
`IndexRuns` column, in a group of one, through 24 marked frames against a plain
oracle (the `mark_and_compact` entry points were deleted on 2026-09-18: they were
dead-code aliases of `mark`, since compression folds at eviction):
identical contents at every step and after a deep cold restore, `tracking_bytes <
plain`. The follow-up combined mode (index-major runs AND value-dict together, for
the scattered-but-repetitive union-find columns) drops the one-column-at-a-time
invariant and adds a cached `DiffLog` length; it folds into per-column selection.

**The two-stack contract is the per-frame write multiset.** Because sorting reorders,
the two-stack (`CompressedStack`/`TwoStackLog`) cannot preserve the flat `cold@ ++
hot@` sequence. Its contract is `frame_msets(): Seq<Multiset<(T,I)>>` (one multiset
per frame, in stack order): `compress_frame` guarantees `decode().to_multiset() ==
diffs@.to_multiset()` for every mode, `flush_cold` preserves `frame_msets` exactly,
and the flat `@` survives only as one linearization for `pop_frame`. This is sound
because a finalized frame writes each cell once, so the restore overlay is determined
by the write set, not its order (`vec::lemma_multiset_eq_overlay`). Sorting requires
unique indices; `compress_frame` checks `is_unique_idx` at runtime and falls back to
the write-order encoder otherwise, so it carries no uniqueness precondition.

**Per-column decision (measured, `scheme_comparison_bench`; ratio vs plain):**

| shape | plain | idx sorted | val usize | val byte | val packed |
|-------|-------|-----------|-----------|----------|------------|
| union_find D=64 | 1.00x | 1.37x | 1.50x | 0.63x | **0.36x** |
| union_find D=4  | 1.00x | 1.37x | 1.50x | 0.63x | **0.30x** |
| contiguous      | 1.00x | **0.51x** | 2.00x | 1.25x | 0.95x |
| scattered_unique| 1.00x | 1.37x | 2.00x | 1.25x | 0.98x |

Value-major wins the union-find shape (0.30-0.36x packed), the memory-critical eq-sat
column where index-major loses (indices scattered). Sorted index-major wins the
contiguous shape (0.51x). Plain wins scattered-unique. So the per-column defaults are:
union-find `parent`/`rank` value-major (packed), contiguous-batch columns sorted
index-major, everything else plain. Value-major is retained precisely because it is
the only scheme that wins the union-find column.

**The selector costs the shipped widths.** `FrameStats::best_mode`/`code_bits` cost
value-major at the packed bit width and index-major at the sorted run count, so `Auto`
and calibration compare the sizes that actually ship; the runs winner returned is
`IndexRunsSorted`.

**Rejected: plain dict + `usize` codes (negative result, do not re-propose).** As
first built it is 1.50x plain, a loss: a `usize` code is wider than the `u32` value it
replaces and the index column is still stored. Byte-granular then bit-packed codes are
what turn it into the 0.63x / 0.30x win.
