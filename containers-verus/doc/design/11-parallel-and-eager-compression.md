# Parallel frame compression and eager active-frame compression

Two investigations into moving compression work off the critical path. Both are
measured, and the measurements decide the design. This is not a status page: what
ships is what the benches and CI assert.

## Parallel per-column compress/restore (rayon), measured 2026-09-07

A composite (union_find = 2 columns, sparse_set = 3, the e-graph `EClasses`
aggregate = ~10 leaf columns) is a set of independent columns with disjoint backing
stores, so at mark time each can compress its own frame on a separate thread with no
locks and no data race (the borrow checker proves the `&mut` columns disjoint), and
at restore each reconstructs independently. The shared fork history does its O(1)
stamp step once, sequentially; only the per-column frame work fans out.

**Feasibility: rayon coexists with `cargo verus verify`.** Adding rayon and calling
it from an `external_body` fn leaves the crate verifying at 1833/0. The per-column
`flush_cold`/`restore_frame`/`compress_frame` stay fully verified; only the fan-out
is `external_body` (trust ledger group B, scoped joins over disjoint `&mut`, no
`unsafe`). Because independent columns produce identical results in any order, the
existing differential oracle checks a parallel path against the sequential semantics
for free.

**Measured win (`parallel_frame_bench`, K frames compressed sequentially vs on the
rayon pool, `compress` per frame):**

| columns | frame entries | total work | sequential | rayon | speedup |
|---------|---------------|-----------|-----------:|------:|--------:|
| 2  | 64    | 128    | 7.4µs   | 44µs  | 0.17x |
| 2  | 1024  | 2048   | 36µs    | 55µs  | 0.66x |
| 2  | 4096  | 8192   | 110µs   | 83µs  | **1.32x** |
| 2  | 16384 | 32768  | 399µs   | 231µs | **1.73x** |
| 5  | 1024  | 5120   | 92µs    | 92µs  | 1.00x |
| 5  | 4096  | 20480  | 277µs   | 154µs | **1.80x** |
| 5  | 16384 | 81920  | 1003µs  | 308µs | **3.25x** |
| 10 | 256   | 2560   | 89µs    | 73µs  | **1.21x** |
| 10 | 1024  | 10240  | 184µs   | 93µs  | **1.98x** |
| 10 | 16384 | 163840 | 2009µs  | 381µs | **5.3x** |

**Decision: parallelize above ~4000 total diff entries across the composite; run
sequentially below it.** The rayon pool has a fixed dispatch cost of ~40-60µs, so on
small frames it loses (0.17x at 2 columns of 64). The crossover is ~4000 total
entries, roughly independent of how the work splits across columns; above it the
speedup grows with both column count and frame size, reaching 5.3x at 10 columns of
16384. The e-graph aggregate is 5-10 leaf columns, so at eq-sat frame sizes (100s to
1000s of writes per column) it sits at or above the crossover. `parallel::
PAR_THRESHOLD` is set to 4096 total entries.

## Eager active-frame compression (compress-on-write), measured 2026-09-07

Today the active frame accumulates raw `(value, index)` writes on a plain `Vec` and
compression happens lazily at `mark`/`flush`. The alternative compresses the active
frame as writes arrive, trading a cheaper write for a smaller, cache-friendlier hot
frame. Whether that trade pays is a measurement.

**Measured write-path cost and resulting hot-frame size (`eager_write_bench`, 4096
writes; per-write cost is the interesting axis because the write path is the e-graph's
hottest loop):**

| column shape | plain | eager value-major | eager index-major (write-order) |
|--------------|------:|------------------:|-------------------------------:|
| union-find (D=4, scattered) | 2.1µs / 32KB | 31µs (15x) / **17KB (0.53x)** | 78µs (37x) / 32KB |
| contiguous batch (D=N)      | 2.1µs / 32KB | 119µs (56x) / 33KB | **6.6µs (3x) / 16KB (0.50x)** |
| scattered unique (D=N)      | 2.1µs / 32KB | 119µs (56x) / 33KB | 78µs (37x) / 32KB |

**Eager value-major loses on the write path.** One hashmap get-or-insert per write
costs 15x (D=4) to 56x (D=N, the dict grows to N and the map thrashes) the plain
push, and the hot-frame size win (0.53x) appears only on value-repetitive columns.
Plain push is ~0.5ns, so 15x is ~7.6ns per write; on the write-heavy SMT profile
(billions of parent/rank writes) that added time is not plausibly offset by the
smaller frame. Recommendation: keep value-major LAZY (compress at flush), which is
what ships.

**Eager index-major write-order is the promising variant, on contiguous columns
only.** Extending the current run when the index is contiguous needs no hashing: on a
contiguous batch column it costs 3x the plain push (6.6µs, still tiny in absolute
terms) and HALVES the hot frame (drops the index column). On scattered columns it is
a 37x loss with no size win, but that number is inflated by this microbench's naive
run representation (a `Vec` allocation per run); a flat value pool with run-boundary
offsets would remove the per-run allocation and bring the scattered case near plain,
with the win preserved on contiguous columns.

**Decision: not a global default; a per-column calibrated knob.** The average effect
depends entirely on the column's write/restore ratio and index shape, which is
exactly what `CalibrationPolicy` already decides per column. Eager index-major
write-order is worth an end-to-end saturation measurement on contiguous-batch columns
(with a flat run pool, not the microbench's per-run `Vec`); eager value-major is not,
given the measured write tax. Neither is built yet. There is also a latency angle not
measured here: eager compression spreads the compress cost across writes instead of a
burst at `mark`, flattening mark-time spikes and reducing what the parallel flush
above has to fan out.
