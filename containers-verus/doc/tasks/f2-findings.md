# F2 findings: the ValueCompressor strategy and the layered modes

Closes phase F2-full of `h4-f2-f5-correctness-goal.md`. Every number names the
test or command that regenerates it.

## What was built (all verified, `cargo verus verify` 0 errors at each commit)

- **F2.1** (`value_compressor.rs`): the `ValueCompressor<T>` trait with exact
  `decode` ensures, and the four bound-on-the-codec impls:
  `NoValueCompression` (`T: Copy`), `ValueRle` (`T: Copy + EqSpec`),
  `ValueDictC` (`T: IndexLike`, delegating to the verified `ValFrame`),
  `ValueDelta` (`T: IndexLike`, successive difference with a ghost model
  carrying the in-range arithmetic). Conformance: 1000-case proptest
  round-trip per codec (`value_compressor_conformance`).
- **F2.2** (`layered.rs`): `LayeredFrame<T, I, VC>`, index layer {plain,
  write-order runs, sorted runs} x any codec on ONE frame, with a
  `RunCol`-style ghost model. Non-sorting compressors are exact; sorted runs
  carry the write multiset. The seven composed modes plus runs x RLE
  round-trip under 1000 proptest cases each against the reference application
  (`layered_conformance`); runs x dict measured at least 4x below plain on a
  bursty small-alphabet frame.
- **F2.3**: `Vec<T, I, S, TRACK, VC = NoValueCompression>` and
  `DiffLog<T, I, VC>` thread the strategy to the per-frame cold tier
  (`ColdFrame` gained the `Layered` arm); every existing use compiles
  unchanged through the defaults. Illegal pairings fail to typecheck at BOTH
  levels: the codec (`ValueDictC` at a struct) and the column (a
  struct-element `Vec` declared with `ValueDictC`), each a `compile_fail`
  doc-test.
- **F2.5**: `ColdFrame::select_layered` ranges over index layer x value layer
  when the column's codec answers `enabled()` (the identity codec does not,
  so default columns pay nothing), self-demoting through the base to plain.
  The live differential (`vec::layered_selector_tests`): a `ValueDictC`
  column and a default twin agree at every mark and after a deep restore, and
  the layered column's diff log lands strictly below the index-only twin's.

## F2.4: struct columns, MEASURED, and the RLE negative

The node-cache structs (`FixedArityNode`, `VariableArityNode`) implement
`EqSpec` as trusted one-liners in the unverified e-graph crate (reprs compare
through `(from_repr, tag)`, equal to repr equality on well-formed reprs by
`Tagged`'s extensionality); `ClassData`'s `EqSpec` is fully verified in
`eclasses.rs` (ids through `as_usize` plus injectivity, the negative
direction by contrapositive). With all five struct columns instantiated at
`ValueRle`, the full corpus ran under `SEMPER_COMPRESS=auto` with
`SEMPER_SHADOW` logging every frame's real candidate encodings (438 total /
427 correct / 0 incorrect / 11 timeout, unchanged):

| column type | frames | entries | plain B | sorted-runs B | layered sorted x RLE | layered plain x RLE | frames choosing RLE |
|---|---|---|---|---|---|---|---|
| FixedArityNode | 39,272 | 222,233 | 5,060,068 | 4,615,528 | 7,282,176 | 6,837,932 | 0 |
| ClassData | 9,845 | 103,295 | 2,479,080 | 2,286,848 | 3,555,104 | 3,305,440 | 0 |
| VariableArityNode | 537 | 973 | 35,028 | 33,784 | 46,864 | 42,812 | 0 |

**RLE refuted on SMT struct frames**: 1.33x to 1.44x of plain on every
column, zero wins in 49,654 frames, because SMT frames write DISTINCT struct
values (each captured node or class payload differs), so equality runs
degenerate to one run per entry plus a count word. The selector self-demoted
on every frame, so the live bytes stayed exactly the index-layer choice
(sorted runs, 0.91x on the biggest pool). Per the goal's own rule the columns
ship `NoValueCompression` under the SMT profile, with the refutation recorded
at the declaration sites; the `EqSpec` capability and the one-line
re-instantiation remain for the EqSat-scale revisit (F5), where frames are
per-rewrite-round and repeated payloads are the hypothesis to test.

Regenerate: instantiate the columns with `ValueRle`, then
`SEMPER_COMPRESS=auto SEMPER_SHADOW=<file> cargo test --release
--no-default-features --features semper-egraph --test regression_test` in the
Sundance checkout and aggregate the SHADOW lines by element type.

## Interface deviations from the predecessor appendix (its own rule: record with reasons)

- `ValueRle` bounds `T: Copy + EqSpec`, not `Copy + PartialEq`: an exec
  `PartialEq` call proves nothing in Verus, and RLE's exactness turns on the
  coalesced value BEING the input value.
- `ValueDelta` codes against the previous value, not the cell index: the
  interface sees only the value column; against-cell-index delta remains
  `DeltaFrame` (F3) at the `(value, index)` level.
- `DiffStore`'s two methods gained a method-level `VC` generic: their
  signatures name `DiffLog`, which the appendix's "the store never sees
  compressed bytes" did not account for. No store impl gained any obligation.
