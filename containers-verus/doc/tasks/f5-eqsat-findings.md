# F5-EqSat findings: the per-column decision in the big-frame regime

Closes phase F5-EqSat of `h4-f2-f5-correctness-goal.md`. The sweep, the
tables, and the applied configuration; every number names its regenerating
command.

## The workload (F5.1)

`f5_eqsat_sweep` (egraph tests, `--ignored`): 200 generated arithmetic
instances under the growth-heavy ruleset (commutativity, associativity,
distributivity, constant folding), each driven ROUND BY ROUND with a mark per
rewrite round to a 40k-node budget, one mid-run restore and regrow per
instance (the backtracking-EqSat shape, exercising the branch cut). 2,753
marks total; 1,257 to 2,668 sealed frames logged per hot column with real
candidate encodings, under `SEMPER_COMPRESS=auto` and `SEMPER_SHADOW`.
Frames are EqSat scale: the ENodeId (union-find) columns average 4,661
entries per frame against roughly 6 in the SMT corpus.

## The per-column table (F5.2, size axis; ratios vs plain)

| column | frames | entries | plain B | write-order runs | sorted runs | dict | delta | sorted x dict | plain x dict |
|---|---|---|---|---|---|---|---|---|---|
| ENodeId (union-find) | 2,484 | 11,577,149 | 92,617,192 | 0.99 | 0.52 | 0.66 | 1.98 | **0.20** | 0.66 |
| FixedArityNode | 1,257 | 341,834 | 8,204,016 | 1.00 | **0.93** | - | - | 1.46 (RLE) | 1.33 (RLE) |
| ClassData | 1,497 | 277,994 | 6,671,856 | 0.97 | **0.85** | - | - | 1.21 (RLE) | 1.33 (RLE) |
| ListHead | 1,497 | 287,256 | 4,596,096 | 1.00 | 0.98 | - | - | - | - |
| CircularListNode | 1,497 | 277,879 | 3,334,548 | 0.99 | 0.98 | - | - | - | - |
| u32 (pool/aux) | 2,668 | 344,663 | 2,757,304 | 0.97 | **0.57** | - | - | - | - |
| ListNode | 1,275 | 193,201 | 2,318,412 | 1.00 | 0.99 | - | - | - | - |
| u8 (rank) | 2,537 | 55,625 | 278,125 | 0.95 | 0.93 | 0.86 | 2.60 | 2.25 | **0.86** |

Median big ENodeId frame: 4,530 entries, 103 distinct values, 173 sorted
runs (3% distinct: the value column is extremely repetitive at this scale).

## The restore-time axis (F5.2, `f5_restore_axis`, representative frame)

| mode | encoded B | restore wall |
|---|---|---|
| plain (scattered) | 34,920 | 4.7 us |
| sorted runs (sliced memcpy) | 18,092 | **1.3 us** |
| dict (scattered decode) | 22,237 | 11.3 us |
| sorted runs x dict | **6,673** | 9.9 us |
| plain x dict | 22,237 | 8.5 us |

The size/speed trade is real and quantified: the composed mode buys 2.7x
bytes over sorted runs at 7.6x its restore wall.

## Verdicts (F5.3)

- **Dict at EqSat scale: CONFIRMED against plain, superseded by the composed
  mode.** The SMT refutation (1.12x at ~6-entry frames) reverses to 0.66x at
  4,661-entry frames; the synthetic 0.30x is not reproduced by dict alone,
  and the COMPOSED sorted-runs-x-dict reaches 0.20x, which is the number the
  hypothesis was chasing. The index layer and value layer win independently
  and compose.
- **Delta: REFUTED at both scales** (1.98x here, previously 1.12-2.6x on
  SMT). Successive-difference coding fights the union-find's value
  distribution instead of exploiting it.
- **Equality-RLE on struct columns: REFUTED at both scales** (1.21-1.46x
  here, 1.33-1.44x on SMT): even EqSat rounds write DISTINCT node and class
  payloads, so equality runs degenerate. The struct columns' win stays the
  index layer (0.85-0.93x).
- **Sorted runs everywhere: CONFIRMED** as the universal default (0.52-0.99x,
  never losing after self-demotion), consistent with the SMT-scale finding.

## The applied configuration (F5.4)

Union-find `parent` and `rank` ship as `ValueDictC` columns; every other
column ships `NoValueCompression` (struct RLE refuted, other id columns'
composed candidates dominated by their sorted-runs base). The selector is
what makes this a per-frame decision: at SMT frame sizes the dict candidates
lose the byte costing and the columns self-demote to exactly the pre-F5
behavior, which is why the Sundance corpus is unchanged under the applied
configuration.

End-to-end re-measurement on the sweep (`/usr/bin/time -l`, 200 instances):
149.0s wall / 1,347.8 MB peak RSS before, 149.6s / 1,349.5 MB after:
NEUTRAL on both axes, and the profile explains it rather than asserts it:
sealed frames at depth <= 28 hold about 1 MB per instance against a peak
dominated by the live stores and interpreter allocations. The frame-level
win (92.6 MB of plain ENodeId frames encoding to about 18.6 MB) becomes an
end-to-end win only when sealed-frame depth or width grows by orders of
magnitude; revisit if a workload is measured to hold hundreds of deep
frames live (long non-backtracking saturation with per-round marks retained).

Regenerate: sweep `SEMPER_COMPRESS=auto SEMPER_SHADOW=<file> cargo test
--release --test f5_eqsat_sweep -- --ignored --nocapture`; restore axis
`cargo test --release --test f5_restore_axis -- --ignored --nocapture`;
aggregation by element type over the SHADOW/SHADOWF lines.
