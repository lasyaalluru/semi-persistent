# C1 findings: the 26 incorrect corpus results

Closes phase C1 of `h4-f2-f5-correctness-goal.md`. Two independent defects, both
diagnosed from evidence, both fixed on this branch. The corpus reports
**Incorrect: 0** with and without `SEMPER_COMPRESS=auto` (438 total, 427 correct,
0 incorrect, 11 timeout, identical splits). Regenerate with:

    cargo test --release --no-default-features --features semper-egraph \
      --test regression_test regression_test -- --nocapture

**The branch-divergence hypothesis is refuted.** The goal assumed the 26 failures
came from divergence between this branch and the satcore-layer0 pin `ec1eb8ae`
the Sundance adapter was written for. Running one failing instance against a
worktree at the pin and against a pre-compression tree reproduced the same
failure at both: neither defect is compression work and neither is branch
divergence. Do not cite the goal's starting-state paragraph as the diagnosis.

## Defect 1: cache restore re-read deleted suffix nodes (24 of 26 files)

24 of the 26 "incorrect" results were crashes, not wrong answers: the harness
records an aborted solve as incorrect. The abort was the runtime contract guard
(`guard.rs check_precondition`, `Vec::get_index: index out of bounds`) firing in
`notify_backtrack` under `FixedArityCache::restore`.

`note_dirty` filters a re-keyed node against the TOP frame's `saved_len` at push
time, but a restore can target an OLDER frame with a smaller `saved_len`: a node
added after that frame's mark and later re-keyed sits in `dirty` yet belongs to
the suffix the restore deletes, and re-inserting its entry read a rolled-back
slot. The restore now skips dirty ids at or above the target frame's
`saved_len`; a debug-build assertion checks the incremental index against the
from-scratch rebuild on every restore, and both cache types carry a regression
test for the re-keyed-inner-suffix-node case. Fixed in commit
`egraph: restore re-inserts only dirty ids that survive the target frame`.

The verified layer is not implicated: the guard fired because a `requires`
clause was violated by unverified cache code, which is the guard doing its job.
The unproven surface this exposed is the cache's hashcons index invariant,
previously a `debug_assert` on nothing; it is now checked against the rebuild
reference in debug builds.

## Defect 2: unsound conflict clauses from the true=false-collision fallback (2 files)

`datatypes/tester_duplication_unknown{2,6}` answered `unsat` where the expected
answer is `unknown` (z3 times out at 600s, cvc5 answers unknown under fmf and
enum-inst: no external oracle decides the instances, so an unsat needs a valid
proof). The final UF lemma in the eDRAT proof was mechanically invalid: z3
answers `sat` on the conjunction of its five premises (`/tmp/lemma_validity.smt2`
at the time of the diagnosis; rebuild it from the `--proof` output's
`edrat-literal` declarations).

The adapter's true=false-collision fallback emitted conflict clauses whose
antecedent set cited assumption pairs about terms that had interned onto nodes
CREATED by syntactically different terms. Hash-cons keys on canonical children,
so merely class-equal children suffice to reuse a node, and that equality
judgment is never recorded as a forest edge; the explanation walked the forest
and omitted it. On the failing file the collision path was two assumptions
(`or`-atom = true, different `or`-atom = false) over one shared node, and the
child-level conflation repeated one level down.

The fix grounds every cited term to its node's first registrant
(`node_to_driver`, whose syntax the node's stored children match), recursively
through the matched children, on a worklist that also aligns terms cited by
pairs the alignment itself appends; chains terminate because a creator
registered before any term that interns onto its node. A child the alignment
cannot match by class taints the run and the driver widens `unsat` to
`unknown` (`EgraphTrait::refutation_tainted`): strictly sound-direction. Fixed
in Sundance commit `semper: ground true=false-collision antecedents through
intern-time conflations`.

Two rejected fixes, recorded so they are not re-run: a blanket taint whenever
the fallback fires degrades 203 corpus answers to incorrect (the fallback fires
on legitimate refutations and the taint sticks for the solve); a taint only on
the expansion's skip branches keeps the corpus at 425 correct but misses these
two files (the skip branches never execute on them).

## Timeout split movement

Correct went 425 to 427 and timeout stayed 11: the crash fix converted 24
crashes to 22 correct answers plus 2 honest timeouts under the harness's 10s
cap (heavy Verus/SplinterDB-generated instances, e.g.
`arithmetic/subtraction.smt2`), while the two unsound files moved from
incorrect to correct (`unknown` as expected) and two prior timeouts resolved.
Direct single-file runs must pass `--infer-triggers` as the harness does:
without it, untriggered foralls diverge and any comparison is meaningless.

## Open follow-through

The Sundance pin still names `ec1eb8ae`; the working tree overrides it with a
path dependency. Bumping the pin needs this branch pushed to a remote first,
at or past commit `egraph: restore re-inserts only dirty ids that survive the
target frame`.
