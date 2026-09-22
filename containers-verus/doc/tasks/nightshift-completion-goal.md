# Nightshift goal: finish verified semi-persistence

Work autonomously on branch `d21-exec` in `/Users/remidelmas/projects/sp-d21-exec`
until the remaining semi-persistence work meets every acceptance criterion in
[semi-persistence-completion-goal.md](semi-persistence-completion-goal.md).
Use [three-tier-top-down-proof-engineering.md](three-tier-top-down-proof-engineering.md)
as the proof-engineering plan and preserve the original scope in
[all-tier-semi-persistence-goal.md](all-tier-semi-persistence-goal.md).

## Required outcomes

1. **Mixed-tier mutation and mark:** discharge actual constructor, capture, set,
   push/pop, regrowth and mark implementations for every supported DiffStore
   discipline, preserving public contents, history, error and capture contracts.
2. **Conversions and rollover:** discharge actual transforms, pool assembly,
   migration and configured/forced/adaptive execution. Prove every legal rollover
   sequence preserves logical frame meaning, snapshots and live contents.
3. **Concrete end-to-end theorem:** discharge every provisional interface and
   connect the complete sequence theorem to production public dispatch, including
   mixed-tier restore, survivor reopening, capture rebuilding and mutation followed
   by an older restore. Preserve canonical-history and token contracts.
4. **Derived/parallel closure and final validation:** finish the original container
   and group/parallel scope, reconcile trust and CI documentation, pass all required
   verification/regression gates, and validate conformance benchmark parity with
   the unchanged legacy implementation according to the linked performance protocol.
   Reproducible slowdowns must be fixed; unresolved or inconclusive required
   comparisons keep the goal incomplete.

The linked checklist defines the detailed acceptance criteria and evidence for
each outcome. Do not substitute a narrower interpretation of these summaries.

## Execution instructions

- Start by inspecting the worktree, current commit, progress documents and any
  running verification. Reuse completed evidence and ongoing processes. The last
  recorded verified checkpoint is `d191c4a`; inspect for subsequent work before
  editing. Preserve the newly written goal/checklist documents as well.
- Preserve existing verified work. Reuse matching proofs, adapt insufficient
  contracts and remove superseded proofs only after replacements verify. Do not
  weaken the top-level theorem to fit existing implementations.
- Add no proof holes, assumptions, axioms, trusted semantic wrappers, persistent
  ghost history or increased solver limits. Keep runtime batching, direct Cold
  replay, Trail duplicate appends and existing payload capabilities.
- Tie proofs to actual DiffStore methods and instance discipline. Keep rollover
  selection distinct from writable-tier selection and prove eligibility.
- Keep `containers/` unchanged as the correctness and performance reference.
  Follow the benchmark protocol for matched workloads, repeatability, uncertainty
  and per-case acceptance; aggregate speedups must not conceal regressions.
- Reverify conditional composition after interface changes. Run checks appropriate
  to each milestone and all required gates on the final source revision.
- Update the acceptance checklist and proof-progress records with concrete source
  references, commands, results and remaining dependencies. Commit independently
  verified milestones locally using the authorized signing key. **Do not push to
  origin or publish changes.**
- Do not spawn subagents unless the user explicitly authorizes delegation.
- Continue through routine implementation choices and proof failures. If genuinely
  blocked, record the exact blocker, evidence, attempted resolutions and required
  external input. Do not label incomplete work complete because the night ends.

## Completion and handoff

Declare completion only when all four outcomes and their detailed acceptance
criteria are satisfied. Conditional verification, a passing test suite or the
removal of some trusted bodies alone is insufficient.

Provide a final handoff with signed local commit IDs, completed contract inventory,
per-container proof coverage, final verification/test results, reconciled trust
counts and benchmark ratios with uncertainty. State explicitly that nothing was
pushed. If work remains, identify the outstanding criteria and next concrete
actions without claiming completion or unsupported performance parity.
