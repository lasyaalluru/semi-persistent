## Goal: complete the semi-persistence proofs across all tiers

  Review and finish the verified containers’ persistence proofs. Establish that the actual public execution paths preserve the snapshot-stack contracts, without weakening contracts or hiding obligations behind
  assumptions or trusted wrappers.

  ### Central proof argument

  Fix a target snapshot k and an index i < snapshot[k].len().

  Starting at frame k and moving toward newer frames:

  - If a frame captures i, its earliest capture supplies the value inherited from snapshot k.
  - Otherwise, the frame invariant guarantees that the newer layer contains the same value at i; continue into that layer.
  - If no frame captures i, the live vector contains the target value.

  Thus the winning record is in the oldest frame at or above k that captures i, and within a Trail frame it is the earliest chronological entry. Newest-to-oldest replay writes that winning value last.

  ### 1. Establish one logical frame contract

  Expose a common interpretation for every frame:

  saved_len(f)
  saved_value(f, i): optional value

  Its meaning is:

  - Trail: earliest chronological entry for i.
  - Hot: unique entry for i.
  - Cold: value in the run covering i.

  For every i < saved_len(f):

  Some(v) ⇒ v == snapshot[f][i]

  None ⇒ i < layer_above(f).len()
         && layer_above(f)[i] == snapshot[f][i]

  Here layer_above(f) is the next newer snapshot, or the current live vector for the newest frame.

  Reuse the existing frame_cell_inv, first_hitter, frame_inv_range, and cold_reconstructs definitions. Never assume adjacent saved lengths are monotone.

  ### 2. Prove physical replay against that contract

  Each frame’s replay must:

  - Preserve buffer length.
  - Write its saved value at recorded indices within the buffer.
  - Preserve all other cells.

  Prove Trail replay first to handle duplicate writes explicitly: backward replay makes the earliest capture win. Reuse existing Hot proofs; prove Cold’s disjoint run copies implement the same operation.

  ### 3. Compose across all frames and tiers

  Resize once to L = snapshot[k].len(), preserving the existing live prefix. Replay logical frames newest-to-oldest, physically traversing Trail → Hot → Cold, stopping after the target frame.

  Maintain:

  After processing frame f:
      buffer[i] == snapshot[f][i]
      for every i < min(L, saved_len(f))

  Intermediate snapshots may be shorter than the target. Cells outside their saved domain may remain pending; older frames must reconstruct them before reaching k.

  At f = k, the invariant establishes the entire target snapshot.

  Connect the existing telescope argument to the real runtime. An unused general lemma beside a trusted restore implementation is not completion.

  ### 4. Prove representation changes preserve frame meaning

  For each conversion, preserve frame order, logical identity, saved length, and the per-index saved-value mapping:

  - Trail → Hot: deduplication retains the earliest value.
  - Hot sorting: permutation preserves the unique mapping.
  - Hot → Cold: run formation preserves that mapping.

  Empty frames must survive conversion. Persistent Hot frames need not be sorted.

  Prove rollover policies by composing these conversion theorems, including configured, forced, and adaptive migrations.

  ### 5. Preserve the surviving history after restore

  Restore must also:

  - Remove the target and all newer frames.
  - Retain precisely the older snapshots and physical history.
  - Retain the corresponding canonical ghost-history prefix.
  - Prove any survivor promotion preserves frame meaning.
  - Rebuild capture state for the surviving writable frame.

  The key transfer fact is that surviving frame k−1 sees snapshot[k] as its newer layer both before and after restore.

  Only restore to frame zero may clear the entire canonical history.

  ### 6. Prove invariant preservation and public composition

  Check constructors, writes, push/pop, marks, conversions, and restore against the shared invariant. Cover shrinking below saved lengths, regrowth, duplicate writes, and empty frames.

  Preserve the separation:

  - DiffStore selects capture discipline: Trail versus unique Hot capture.
  - The mark’s rollover argument controls migration.
  - The theorem must cover Trail-only, Hot-only, and mixed-tier histories.

  Keep the existing vector fields. Do not introduce optional tier storage. Unused vectors already avoid heap-buffer allocation.

  Then reverify all derived containers against the checked public Vec contract, including SparseSet, CircularList, ListArena, UnionFind, BPlusTreeSet, EClasses, and SpMap/AppendOnlyVec. Audit public and parallel
  paths for missing contracts or residual trust.

  ### Constraints and completion criteria

  - Preserve public snapshot, depth, and surviving-prefix contracts.
  - Use physical pools and Cold runs as storage authority; never use inert diff_log to justify reconstruction.
  - Add no proof holes, assumptions, or trusted wrappers to obtain verification.
  - Preserve supported runtime behavior and the containers/ differential oracle.
  - Inspect the current worktree and running verification before proceeding; reuse ongoing work.
  - Record and commit independently verified milestones.
  - Require full Verus verification, feature checks, runtime regressions, differential policy tests, and consumer tests.
  - Reconcile trust counts and documentation with the final source.

  Completion means the shared argument is connected through every supported physical path to the public persistence theorems—not merely that a verifier run is green.