# Poseidon / OneGraph Data: Ingestion and Reasoning

**Status**: design for future work; nothing in this document is implemented.
It records how data shaped like Amazon Neptune Analytics' Poseidon engine
(Bebee et al., "Poseidon: A OneGraph Engine", arXiv:2510.11166, 2025) could be
loaded into this engine, what reasoning and data transformation the existing
machinery would enable over it, the semantic decision that must be ruled
before any code, and the measurements that decide whether the approach scales
past a demo. It builds on [datalog-integration.md](datalog-integration.md)
and inherits its caveat: statements-as-terms is the relations-as-unit-functions
encoding, and that encoding is an option to measure, not an already wired API.

## 1. The source model

Poseidon's 1G model unifies RDF and labeled property graphs as SPOI
statements: subject, predicate, object, plus a statement identifier (SID)
that may itself appear as the subject or object of other statements
(meta-edges, meta-properties; the RDF-star pattern). Physically the engine
stores 13 dictionary-encoded relations over partitioned heaps; two
dictionaries map IRIs and literals to 64-bit identifiers, of which 28 bits
are a partition-local id (at most 256M elements per partition).

Two facts about the source matter for ingestion:

- **There is no public physical format.** Durability is an internal logical
  log plus S3 checkpoints. Loading Poseidon data means consuming Neptune's
  export surface (RDF / RDF-star dumps, CSV), not attaching a store.
- **Duplicate statements are legal.** Multiple statements with identical
  S, P, O may coexist (LPG multi-edges); identity is the SID, not the triple.

## 2. Ingestion path

1. Parse N-Quads / Turtle / RDF-star with an off-the-shelf Rust parser (rio
   or the oxigraph parser family); do not write a parser.
2. Map both Poseidon dictionaries onto the engine's interning layer: IRI and
   literal lexical forms intern to ids exactly as `map_intern` does today.
3. Emit one term per statement (section 3) and one atom per vertex, literal,
   and SID.

The id-width limit is real: the engine's `define_id31!` ids hold 2^31
elements against Poseidon's 64-bit space. A single partition's worth of data
(<= 256M elements) fits; multi-partition stores do not without widening ids.
Scope ingestion to analytics subsets and record the widening as its own task
if a workload is measured to need it.

## 3. Data model: statements as terms, SIDs as atoms

A statement becomes the term

    stmt(S, P, O, sid)

where `sid` is a fresh atom (a nullary constant), not a structural product of
S, P, O. This one argument carries the load:

- **Multi-edges survive.** Two statements with equal S, P, O differ in their
  `sid` argument, so hash-consing does not conflate them.
- **Congruence stays sound.** Merging two vertices makes the corresponding
  `stmt` terms congruent *except* in the `sid` position, so distinct
  statements' identities - and therefore their meta-properties - are not
  silently merged. Without the explicit `sid` argument, a vertex merge would
  unify unrelated statements, which is wrong under LPG semantics.
- **Meta-edges are free.** A statement about a statement is a term whose S or
  O position holds another statement's `sid` atom. Poseidon needs seven extra
  relations for this; a term store needs nothing.

**The open ruling (blocks everything downstream).** When two vertices merge,
should duplicate statements that become S,P,O-identical unify or stay
distinct? RDF semantics says triples are a set (unify); LPG multi-edge
semantics says identity is the edge, not the endpoints (stay distinct). The
`sid`-argument encoding implements "stay distinct" and can recover "unify" by
a rewrite rule that merges sids of congruent-modulo-sid statements; the
reverse direction is not recoverable. Rule which semantics the first workload
needs before writing the ingestion.

## 4. Reasoning the existing machinery enables

- **Congruence closure over graph identity.** `sameAs`-style merges are
  unions; congruence propagates the merge through every statement mentioning
  the merged vertices. Functional-property inference (two objects of a
  functional predicate for one subject merge) is one rewrite rule plus the
  existing closure.
- **Multi-hop rules as worst-case-optimal joins.** Graph inference rules
  (transitivity, property chains, type propagation) are conjunctive queries
  over `stmt` atoms. The engine already matches rules by leapfrog triejoin
  over sorted cursors (`leapfrog.rs`, Veldhuizen ICDT 2014) with semi-naive
  deltas (`IndexStore::build_delta`, the `Difference` cursor), so the join
  machinery is present, not future work. What the SPOI workload adds is
  access-path demand - (P,S)->O and (P,O)->S orderings - which are
  argument-position indexes of `stmt` terms, the same shape the existing
  child-position fan-outs serve.
- **Speculative reasoning, which Poseidon does not have.** Poseidon offers
  MVCC snapshots; this engine offers mark / hypothesize / propagate /
  restore. The paper's own motivating example (a compromised phone makes all
  newer actions suspect) is a semi-persistent transaction: mark, assert the
  taint edge, saturate, read the consequences, restore. That is the
  differentiating capability, and it is already the engine's core discipline.

## 5. Data transformations enabled

- **Canonicalization and deduplication**: hash-consing plus closure yields
  the quotient graph under any asserted equalities - entity resolution as a
  by-product of representation.
- **Materialized inference**: saturation under a rule set materializes
  derived edges (closures, hierarchies) that Poseidon's query layer would
  recompute per query.
- **Model harmonization**: 1G's LPG-vs-RDF impedance (local ids vs IRIs,
  properties vs triples) becomes rewrite rules between term shapes rather
  than engine features; both views coexist in one e-graph and extraction
  chooses a view.

## 6. Limits, stated with their triggers

- **Deletions are structural, not incremental effort.** Semi-persistence
  gives rollback, not retraction; a live mutating graph does not fit.
  Monotone workloads (accreting fraud evidence, static snapshots) do.
- **Memory density.** An e-node costs several times Poseidon's 16-byte
  topology tuple; expect a 5-10x footprint against their figures. This bounds
  the subset size, not the design.
- **Ordering quality on skewed data.** Leapfrog's worst-case bound does not
  rescue a bad trie ordering on celebrity vertices and hot predicates;
  Poseidon leans on cost-based ordering from collected statistics, this
  engine on compile-time heuristics plus `seek_stats`. Which one binds first
  is a measurement, not an inference.

## 7. Work items

1. **Rule the duplicate-statement semantics** (section 3). Acceptance: the
   decision and its losing alternative recorded here, with the workload that
   forced it.
2. **Ingestion frontend**: RDF-star dump -> interned `stmt` terms.
   Acceptance: a Neptune export round-trips through ingestion and extraction
   with statement count and dictionary sizes matching the source's reported
   counts.
3. **The three scale measurements**, each against a public graph dataset of
   a few million statements: (a) leapfrog seeks per saturation round on a
   2-3 hop rule, planner ordering vs adversarial ordering; (b) `IndexStore`
   rebuild throughput per round at that scale; (c) resident bytes per
   statement against Poseidon's 16-byte baseline. Acceptance: numbers in
   `doc/benchmarks/` with the bench that regenerates them; each ceiling
   either cleared for the target subset size or recorded with its tuning
   task.
4. **Hypothetical-reasoning demo**: the paper's fraud scenario as a
   mark/saturate/restore transaction over an ingested subset. Acceptance: a
   conformance-style test asserting the tainted-consequence set appears
   under the mark and vanishes after restore.
