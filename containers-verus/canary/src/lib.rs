// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Egraph shape canary.
//!
//! Each module instantiates the verus containers API with shapes lifted
//! verbatim from the egraph container inventory. A fixture compiling IS the
//! test; smoke tests in `tests/` exercise a handful of operation sequences.
//!
//! It provides two independent checks:
//!
//! 1. [`tagged_fuzzer_template::check_tagged_laws`] is the only executable
//!    check of the `Tagged` refinement laws in the workspace. Consumer-side
//!    `Tagged` impls are trusted code (trust group E,
//!    `doc/design/02-trust-boundary.md` §3.5) and the egraph's six impls
//!    (`classes.rs`, `director.rs`, `union_find.rs`, `node_types.rs` ×3) rely
//!    on this consumer-shaped contract check.
//! 2. The fixtures pin API shapes at their *narrowest* usable form, so a
//!    signature change that the egraph happens to tolerate still breaks here.
//!
//! The `compat-*` features select fixture groups; `compat-all` enables every
//! fixture and is the CI configuration.

#![allow(dead_code)]

use semi_persistent_containers_verus as cv;

// ---------------------------------------------------------------------------
// Always-on fixtures: shapes the CURRENT verus API already serves.
// ---------------------------------------------------------------------------

/// AU arenas store heap payloads in AppendOnlyVec (mcgs.rs:181,395-397):
/// `AppendOnlyVec<Vec<TransportActionDesc>>`, `AppendOnlyVec<Vec<u32>>`, ...
/// AppendOnlyVec has no `T` bound — heap elements must keep working.
mod aov_heap_payloads {
    use super::cv;

    struct TransportActionDescShaped {
        left: Vec<(u32, u32)>, // Monomial<C> = Vec<(C, u32)>
        right: Vec<(u32, u32)>,
        legal_cells: Vec<bool>,
    }

    // The index word is `u32`, matching `DefaultConfig::Index` at the AU sites these
    // shapes mirror: an arena slot per spilled matrix, addressed by the same word the
    // config's ids use.
    struct OrStatsArenaShaped {
        transport_descs:
            cv::append_only_vec::AppendOnlyVec<Vec<TransportActionDescShaped>, u32, true>,
        transport_rows: cv::append_only_vec::AppendOnlyVec<Vec<u32>, u32, true>,
        transport_cell_map: cv::append_only_vec::AppendOnlyVec<Vec<Option<u32>>, u32, true>,
    }

    fn build() -> OrStatsArenaShaped {
        OrStatsArenaShaped {
            transport_descs: cv::append_only_vec::AppendOnlyVec::new(),
            transport_rows: cv::append_only_vec::AppendOnlyVec::new(),
            transport_cell_map: cv::append_only_vec::AppendOnlyVec::new(),
        }
    }

    pub fn smoke() {
        let mut a = build();
        a.transport_rows
            .try_push(vec![1, 2, 3])
            .expect("push: within index word");
        let row: &Vec<u32> = a.transport_rows.get(0);
        assert_eq!(row.len(), 3);
    }
}

/// TermPool ops log (au/terms.rs:38): `AppendOnlyVec<TermOp<O,V>>` where
/// TermOp derives Clone but NOT Copy.
mod aov_clone_only_payload {
    use super::cv;

    #[derive(Clone)]
    enum TermOpShaped {
        EGraph(u32),
        Literal(u32, u64),
        Variants,
    }

    struct PoolShaped {
        ops: cv::append_only_vec::AppendOnlyVec<TermOpShaped, u32, true>,
    }

    pub fn smoke() {
        let mut p = PoolShaped {
            ops: cv::append_only_vec::AppendOnlyVec::new(),
        };
        p.ops
            .try_push(TermOpShaped::Variants)
            .expect("push: within index word");
        p.ops
            .try_push(TermOpShaped::EGraph(7))
            .expect("push: within index word");
        assert_eq!(p.ops.len(), 2);
        let _ = p.ops.get(1);
        let _ = TermOpShaped::Literal(0, 0);
    }
}

/// UnionFind's dual-vec shape (union_find.rs:121-128) at the CURRENT verus
/// surface: DenseId31 payload indexed by its own Index type, u8 rank vector.
/// (The macro-generated egraph ids arrive with compat-ids.)
mod union_find_shaped {
    use super::cv;
    use cv::dense_id::DenseId31;

    type ParentVec =
        cv::vec::Vec<DenseId31, u32, cv::inline_store::InlineStore<DenseId31, u32>, true>;
    type RankVec = cv::vec::Vec<u8, u32, cv::inline_store::InlineStore<u8, u32>, true>;

    /// The pair of columns a union-find keeps in lockstep, driven by one
    /// external history: the shape a consumer writes now (the columns carry no
    /// tokens of their own, the group mints one stamp for both).
    type UnionFindShaped = cv::group::ForkHistory<cv::group::Pair<ParentVec, RankVec>>;

    pub fn smoke() {
        let mut uf: UnionFindShaped =
            cv::group::ForkHistory::new(cv::group::Pair::new(ParentVec::new(), RankVec::new()));
        uf.member
            .a
            .try_push(DenseId31::new(0))
            .expect("push: within index word");
        uf.member.b.try_push(0u8).expect("push: within index word");
        // One mark for the pair; both columns advance in lockstep.
        let tok = uf
            .mark(cv::vec::ShrinkPolicy::Never)
            .expect("mark: depth bounded by this harness");
        uf.member
            .a
            .try_push(DenseId31::new(1))
            .expect("push: within index word");
        uf.member.b.try_push(1u8).expect("push: within index word");
        assert!(uf.is_valid(tok));
        // One restore moves both columns; the checkpoint stays valid after it
        // (semantics B).
        assert!(uf.restore(tok), "restore: the group's own live token");
        assert!(uf.is_valid(tok));
        assert_eq!(uf.member.a.len(), 1);
        assert_eq!(uf.member.b.len(), 1);
        // The fused pop lands below the checkpoint and kills it.
        assert!(uf.restore_and_pop(tok));
        assert!(!uf.is_valid(tok));
        assert_eq!(uf.depth(), 0);
    }
}

/// EClasses' min_pool (classes.rs:208): `VecP<Opt<T>, usize, TRACK>` — Opt is
/// deliberately NOT Tagged, so it must ride in a ParallelStore.
mod min_pool_shaped {
    use super::cv;
    use cv::dense_id::DenseId31;
    use cv::opt::Opt;

    type MinPool = cv::vec::Vec<
        Opt<DenseId31>,
        usize,
        cv::parallel_store::ParallelStore<Opt<DenseId31>, usize>,
        true,
    >;

    pub fn smoke() {
        let mut pool = MinPool::new();
        pool.try_push(Opt::some(DenseId31::new(5)))
            .expect("push: within index word");
        let o = pool.get(0usize);
        assert!(o.is_some());
    }
}

/// EGraph's unit_node / inverse_op maps (egraph.rs:102-108) at the Copy-key
/// surface available today: SpUniqueMap<Copy, Copy>.
mod copy_key_maps {
    use super::cv;

    // Index word `u32`, as at the egraph sites: both maps are keyed by an operator id
    // whose `Index` is the config word, so a log position shares that word.
    struct EGraphMapsShaped {
        unit_node: cv::map::SpUniqueMap<u32, u32, u32, true>,
        inverse_op: cv::map::SpUniqueMap<u32, u32, u32, true>,
    }

    pub fn smoke() {
        let mut m = EGraphMapsShaped {
            unit_node: cv::map::SpUniqueMap::new(),
            inverse_op: cv::map::SpUniqueMap::new(),
        };
        m.unit_node
            .try_insert(1, 100)
            .expect("insert: within index word");
        m.inverse_op
            .try_insert(2, 3)
            .expect("insert: within index word");
        assert!(m.unit_node.contains_key(&1));
        assert_eq!(m.inverse_op.id_of(&2), Some(0));
    }
}

/// Template for fuzzing a custom `Tagged` implementation's contract.
///
/// Egraph implements `Tagged` on its own types (Justification, EClassEntry,
/// ClassData, PoolDirector, node types). Those impls are consumer-side trusted
/// code; each gets a fuzzer stamped from this template: recompute the spec
/// projections in plain Rust from public state, assert the exec methods refine
/// them, over randomized cases.
pub mod tagged_fuzzer_template {
    use super::cv;
    use cv::tagged::Tagged;

    /// Justification-shaped enum (union_find.rs:99): `(bool, Self)` pair repr
    /// via BoolTagged — the shape the production tuple blanket impl serves.
    #[derive(Copy, Clone, PartialEq, Debug, Default)]
    pub enum JustificationShaped {
        #[default]
        Filler,
        Root,
        ChildOf(u32, u16, bool),
    }

    impl Tagged for JustificationShaped {
        type Repr = cv::tagged::BoolTagged<JustificationShaped>;
        fn into_repr(self) -> Self::Repr {
            cv::tagged::BoolTagged {
                tagged: false,
                value: self,
            }
        }
        fn from_repr(r: &Self::Repr) -> Self {
            r.value
        }
        fn tag(r: &Self::Repr) -> bool {
            r.tagged
        }
        fn set_tag(r: &mut Self::Repr) {
            r.tagged = true;
        }
        fn clear_tag(r: &mut Self::Repr) {
            r.tagged = false;
        }
    }

    /// The refinement laws every Tagged impl must satisfy at runtime. A
    /// consumer impl's fuzzer calls this with randomized values.
    pub fn check_tagged_laws<T: Tagged + Copy + PartialEq + core::fmt::Debug>(val: T) {
        let mut r = val.into_repr();
        assert!(!T::tag(&r), "into_repr must clear the tag");
        assert_eq!(T::from_repr(&r), val, "from_repr(into_repr(v)) == v");
        T::set_tag(&mut r);
        assert!(T::tag(&r), "set_tag must set the tag");
        assert_eq!(T::from_repr(&r), val, "set_tag must preserve the value");
        T::clear_tag(&mut r);
        assert!(!T::tag(&r), "clear_tag must clear the tag");
        assert_eq!(T::from_repr(&r), val, "clear_tag must preserve the value");
    }

    pub fn smoke() {
        check_tagged_laws(JustificationShaped::Filler);
        check_tagged_laws(JustificationShaped::Root);
        check_tagged_laws(JustificationShaped::ChildOf(0x7FFF_FFFF, 42, true));
    }
}

// ---------------------------------------------------------------------------
// Feature-gated fixtures: land with their parity phase.
// ---------------------------------------------------------------------------

/// E-graph-shaped `define_id` invocations (id.rs, nodes.rs, au/mod.rs).
#[cfg(feature = "compat-ids")]
mod id_macro_shapes {
    use super::cv;

    cv::define_id31! { pub struct ENodeIdShaped / StoredENodeIdShaped, "e"; }
    cv::define_id31! { pub struct SortIdShaped / StoredSortIdShaped, "s"; }
    cv::define_id15! { pub struct RuleIdShaped / StoredRuleIdShaped, "r"; }
    cv::define_id7! { pub struct TinyIdShaped / StoredTinyIdShaped, "t"; }
    cv::define_id63! { pub struct WideIdShaped / StoredWideIdShaped, "w"; }

    pub fn smoke() {
        let mut f = cv::IdFactory::<ENodeIdShaped>::new();
        let a = f.alloc();
        let b = f.alloc();
        assert_ne!(a, b);
        assert_eq!(a.to_usize(), 0);
        assert_eq!(f.count(), 2);
        // Eq/Ord/Hash mask the MSB; Display carries the prefix.
        assert_eq!(format!("{}", a), "e0");
        // VecI over a macro-generated id: index AND payload.
        let mut v: cv::VecI<ENodeIdShaped, u32, true> = cv::VecI::new();
        v.try_push(a).expect("canary: capacity");
        assert_eq!(v.get(0u32), a);
    }
}

/// Registry-shaped Clone-key maps (registry.rs:142-587,
/// literal.rs:24, au/terms.rs:43, au/space.rs:63).
#[cfg(feature = "compat-composites")]
mod clone_key_maps {
    use super::cv;

    #[derive(Clone)]
    struct OpInfoShaped {
        name: String,
        args: Vec<u32>,
        unit: Option<String>,
        is_constructor: bool,
    }

    // Index word `u32` at every site, as in the egraph: each of these maps mints its
    // ids from its own log positions, and those ids' `Index` is the config word.
    struct RegistriesShaped {
        sorts: cv::map::SpUniqueMap<String, (), u32, true>,
        ops: cv::map::SpUniqueMap<String, OpInfoShaped, u32, true>,
        // au/terms.rs:43 — Vec inside the key tuple.
        by_structure: cv::map::SpUniqueMap<(u32, Vec<u32>), u32, u32, true>,
        // au/space.rs:63 — Vec as the whole key.
        ctx_index: cv::map::SpUniqueMap<Vec<u32>, u32, u32, true>,
    }

    pub fn smoke() {
        let mut r = RegistriesShaped {
            sorts: cv::map::SpUniqueMap::new(),
            ops: cv::map::SpUniqueMap::new(),
            by_structure: cv::map::SpUniqueMap::new(),
            ctx_index: cv::map::SpUniqueMap::new(),
        };
        r.sorts
            .try_insert("Int".to_string(), ())
            .expect("canary: capacity");
        let idx = r
            .ops
            .try_insert(
                "+".to_string(),
                OpInfoShaped {
                    name: "+".to_string(),
                    args: vec![0, 0],
                    unit: None,
                    is_constructor: false,
                },
            )
            .expect("canary: capacity");
        // Unique-keyed: a second registration under the same name is refused,
        // which is the registry's duplicate check; the first entry stands.
        let mut updated = r.ops.get_val(idx).clone();
        updated.is_constructor = true;
        assert_eq!(
            r.ops.try_insert("+".to_string(), updated),
            Err(cv::error::ContainerError::DuplicateKey),
            "unique map refuses a present key"
        );
        assert!(!r.ops.get_by_key(&"+".to_string()).unwrap().is_constructor);
        assert_eq!(r.ops.len(), 1, "one live key, no shadow");
        // Interning answers with the existing entry, in one hash.
        let (hit, fresh) = r
            .ops
            .try_intern(
                "+".to_string(),
                OpInfoShaped {
                    name: "+".to_string(),
                    args: vec![0, 0],
                    unit: None,
                    is_constructor: true,
                },
            )
            .expect("canary: capacity");
        assert!(!fresh && hit == idx, "intern of a present key is a hit");

        r.by_structure
            .try_insert((3, vec![1, 2]), 9)
            .expect("canary: capacity");
        assert_eq!(r.by_structure.id_of(&(3, vec![1, 2])), Some(0));
        r.ctx_index
            .try_insert(vec![4, 5, 6], 1)
            .expect("canary: capacity");
        assert!(r.ctx_index.contains_key(&vec![4, 5, 6]));
    }
}

/// SparseSet constructors and typed ListArena
/// (classes.rs:191-208 — the EClasses quartet).
#[cfg(all(feature = "compat-list", feature = "compat-ids"))]
mod eclasses_shaped {
    use super::cv;

    cv::define_id31! { pub struct ClassIdShaped / StoredClassIdShaped, "c"; }
    cv::define_id31! { pub struct UseListIdShaped / StoredUseListIdShaped, "ul"; }
    cv::define_id31! { pub struct UseNodeIdShaped / StoredUseNodeIdShaped, "un"; }

    struct EClassesShaped {
        uses: cv::ListArena<ClassIdShaped, UseListIdShaped, UseNodeIdShaped, true>,
        reprs: cv::SparseSet<u32, u32, cv::inline_store::InlineStore<u32, u32>, true>,
    }

    pub fn smoke() {
        let mut e = EClassesShaped {
            uses: cv::ListArena::new(),
            reprs: cv::SparseSet::new_inline(),
        };
        let l1 = e.uses.try_new_list().expect("canary: id range");
        let l2 = e.uses.try_new_list().expect("canary: id range");
        e.uses
            .try_append(l1, ClassIdShaped::new(1))
            .expect("canary: node range");
        e.uses
            .try_append(l1, ClassIdShaped::new(2))
            .expect("canary: node range");
        e.uses
            .try_append(l2, ClassIdShaped::new(3))
            .expect("canary: node range");
        // O(1) splice: l1 := l1 ++ l2, l2 cleared but valid.
        e.uses.splice(l1, l2);
        assert_eq!(e.uses.len(l1), 3);
        assert!(e.uses.is_empty(l2));
        let collected: Vec<u32> = e.uses.iter(l1).map(|c| c.raw()).collect();
        assert_eq!(collected.len(), 3);

        let id = e.reprs.try_add(77).expect("canary: capacity");
        assert!(e.reprs.contains(id));
    }
}

/// B+tree production surface (cursor(), from_sorted, Branchless,
/// generic defaults, SortedCursor).
#[cfg(all(feature = "compat-bplus", feature = "compat-ids"))]
mod bplus_shaped {
    use super::cv;

    cv::define_id31! { pub struct KeyShaped / StoredKeyShaped, "k"; }

    pub fn smoke() {
        // Generic defaults: Layout64U32 + BinarySearch + TRACK=true implied.
        let mut t: cv::BPlusTreeSet<KeyShaped> = cv::BPlusTreeSet::new();
        assert!(t.insert(KeyShaped::new(10)));
        assert!(!t.insert(KeyShaped::new(10)));

        let keys: Vec<KeyShaped> = (0..100u32).map(KeyShaped::new).collect();
        let bulk = cv::BPlusTreeSet::<KeyShaped>::from_sorted(&keys);
        assert_eq!(bulk.len(), 100);

        // SortedCursor trait — the leapfrog-join surface (leapfrog.rs:10).
        let mut c = bulk.cursor();
        c.seek(KeyShaped::new(50));
        assert_eq!(c.key().map(|k| k.raw()), Some(50));
        c.step();
        assert_eq!(c.key().map(|k| k.raw()), Some(51));

        // Branchless search kind compiles with the same tree shape.
        let _t2: cv::BPlusTreeSet<KeyShaped, cv::Layout64U32, cv::Branchless, false> =
            cv::BPlusTreeSet::new();
    }
}

/// Run every un-gated smoke fixture (called from tests/smoke.rs).
pub fn run_all_smoke() {
    aov_heap_payloads::smoke();
    aov_clone_only_payload::smoke();
    union_find_shaped::smoke();
    min_pool_shaped::smoke();
    copy_key_maps::smoke();
    tagged_fuzzer_template::smoke();
    #[cfg(feature = "compat-ids")]
    id_macro_shapes::smoke();
    #[cfg(feature = "compat-composites")]
    clone_key_maps::smoke();
    #[cfg(all(feature = "compat-list", feature = "compat-ids"))]
    eclasses_shaped::smoke();
    #[cfg(all(feature = "compat-bplus", feature = "compat-ids"))]
    bplus_shaped::smoke();
}
