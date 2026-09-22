// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E4 differential campaign for the policy-driven three-tier Vec runtime.
//!
//! Generated tapes run against production, the verified runtime, and an
//! independent full-snapshot oracle. Policy-only operations are applied only to
//! the verified runtime; all three implementations must remain observationally
//! equivalent afterward. Production and the raw verified Vec intentionally
//! expose different token-validity predicates, so each is checked against its
//! documented oracle predicate.

use proptest::prelude::*;
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::panic::{AssertUnwindSafe, catch_unwind};
use verus::error::ContainerError;
use verus::group::ForkHistory;
use verus::{
    AdaptiveInput, AdaptiveReport, MarkOptions, Ratio, ReclaimPolicy, RolloverPolicy, ShrinkPolicy,
    StoreKind, TierLimit, TierPolicy, VecD, VecI, VecP, VecT,
};

const MAX_DEPTH: usize = 7;

// ---------------------------------------------------------------------------
// Independent full-snapshot oracle
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
struct Origin {
    parent: u32,
    depth: u32,
}

#[derive(Clone, Copy, Debug)]
struct OracleToken {
    branch: u32,
    /// The generation stamp at the mark depth (the verified container's own
    /// genealogy: a standalone vec is a group of one).
    generation: u64,
    depth: u32,
    frame: u32,
}

#[derive(Debug)]
struct SnapshotOracle {
    values: Vec<u32>,
    snapshots: Vec<Vec<u32>>,
    branch: u32,
    origins: Vec<Origin>,
    /// Per-depth generation stamps, mirroring the verified `Genealogy`: a
    /// restore to depth `d` bumps `d` and deeper (the consumed token dies).
    gen_levels: Vec<u64>,
}

impl SnapshotOracle {
    fn new() -> Self {
        Self {
            values: Vec::new(),
            snapshots: Vec::new(),
            branch: 0,
            origins: Vec::new(),
            gen_levels: Vec::new(),
        }
    }

    fn depth(&self) -> usize {
        self.snapshots.len()
    }

    fn mark(&mut self) -> OracleToken {
        let depth = self.snapshots.len() as u32;
        while self.gen_levels.len() <= depth as usize {
            self.gen_levels.push(1);
        }
        let token = OracleToken {
            branch: self.branch,
            generation: self.gen_levels[depth as usize],
            depth,
            frame: depth,
        };
        self.snapshots.push(self.values.clone());
        token
    }

    fn restore(&mut self, token: OracleToken) {
        let frame = token.frame as usize;
        assert!(self.is_restorable(token));
        self.values = self.snapshots[frame].clone();
        self.snapshots.truncate(frame);
        self.origins.push(Origin {
            parent: token.branch,
            depth: token.depth,
        });
        self.branch = self.origins.len() as u32;
        // The verified cut starts AT the restored depth.
        let mut i = token.depth as usize;
        while i < self.gen_levels.len() {
            self.gen_levels[i] += 1;
            i += 1;
        }
    }

    fn structurally_live(&self, token: OracleToken) -> bool {
        (token.frame as usize) < self.snapshots.len()
    }

    /// The verified `is_valid_token` meaning: the frame is live AND the
    /// token's generation is still the live stamp at its depth.
    fn verified_live(&self, token: OracleToken) -> bool {
        self.structurally_live(token)
            && (token.depth as usize) < self.gen_levels.len()
            && self.gen_levels[token.depth as usize] == token.generation
    }

    fn is_restorable(&self, token: OracleToken) -> bool {
        self.structurally_live(token) && self.on_branch(token)
    }

    fn on_branch(&self, token: OracleToken) -> bool {
        let current_depth = self.snapshots.len() as u32;
        if token.branch == self.branch {
            return token.depth <= current_depth;
        }

        let mut branch = self.branch;
        while branch != token.branch {
            if branch == 0 {
                return false;
            }
            let origin = self.origins[(branch - 1) as usize];
            if origin.parent == token.branch {
                return token.depth <= origin.depth;
            }
            branch = origin.parent;
        }
        token.depth <= current_depth
    }
}

// ---------------------------------------------------------------------------
// Runtime adapters
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum Backend {
    StaticInline,
    StaticParallel,
    StaticTrail,
    DynamicInline,
    DynamicParallel,
    DynamicTrail,
}

const BACKENDS: [Backend; 6] = [
    Backend::StaticInline,
    Backend::StaticParallel,
    Backend::StaticTrail,
    Backend::DynamicInline,
    Backend::DynamicParallel,
    Backend::DynamicTrail,
];

#[derive(Clone, Copy, Debug)]
enum Profile {
    Smt,
    Adaptive,
    RestoreOptimized,
    FullyBufferedUnique,
    FiniteFrames,
    FiniteEntries,
    FiniteBytes,
}

const PROFILES: [Profile; 7] = [
    Profile::Smt,
    Profile::Adaptive,
    Profile::RestoreOptimized,
    Profile::FullyBufferedUnique,
    Profile::FiniteFrames,
    Profile::FiniteEntries,
    Profile::FiniteBytes,
];

impl Profile {
    fn policy(self) -> TierPolicy {
        match self {
            Self::Smt => TierPolicy::smt(),
            Self::Adaptive => TierPolicy::adaptive(),
            Self::RestoreOptimized => TierPolicy::restore_optimized(),
            Self::FullyBufferedUnique => TierPolicy::fully_buffered_unique(),
            Self::FiniteFrames => custom_policy(TierLimit::Frames(1), TierLimit::Frames(1)),
            Self::FiniteEntries => custom_policy(TierLimit::Entries(3), TierLimit::Entries(2)),
            Self::FiniteBytes => TierPolicy {
                trail: TierLimit::Bytes(2 * core::mem::size_of::<(u32, u32)>()),
                hot: TierLimit::Bytes(core::mem::size_of::<(u32, u32)>()),
                cold_reclaim: ReclaimPolicy::ShrinkToFit,
            },
        }
    }
}

fn custom_policy(trail: TierLimit, hot: TierLimit) -> TierPolicy {
    TierPolicy {
        trail,
        hot,
        cold_reclaim: ReclaimPolicy::RetainCapacity,
    }
}

enum ProductionVec {
    Inline(prod::VecI<u32, u32, true>),
    Parallel(prod::VecP<u32, u32, true>),
}

impl ProductionVec {
    fn new(backend: Backend) -> Self {
        match backend {
            Backend::StaticInline | Backend::DynamicInline => Self::Inline(prod::VecI::new()),
            Backend::StaticParallel
            | Backend::StaticTrail
            | Backend::DynamicParallel
            | Backend::DynamicTrail => Self::Parallel(prod::VecP::new()),
        }
    }

    fn push(&mut self, value: u32) {
        match self {
            Self::Inline(vec) => vec.push(value),
            Self::Parallel(vec) => vec.push(value),
        }
    }

    fn pop(&mut self) -> Option<u32> {
        match self {
            Self::Inline(vec) => vec.pop(),
            Self::Parallel(vec) => vec.pop(),
        }
    }

    fn set(&mut self, index: u32, value: u32) {
        match self {
            Self::Inline(vec) => vec.set(index, value),
            Self::Parallel(vec) => vec.set(index, value),
        }
    }

    fn get(&self, index: u32) -> u32 {
        match self {
            Self::Inline(vec) => vec.get(index),
            Self::Parallel(vec) => vec.get(index),
        }
    }

    fn len(&self) -> usize {
        match self {
            Self::Inline(vec) => vec.len() as usize,
            Self::Parallel(vec) => vec.len() as usize,
        }
    }

    fn depth(&self) -> usize {
        match self {
            Self::Inline(vec) => vec.depth(),
            Self::Parallel(vec) => vec.depth(),
        }
    }

    fn mark(&mut self) -> prod::VecToken {
        match self {
            Self::Inline(vec) => vec.mark(prod::ShrinkPolicy::Never),
            Self::Parallel(vec) => vec.mark(prod::ShrinkPolicy::Never),
        }
    }

    fn restore(&mut self, token: prod::VecToken) {
        match self {
            Self::Inline(vec) => vec.restore(token),
            Self::Parallel(vec) => vec.restore(token),
        }
    }

    fn is_valid_token(&self, token: &prod::VecToken) -> bool {
        match self {
            Self::Inline(vec) => vec.is_valid_token(token),
            Self::Parallel(vec) => vec.is_valid_token(token),
        }
    }
}

enum VerifiedVec {
    Inline(ForkHistory<VecI<u32, u32, true>>),
    Parallel(ForkHistory<VecP<u32, u32, true>>),
    Trail(ForkHistory<VecT<u32, u32, true>>),
    Dynamic(ForkHistory<VecD<u32, u32, true>>),
}

impl VerifiedVec {
    fn new(backend: Backend, policy: TierPolicy) -> Self {
        match backend {
            Backend::StaticInline => Self::Inline(ForkHistory::new(VecI::new_with_policy(policy))),
            Backend::StaticParallel => {
                Self::Parallel(ForkHistory::new(VecP::new_with_policy(policy)))
            }
            Backend::StaticTrail => Self::Trail(ForkHistory::new(VecT::new_with_policy(policy))),
            Backend::DynamicInline => Self::Dynamic(ForkHistory::new(VecD::new_kind_with_policy(
                StoreKind::Inline,
                policy,
            ))),
            Backend::DynamicParallel => Self::Dynamic(ForkHistory::new(
                VecD::new_kind_with_policy(StoreKind::Parallel, policy),
            )),
            Backend::DynamicTrail => Self::Dynamic(ForkHistory::new(VecD::new_kind_with_policy(
                StoreKind::Trail,
                policy,
            ))),
        }
    }

    fn push(&mut self, value: u32) {
        match self {
            Self::Inline(vec) => vec
                .try_push(value)
                .expect("u32 test index remains in range"),
            Self::Parallel(vec) => vec
                .try_push(value)
                .expect("u32 test index remains in range"),
            Self::Trail(vec) => vec
                .try_push(value)
                .expect("u32 test index remains in range"),
            Self::Dynamic(vec) => vec
                .try_push(value)
                .expect("u32 test index remains in range"),
        }
    }

    fn pop(&mut self) -> Option<u32> {
        match self {
            Self::Inline(vec) => vec.pop(),
            Self::Parallel(vec) => vec.pop(),
            Self::Trail(vec) => vec.pop(),
            Self::Dynamic(vec) => vec.pop(),
        }
    }

    fn set(&mut self, index: u32, value: u32) {
        match self {
            Self::Inline(vec) => vec.set(index, value),
            Self::Parallel(vec) => vec.set(index, value),
            Self::Trail(vec) => vec.set(index, value),
            Self::Dynamic(vec) => vec.set(index, value),
        }
    }

    fn get(&self, index: u32) -> u32 {
        match self {
            Self::Inline(vec) => vec.get(index),
            Self::Parallel(vec) => vec.get(index),
            Self::Trail(vec) => vec.get(index),
            Self::Dynamic(vec) => vec.get(index),
        }
    }

    fn len(&self) -> usize {
        match self {
            Self::Inline(vec) => vec.len() as usize,
            Self::Parallel(vec) => vec.len() as usize,
            Self::Trail(vec) => vec.len() as usize,
            Self::Dynamic(vec) => vec.len() as usize,
        }
    }

    fn depth(&self) -> usize {
        match self {
            Self::Inline(vec) => vec.depth(),
            Self::Parallel(vec) => vec.depth(),
            Self::Trail(vec) => vec.depth(),
            Self::Dynamic(vec) => vec.depth(),
        }
    }

    fn mark(&mut self) -> verus::vec::VecToken {
        match self {
            Self::Inline(vec) => vec.mark(ShrinkPolicy::Never).expect("depth is bounded"),
            Self::Parallel(vec) => vec.mark(ShrinkPolicy::Never).expect("depth is bounded"),
            Self::Trail(vec) => vec.mark(ShrinkPolicy::Never).expect("depth is bounded"),
            Self::Dynamic(vec) => vec.mark(ShrinkPolicy::Never).expect("depth is bounded"),
        }
    }

    fn try_restore(&mut self, token: verus::vec::VecToken) -> Result<(), ContainerError> {
        let ok = match self {
            Self::Inline(vec) => vec.restore(token),
            Self::Parallel(vec) => vec.restore(token),
            Self::Trail(vec) => vec.restore(token),
            Self::Dynamic(vec) => vec.restore(token),
        };
        if ok {
            Ok(())
        } else {
            Err(ContainerError::InvalidToken)
        }
    }

    /// Drop the open top frame (the SMT-LIB pop). The verified restore keeps
    /// the checkpoint open (semantics B, design doc 08 §1) while production
    /// pops it, so the paired discipline pops after every verified restore.
    fn pop_scope(&mut self) {
        let ok = match self {
            Self::Inline(vec) => vec.pop_scope(),
            Self::Parallel(vec) => vec.pop_scope(),
            Self::Trail(vec) => vec.pop_scope(),
            Self::Dynamic(vec) => vec.pop_scope(),
        };
        assert!(ok, "pop: an open scope");
        #[allow(clippy::match_single_binding)]
        match () {
            () => {}
        }
    }

    fn is_valid_token(&self, token: &verus::vec::VecToken) -> bool {
        match self {
            Self::Inline(vec) => vec.is_valid(*token),
            Self::Parallel(vec) => vec.is_valid(*token),
            Self::Trail(vec) => vec.is_valid(*token),
            Self::Dynamic(vec) => vec.is_valid(*token),
        }
    }

    fn set_policy(&mut self, policy: TierPolicy) {
        match self {
            Self::Inline(vec) => vec.set_tier_policy(policy),
            Self::Parallel(vec) => vec.set_tier_policy(policy),
            Self::Trail(vec) => vec.set_tier_policy(policy),
            Self::Dynamic(vec) => vec.set_tier_policy(policy),
        }
    }

    fn apply_policy(&mut self) {
        match self {
            Self::Inline(vec) => vec.apply_tier_policy(),
            Self::Parallel(vec) => vec.apply_tier_policy(),
            Self::Trail(vec) => vec.apply_tier_policy(),
            Self::Dynamic(vec) => vec.apply_tier_policy(),
        }
    }

    fn apply_adaptive(&mut self, input: AdaptiveInput) -> AdaptiveReport {
        match self {
            Self::Inline(vec) => vec.apply_adaptive(input),
            Self::Parallel(vec) => vec.apply_adaptive(input),
            Self::Trail(vec) => vec.apply_adaptive(input),
            Self::Dynamic(vec) => vec.apply_adaptive(input),
        }
    }

    fn mark_adaptive(&mut self, input: AdaptiveInput) -> (verus::vec::VecToken, AdaptiveReport) {
        // The member pushes its frame by the adaptive variant; the group mints.
        let report = match self {
            Self::Inline(vec) => vec
                .member
                .try_push_frame_adaptive(ShrinkPolicy::Never, input)
                .expect("depth is bounded"),
            Self::Parallel(vec) => vec
                .member
                .try_push_frame_adaptive(ShrinkPolicy::Never, input)
                .expect("depth is bounded"),
            Self::Trail(vec) => vec
                .member
                .try_push_frame_adaptive(ShrinkPolicy::Never, input)
                .expect("depth is bounded"),
            Self::Dynamic(vec) => vec
                .member
                .try_push_frame_adaptive(ShrinkPolicy::Never, input)
                .expect("depth is bounded"),
        };
        let token = match self {
            Self::Inline(vec) => vec.mint_pushed(),
            Self::Parallel(vec) => vec.mint_pushed(),
            Self::Trail(vec) => vec.mint_pushed(),
            Self::Dynamic(vec) => vec.mint_pushed(),
        }
        .expect("the member is exactly one frame ahead");
        (token, report)
    }

    fn flush_trail(&mut self) {
        match self {
            Self::Inline(vec) => vec.flush_trail(),
            Self::Parallel(vec) => vec.flush_trail(),
            Self::Trail(vec) => vec.flush_trail(),
            Self::Dynamic(vec) => vec.flush_trail(),
        }
    }

    fn compress_hot(&mut self) {
        match self {
            Self::Inline(vec) => vec.compress_hot(),
            Self::Parallel(vec) => vec.compress_hot(),
            Self::Trail(vec) => vec.compress_hot(),
            Self::Dynamic(vec) => vec.compress_hot(),
        }
    }

    fn tier_counts(&self) -> (usize, usize, usize) {
        let stats = match self {
            Self::Inline(vec) => vec.tier_stats(),
            Self::Parallel(vec) => vec.tier_stats(),
            Self::Trail(vec) => vec.tier_stats(),
            Self::Dynamic(vec) => vec.tier_stats(),
        };
        (stats.cold_frames, stats.hot_frames, stats.trail_frames)
    }
}

// ---------------------------------------------------------------------------
// Generated tapes and differential runner
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum Op {
    Push(u32),
    Pop,
    Set { at: u16, value: u32 },
    DuplicateBurst { at: u16, value: u32, count: u8 },
    Mark,
    RestoreLive { which: u16 },
    RetryLastRestore,
    SetPolicy(u8),
    ApplyPolicy,
    ApplyAdaptive(u8),
    MarkAdaptive(u8),
    FlushTrail,
    CompressHot,
    DeepUnwind,
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        5 => any::<u32>().prop_map(Op::Push),
        2 => Just(Op::Pop),
        4 => (any::<u16>(), any::<u32>()).prop_map(|(at, value)| Op::Set { at, value }),
        2 => (any::<u16>(), any::<u32>(), 2u8..6).prop_map(|(at, value, count)| {
            Op::DuplicateBurst { at, value, count }
        }),
        3 => Just(Op::Mark),
        2 => any::<u16>().prop_map(|which| Op::RestoreLive { which }),
        1 => Just(Op::RetryLastRestore),
        2 => any::<u8>().prop_map(Op::SetPolicy),
        1 => Just(Op::ApplyPolicy),
        2 => any::<u8>().prop_map(Op::ApplyAdaptive),
        2 => any::<u8>().prop_map(Op::MarkAdaptive),
        1 => Just(Op::FlushTrail),
        1 => Just(Op::CompressHot),
        1 => Just(Op::DeepUnwind),
    ]
}

fn tape_strategy() -> impl Strategy<Value = Vec<Op>> {
    proptest::collection::vec(op_strategy(), 8..20).prop_map(|random| {
        // Every generated case retains this compact semantic spine while the
        // suffix explores different operation orders and values. It guarantees
        // duplicate writes, an empty frame, pop/regrow, explicit migrations,
        // an ancestor restore followed by a repeated-restore failure, and a
        // token-by-token unwind.
        let mut tape = vec![
            Op::Mark,
            Op::DuplicateBurst {
                at: 0,
                value: 100,
                count: 4,
            },
            Op::Mark,
            Op::Mark,
            Op::Pop,
            Op::Push(900),
            Op::Set {
                at: u16::MAX,
                value: 901,
            },
            Op::SetPolicy(Profile::FiniteFrames as u8),
            Op::ApplyPolicy,
            Op::ApplyAdaptive(0),
            Op::FlushTrail,
            Op::CompressHot,
            Op::RestoreLive { which: 0 },
            Op::RetryLastRestore,
            Op::Mark,
            Op::Set { at: 1, value: 700 },
            Op::MarkAdaptive(2),
            Op::DuplicateBurst {
                at: u16::MAX,
                value: 800,
                count: 3,
            },
            Op::Mark,
            Op::DeepUnwind,
        ];
        tape.extend(random);
        tape
    })
}

fn cases() -> u32 {
    std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(64)
}

fn config() -> ProptestConfig {
    ProptestConfig {
        cases: cases(),
        ..ProptestConfig::default()
    }
}

fn scale(ratio: u16, len: usize) -> Option<usize> {
    if len == 0 {
        None
    } else {
        Some((ratio as usize * len) / (u16::MAX as usize + 1))
    }
}

const ADAPTIVE_BUDGETS: [usize; 6] = [0, 32, 64, 128, 512, usize::MAX];

fn adaptive_input(selection: u8) -> AdaptiveInput {
    AdaptiveInput {
        max_closed_history_bytes: ADAPTIVE_BUDGETS[selection as usize % ADAPTIVE_BUDGETS.len()],
        min_writes_per_unique: Ratio::new(2, 1).expect("nonzero denominator"),
        min_uniques_per_run: Ratio::new(2, 1).expect("nonzero denominator"),
    }
}

fn check_adaptive_report(
    report: AdaptiveReport,
    input: AdaptiveInput,
) -> Result<(), TestCaseError> {
    prop_assert_eq!(
        report.inspected_frames,
        report.inspected_trail_frames + report.inspected_hot_frames
    );
    prop_assert_eq!(
        report.migrated_frames,
        report.migrated_trail_frames + report.migrated_hot_frames
    );
    prop_assert!(report.migrated_trail_frames <= report.inspected_trail_frames);
    prop_assert!(report.migrated_hot_frames <= report.inspected_hot_frames);
    prop_assert!(report.logical_bytes_after <= report.logical_bytes_before);
    prop_assert_eq!(
        report.budget_unmet_bytes,
        report
            .logical_bytes_after
            .saturating_sub(input.max_closed_history_bytes)
    );
    if report.logical_bytes_before <= input.max_closed_history_bytes {
        prop_assert_eq!(report.inspected_frames, 0);
        prop_assert_eq!(report.migrated_frames, 0);
        prop_assert_eq!(report.logical_bytes_after, report.logical_bytes_before);
    }
    Ok(())
}

type TokenTriple = (prod::VecToken, verus::vec::VecToken, OracleToken);

struct Harness {
    production: ProductionVec,
    verified: VerifiedVec,
    oracle: SnapshotOracle,
    tokens: Vec<TokenTriple>,
    last_restored: Option<TokenTriple>,
    backend: Backend,
    profile: Profile,
}

impl Harness {
    fn new(backend: Backend, profile: Profile) -> Self {
        Self {
            production: ProductionVec::new(backend),
            verified: VerifiedVec::new(backend, profile.policy()),
            oracle: SnapshotOracle::new(),
            tokens: Vec::new(),
            last_restored: None,
            backend,
            profile,
        }
    }

    fn seed(&mut self) {
        for value in 0..6 {
            self.production.push(value);
            self.verified.push(value);
            self.oracle.values.push(value);
        }
    }

    fn live_token(&self, which: u16) -> Option<usize> {
        let live: Vec<usize> = self
            .tokens
            .iter()
            .enumerate()
            .filter_map(|(index, (_, _, token))| {
                (self.oracle.is_restorable(*token) && self.oracle.verified_live(*token))
                    .then_some(index)
            })
            .collect();
        scale(which, live.len()).map(|index| live[index])
    }

    fn execute(&mut self, step: usize, op: Op) -> Result<(), TestCaseError> {
        match op {
            Op::Push(value) => {
                self.production.push(value);
                self.verified.push(value);
                self.oracle.values.push(value);
            }
            Op::Pop => {
                let production = self.production.pop();
                let verified = self.verified.pop();
                let oracle = self.oracle.values.pop();
                prop_assert_eq!(
                    production,
                    verified,
                    "{}/{:?}/{:?} step {}: pop production/verified",
                    protocol_name(self.backend),
                    self.backend,
                    self.profile,
                    step
                );
                prop_assert_eq!(
                    production,
                    oracle,
                    "{}/{:?}/{:?} step {}: pop production/oracle",
                    protocol_name(self.backend),
                    self.backend,
                    self.profile,
                    step
                );
            }
            Op::Set { at, value } => {
                if let Some(index) = scale(at, self.oracle.values.len()) {
                    self.production.set(index as u32, value);
                    self.verified.set(index as u32, value);
                    self.oracle.values[index] = value;
                }
            }
            Op::DuplicateBurst { at, value, count } => {
                if let Some(index) = scale(at, self.oracle.values.len()) {
                    for offset in 0..count {
                        let next = value.wrapping_add(offset as u32);
                        self.production.set(index as u32, next);
                        self.verified.set(index as u32, next);
                        self.oracle.values[index] = next;
                        self.check(step)?;
                    }
                }
            }
            Op::Mark => {
                if self.oracle.depth() < MAX_DEPTH {
                    let production = self.production.mark();
                    let verified = self.verified.mark();
                    let oracle = self.oracle.mark();
                    self.tokens.push((production, verified, oracle));
                }
            }
            Op::RestoreLive { which } => {
                if let Some(index) = self.live_token(which) {
                    let triple = self.tokens[index];
                    prop_assert!(self.production.is_valid_token(&triple.0));
                    prop_assert!(self.verified.is_valid_token(&triple.1));
                    self.production.restore(triple.0);
                    self.verified
                        .try_restore(triple.1)
                        .expect("oracle-selected token is structurally live");
                    prop_assert!(
                        self.verified.is_valid_token(&triple.1),
                        "restored checkpoint stays valid (semantics B)"
                    );
                    self.verified.pop_scope();
                    self.oracle.restore(triple.2);
                    self.last_restored = Some(triple);
                }
            }
            Op::RetryLastRestore => {
                if let Some((production, verified, oracle)) = self.last_restored {
                    // An immediate replay has no live frame. Raw verified Vec
                    // reports InvalidToken; production still reports genealogy
                    // validity and traps on the separate structural check. The
                    // latter is exercised once in the focused regression below
                    // rather than producing one caught panic per matrix cell.
                    if !self.oracle.structurally_live(oracle) {
                        prop_assert!(!self.verified.is_valid_token(&verified));
                        prop_assert_eq!(
                            self.verified.try_restore(verified),
                            Err(ContainerError::InvalidToken)
                        );
                        prop_assert_eq!(
                            self.production.is_valid_token(&production),
                            self.oracle.on_branch(oracle)
                        );
                    }
                }
            }
            Op::SetPolicy(selection) => {
                self.verified
                    .set_policy(PROFILES[selection as usize % PROFILES.len()].policy());
            }
            Op::ApplyPolicy => self.verified.apply_policy(),
            Op::ApplyAdaptive(selection) => {
                let input = adaptive_input(selection);
                let report = self.verified.apply_adaptive(input);
                check_adaptive_report(report, input)?;
            }
            Op::MarkAdaptive(selection) => {
                if self.oracle.depth() < MAX_DEPTH {
                    let input = adaptive_input(selection);
                    let production = self.production.mark();
                    let (verified, report) = self.verified.mark_adaptive(input);
                    let oracle = self.oracle.mark();
                    check_adaptive_report(report, input)?;
                    self.tokens.push((production, verified, oracle));
                }
            }
            Op::FlushTrail => self.verified.flush_trail(),
            Op::CompressHot => self.verified.compress_hot(),
            Op::DeepUnwind => {
                while let Some(index) = self
                    .tokens
                    .iter()
                    .enumerate()
                    .filter(|(_, (_, _, token))| {
                        self.oracle.is_restorable(*token) && self.oracle.verified_live(*token)
                    })
                    .max_by_key(|(_, (_, _, token))| token.frame)
                    .map(|(index, _)| index)
                {
                    let triple = self.tokens[index];
                    self.production.restore(triple.0);
                    self.verified
                        .try_restore(triple.1)
                        .expect("deep-unwind token is live");
                    prop_assert!(
                        self.verified.is_valid_token(&triple.1),
                        "restored checkpoint stays valid (semantics B)"
                    );
                    self.verified.pop_scope();
                    self.oracle.restore(triple.2);
                    self.last_restored = Some(triple);
                    self.check(step)?;
                }
            }
        }
        self.check(step)
    }

    fn check(&self, step: usize) -> Result<(), TestCaseError> {
        let context = format!(
            "{}/{:?}/{:?} step {step}",
            protocol_name(self.backend),
            self.backend,
            self.profile
        );
        prop_assert_eq!(
            self.production.len(),
            self.verified.len(),
            "{}: length production/verified",
            context
        );
        prop_assert_eq!(
            self.production.len(),
            self.oracle.values.len(),
            "{}: length production/oracle",
            context
        );
        prop_assert_eq!(
            self.production.depth(),
            self.verified.depth(),
            "{}: depth production/verified",
            context
        );
        prop_assert_eq!(
            self.production.depth(),
            self.oracle.depth(),
            "{}: depth production/oracle",
            context
        );
        let (cold, hot, trail) = self.verified.tier_counts();
        prop_assert_eq!(cold + hot + trail, self.verified.depth());
        if matches!(self.backend, Backend::StaticTrail | Backend::DynamicTrail) {
            if self.verified.depth() > 0 {
                prop_assert!(trail >= 1, "{}: trail ingress lacks open frame", context);
            }
        } else {
            prop_assert_eq!(trail, 0, "{}: hot ingress retained trail frames", context);
            if self.verified.depth() > 0 {
                prop_assert!(hot >= 1, "{}: hot ingress lacks open frame", context);
            }
        }

        for (index, expected) in self.oracle.values.iter().copied().enumerate() {
            prop_assert_eq!(
                self.production.get(index as u32),
                expected,
                "{}: production value {}",
                context,
                index
            );
            prop_assert_eq!(
                self.verified.get(index as u32),
                expected,
                "{}: verified value {}",
                context,
                index
            );
        }

        for (index, (production, verified, oracle)) in self.tokens.iter().enumerate() {
            prop_assert_eq!(
                self.production.is_valid_token(production),
                self.oracle.on_branch(*oracle),
                "{}: production token {}",
                context,
                index
            );
            prop_assert_eq!(
                self.verified.is_valid_token(verified),
                self.oracle.verified_live(*oracle),
                "{}: verified token {}",
                context,
                index
            );
        }
        Ok(())
    }
}

fn protocol_name(backend: Backend) -> &'static str {
    match backend {
        Backend::StaticTrail | Backend::DynamicTrail => "trail",
        Backend::StaticInline | Backend::DynamicInline => "inline-hot",
        Backend::StaticParallel | Backend::DynamicParallel => "parallel-hot",
    }
}

fn run_tape(backend: Backend, profile: Profile, tape: &[Op]) -> Result<(), TestCaseError> {
    let mut harness = Harness::new(backend, profile);
    harness.seed();
    harness.check(0)?;
    for (step, op) in tape.iter().copied().enumerate() {
        harness.execute(step, op)?;
    }
    Ok(())
}

proptest! {
    #![proptest_config(config())]

    #[test]
    fn generated_three_tier_policy_matrix(tape in tape_strategy()) {
        // Profiles and backends are deterministic outer loops so 1024 cases
        // means 1024 tapes through every configuration, not probabilistic
        // coverage that can miss a matrix cell.
        for profile in PROFILES {
            for backend in BACKENDS {
                run_tape(backend, profile, &tape)?;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Guaranteed tier-target and failure regressions
// ---------------------------------------------------------------------------

#[test]
fn restore_targets_deliberately_span_every_populated_tier() {
    for backend in BACKENDS {
        let mut harness = Harness::new(backend, Profile::FiniteFrames);
        harness.seed();

        let prefix = [
            Op::Mark,
            Op::Set { at: 0, value: 10 },
            Op::Mark,
            Op::Pop,
            Op::Pop,
            Op::Set { at: 0, value: 20 },
            Op::Mark,
            Op::Push(60),
            Op::Set {
                at: 20_000,
                value: 30,
            },
            Op::Mark,
            Op::Set {
                at: 40_000,
                value: 40,
            },
        ];
        for (step, op) in prefix.into_iter().enumerate() {
            harness.execute(step, op).unwrap();
        }

        let counts = harness.verified.tier_counts();
        if matches!(backend, Backend::StaticTrail | Backend::DynamicTrail) {
            assert_eq!(counts, (1, 1, 2), "backend {backend:?}");
        } else {
            assert_eq!(counts, (2, 2, 0), "backend {backend:?}");
        }

        // Newest-to-oldest restoration reaches the ingress tier first,
        // then each older populated tier. Every restore remains a full
        // production/verified/oracle differential operation.
        for step in 20..24 {
            harness
                .execute(step, Op::RestoreLive { which: u16::MAX })
                .unwrap();
        }
        assert_eq!(harness.oracle.depth(), 0);
        assert_eq!(harness.oracle.values, (0..6).collect::<Vec<_>>());
    }
}

#[test]
fn repeated_restore_failure_matches_each_documented_api() {
    let mut production: prod::VecP<u32, u32, true> = prod::VecP::new();
    let mut verified: ForkHistory<VecP<u32, u32, true>> =
        ForkHistory::new(VecP::new_with_policy(TierPolicy::smt()));
    production.push(1);
    verified.try_push(1).unwrap();
    let production_token = production.mark(prod::ShrinkPolicy::Never);
    let verified_token = verified.mark(ShrinkPolicy::Never).unwrap();

    production.restore(production_token);
    assert!(verified.restore(verified_token));
    // Semantics B: the verified checkpoint stays open and valid; the paired
    // discipline pops it to match production's pop.
    assert!(verified.is_valid(verified_token));
    assert!(verified.restore(verified_token));
    assert!(verified.pop_scope());

    assert!(
        production.is_valid_token(&production_token),
        "production validity is genealogy-only"
    );
    assert!(!verified.is_valid(verified_token));
    assert!(
        !verified.restore(verified_token),
        "the group refuses the consumed token without mutating"
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| production.restore(production_token))).is_err(),
        "production must reject the consumed frame structurally"
    );
}

#[test]
fn static_aliases_execute_native_capture_rollover_and_restore_paths() {
    let force_hot = MarkOptions::new(
        ShrinkPolicy::Never,
        RolloverPolicy::ForceClosed {
            trail_to_hot: false,
            hot_to_cold: true,
        },
    );
    let force_both = MarkOptions::new(
        ShrinkPolicy::Never,
        RolloverPolicy::ForceClosed {
            trail_to_hot: true,
            hot_to_cold: true,
        },
    );

    // Explicit-rollover marks are the member's own structural push followed
    // by the group's mint (the group cannot spell the rollover choice).
    let mut parallel: ForkHistory<VecP<u32, u32>> = ForkHistory::new(VecP::new());
    parallel.try_push(1).unwrap();
    let parallel_root = parallel.mark(ShrinkPolicy::Never).unwrap();
    parallel.set(0u32, 2);
    parallel.set(0u32, 3);
    parallel.member.try_push_frame_with(force_hot).unwrap();
    parallel.mint_pushed().unwrap();
    assert_eq!(parallel.tier_stats().cold_frames, 1);
    assert_eq!(parallel.tier_stats().cold_values, 1);
    assert!(parallel.restore(parallel_root));
    assert_eq!(parallel.get(0u32), 1);

    let mut inline: ForkHistory<VecI<u32, u32>> = ForkHistory::new(VecI::new());
    inline.try_push(4).unwrap();
    let inline_root = inline.mark(ShrinkPolicy::Never).unwrap();
    inline.set(0u32, 5);
    inline.set(0u32, 6);
    inline
        .member
        .try_push_frame_with(MarkOptions::new(ShrinkPolicy::Never, RolloverPolicy::Defer))
        .unwrap();
    inline.mint_pushed().unwrap();
    assert_eq!(inline.tier_stats().hot_entries, 1);
    assert!(inline.restore(inline_root));
    assert_eq!(inline.get(0u32), 4);

    let mut trail: ForkHistory<VecT<u32, u32>> = ForkHistory::new(VecT::new());
    trail.try_push(7).unwrap();
    let trail_root = trail.mark(ShrinkPolicy::Never).unwrap();
    trail.set(0u32, 8);
    trail.set(0u32, 9);
    trail.member.try_push_frame_with(force_both).unwrap();
    trail.mint_pushed().unwrap();
    assert_eq!(trail.tier_stats().cold_frames, 1);
    assert_eq!(trail.tier_stats().cold_values, 1);
    assert!(trail.restore(trail_root));
    assert_eq!(trail.get(0u32), 7);
}
