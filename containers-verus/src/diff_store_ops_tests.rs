// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Cold-run restore clamping, driven through the store protocol directly.
//! In-crate (not an integration test) because the protocol operations are
//! sealed on the crate-private `DiffStoreOps` supertrait.

use crate::diff_store_ops::DiffStoreOps;
use crate::dyn_store::DynStore;
use crate::{DiffStore, InlineStore, StoreKind};

fn check_clamped_run<S: DiffStore<u32, u64, true>>(mut store: S) {
    store.push(7);
    store.push(8);
    // A run entirely outside the live window must be a no-op, including when
    // computing its unclamped end would overflow the machine index word.
    store.restore_run(u64::MAX, &[1, 2]);
    assert_eq!(store.get(0), 7);
    assert_eq!(store.get(1), 8);
    store.restore_run(1, &[3, 4, 5]);
    assert_eq!(store.raw_len(), 2);
    assert_eq!(store.get(0), 7);
    assert_eq!(store.get(1), 3);
}

#[test]
fn inline_cold_run_is_clamped_before_index_arithmetic() {
    check_clamped_run(InlineStore::<u32, u64>::default());
}

#[test]
fn dynamic_cold_runs_are_clamped_for_every_backend() {
    for kind in [StoreKind::Inline, StoreKind::Parallel, StoreKind::Trail] {
        check_clamped_run(DynStore::<u32, u64>::new_kind::<true>(kind));
    }
}

#[test]
fn inline_cold_run_preserves_tags_even_when_untracked() {
    type Store = InlineStore<u32, u64>;
    let mut store = Store::default();
    <Store as DiffStoreOps<u32, u64, true>>::push(&mut store, 7);
    <Store as DiffStoreOps<u32, u64, true>>::mark_captured(&mut store, 0);
    <Store as DiffStore<u32, u64, false>>::restore_run(&mut store, 0, &[9]);
    let mut log = Vec::new();
    <Store as DiffStoreOps<u32, u64, true>>::capture(&mut store, 0, 1, &mut log);
    assert!(
        log.is_empty(),
        "Cold replay must preserve the existing capture tag"
    );
    assert_eq!(<Store as DiffStoreOps<u32, u64, true>>::get(&store, 0), 9);
}
