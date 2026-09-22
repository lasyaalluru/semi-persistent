// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Read-only byte reporters, OUTSIDE the verified perimeter (stratified).
//!
//! Every function here (and every `*_bytes` method the containers define in
//! their ordinary-Rust impl blocks, next to their `verus!` blocks) reports how
//! much heap a container currently holds. They read capacities, which vstd does
//! not model, and they return a number nothing in the crate branches on: no
//! verified function calls them, they take `&self`, and they cannot alter
//! execution. They are therefore not part of the verified surface at all —
//! neither proved nor trusted — rather than `external_body` items the trust
//! ledger has to argue about. Production parity: the legacy crate exposes the
//! same `total_bytes`/`tracking_bytes` introspection.

/// Heap bytes held by a store's backing storage (capacity-based).
pub trait HeapBytes {
    fn heap_bytes(&self) -> usize;
}

/// Heap bytes of a bare diff log (capacity-based).
pub(crate) fn log_heap_bytes<T, I>(d: &std::vec::Vec<(T, I)>) -> usize {
    d.capacity() * core::mem::size_of::<(T, I)>()
}
