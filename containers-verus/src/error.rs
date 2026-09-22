// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Error types for total public container operations.
//!
//! `ContainerError` names failures shared by total container operations.
//! Additive APIs with narrower failure domains use dedicated error types so
//! this enum's public variant surface remains stable.

use vstd::prelude::*;

verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ContainerError {
    /// The container's index word cannot represent one more element.
    CapacityExhausted,
    /// The mark/restore frame stack is at its u32 depth ceiling.
    DepthLimit,
    /// The fork counter is at its u32 ceiling.
    ForkLimit,
    /// The token does not name a restorable frame of this container
    /// (wrong container, stale genealogy, or cut branch).
    InvalidToken,
    /// The operation needs TRACK=true (mark/restore on an untracked container).
    Untracked,
    /// `pop` on an empty frame stack: there is no open frame to drop.
    NoOpenFrame,
    /// An index beyond the current length.
    IndexOutOfBounds,
    /// Input violates an ordering/shape requirement (e.g. `from_sorted` on
    /// keys that are not strictly ascending).
    NotSorted,
    /// The key type lacks a property the container requires statically
    /// (e.g. a non-bit-stealing id family on the B+tree).
    UnsupportedKey,
    /// The key is already present in a unique-keys map (`SpUniqueMap`), which
    /// never overwrites.
    DuplicateKey,
}

} // verus!

impl core::fmt::Display for ContainerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self {
            ContainerError::CapacityExhausted => "container capacity exhausted for its index word",
            ContainerError::DepthLimit => "mark depth at u32 ceiling",
            ContainerError::ForkLimit => "fork count at u32 ceiling",
            ContainerError::InvalidToken => "token does not name a restorable frame",
            ContainerError::Untracked => "operation requires a tracked (TRACK=true) container",
            ContainerError::NoOpenFrame => "pop on an empty frame stack: no open frame to drop",
            ContainerError::IndexOutOfBounds => "index beyond current length",
            ContainerError::NotSorted => "input keys not strictly ascending",
            ContainerError::UnsupportedKey => "key type lacks a required static property",
            ContainerError::DuplicateKey => "key already present in a unique-keys map",
        };
        f.write_str(s)
    }
}

impl std::error::Error for ContainerError {}
