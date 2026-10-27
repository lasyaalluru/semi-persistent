// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
/// Multi-width abstract domains via macro instantiation.
///
/// The `abstract_domain!` macro stamps out ExecAnum, ExecUnum and Interval for
/// each unsigned integer width. All `by(bit_vector)` proofs work generically
/// because they only use the type's native operators. ExecTnum is not stamped:
/// each width aliases the generic `exec_tnum::ExecTnum<W>`. These domains are
/// combined through `reduce::Product`, not a product of their own.
macro_rules! abstract_domain {
    ($mod_name:ident, $uint:ty, $bits:expr, $max_val:expr) => {
        pub mod $mod_name {
            use vstd::prelude::*;
            use crate::bools::Bit;
            use crate::nats::*;
            use crate::tnum::Tnum;
            use crate::anum::Anum;
            use crate::unum::Unum;
            use crate::chopped::{ChoppedAnum, ChoppedTnum, ChoppedUnum};
            use crate::div::*;
            use crate::tbit::TBit;
            verus! {

            // ============================================================
            // Bridge: native wrapping ops == chop(nat ops, W)
            // ============================================================
            pub proof fn bridge_add(a: $uint, b: $uint)
                ensures (a.wrapping_add(b)) as nat == chop(nat_add(a as nat, b as nat), $bits as nat)
            {
                let w: nat = $bits as nat;
                nat_add_correct(a as nat, b as nat);
                chop_is_mod(nat_add(a as nat, b as nat), w);
                // exp(W) == MAX+1: Verus knows wrapping_add == (a+b) % (MAX+1)
                // and chop(n, W) == n % exp(W), so we need exp(W) == MAX+1
                // exp(W) == MAX+1: call concrete lemma for this width
                exp_concrete($bits as nat);
            }

            pub proof fn bridge_mul(a: $uint, b: $uint)
                ensures (a.wrapping_mul(b)) as nat == chop(prod(a as nat, b as nat), $bits as nat)
            {
                let w: nat = $bits as nat;
                chop_is_mod(prod(a as nat, b as nat), w);
                // exp(W) == MAX+1: call concrete lemma for this width
                exp_concrete($bits as nat);
            }

            /// A native addition that did not wrap is the corresponding
            /// natural-number addition and fits in the native width.
            #[verifier::spinoff_prover]
            pub proof fn add_no_overflow(a: $uint, b: $uint, sum: $uint)
                requires
                    sum == a.wrapping_add(b),
                    sum >= a,
                    sum >= b,
                ensures
                    sum as nat == a as nat + b as nat,
                    nat_add(a as nat, b as nat) == sum as nat,
                    nat_add(a as nat, b as nat) < exp($bits as nat),
                    fits(nat_add(a as nat, b as nat), $bits as nat),
            {
                assert(sum as nat == a as nat + b as nat) by(bit_vector)
                    requires
                        sum == a.wrapping_add(b),
                        sum >= a,
                        sum >= b;
                nat_add_correct(a as nat, b as nat);
                exp_concrete($bits as nat);
                chop_id(nat_add(a as nat, b as nat), $bits as nat);
            }

            pub proof fn native_fits(n: $uint)
                ensures fits(n as nat, $bits as nat)
            {
                exp_concrete($bits as nat);
                chop_id(n as nat, $bits as nat);
            }

            /// Bridge a successful standard-library `checked_mul` result to
            /// the multiplication specification.
            pub proof fn mul_exact(a: $uint, b: $uint, product: $uint)
                requires
                    product as nat == (a as nat) * (b as nat),
                ensures
                    product as nat == (a as nat) * (b as nat),
                    prod(a as nat, b as nat) == product as nat,
                    prod(a as nat, b as nat) < exp($bits as nat),
                    fits(prod(a as nat, b as nat), $bits as nat),
            {
                native_fits(product);
                assert(prod(a as nat, b as nat) == product as nat);
                exp_concrete($bits as nat);
                assert((product as nat) <= ($max_val as nat));
                assert(($max_val as nat) < exp($bits as nat));
            }

            // ============================================================
            // Bridge: native bitwise ops == spec bitwise ops on nat
            // ============================================================

            /// For n < exp(W), bits at position >= W are false.
            pub proof fn bit_above_width(n: nat, w: nat, i: nat)
                requires n < exp(w), i >= w
                ensures !bit(n, i).b()
                decreases i
            {
                exp_pos(w);
                if w == 0 { bit_zero(i); }
                else if i > 0 { bit_above_width(tl(n), (w-1) as nat, (i-1) as nat); }
            }

            /// Per-bit bridge: spec bit(n, i) == native bit extraction.
            pub proof fn bit_is_native_bit(n: $uint, i: nat)
                requires i < ($bits as nat)
                ensures bit(n as nat, i).b() == ((n >> (i as $uint)) & (1 as $uint) == (1 as $uint))
                decreases i
            {
                if i == 0 {
                    assert(((n >> (0 as $uint)) & (1 as $uint)) == (n % 2)) by(bit_vector);
                } else {
                    let iu = i as $uint;
                    assert((n >> (1 as $uint)) as nat == n as nat / 2) by(bit_vector);
                    bit_is_native_bit(n >> (1 as $uint), (i - 1) as nat);
                    assert(((n >> iu) & (1 as $uint)) == (((n >> (1 as $uint)) >> ((iu - (1 as $uint)) as $uint)) & (1 as $uint))) by(bit_vector)
                        requires iu < ($bits as $uint), iu > (0 as $uint);
                }
            }

            /// Native XOR == spec bw_xor on nat.
            #[verifier::spinoff_prover]
            pub proof fn native_xor(a: $uint, b: $uint)
                ensures (a ^ b) as nat == bw_xor(a as nat, b as nat)
            {
                assert forall|i: nat| #![auto] bit((a ^ b) as nat, i) == bit(bw_xor(a as nat, b as nat), i) by {
                    xor_bit(a as nat, b as nat, i);
                    if i < ($bits as nat) {
                        bit_is_native_bit(a, i);
                        bit_is_native_bit(b, i);
                        bit_is_native_bit(a ^ b, i);
                        let iu = i as $uint;
                        assert(((a ^ b) >> iu) & (1 as $uint) ==
                               if (((a >> iu) & (1 as $uint)) == (1 as $uint)) != (((b >> iu) & (1 as $uint)) == (1 as $uint)) { 1 as $uint } else { 0 as $uint })
                            by(bit_vector) requires iu < ($bits as $uint);
                    } else {
                        exp_concrete($bits as nat);
                        bit_above_width((a ^ b) as nat, $bits as nat, i);
                        bit_above_width(a as nat, $bits as nat, i);
                        bit_above_width(b as nat, $bits as nat, i);
                    }
                };
                eq_from_bits((a ^ b) as nat, bw_xor(a as nat, b as nat));
            }

            /// Native OR == spec bw_or on nat.
            #[verifier::spinoff_prover]
            pub proof fn native_or(a: $uint, b: $uint)
                ensures (a | b) as nat == bw_or(a as nat, b as nat)
            {
                assert forall|i: nat| #![auto] bit((a | b) as nat, i) == bit(bw_or(a as nat, b as nat), i) by {
                    or_bit(a as nat, b as nat, i);
                    if i < ($bits as nat) {
                        bit_is_native_bit(a, i);
                        bit_is_native_bit(b, i);
                        bit_is_native_bit(a | b, i);
                        let iu = i as $uint;
                        assert(((a | b) >> iu) & (1 as $uint) ==
                               if (((a >> iu) & (1 as $uint)) == (1 as $uint)) || (((b >> iu) & (1 as $uint)) == (1 as $uint)) { 1 as $uint } else { 0 as $uint })
                            by(bit_vector) requires iu < ($bits as $uint);
                    } else {
                        exp_concrete($bits as nat);
                        bit_above_width((a | b) as nat, $bits as nat, i);
                        bit_above_width(a as nat, $bits as nat, i);
                        bit_above_width(b as nat, $bits as nat, i);
                    }
                };
                eq_from_bits((a | b) as nat, bw_or(a as nat, b as nat));
            }

            /// Native AND == spec bw_and on nat.
            #[verifier::spinoff_prover]
            pub proof fn native_and(a: $uint, b: $uint)
                ensures (a & b) as nat == bw_and(a as nat, b as nat)
            {
                assert forall|i: nat| #![auto] bit((a & b) as nat, i) == bit(bw_and(a as nat, b as nat), i) by {
                    and_bit(a as nat, b as nat, i);
                    if i < ($bits as nat) {
                        bit_is_native_bit(a, i);
                        bit_is_native_bit(b, i);
                        bit_is_native_bit(a & b, i);
                        let iu = i as $uint;
                        assert(((a & b) >> iu) & (1 as $uint) ==
                               if (((a >> iu) & (1 as $uint)) == (1 as $uint)) && (((b >> iu) & (1 as $uint)) == (1 as $uint)) { 1 as $uint } else { 0 as $uint })
                            by(bit_vector) requires iu < ($bits as $uint);
                    } else {
                        exp_concrete($bits as nat);
                        bit_above_width((a & b) as nat, $bits as nat, i);
                        bit_above_width(a as nat, $bits as nat, i);
                        bit_above_width(b as nat, $bits as nat, i);
                    }
                };
                eq_from_bits((a & b) as nat, bw_and(a as nat, b as nat));
            }

            /// Native AND-NOT == spec bw_and_not on nat.
            #[verifier::spinoff_prover]
            pub proof fn native_and_not(a: $uint, b: $uint)
                ensures (a & !b) as nat == bw_and_not(a as nat, b as nat)
            {
                assert forall|i: nat| #![auto] bit((a & !b) as nat, i) == bit(bw_and_not(a as nat, b as nat), i) by {
                    and_not_bit(a as nat, b as nat, i);
                    if i < ($bits as nat) {
                        bit_is_native_bit(a, i);
                        bit_is_native_bit(b, i);
                        bit_is_native_bit(a & !b, i);
                        let iu = i as $uint;
                        assert(((a & !b) >> iu) & (1 as $uint) ==
                               if (((a >> iu) & (1 as $uint)) == (1 as $uint)) && !(((b >> iu) & (1 as $uint)) == (1 as $uint)) { 1 as $uint } else { 0 as $uint })
                            by(bit_vector) requires iu < ($bits as $uint);
                    } else {
                        exp_concrete($bits as nat);
                        bit_above_width((a & !b) as nat, $bits as nat, i);
                        bit_above_width(a as nat, $bits as nat, i);
                        bit_above_width(b as nat, $bits as nat, i);
                    }
                };
                eq_from_bits((a & !b) as nat, bw_and_not(a as nat, b as nat));
            }

            /// Native fixed-width left shift is infinite-bitstring left shift,
            /// truncated back to the native width.
            #[verifier::spinoff_prover]
            pub proof fn native_lsh(a: $uint)
                ensures (a << (1 as $uint)) as nat == chop(lsh(a as nat), $bits as nat)
            {
                assert forall|i: nat| #![auto]
                    bit((a << (1 as $uint)) as nat, i)
                        == bit(chop(lsh(a as nat), $bits as nat), i) by {
                    chop_bit(lsh(a as nat), $bits as nat, i);
                    if i < ($bits as nat) {
                        bit_is_native_bit(a << (1 as $uint), i);
                        bit_cons(a as nat, Bit::f(), i);
                        let iu = i as $uint;
                        if i == 0 {
                            assert((((a << (1 as $uint)) >> iu) & (1 as $uint))
                                == (0 as $uint)) by(bit_vector)
                                requires iu == (0 as $uint);
                        } else {
                            bit_is_native_bit(a, (i - 1) as nat);
                            assert((((a << (1 as $uint)) >> iu) & (1 as $uint))
                                == ((a >> ((iu - (1 as $uint)) as $uint)) & (1 as $uint)))
                                by(bit_vector)
                                requires iu < ($bits as $uint), iu > (0 as $uint);
                        }
                    } else {
                        exp_concrete($bits as nat);
                        bit_above_width((a << (1 as $uint)) as nat, $bits as nat, i);
                    }
                };
                eq_from_bits(
                    (a << (1 as $uint)) as nat,
                    chop(lsh(a as nat), $bits as nat),
                );
            }

            // ============================================================
            // ExecTnum: the generic exec_tnum::ExecTnum at this width
            // ============================================================
            pub type ExecTnum = crate::exec_tnum::ExecTnum<$uint>;

            // ============================================================
            // EAn: Executable Anum
            // ============================================================
            #[derive(Clone, Copy)]
            pub struct ExecAnum { pub base: $uint, pub span: $uint }
            impl ExecAnum {
                pub open spec fn to_an(self) -> Anum { Anum { base: self.base as nat, span: self.span as nat } }
                pub open spec fn has(self, x: $uint) -> bool { self.to_an().has(x as nat) }
                proof fn to_chopped(self)
                    ensures (ChoppedAnum { anum: self.to_an(), w: $bits as nat }).inv()
                {
                    self.to_an().to_tnum_inv();
                    native_fits(self.base);
                    native_fits(self.span);
                }
                /// has in terms of $uint ops (for by(bit_vector) proofs)
                proof fn has_eq_uint(self, x: $uint)
                    ensures self.has(x) <==> (x >= self.base && ((x - self.base) as $uint) & !self.span == (0 as $uint))
                {
                    let w: nat = $bits as nat;
                    exp_concrete(w);
                    if x >= self.base {
                        self.to_an().mask_tnum().has_equiv(nat_sub(x as nat, self.base as nat));
                        native_and_not((x - self.base) as $uint, self.span);
                    }
                }
                pub proof fn top_has(n: $uint)
                    ensures (ExecAnum { base: 0, span: !(0 as $uint) }).has(n)
                {
                    let w: nat = $bits as nat;
                    let max_nat = !(0 as $uint) as nat;
                    exp_concrete(w);
                    // Prove bw_and_not(n, max_nat) == 0 per-bit
                    assert forall|i: nat| #![auto] bit(bw_and_not(n as nat, max_nat), i) == bit(0nat, i) by {
                        and_not_bit(n as nat, max_nat, i);
                        bit_zero(i);
                        if i < w {
                            let iu: $uint = i as $uint;
                            bit_is_native_bit(!(0 as $uint), i);
                            assert(((!(0 as $uint)) >> iu) & (1 as $uint) == (1 as $uint)) by(bit_vector)
                                requires iu < ($bits as $uint);
                        } else {
                            bit_above_width(n as nat, w, i);
                        }
                    };
                    eq_from_bits(bw_and_not(n as nat, max_nat), 0);
                    Tnum::ctor(0, max_nat).has_equiv(n as nat);
                }
                #[inline] pub fn constant(n: $uint) -> (r: ExecAnum) ensures r.has(n) {
                    let r = ExecAnum { base: n, span: 0 };
                    proof {
                        r.has_eq_uint(n);
                        assert((0 as $uint) & !(0 as $uint) == (0 as $uint)) by(bit_vector);
                    }
                    r
                }
                #[inline] pub fn top() -> (r: ExecAnum)
                    ensures forall|n: $uint| #![auto] r.has(n)
                {
                    let r = ExecAnum { base: 0, span: !(0 as $uint) };
                    proof {
                        assert forall|n: $uint| #![auto] r.has(n) by {
                            ExecAnum::top_has(n);
                        };
                    }
                    r
                }
                /// Sound fixed-width addition, through ChoppedAnum::add_sound: top when
                /// a represented bound or the span sum would wrap, otherwise the spec
                /// add, whose members cannot wrap because each is at most base + span.
                #[inline] pub fn add(&self, t: &ExecAnum) -> (r: ExecAnum)
                    ensures forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_add(c2))
                {
                    let b1 = self.base; let s1 = self.span;
                    let b2 = t.base; let s2 = t.span;
                    let v = b1.wrapping_add(b2);
                    let sm = s1.wrapping_add(s2) | s1 | s2;
                    // Overflow check: if max1 + max2 overflows, or base sum overflows, return top
                    let max1 = b1.wrapping_add(s1);
                    let max2 = b2.wrapping_add(s2);
                    let max_sum = max1.wrapping_add(max2);
                    if max1 < b1 || max2 < b2 || max_sum < max1 || max_sum < max2 || v < b1 {
                        let r = ExecAnum { base: 0, span: !(0 as $uint) };
                        proof {
                            assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_add(c2)) by {
                                ExecAnum::top_has(c1.wrapping_add(c2));
                            };
                        }
                        return r;
                    }
                    let r = ExecAnum { base: v, span: sm };
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ca_s = ChoppedAnum { anum: self.to_an(), w };
                        let ca_t = ChoppedAnum { anum: t.to_an(), w };
                        ca_s.add_sound(ca_t);
                        // On this path no sum wraps: each max is above its base and
                        // the max sum is above both maxes.
                        let s12 = s1.wrapping_add(s2);
                        assert(v >= b2 && max1 >= s1 && max2 >= s2 && s12 >= s1 && s12 >= s2) by(bit_vector)
                            requires v == b1.wrapping_add(b2), v >= b1,
                                     max1 == b1.wrapping_add(s1), max1 >= b1,
                                     max2 == b2.wrapping_add(s2), max2 >= b2,
                                     max_sum == max1.wrapping_add(max2), max_sum >= max1, max_sum >= max2,
                                     s12 == s1.wrapping_add(s2);
                        add_no_overflow(b1, b2, v);
                        add_no_overflow(b1, s1, max1);
                        add_no_overflow(b2, s2, max2);
                        add_no_overflow(max1, max2, max_sum);
                        add_no_overflow(s1, s2, s12);
                        // Bridge: the executable span is the spec span, which adds
                        // the two span Tnums (0, s1) + (0, s2).
                        let mt_s = self.to_an().mask_tnum();
                        let mt_t = t.to_an().mask_tnum();
                        disj_zero(s1 as nat); disj_zero(s2 as nat);
                        mt_s.add_bitwise_eq(mt_t);
                        nat_add_correct(0, 0);
                        nat_add_correct(0, nat_add(s1 as nat, s2 as nat));
                        native_xor(s12, 0);
                        assert(s12 ^ (0 as $uint) == s12) by(bit_vector);
                        native_or(s12, s1);
                        native_or(s12 | s1, s2);
                        assert(r.to_an() == self.to_an().add(t.to_an()));
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_add(c2)) by {
                            native_fits(c1); native_fits(c2);
                            // Members are at most their max, so the sum does not wrap.
                            self.to_an().has_le_max(c1 as nat);
                            t.to_an().has_le_max(c2 as nat);
                            let cs = c1.wrapping_add(c2);
                            assert(cs as nat == c1 as nat + c2 as nat);
                            nat_add_correct(c1 as nat, c2 as nat);
                            native_fits(cs);
                            assert(ca_s.has(c1 as nat) && ca_t.has(c2 as nat));
                            assert(fits(nat_add(c1 as nat, c2 as nat), w));
                        };
                    }
                    r
                }
                /// Sound fixed-width subtraction, through ChoppedAnum::sub_sound: top
                /// when t's maximum wraps or exceeds self's base, otherwise the spec
                /// sub, whose differences cannot wrap because every member of t is at
                /// most t's maximum.
                #[inline] pub fn sub(&self, t: &ExecAnum) -> (r: ExecAnum)
                    ensures forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_sub(c2))
                {
                    let b1 = self.base; let s1 = self.span;
                    let b2 = t.base; let s2 = t.span;
                    let max2 = b2.wrapping_add(s2);
                    let v = b1.wrapping_sub(max2);
                    let s12 = s1.wrapping_add(s2);
                    let m = s12 | s1 | s2;
                    if max2 < b2 || v > b1 {
                        return Self::top();
                    }
                    let r = ExecAnum { base: v, span: m };
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped(); t.to_chopped();
                        let ca_s = ChoppedAnum { anum: self.to_an(), w };
                        let ca_t = ChoppedAnum { anum: t.to_an(), w };
                        // On this path t's maximum does not wrap and is at most b1.
                        assert(max2 >= s2 && b1 >= max2) by(bit_vector)
                            requires max2 == b2.wrapping_add(s2), max2 >= b2,
                                     v == b1.wrapping_sub(max2), v <= b1;
                        add_no_overflow(b2, s2, max2);
                        ca_s.sub_sound(ca_t);
                        // Bridge: the executable span is the chopped spec span,
                        // which adds the span Tnums (0, s1) + (0, s2).
                        let mt_s = self.to_an().mask_tnum();
                        let mt_t = t.to_an().mask_tnum();
                        disj_zero(s1 as nat); disj_zero(s2 as nat);
                        mt_s.add_bitwise_eq(mt_t);
                        let sn = nat_add(s1 as nat, s2 as nat);
                        nat_add_correct(0, 0);
                        nat_add_correct(0, sn);
                        bridge_add(s1, s2);
                        native_xor(s12, 0);
                        assert(s12 ^ (0 as $uint) == s12) by(bit_vector);
                        native_or(s12, s1);
                        native_or(s12 | s1, s2);
                        exp_concrete(w);
                        chop_id(0, w); chop_id(s1 as nat, w); chop_id(s2 as nat, w);
                        chop_bw_xor(sn, 0, w);
                        chop_bw_or(bw_xor(sn, 0), s1 as nat, w);
                        chop_bw_or(bw_or(bw_xor(sn, 0), s1 as nat), s2 as nat, w);
                        assert(r.to_an() == ca_s.sub(ca_t).anum);
                        assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies r.has(c1.wrapping_sub(c2)) by {
                            native_fits(c1); native_fits(c2);
                            // Every member of t is at most max2 <= b1 <= c1, so no wrap.
                            t.to_an().has_le_max(c2 as nat);
                            assert(ca_s.has(c1 as nat) && ca_t.has(c2 as nat));
                            assert(c1.wrapping_sub(c2) as nat == (c1 - c2) as nat);
                        };
                    }
                    r
                }
                pub fn div_const(&self, d: $uint) -> (r: ExecAnum)
                    requires d > 0
                    ensures forall|c: $uint| #![auto] self.has(c) ==> r.has(c / d)
                {
                    let min_q = self.base / d;
                    let max_v = self.base.wrapping_add(self.span);
                    let max_q = max_v / d;
                    if max_q < min_q || max_v < self.base {
                        let r = ExecAnum { base: 0, span: !(0 as $uint) };
                        proof {
                            assert forall|c: $uint| #![auto] self.has(c) implies r.has(c / d) by {
                                ExecAnum::top_has(c / d);
                            };
                        }
                        return r;
                    }
                    let range = max_q - min_q;
                    let mask = Self::ones_mask(range);
                    let r = ExecAnum { base: min_q, span: mask };
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped();
                        let ca = ChoppedAnum { anum: self.to_an(), w };
                        ca.div_const_sound(d as nat);
                        // On this path base + span does not wrap.
                        let b = self.base; let sp = self.span;
                        assert(max_v >= sp) by(bit_vector)
                            requires max_v == b.wrapping_add(sp), max_v >= b;
                        add_no_overflow(b, sp, max_v);
                        assert(r.to_an() == self.to_an().div_const(d as nat));
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c / d) by {
                            native_fits(c);
                            assert(ca.has(c as nat));
                        };
                    }
                    r
                }
                /// The least 2^k - 1 at or above n, which is the spec all_ones(len(n)).
                pub fn ones_mask(n: $uint) -> (r: $uint)
                    ensures r >= n, r & r.wrapping_add(1) == 0, r as nat == all_ones(len(n as nat))
                {
                    if n == 0 {
                        proof {
                            assert((0 as $uint) & (0 as $uint).wrapping_add(1) == (0 as $uint)) by(bit_vector);
                            assert(exp(0) == 1) by { assert(lshi(1, 0) == 1); }
                        }
                        return 0;
                    }
                    // Build 2^k - 1 by repeated doubling + 1
                    let mut mask: $uint = 1;
                    proof {
                        assert((1 as $uint) & (1 as $uint).wrapping_add(1) == (0 as $uint)) by(bit_vector);
                        assert(exp(0) == 1) by { assert(lshi(1, 0) == 1); }
                        exp_succ(0);
                        exp_concrete($bits as nat);
                    }
                    let mut i: u32 = 0;
                    while mask < n && i < $bits
                        invariant
                            n > 0,
                            i < $bits,
                            mask & mask.wrapping_add(1) == 0,
                            mask as nat == all_ones((i + 1) as nat),
                            all_ones(i as nat) < n as nat,
                            exp($bits as nat) == ($max_val as nat) + 1,
                        decreases ($bits - i)
                    {
                        proof {
                            assert(mask & mask.wrapping_add(1) == (0 as $uint) ==>
                                (mask.wrapping_add(mask).wrapping_add(1)) & (mask.wrapping_add(mask).wrapping_add(1)).wrapping_add(1) == (0 as $uint))
                                by(bit_vector);
                            // mask < n <= MAX = all_ones(bits), so i + 1 < bits and doubling does not wrap.
                            exp_succ((i + 1) as nat);
                            exp_succ(i as nat);
                            if (i + 1) as nat >= $bits as nat {
                                exp_le($bits as nat, (i + 1) as nat);
                            }
                            assert((i + 2) as nat <= $bits as nat);
                            exp_le((i + 2) as nat, $bits as nat);
                            exp_pos((i + 1) as nat);
                            assert(2 * (mask as nat) + 1 <= $max_val as nat);
                        }
                        let ghost old = mask;
                        mask = mask.wrapping_add(mask).wrapping_add(1);
                        i += 1;
                        proof {
                            assert(mask as nat == 2 * (old as nat) + 1);
                        }
                    }
                    proof {
                        all_ones_len_unique(n as nat, (i + 1) as nat);
                    }
                    mask
                }
                /// An Anum read as a Tnum: Tn(0, span) + Tn(base, 0), the spec
                /// ChoppedAnum::to_tnum. The addition carries the base into the
                /// span, so a base whose bits overlap the span is covered.
                pub fn to_etn(&self) -> (r: ExecTnum)
                    ensures r.wf(), forall|c: $uint| #![auto] self.has(c) ==> r.has(c),
                        r.to_tn() == (ChoppedAnum { anum: self.to_an(), w: $bits as nat }).to_tnum().tnum
                {
                    proof {
                        disj_zero(self.span as nat);
                        disj_zero_r(self.base as nat);
                    }
                    let m = ExecTnum { val: 0, mask: self.span };
                    let v = ExecTnum { val: self.base, mask: 0 };
                    let r = m.add(&v);
                    proof {
                        let w: nat = $bits as nat;
                        self.to_chopped();
                        let ca = ChoppedAnum { anum: self.to_an(), w };
                        ca.to_tnum_sound();
                        let an = self.to_an();
                        disj_zero(an.span);
                        disj_zero_r(an.base);
                        an.mask_tnum().add_bitwise_eq(an.val_tnum());
                        assert(m.to_tn() == an.mask_tnum() && v.to_tn() == an.val_tnum());
                        assert(r.to_tn() == ca.to_tnum().tnum);
                        assert forall|c: $uint| #![auto] self.has(c) implies r.has(c) by {
                            native_fits(c);
                            assert(ca.has(c as nat));
                        };
                    }
                    r
                }
                /// A Tnum read as an Anum: the spec ChoppedAnum::from_tnum.
                #[inline] pub fn from_etn(t: &ExecTnum) -> (r: ExecAnum)
                    requires t.wf()
                    ensures forall|c: $uint| #![auto] t.has(c) ==> r.has(c),
                        r.to_an() == ChoppedAnum::from_tnum(ChoppedTnum { tnum: t.to_tn(), w: $bits as nat }).anum
                {
                    let r = ExecAnum { base: t.val, span: t.mask };
                    proof {
                        let w: nat = $bits as nat;
                        t.lemma_ct();
                        let ct = ChoppedTnum { tnum: t.to_tn(), w };
                        ChoppedAnum::from_tnum_sound(ct);
                        assert(r.to_an() == ChoppedAnum::from_tnum(ct).anum);
                        assert forall|c: $uint| #![auto] t.has(c) implies r.has(c) by {
                            native_fits(c);
                            assert(ct.has(c as nat));
                        };
                    }
                    r
                }
                #[inline] pub fn min_val(&self) -> (r: $uint) ensures r == self.base { self.base }
                #[inline] pub fn max_val(&self) -> (r: $uint) ensures r == self.base.wrapping_add(self.span) { self.base.wrapping_add(self.span) }
                proof fn has_bounds(&self, c: $uint)
                    requires self.has(c)
                    ensures c >= self.base
                {
                    self.has_eq_uint(c);
                }
                /// Upper bound only valid when base + span doesn't wrap
                proof fn has_upper_bound(&self, c: $uint)
                    requires self.has(c), self.base.wrapping_add(self.span) >= self.base
                    ensures c <= self.base.wrapping_add(self.span)
                {
                    self.has_eq_uint(c);
                    let b = self.base; let s = self.span;
                    assert(c <= b.wrapping_add(s)) by(bit_vector)
                        requires c >= b, ((c - b) as $uint) & !s == (0 as $uint), b.wrapping_add(s) >= b;
                }
                proof fn has_narrow(&self, c: $uint, possible: $uint)
                    requires self.has(c), c <= possible,
                        possible & (possible.wrapping_add(1)) == 0,
                    ensures (ExecAnum { base: self.base, span: self.span & possible }).has(c)
                {
                    self.has_eq_uint(c);
                    let b = self.base; let s = self.span; let p = possible;
                    let d = (c - b) as $uint;
                    // d & !s == 0, c <= p, c >= b
                    // Need: d & !(s & p) == 0
                    // d & !(s & p) == d & (!s | !p) == (d & !s) | (d & !p) == 0 | (d & !p)
                    // d = c - b <= p - 0 = p (since c <= p and b >= 0), so d <= p
                    // d <= p and p = 2^k-1 means bits above k are 0 in d, so d & !p == 0
                    assert(((c - b) as $uint) & !(s & p) == (0 as $uint)) by(bit_vector)
                        requires c >= b, ((c - b) as $uint) & !s == (0 as $uint), c <= p, p & p.wrapping_add(1) == (0 as $uint);
                    let an2 = ExecAnum { base: b, span: s & p };
                    an2.has_eq_uint(c);
                }
            }

            // ============================================================
            // EUn: Executable Unum — horizontally composable Anum
            // ============================================================
            //
            // A Unum represents a set {v + d | d in D} where D is described
            // by bitfields in (w, x). Register w marks bitfield boundaries:
            //   - A 1-bit in w starts a new bitfield (the "leader").
            //   - A 0-bit in w continues the previous bitfield (a "follower").
            // Register x stores the maximum value for each bitfield.
            //
            // The set D is the set of all sums of per-bitfield values,
            // where each bitfield's value ranges from 0 to its max.
            //
            // The unbounded operation has the precise carry-boundary formula. The
            // executable operation below proves soundness at fixed width and widens
            // to top whenever a represented bound or result range would wrap.
            #[derive(Clone, Copy)]
            pub struct ExecUnum { pub base: $uint, pub walls: $uint, pub extent: $uint }

            impl ExecUnum {
                pub open spec fn to_un(self) -> Unum { Unum { base: self.base as nat, walls: self.walls as nat, extent: self.extent as nat } }
                pub open spec fn has(self, n: $uint) -> bool { self.to_un().has(n as nat) }

                proof fn to_chopped(self)
                    ensures (ChoppedUnum { unum: self.to_un(), w: $bits as nat }).inv()
                {
                    exp_concrete($bits as nat);
                    chop_id(self.base as nat, $bits as nat);
                    chop_id(self.walls as nat, $bits as nat);
                    chop_id(self.extent as nat, $bits as nat);
                }

                /// top contains everything.
                pub proof fn top_has(n: $uint)
                    ensures (ExecUnum { base: 0, walls: 0, extent: !(0 as $uint) }).has(n)
                {
                    assert(!(0 as $uint) >= n) by(bit_vector);
                    Unum::offset_from_bound((!(0 as $uint)) as nat, n as nat);
                }

                #[inline] pub fn constant(n: $uint) -> (r: ExecUnum) ensures r.has(n) {
                    proof { Unum::zero_offset_admitted((!(0 as $uint)) as nat, true); }
                    ExecUnum { base: n, walls: !(0 as $uint), extent: 0 }
                }
                #[inline] pub fn top() -> (r: ExecUnum)
                    ensures forall|n: $uint| #![auto] r.has(n)
                {
                    let r = ExecUnum { base: 0, walls: 0, extent: !(0 as $uint) };
                    proof {
                        assert forall|n: $uint| #![auto] r.has(n) by {
                            ExecUnum::top_has(n);
                        };
                    }
                    r
                }

                /// Sound fixed-width addition. Uses the precise field formula when
                /// represented bounds do not wrap; otherwise widens to top.
                /// cout = (x1 & x2) | ((x1 | x2) & ~(x1 + x2))
                /// w = (w1 & w2) & ~(cout << 1)
                #[verifier::rlimit(30)]
                #[verifier::spinoff_prover]
                #[inline] pub fn add(&self, t: &ExecUnum) -> (r: ExecUnum)
                    ensures forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_add(c2))
                {
                    let b1 = self.base; let sx = self.extent;
                    let b2 = t.base;    let tx = t.extent;
                    let v = b1.wrapping_add(b2);
                    let x12 = sx.wrapping_add(tx);
                    let max1 = b1.wrapping_add(sx);
                    let max2 = b2.wrapping_add(tx);
                    let max_sum = max1.wrapping_add(max2);
                    if v < b1 || v < b2
                        || x12 < sx || x12 < tx
                        || max1 < b1 || max2 < b2
                        || max_sum < max1 || max_sum < max2
                    {
                        let r = ExecUnum::top();
                        proof {
                            assert forall|c1: $uint, c2: $uint| #![auto]
                                self.has(c1) && t.has(c2)
                                implies r.has(c1.wrapping_add(c2)) by {
                                ExecUnum::top_has(c1.wrapping_add(c2));
                            };
                        }
                        return r;
                    }
                    let cout = (sx & tx) | ((sx | tx) & !x12);
                    let carry_in = cout << 1;
                    let sw = self.walls; let tw = t.walls;
                    let w = (sw & tw) & !carry_in;
                    let r = ExecUnum { base: v, walls: w, extent: x12 };
                    proof {
                        let width = $bits as nat;
                        let left = ChoppedUnum { unum: self.to_un(), w: width };
                        let right = ChoppedUnum { unum: t.to_un(), w: width };
                        self.to_chopped();
                        t.to_chopped();

                        add_no_overflow(b1, b2, v);
                        add_no_overflow(sx, tx, x12);

                        native_and(sx, tx);
                        native_or(sx, tx);
                        native_and_not(sx | tx, x12);
                        native_or(sx & tx, (sx | tx) & !x12);
                        Unum::carry_out_formula(sx as nat, tx as nat);
                        assert(cout as nat == Unum::carry_out(sx as nat, tx as nat));

                        native_lsh(cout);
                        native_and(sw, tw);
                        native_and_not(sw & tw, carry_in);
                        chop_bw_and_not(
                            bw_and(sw as nat, tw as nat),
                            lsh(Unum::carry_out(sx as nat, tx as nat)),
                            width,
                        );
                        native_fits(sw & tw);
                        assert(w as nat
                            == chop(
                                bw_and_not(
                                    bw_and(sw as nat, tw as nat),
                                    lsh(Unum::carry_out(sx as nat, tx as nat)),
                                ),
                                width,
                            ));
                        assert(r.to_un() == self.to_un().add(t.to_un()).truncate(width));

                        assert forall|c1: $uint, c2: $uint| #![auto]
                            self.has(c1) && t.has(c2)
                            implies r.has(c1.wrapping_add(c2)) by {
                            self.has_upper_bound(c1);
                            t.has_upper_bound(c2);
                            assert(c1.wrapping_add(c2) >= c1
                                && c1.wrapping_add(c2) >= c2) by(bit_vector)
                                requires c1 <= max1, c2 <= max2,
                                    max_sum == max1.wrapping_add(max2),
                                    max_sum >= max1, max_sum >= max2;
                            add_no_overflow(c1, c2, c1.wrapping_add(c2));
                            native_fits(c1);
                            native_fits(c2);
                            assert(left.has(c1 as nat));
                            assert(right.has(c2 as nat));
                            self.to_un().add_bounded_sound(
                                t.to_un(),
                                c1 as nat,
                                c2 as nat,
                                width,
                            );
                            assert(r.has(c1.wrapping_add(c2)));
                        };
                    }
                    r
                }

                /// Convert to EAn: widen each field's max to ones_mask.
                /// Unum fields are contiguous ranges `[0, max]`; Anum needs
                /// per-bit independence, so we round max up to 2^k - 1.
                pub fn to_ean(&self) -> ExecAnum {
                    // Sound overapproximation: ones_mask(x) >= x for the whole register.
                    // This treats the entire x as one field, which is always sound
                    // (it may be less precise than per-field widening for multi-field Unums,
                    // but it avoids trailing_zeros which Verus doesn't support).
                    ExecAnum { base: self.base, span: ExecAnum::ones_mask(self.extent) }
                }

                /// Convert to ETn: Anum->Tnum via Tnum addition Tn(v,0)+Tn(0,m).
                pub fn to_etn(&self) -> (r: ExecTnum) ensures r.wf() {
                    let an = self.to_ean();
                    let lbv = an.base; let lbm = an.span;
                    let ub = lbv.wrapping_add(lbm);
                    let mask = (ub ^ lbv) | an.span;
                    proof {
                        native_and_not(lbv, mask);
                        crate::exec_tnum::disj_and_not(lbv as nat, mask as nat);
                    }
                    ExecTnum { val: lbv & !mask, mask }
                }

                /// Build from an EAn: each uncertain bit becomes its own 1-wide bitfield.
                #[inline] pub fn from_ean(a: &ExecAnum) -> ExecUnum {
                    // Each bit of a.span is an independent bitfield of width 1.
                    // w = all 1s (every bit is a leader), x = a.span
                    ExecUnum { base: a.base, walls: !(0 as $uint), extent: a.span }
                }

                /// Build from an Interval: single bitfield covering the range.
                pub fn from_interval(iv: &Interval) -> (r: ExecUnum)
                    requires iv.wf()
                    ensures forall|c: $uint| #![auto] iv.has(c) ==> r.has(c)
                {
                    let range = iv.hi - iv.lo;
                    let r = ExecUnum { base: iv.lo, walls: 0, extent: range };
                    proof {
                        assert forall|c: $uint| #![auto] iv.has(c) implies r.has(c) by {
                            assert(c >= iv.lo && c <= iv.hi);
                            assert((c - iv.lo) as nat <= range as nat);
                            Unum::offset_from_bound(range as nat, (c - iv.lo) as nat);
                            assert(nat_sub(c as nat, iv.lo as nat) == (c - iv.lo) as nat);
                        };
                    }
                    r
                }

                /// Negation: negate v, keep uncertainty structure.
                /// -(v + d) = -v - d. The set of d values is {0..max per bitfield}.
                /// We need -d which ranges from -max to 0.
                /// So result.base = -v - total_max, result uncertainty = same structure.
                #[inline] pub fn neg(&self) -> ExecUnum {
                    // The negated range wraps when the input range does, or when it
                    // holds 0 and something else: -[0, e] = {0} u [-e, MAX].
                    if self.base.wrapping_add(self.extent) < self.base || (self.base == 0 && self.extent != 0) {
                        return ExecUnum::top();
                    }
                    let new_v = (0 as $uint).wrapping_sub(self.base).wrapping_sub(self.extent);
                    ExecUnum { base: new_v, walls: self.walls, extent: self.extent }
                }

                #[inline] pub fn sub(&self, t: &ExecUnum) -> ExecUnum {
                    self.add(&t.neg())
                }

                /// Multiplication: bilinear expansion.
                /// (v1+d1)*(v2+d2) = v1*v2 + v1*d2 + v2*d1 + d1*d2
                /// Uncertainty bounded by v1*x2 + v2*x1 + x1*x2.
                pub fn mul(&self, t: &ExecUnum) -> (r: ExecUnum)
                    ensures forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_mul(c2))
                {
                    let v1 = self.base; let x1 = self.extent;
                    let v2 = t.base;   let x2 = t.extent;
                    let max1 = v1.wrapping_add(x1);
                    let max2 = v2.wrapping_add(x2);
                    if max1 < v1 || max1 < x1 || max2 < v2 || max2 < x2 {
                        return ExecUnum::top();
                    }
                    let max_product = match max1.checked_mul(max2) {
                        Some(value) => value,
                        None => return ExecUnum::top(),
                    };
                    let base = match v1.checked_mul(v2) {
                        Some(value) => value,
                        None => return ExecUnum::top(),
                    };
                    let v1x2 = match v1.checked_mul(x2) {
                        Some(value) => value,
                        None => return ExecUnum::top(),
                    };
                    let v2x1 = match v2.checked_mul(x1) {
                        Some(value) => value,
                        None => return ExecUnum::top(),
                    };
                    let x1x2 = match x1.checked_mul(x2) {
                        Some(value) => value,
                        None => return ExecUnum::top(),
                    };
                    let unc1 = v1x2.wrapping_add(v2x1);
                    if unc1 < v1x2 || unc1 < v2x1 { return ExecUnum::top(); }
                    let unc = unc1.wrapping_add(x1x2);
                    if unc < unc1 || unc < x1x2 { return ExecUnum::top(); }
                    let upper = base.wrapping_add(unc);
                    if upper < base || upper < unc { return ExecUnum::top(); }
                    let r = ExecUnum { base, walls: 0, extent: unc };
                    proof {
                        let width = $bits as nat;
                        mul_exact(max1, max2, max_product);
                        mul_exact(v1, v2, base);
                        mul_exact(v1, x2, v1x2);
                        mul_exact(v2, x1, v2x1);
                        mul_exact(x1, x2, x1x2);
                        add_no_overflow(v1x2, v2x1, unc1);
                        add_no_overflow(unc1, x1x2, unc);
                        add_no_overflow(base, unc, upper);
                        assert(upper == max_product) by(nonlinear_arith)
                            requires
                                max1 as nat == v1 as nat + x1 as nat,
                                max2 as nat == v2 as nat + x2 as nat,
                                max_product as nat == (max1 as nat) * (max2 as nat),
                                base as nat == (v1 as nat) * (v2 as nat),
                                v1x2 as nat == (v1 as nat) * (x2 as nat),
                                v2x1 as nat == (v2 as nat) * (x1 as nat),
                                x1x2 as nat == (x1 as nat) * (x2 as nat),
                                unc1 as nat == v1x2 as nat + v2x1 as nat,
                                unc as nat == unc1 as nat + x1x2 as nat,
                                upper as nat == base as nat + unc as nat;
                        native_fits(base);
                        native_fits(unc);
                        assert(chop(base as nat, width) == base as nat);
                        assert(chop(unc as nat, width) == unc as nat);
                        chop_id(0, width);
                        assert(self.to_un().mul(t.to_un()).base == base as nat);
                        assert(self.to_un().mul(t.to_un()).walls == 0);
                        assert(self.to_un().mul(t.to_un()).extent == unc as nat);
                        assert(r.to_un() == self.to_un().mul(t.to_un()).truncate(width));

                        assert forall|c1: $uint, c2: $uint| #![auto]
                            self.has(c1) && t.has(c2)
                            implies r.has(c1.wrapping_mul(c2)) by {
                            self.has_upper_bound(c1);
                            t.has_upper_bound(c2);
                            let concrete = c1.wrapping_mul(c2);
                            vstd::arithmetic::mul::lemma_mul_upper_bound(
                                c1 as int,
                                max1 as int,
                                c2 as int,
                                max2 as int,
                            );
                            assert(prod(c1 as nat, c2 as nat) <= max_product as nat);
                            assert((max_product as nat) < exp(width));
                            chop_id(prod(c1 as nat, c2 as nat), width);
                            bridge_mul(c1, c2);
                            assert(concrete as nat == prod(c1 as nat, c2 as nat));
                            native_fits(v1);
                            native_fits(x1);
                            native_fits(v2);
                            native_fits(x2);
                            self.to_un().mul_bounded_sound(
                                t.to_un(),
                                c1 as nat,
                                c2 as nat,
                                width,
                            );
                            assert(r.has(concrete));
                        };
                    }
                    r
                }

                #[inline] pub fn min_val(&self) -> (r: $uint) ensures r == self.base { self.base }
                #[inline] pub fn max_val(&self) -> (r: $uint) ensures r == self.base.wrapping_add(self.extent) { self.base.wrapping_add(self.extent) }
                proof fn has_bounds(&self, c: $uint)
                    requires self.has(c)
                    ensures c >= self.base
                {
                }
                /// Upper bound only valid when base + extent doesn't wrap.
                proof fn has_upper_bound(&self, c: $uint)
                    requires self.has(c), self.base.wrapping_add(self.extent) >= self.base
                    ensures c <= self.base.wrapping_add(self.extent)
                {
                    Unum::offset_bounded(self.walls as nat, self.extent as nat, nat_sub(c as nat, self.base as nat));
                }
                #[inline] pub fn is_const(&self) -> bool { self.extent == 0 }
            }

            // ============================================================
            // Interval
            // ============================================================
            #[derive(Clone, Copy)]
            pub struct Interval { pub lo: $uint, pub hi: $uint }
            impl Interval {
                pub open spec fn wf(self) -> bool { self.lo <= self.hi }
                pub open spec fn has(self, x: $uint) -> bool { self.lo <= x && x <= self.hi }
                #[inline] pub fn constant(n: $uint) -> (r: Interval) ensures r.wf() { Interval { lo: n, hi: n } }
                #[inline] pub fn top() -> (r: Interval) ensures r.wf() { Interval { lo: 0, hi: !(0 as $uint) } }
                /// top contains everything.
                pub proof fn top_has(x: $uint)
                    ensures (Interval { lo: 0, hi: !(0 as $uint) }).has(x)
                {
                    assert(!(0 as $uint) >= x) by(bit_vector);
                }
                #[inline] pub fn add(&self, t: &Interval) -> (r: Interval)
                    ensures r.wf(),
                        forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) ==> r.has(c1.wrapping_add(c2))
                {
                    let slo = self.lo; let shi = self.hi; let tlo = t.lo; let thi = t.hi;
                    let lo = slo.wrapping_add(tlo);
                    let hi = shi.wrapping_add(thi);
                    if lo < slo || hi < shi || hi < lo {
                        proof {
                            assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies (Interval { lo: 0, hi: !(0 as $uint) }).has(c1.wrapping_add(c2)) by {
                                Self::top_has(c1.wrapping_add(c2));
                            };
                        }
                        Interval { lo: 0, hi: !(0 as $uint) }
                    } else {
                        proof {
                            assert forall|c1: $uint, c2: $uint| #![auto] self.has(c1) && t.has(c2) implies (Interval { lo, hi }).has(c1.wrapping_add(c2)) by {
                                // In non-overflow branch: lo >= slo, hi >= shi, hi >= lo
                                // c1 <= shi, c2 <= thi, shi+thi = hi doesn't wrap
                                // So c1+c2 <= shi+thi doesn't wrap either
                                assert(c1.wrapping_add(c2) >= c1 && c1.wrapping_add(c2) >= c2) by(bit_vector)
                                    requires c1 <= shi, c2 <= thi, hi == shi.wrapping_add(thi), hi >= shi;
                                // lower bound
                                assert(slo.wrapping_add(tlo) <= c1.wrapping_add(c2)) by(bit_vector)
                                    requires slo <= c1, tlo <= c2, c1.wrapping_add(c2) >= c1, lo == slo.wrapping_add(tlo), lo >= slo;
                                // upper bound
                                assert(c1.wrapping_add(c2) <= shi.wrapping_add(thi)) by(bit_vector)
                                    requires c1 <= shi, c2 <= thi, c1.wrapping_add(c2) >= c2, hi == shi.wrapping_add(thi), hi >= shi;
                            };
                        }
                        Interval { lo, hi }
                    }
                }
                #[inline] pub fn meet(&self, t: &Interval) -> (r: Interval)
                    ensures r.wf(),
                        forall|x: $uint| #![auto] self.has(x) && t.has(x) ==> r.has(x)
                {
                    let lo = if self.lo > t.lo { self.lo } else { t.lo };
                    let hi = if self.hi < t.hi { self.hi } else { t.hi };
                    if hi < lo {
                        proof {
                            assert forall|x: $uint| #![auto] self.has(x) && t.has(x) implies (Interval { lo: 0, hi: !(0 as $uint) }).has(x) by {
                                Self::top_has(x);
                            };
                        }
                        Interval::top()
                    } else { Interval { lo, hi } }
                }
                #[inline] pub fn join(&self, t: &Interval) -> (r: Interval)
                    requires self.wf(), t.wf()
                    ensures r.wf(),
                        forall|x: $uint| #![auto] self.has(x) ==> r.has(x),
                        forall|x: $uint| #![auto] t.has(x) ==> r.has(x)
                {
                    Interval {
                        lo: if self.lo < t.lo { self.lo } else { t.lo },
                        hi: if self.hi > t.hi { self.hi } else { t.hi },
                    }
                }
                #[inline] pub fn div_const(&self, d: $uint) -> (r: Interval)
                    requires self.wf(), d > 0
                    ensures r.wf(),
                        forall|x: $uint| #![auto] self.has(x) ==> r.has(x / d)
                {
                    proof {
                        vstd::arithmetic::div_mod::lemma_div_is_ordered(self.lo as int, self.hi as int, d as int);
                        assert forall|x: $uint| #![auto] self.has(x) implies Interval { lo: self.lo / d, hi: self.hi / d }.has(x / d) by {
                            vstd::arithmetic::div_mod::lemma_div_is_ordered(self.lo as int, x as int, d as int);
                            vstd::arithmetic::div_mod::lemma_div_is_ordered(x as int, self.hi as int, d as int);
                        };
                    }
                    Interval { lo: self.lo / d, hi: self.hi / d }
                }
            }

            } // verus!
        }
    };
}

abstract_domain!(d8, u8, 8u32, 0xFFu8);
abstract_domain!(d16, u16, 16u32, 0xFFFFu16);
abstract_domain!(d32, u32, 32u32, 0xFFFF_FFFFu32);
abstract_domain!(d64, u64, 64u32, 0xFFFF_FFFF_FFFF_FFFFu64);
// d128 disabled: u128 bitvector proofs exceed Z3 capacity
// abstract_domain!(d128, u128, 128u32, 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFFu128);
