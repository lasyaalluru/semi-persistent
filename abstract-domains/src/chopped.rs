// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
use crate::anum::*;
use crate::bools::*;
use crate::div::*;
use crate::nats::*;
use crate::tbit::*;
use crate::tnum::*;
use crate::unum::*;
/// Layer 3: Bounded register simulation.
///
/// `ChoppedTnum{tn, w}` wraps an unbounded Tnum with a bit-width `w`.
/// Proves that all operations on w-bit values produce w-bit results:
/// - Bitwise ops preserve width (via `fits_mapd`)
/// - Arithmetic ops are chopped to w bits (via `chop_sound`)
/// - Soundness: `ChoppedTnum.has(x) && ChoppedTnum.has(y) ==> ChoppedTnum.op(x,y).has(chop(x op y, w))`
///
/// This is the bridge between the unbounded Layer 2 proofs and the
/// bounded Layer 4 executable implementations.
use vstd::prelude::*;

verus! {

/// A bounded Tnum: fits in w bits.
pub struct ChoppedTnum {
    pub tnum: Tnum,
    pub w: nat,
}

impl ChoppedTnum {
    pub open spec fn inv(self) -> bool {
        self.tnum.inv() && fits(self.tnum.val, self.w) && fits(self.tnum.mask, self.w)
    }

    pub open spec fn has(self, n: nat) -> bool {
        self.tnum.has(n) && fits(n, self.w)
    }

    // Helper to construct ChoppedTnum without struct literal in ensures
    pub open spec fn mk(tnum: Tnum, w: nat) -> ChoppedTnum { ChoppedTnum { tnum, w } }

    // ================================================================
    // Width preservation: bitwise ops on w-bit Tnums produce w-bit Tnums
    // ================================================================

    pub open spec fn bw_or(self, t: ChoppedTnum) -> ChoppedTnum { Self::mk(self.tnum.bw_or(t.tnum), self.w) }
    pub open spec fn bw_and(self, t: ChoppedTnum) -> ChoppedTnum { Self::mk(self.tnum.bw_and(t.tnum), self.w) }
    pub open spec fn bw_xor(self, t: ChoppedTnum) -> ChoppedTnum { Self::mk(self.tnum.bw_xor(t.tnum), self.w) }

    /// Helper: mapd preserves fits when inputs fit.
    proof fn fits_mapd(a: nat, b: nat, f: spec_fn(Bit, Bit) -> Bit, w: nat)
        requires fits(a, w), fits(b, w), f(Bit::f(), Bit::f()) == Bit::f()
        ensures fits(mapd(a, b, f), w)
    {
        chop_mapd(a, b, f, w);
        // chop(mapd(a,b,f), w) == mapd(chop(a,w), chop(b,w), f) == mapd(a,b,f)
    }

    pub proof fn or_inv(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures self.bw_or(t).inv()
    {
        let w = self.w;
        self.tnum.or_sound(t.tnum);
        // fits: or(sv,tv) and andnot(or(sm,tm), or(sv,tv))
        Self::fits_mapd(self.tnum.val, t.tnum.val, |x: Bit, y: Bit| x.or(y), w);
        Self::fits_mapd(self.tnum.mask, t.tnum.mask, |x: Bit, y: Bit| x.or(y), w);
        Self::fits_mapd(bw_or(self.tnum.mask, t.tnum.mask), bw_or(self.tnum.val, t.tnum.val), |x: Bit, y: Bit| x.and_not(y), w);
    }

    pub proof fn and_inv(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures self.bw_and(t).inv()
    {
        let w = self.w;
        self.tnum.and_sound(t.tnum);
        Self::fits_mapd(self.tnum.val, t.tnum.val, |x: Bit, y: Bit| x.and(y), w);
        Self::fits_mapd(self.tnum.mask, t.tnum.mask, |x: Bit, y: Bit| x.or(y), w);
    }

    pub proof fn xor_inv(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures self.bw_xor(t).inv()
    {
        let sv = self.tnum.val; let sm = self.tnum.mask;
        let tv = t.tnum.val; let tm = t.tnum.mask;
        let w = self.w;
        Self::fits_mapd(sv, tv, |x: Bit, y: Bit| x.xor(y), w);
        Self::fits_mapd(sm, tm, |x: Bit, y: Bit| x.or(y), w);
        Self::fits_mapd(bw_xor(sv, tv), bw_or(sm, tm), |x: Bit, y: Bit| x.and_not(y), w);
        assert forall|i: nat| #![auto] !(bit(bw_and_not(bw_xor(sv, tv), bw_or(sm, tm)), i).b() && bit(bw_or(sm, tm), i).b()) by {
            and_not_bit(bw_xor(sv, tv), bw_or(sm, tm), i);
        };
        disj_bits(bw_and_not(bw_xor(sv, tv), bw_or(sm, tm)), bw_or(sm, tm));
    }

    // ================================================================
    // Bitwise soundness at width w: the L2 theorems, and w-bit operands
    // give a w-bit result
    // ================================================================

    pub proof fn or_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_or(t).has(bw_or(x, y))
    {
        self.tnum.or_sound(t.tnum);
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.bw_or(t).has(bw_or(x, y)) by {
            Self::fits_mapd(x, y, |a: Bit, b: Bit| a.or(b), self.w);
        };
    }

    pub proof fn and_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_and(t).has(bw_and(x, y))
    {
        self.tnum.and_sound(t.tnum);
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.bw_and(t).has(bw_and(x, y)) by {
            Self::fits_mapd(x, y, |a: Bit, b: Bit| a.and(b), self.w);
        };
    }

    pub proof fn xor_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_xor(t).has(bw_xor(x, y))
    {
        self.tnum.xor_sound(t.tnum);
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.bw_xor(t).has(bw_xor(x, y)) by {
            Self::fits_mapd(x, y, |a: Bit, b: Bit| a.xor(b), self.w);
        };
    }

    pub open spec fn bw_and_not(self, t: ChoppedTnum) -> ChoppedTnum { Self::mk(self.tnum.bw_and_not(t.tnum), self.w) }

    pub proof fn and_not_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.bw_and_not(t).has(bw_and_not(x, y))
    {
        self.tnum.and_not_sound(t.tnum);
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.bw_and_not(t).has(bw_and_not(x, y)) by {
            Self::fits_mapd(x, y, |a: Bit, b: Bit| a.and_not(b), self.w);
        };
    }

    /// Bounded NOT: XOR with the w-bit all-ones constant.
    pub open spec fn bw_not(self) -> ChoppedTnum {
        Self::mk(self.tnum.bw_xor(Tnum::unit(all_ones(self.w))), self.w)
    }

    pub proof fn not_sound(self)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.bw_not().has(bw_xor(n, all_ones(self.w)))
    {
        let ones = all_ones(self.w);
        exp_pos(self.w);
        chop_id(ones, self.w);
        Tnum::unit_has(ones);
        self.tnum.xor_sound(Tnum::unit(ones));
        assert forall|n: nat| #![auto] self.has(n) implies self.bw_not().has(bw_xor(n, ones)) by {
            Self::fits_mapd(n, ones, |a: Bit, b: Bit| a.xor(b), self.w);
        };
    }

    // ================================================================
    // Bounded arithmetic: chop(op(a, b), w)
    // ================================================================

    /// Bounded addition: add_bitwise chopped to w bits.
    pub open spec fn add(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.add_bitwise(t.tnum).chop_tn(self.w), w: self.w }
    }

    pub proof fn add_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) ==>
            self.add(t).has(chop(nat_add(x, y), self.w))
    {
        self.tnum.add_sound(t.tnum);
        self.tnum.add_bitwise_eq(t.tnum);
        let sum = self.tnum.add_bitwise(t.tnum);
        Tnum::add_bitwise_inv(self.tnum, t.tnum);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y)
            implies self.add(t).has(chop(nat_add(x, y), self.w)) by {
            assert(sum.has(nat_add(x, y)));
            sum.chop_sound(self.w);
            chop_idem(nat_add(x, y), self.w);
        };
    }

    pub proof fn add_inv(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures self.add(t).inv()
    {
        Tnum::add_bitwise_inv(self.tnum, t.tnum);
        self.tnum.add_bitwise(t.tnum).chop_sound(self.w);
        // chop_tn always produces fits values
        chop_idem(self.tnum.add_bitwise(t.tnum).val, self.w);
        chop_idem(self.tnum.add_bitwise(t.tnum).mask, self.w);
        // chop_tn(x, w).v = chop(x.v, w), chop_tn(x, w).m = chop(x.m, w)
        // fits(chop(_, w), w) from chop_idem
    }

    /// Bounded multiplication: pair-join (`Tnum::pair_mul`) chopped to w bits.
    pub open spec fn mul(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: Tnum::pair_mul(self.tnum, t.tnum).chop_tn(self.w), w: self.w }
    }

    pub proof fn mul_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            self.mul(t).inv(),
            forall|x: nat, y: nat| #![auto]
                self.has(x) && t.has(y) ==>
                self.mul(t).has(chop(nat_mul_acc(x, y, 0), self.w))
    {
        let prod = Tnum::pair_mul(self.tnum, t.tnum);
        Tnum::pair_mul_sound(self.tnum, t.tnum);
        prod.chop_sound(self.w);
        chop_idem(prod.val, self.w);
        chop_idem(prod.mask, self.w);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y)
            implies self.mul(t).has(chop(nat_mul_acc(x, y, 0), self.w)) by {
            assert(prod.has(nat_mul_acc(x, y, 0)));
            chop_idem(nat_mul_acc(x, y, 0), self.w);
        };
    }

    /// Bounded division.
    pub open spec fn div(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.div(t.tnum, self.w).0, w: self.w }
    }

    /// Bounded guarded division: Tnum::div_g with w iterations and the remainder
    /// width k = len(t.max()), the bit length of the largest divisor; quotient and
    /// remainder are chopped to w bits.
    pub open spec fn div_g(self, t: ChoppedTnum) -> (ChoppedTnum, ChoppedTnum) {
        let (q, r) = self.tnum.div_g(t.tnum, self.w, len(t.tnum.max()));
        (ChoppedTnum { tnum: q.chop_tn(self.w), w: self.w }, ChoppedTnum { tnum: r.chop_tn(self.w), w: self.w })
    }

    /// div_g is well formed and contains x / y and x % y for all members x, y.
    pub proof fn div_g_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w, t.tnum.min() > 0
        ensures
            self.div_g(t).0.inv(),
            self.div_g(t).1.inv(),
            forall|x: nat, y: nat| #![auto]
                self.has(x) && t.has(y) ==> self.div_g(t).0.has(x / y) && self.div_g(t).1.has(x % y),
    {
        let w = self.w;
        let k = len(t.tnum.max());
        Self::fits_mapd(t.tnum.val, t.tnum.mask, |x: Bit, y: Bit| x.or(y), w);
        Self::fits_lt(t.tnum.max(), w);
        len_bound(t.tnum.max());
        self.tnum.div_g_sound(t.tnum, w, k);
        let (q, r) = self.tnum.div_g(t.tnum, w, k);
        q.chop_sound(w);
        r.chop_sound(w);
        chop_idem(q.val, w); chop_idem(q.mask, w);
        chop_idem(r.val, w); chop_idem(r.mask, w);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) implies self.div_g(t).0.has(x / y) && self.div_g(t).1.has(x % y) by {
            Self::fits_lt(x, w);
            t.tnum.has_bounds(y);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, y as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, y as int);
            assert(x / y <= x && x % y <= x) by(nonlinear_arith)
                requires x == y * (x / y) + x % y, y > 0, x / y >= 0, x % y >= 0;
            chop_id(x / y, w);
            chop_id(x % y, w);
        };
    }

    /// The members of t whose highest set bit is i, for t.val == 0: bit i set,
    /// the unknown bits below i free. Its min is 2^i > 0, so div_g applies.
    pub open spec fn top_piece(self, i: nat) -> ChoppedTnum {
        ChoppedTnum { tnum: Tnum::ctor(exp(i), chop(self.tnum.mask, i)), w: self.w }
    }

    /// div_g over the top pieces of t at its unknown bits below j, joined;
    /// None when t has no unknown bit below j.
    pub open spec fn div_z(self, t: ChoppedTnum, j: nat) -> Option<(ChoppedTnum, ChoppedTnum)>
        decreases j
    {
        if j == 0 { None }
        else {
            let i = (j - 1) as nat;
            let acc = self.div_z(t, i);
            if bit(t.tnum.mask, i).b() {
                let p = self.div_g(t.top_piece(i));
                match acc {
                    None => Some(p),
                    Some(a) => Some((a.0.join(p.0), a.1.join(p.1))),
                }
            } else { acc }
        }
    }

    /// Division by the nonzero members of t: div_g when t.min() > 0, otherwise
    /// the join of div_g over the top pieces of t. None when t is {0}.
    pub open spec fn div_nz(self, t: ChoppedTnum) -> Option<(ChoppedTnum, ChoppedTnum)> {
        if t.tnum.val > 0 { Some(self.div_g(t)) } else { self.div_z(t, self.w) }
    }

    /// A nonzero member y of t (t.val == 0) is in the top piece at bit
    /// len(y) - 1, which is an unknown bit of t below w.
    pub proof fn top_piece_has(self, y: nat)
        requires self.inv(), self.tnum.val == 0, self.has(y), y > 0
        ensures
            len(y) > 0,
            (len(y) - 1) < self.w,
            bit(self.tnum.mask, (len(y) - 1) as nat).b(),
            self.top_piece((len(y) - 1) as nat).has(y),
    {
        let m = self.tnum.mask;
        top_bit(y);
        let i = (len(y) - 1) as nat;
        Self::fits_lt(y, self.w);
        len_le(y, self.w);
        self.tnum.has_equiv(y);
        assert forall|j: nat| #![auto] bit(y, j).b() implies bit(m, j).b() by {
            and_not_bit(y, m, j);
            bit_zero(j);
        };
        let p = self.top_piece(i).tnum;
        p.has_equiv(y);
        assert forall|j: nat| #![auto] bit(bw_and_not(y, chop(m, i)), j) == bit(exp(i), j) by {
            and_not_bit(y, chop(m, i), j);
            chop_bit(m, i, j);
            bit_exp(i, j);
            if j > i {
                assert(j >= len(y));
            }
        };
        eq_from_bits(bw_and_not(y, chop(m, i)), exp(i));
    }

    /// A top piece below w is well formed and has a positive min.
    pub proof fn top_piece_inv(self, i: nat)
        requires self.inv(), i < self.w
        ensures self.top_piece(i).inv(), self.top_piece(i).tnum.min() > 0
    {
        let m = self.tnum.mask;
        exp_pos(i);
        assert forall|j: nat| #![auto] !(bit(exp(i), j).b() && bit(chop(m, i), j).b()) by {
            bit_exp(i, j);
            chop_bit(m, i, j);
        };
        disj_bits(exp(i), chop(m, i));
        exp_succ(i);
        exp_le(i + 1, self.w);
        chop_id(exp(i), self.w);
        chop_lt(m, i);
        chop_id(chop(m, i), self.w);
    }

    /// div_z is Some exactly when t has an unknown bit below j; then it is well
    /// formed and contains x / y and x % y for every member y != 0 of t below 2^j.
    pub proof fn div_z_sound(self, t: ChoppedTnum, j: nat)
        requires self.inv(), t.inv(), self.w == t.w, t.tnum.val == 0, j <= self.w
        ensures
            self.div_z(t, j) is Some <==> exists|i: nat| i < j && #[trigger] bit(t.tnum.mask, i).b(),
            match self.div_z(t, j) {
                Some(p) => p.0.inv() && p.1.inv() && p.0.w == self.w && p.1.w == self.w
                    && forall|x: nat, y: nat| #![auto]
                        self.has(x) && t.has(y) && y > 0 && len(y) <= j ==> p.0.has(x / y) && p.1.has(x % y),
                None => true,
            },
        decreases j
    {
        if j > 0 {
            let i = (j - 1) as nat;
            self.div_z_sound(t, i);
            let acc = self.div_z(t, i);
            if bit(t.tnum.mask, i).b() {
                let tp = t.top_piece(i);
                t.top_piece_inv(i);
                self.div_g_sound(tp);
                let p = self.div_g(tp);
                if let Some(a) = acc {
                    a.0.tnum.join_inv(p.0.tnum);
                    a.1.tnum.join_inv(p.1.tnum);
                    a.0.tnum.join_sound(p.0.tnum);
                    a.1.tnum.join_sound(p.1.tnum);
                    Self::join_fits(a.0, p.0);
                    Self::join_fits(a.1, p.1);
                }
                assert forall|x: nat, y: nat| #![auto]
                    self.has(x) && t.has(y) && y > 0 && len(y) <= j
                    implies self.div_z(t, j).unwrap().0.has(x / y) && self.div_z(t, j).unwrap().1.has(x % y) by {
                    t.top_piece_has(y);
                    if len(y) == j {
                        assert(tp.has(y));
                    } else {
                        assert(bit(t.tnum.mask, (len(y) - 1) as nat).b());
                    }
                };
            } else {
                assert forall|x: nat, y: nat| #![auto]
                    self.has(x) && t.has(y) && y > 0 && len(y) <= j
                    implies len(y) <= i by {
                    t.top_piece_has(y);
                };
            }
            if exists|k: nat| k < j && #[trigger] bit(t.tnum.mask, k).b() {
                let k = choose|k: nat| k < j && #[trigger] bit(t.tnum.mask, k).b();
                if k < i { assert(bit(t.tnum.mask, k).b()); }
            }
        }
    }

    /// The join of two w-bit Tnums fits in w bits.
    proof fn join_fits(a: ChoppedTnum, b: ChoppedTnum)
        requires a.inv(), b.inv(), a.w == b.w
        ensures fits(a.join(b).tnum.val, a.w), fits(a.join(b).tnum.mask, a.w)
    {
        let (av, bv) = (a.tnum.val, b.tnum.val);
        Self::fits_mapd(av, bv, |x: Bit, y: Bit| x.and(y), a.w);
        Self::fits_mapd(av, a.tnum.mask, |x: Bit, y: Bit| x.xor(y), a.w);
        Self::fits_mapd(bv, b.tnum.mask, |x: Bit, y: Bit| x.xor(y), a.w);
        Self::fits_mapd(a.tnum.u(), b.tnum.u(), |x: Bit, y: Bit| x.or(y), a.w);
        Self::fits_mapd(bw_and(av, bv), bw_or(a.tnum.u(), b.tnum.u()), |x: Bit, y: Bit| x.xor(y), a.w);
    }

    /// div_nz is None exactly when t is {0}; otherwise it is well formed and
    /// contains x / y and x % y for every member x of self and member y != 0 of t.
    pub proof fn div_nz_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            self.div_nz(t) is None <==> (t.tnum.val == 0 && t.tnum.mask == 0),
            match self.div_nz(t) {
                Some(p) => p.0.inv() && p.1.inv() && p.0.w == self.w && p.1.w == self.w
                    && forall|x: nat, y: nat| #![auto]
                        self.has(x) && t.has(y) && y > 0 ==> p.0.has(x / y) && p.1.has(x % y),
                None => true,
            },
    {
        if t.tnum.val > 0 {
            self.div_g_sound(t);
        } else {
            let m = t.tnum.mask;
            self.div_z_sound(t, self.w);
            assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) && y > 0 implies len(y) <= self.w by {
                t.top_piece_has(y);
            };
            if m == 0 {
                assert forall|i: nat| #![auto] !bit(m, i).b() by { bit_zero(i); };
            } else {
                top_bit(m);
                Self::fits_lt(m, self.w);
                len_le(m, self.w);
                assert(bit(m, (len(m) - 1) as nat).b());
            }
        }
    }

    /// Bounded negation.
    pub open spec fn neg(self) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.neg(self.w), w: self.w }
    }

    /// Bounded right shift.
    pub open spec fn rsh(self) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.rsh(), w: self.w }
    }

    proof fn fits_rsh(n: nat, w: nat)
        requires fits(n, w)
        ensures fits(rsh(n), w)
    {
        assert forall|j: nat| #![auto] bit(chop(rsh(n), w), j) == bit(rsh(n), j) by {
            chop_bit(rsh(n), w, j);
            if j >= w {
                bit_tl(n, j);
                chop_bit(n, w, j + 1);
            }
        };
        eq_from_bits(chop(rsh(n), w), rsh(n));
    }

    pub proof fn rsh_sound(self)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.rsh().has(rsh(n))
    {
        self.tnum.rsh_sound();
        assert forall|n: nat| #![auto] self.has(n) implies self.rsh().has(rsh(n)) by {
            Self::fits_rsh(n, self.w);
        };
    }

    /// Bounded left shift (with chop).
    pub open spec fn lsh(self) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.lsh().chop_tn(self.w), w: self.w }
    }

    pub proof fn lsh_sound(self)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.lsh().has(chop(lsh(n), self.w))
    {
        self.tnum.lsh_sound();
        assert forall|n: nat| #![auto] self.has(n)
            implies self.lsh().has(chop(lsh(n), self.w)) by {
            self.tnum.lsh().chop_sound(self.w);
            chop_idem(lsh(n), self.w);
        };
    }

    /// Bounded right shift by i bits.
    pub open spec fn rshi(self, i: nat) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.rshi(i), w: self.w }
    }

    proof fn fits_rshi(n: nat, w: nat, i: nat)
        requires fits(n, w)
        ensures fits(rshi(n, i), w)
        decreases i
    {
        if i > 0 {
            Self::fits_rsh(n, w);
            Self::fits_rshi(rsh(n), w, (i - 1) as nat);
        }
    }

    pub proof fn rshi_sound(self, i: nat)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.rshi(i).has(rshi(n, i))
    {
        self.tnum.rshi_sound(i);
        assert forall|n: nat| #![auto] self.has(n) implies self.rshi(i).has(rshi(n, i)) by {
            Self::fits_rshi(n, self.w, i);
        };
    }

    /// Bounded left shift by i bits (with chop).
    pub open spec fn lshi(self, i: nat) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.lshi(i).chop_tn(self.w), w: self.w }
    }

    pub proof fn lshi_sound(self, i: nat)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.lshi(i).has(chop(lshi(n, i), self.w))
    {
        self.tnum.lshi_sound(i);
        self.tnum.lshi_inv(i);
        assert forall|n: nat| #![auto] self.has(n)
            implies self.lshi(i).has(chop(lshi(n, i), self.w)) by {
            self.tnum.lshi(i).chop_sound(self.w);
            chop_idem(lshi(n, i), self.w);
        };
    }

    /// A w-bit value is below 2^w.
    proof fn fits_lt(n: nat, w: nat)
        requires fits(n, w)
        ensures n < exp(w)
    {
        chop_is_mod(n, w);
        exp_pos(w);
        vstd::arithmetic::div_mod::lemma_mod_bound(n as int, exp(w) as int);
    }

    pub proof fn neg_sound(self)
        requires self.inv(), self.w > 0
        ensures forall|n: nat| #![auto] self.has(n) ==> self.neg().has(chop((exp(self.w) - n) as nat, self.w))
    {
        self.tnum.neg_sound(self.w);
        assert forall|n: nat| #![auto] self.has(n) implies self.neg().has(chop((exp(self.w) - n) as nat, self.w)) by {
            Self::fits_lt(n, self.w);
            chop_idem((exp(self.w) - n) as nat, self.w);
        };
    }

    /// Bounded subtraction: add the bounded negation.
    pub open spec fn sub(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.sub(t.tnum, self.w), w: self.w }
    }

    pub proof fn sub_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w, self.w > 0
        ensures forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) ==> self.sub(t).has(chop(nat_add(x, (exp(self.w) - y) as nat), self.w))
    {
        self.tnum.sub_sound_all(t.tnum, self.w);
        assert forall|x: nat, y: nat| #![auto]
            self.has(x) && t.has(y) implies self.sub(t).has(chop(nat_add(x, (exp(self.w) - y) as nat), self.w)) by {
            Self::fits_lt(x, self.w);
            Self::fits_lt(y, self.w);
            chop_idem(nat_add(x, (exp(self.w) - y) as nat), self.w);
        };
    }

    /// Bounded join.
    pub open spec fn join(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.join(t.tnum), w: self.w }
    }

    pub proof fn join_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures
            forall|n: nat| #![auto] self.has(n) ==> self.join(t).has(n),
            forall|n: nat| #![auto] t.has(n) ==> self.join(t).has(n),
    {
        self.tnum.join_sound(t.tnum);
    }

    /// Bounded meet.
    pub open spec fn meet(self, t: ChoppedTnum) -> ChoppedTnum {
        ChoppedTnum { tnum: self.tnum.meet(t.tnum), w: self.w }
    }

    pub proof fn meet_sound(self, t: ChoppedTnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|n: nat| #![auto] self.has(n) && t.has(n) ==> self.meet(t).has(n)
    {
        self.tnum.meet_sound(t.tnum);
    }
}

/// A bounded Anum: fits in w bits.
pub struct ChoppedAnum {
    pub anum: Anum,
    pub w: nat,
}

impl ChoppedAnum {
    pub open spec fn inv(self) -> bool {
        self.anum.to_tnum().inv() && fits(self.anum.base, self.w) && fits(self.anum.span, self.w)
    }

    pub open spec fn has(self, n: nat) -> bool {
        self.anum.has(n) && fits(n, self.w)
    }

    /// add_sound: if both inputs and their sum fit, the result contains the sum.
    pub proof fn add_sound(self, t: ChoppedAnum)
        requires self.inv(), t.inv(), self.w == t.w
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) && fits(nat_add(x, y), self.w)
            ==> self.anum.add(t.anum).has(nat_add(x, y))
    {
        self.anum.add_sound(t.anum);
    }


    /// A w-bit Tnum read as an Anum: base is the known bits, span the unknown ones.
    pub open spec fn from_tnum(t: ChoppedTnum) -> ChoppedAnum {
        ChoppedAnum { anum: Anum::from_tnum(t.tnum), w: t.w }
    }

    pub proof fn from_tnum_sound(t: ChoppedTnum)
        requires t.inv()
        ensures forall|n: nat| #![auto] t.has(n) ==> Self::from_tnum(t).has(n)
    {
        Anum::from_tnum_sound(t.tnum);
    }

    /// A w-bit Anum read as a Tnum: Tn(0, span) + Tn(base, 0), chopped to w bits.
    pub open spec fn to_tnum(self) -> ChoppedTnum {
        ChoppedTnum { tnum: self.anum.to_tnum().chop_tn(self.w), w: self.w }
    }

    pub proof fn to_tnum_sound(self)
        requires self.inv()
        ensures forall|n: nat| #![auto] self.has(n) ==> self.to_tnum().has(n)
    {
        self.anum.to_tnum_inv();
        self.anum.to_tnum().chop_sound(self.w);
        assert forall|n: nat| #![auto] self.has(n) implies self.to_tnum().has(n) by {
            Anum::tnum_has_from_anum(self.anum, n);
            chop_idem(n, self.w);
        };
    }

    /// Bounded subtraction: the L2 sub with its span chopped to w bits.
    pub open spec fn sub(self, t: ChoppedAnum) -> ChoppedAnum {
        ChoppedAnum {
            anum: Anum {
                base: self.anum.sub(t.anum).base,
                span: chop(self.anum.sub(t.anum).span, self.w),
            },
            w: self.w,
        }
    }

    /// sub_sound: when self's base is at least t's maximum, no difference of
    /// members wraps, and every difference is a member of the bounded sub.
    pub proof fn sub_sound(self, t: ChoppedAnum)
        requires self.inv(), t.inv(), self.w == t.w, self.anum.base >= nat_add(t.anum.base, t.anum.span)
        ensures forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) ==> self.sub(t).has((x - y) as nat)
    {
        self.anum.sub_sound(t.anum);
        let s = self.anum.sub(t.anum);
        assert forall|x: nat, y: nat| #![auto] self.has(x) && t.has(y) implies self.sub(t).has((x - y) as nat) by {
            ChoppedTnum::fits_lt(x, self.w);
            // y <= t's maximum <= self's base <= x
            t.anum.has_le_max(y);
            nat_add_correct(t.anum.base, t.anum.span);
            assert(y <= x);
            assert(s.has((x - y) as nat));
            let off = ((x - y) - s.base) as nat;
            // The offset is a bit subset of the span and below 2^w, so it is a
            // bit subset of the chopped span too.
            s.mask_tnum().has_equiv(off);
            chop_bw_and_not(off, s.span, self.w);
            exp_pos(self.w);
            chop_id(off, self.w);
            chop_id(0, self.w);
            Tnum::ctor(0, chop(s.span, self.w)).has_equiv(off);
            chop_id((x - y) as nat, self.w);
        };
    }

    /// div_const_sound: delegates to Anum::div_const_sound.
    pub proof fn div_const_sound(self, d: nat)
        requires self.inv(), d > 0
        ensures forall|x: nat| #![auto] self.has(x) ==> self.anum.div_const(d).has(x / d)
    {
        self.anum.div_const_sound(d);
    }


}

/// A bounded Unum: fits in w bits.
pub struct ChoppedUnum {
    pub unum: Unum,
    pub w: nat,
}

impl ChoppedUnum {
    pub open spec fn inv(self) -> bool {
        fits(self.unum.base, self.w) && fits(self.unum.extent, self.w) && fits(self.unum.walls, self.w)
    }

    pub open spec fn has(self, n: nat) -> bool {
        self.inv() && self.unum.has(n) && fits(n, self.w)
    }

    pub proof fn add_sound(self, t: ChoppedUnum)
        requires self.inv(), t.inv(), self.w == t.w,
            fits(nat_add(self.unum.extent, t.unum.extent), self.w),
            fits(nat_add(self.unum.base, t.unum.base), self.w),
        ensures forall|c1: nat, c2: nat| #![auto] self.has(c1) && t.has(c2) && fits(nat_add(c1, c2), self.w)
            ==> self.unum.add(t.unum).truncate(self.w).has(nat_add(c1, c2))
    {
        assert forall|c1: nat, c2: nat| #![auto] self.has(c1) && t.has(c2) && fits(nat_add(c1, c2), self.w)
            implies self.unum.add(t.unum).truncate(self.w).has(nat_add(c1, c2)) by {
            nat_add_correct(c1, c2);
            chop_is_mod(nat_add(c1, c2), self.w);
            exp_pos(self.w);
            self.unum.add_bounded_sound(t.unum, c1, c2, self.w);
        };
    }

    pub proof fn mul_sound(self, t: ChoppedUnum)
        requires self.inv(), t.inv(), self.w == t.w,
            fits(prod(self.unum.base, t.unum.base), self.w),
            fits(prod(self.unum.base, t.unum.extent) + prod(t.unum.base, self.unum.extent) + prod(self.unum.extent, t.unum.extent), self.w),
        ensures forall|c1: nat, c2: nat| #![auto] self.has(c1) && t.has(c2) && fits(prod(c1, c2), self.w)
            ==> self.unum.mul(t.unum).truncate(self.w).has(prod(c1, c2))
    {
        assert forall|c1: nat, c2: nat| #![auto] self.has(c1) && t.has(c2) && fits(prod(c1, c2), self.w)
            implies self.unum.mul(t.unum).truncate(self.w).has(prod(c1, c2)) by {
            chop_is_mod(prod(c1, c2), self.w);
            exp_pos(self.w);
            self.unum.mul_bounded_sound(t.unum, c1, c2, self.w);
        };
    }
}

} // verus!
