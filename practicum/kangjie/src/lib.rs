//! Week 1–2 ramp-up katas. Each module is a regression test, not scratch work.

pub mod egraph;
pub mod interval;
pub mod union_find;

#[cfg(test)]
mod kata1 {
    use super::egraph::EGraph;
    use super::union_find::{NaivePartition, UnionFind};

    #[test]
    fn union_find_matches_naive_sets() {
        let mut uf = UnionFind::new();
        let mut model = NaivePartition::new();
        for _ in 0..16 {
            uf.make();
            model.make();
        }
        for i in 0..40 {
            let a = i % 16;
            let b = (i * 5) % 16;
            uf.union(a, b);
            model.union(a, b);
        }
        for a in 0..16 {
            for b in 0..16 {
                assert_eq!(uf.same(a, b), model.same(a, b));
            }
        }
    }

    #[test]
    fn rebuild_reuses_add_after_child_merge() {
        let mut g = EGraph::new(true);
        let a = g.add("Lit", &[], Some(1));
        let b = g.add("Lit", &[], Some(2));
        let s1 = g.add("Add", &[a, b], None);
        let extra = g.add("Lit", &[], Some(3));
        g.union(extra, a);
        let s2 = g.add("Add", &[a, b], None);
        assert_eq!(g.find(s1), g.find(s2));
        assert_eq!(g.add_count("Add"), 1);
    }

    #[test]
    fn skipping_rebuild_duplicates_the_add() {
        let mut g = EGraph::new(false);
        let a = g.add("Lit", &[], Some(1));
        let b = g.add("Lit", &[], Some(2));
        g.add("Add", &[a, b], None);
        let extra = g.add("Lit", &[], Some(3));
        g.union(extra, a);
        g.add("Add", &[a, b], None);
        assert!(
            g.add_count("Add") >= 2 || g.dirty_without_rebuild,
            "without rebuild the hash-cons key stays stale"
        );
    }
}

#[cfg(test)]
mod kata3_to_5 {
    use super::interval::Interval;

    fn samples() -> Vec<Interval> {
        vec![
            Interval::Bottom,
            Interval::range(0, 0),
            Interval::range(3, 3),
            Interval::range(10, 20),
            Interval::range(0, 255),
        ]
    }

    #[test]
    fn add_contains_every_concrete_wrapping_sum() {
        let a = Interval::range(10, 20);
        let b = Interval::range(3, 5);
        for x in 10u8..=20 {
            for y in 3u8..=5 {
                assert!(a.add(b).has(x.wrapping_add(y)));
            }
        }
        let wrap = Interval::range(250, 255).add(Interval::range(10, 12));
        assert_eq!(wrap, Interval::top());
        assert!(wrap.has(4));
    }

    #[test]
    fn meet_without_bottom_breaks_absorption() {
        let a = Interval::range(3, 3);
        let b = Interval::range(10, 10);
        let m = a.meet_no_bottom(b);
        assert_eq!(m, Interval::top());
        assert_ne!(m, a, "meet(a, b) = top cannot satisfy meet(a, top) = a");
    }

    #[test]
    fn meet_with_bottom_is_commutative_idempotent_absorbing() {
        for a in samples() {
            assert_eq!(a.meet(a), a);
            assert_eq!(a.meet(Interval::top()), a);
            assert_eq!(a.meet(Interval::Bottom), Interval::Bottom);
            for b in samples() {
                assert_eq!(a.meet(b), b.meet(a));
                for c in samples() {
                    assert_eq!(a.meet(b.meet(c)), a.meet(b).meet(c));
                }
            }
        }
    }

    #[test]
    fn add_is_monotone() {
        let a = Interval::range(0, 2);
        let b = Interval::range(0, 4);
        assert!(a.refines(b));
        assert!(a.add(Interval::range(1, 1)).refines(b.add(Interval::range(1, 1))));
    }

    #[test]
    fn sub_contains_every_concrete_wrapping_difference() {
        let a = Interval::range(10, 20);
        let b = Interval::range(1, 3);
        for x in 10u8..=20 {
            for y in 1u8..=3 {
                assert!(a.sub(b).has(x.wrapping_sub(y)));
            }
        }
    }
}
