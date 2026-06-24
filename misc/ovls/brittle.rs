// Reproduction of the proof brittleness shape observed in
// src/allocate.rs.  Per memory `project_ptrs_mut_eq_cascade`, the
// cascade ingredients exercised here are:
//
//   1. Two list invariants sharing the same pointer-typed keys.
//      Supplied structurally by OVList::wf (list1.wf + list2.wf
//      over a shared perms map).
//   2. A closed spec / intro lemma idiom that exposes raw ptr@.addr
//      atoms when invoked.  Supplied by `lemma_ptr_addr_below_intro`
//      and `lemma_structural_facts_intro` in block.rs.
//   3. vstd's broadcasts `ptrs_mut_eq` / `ptrs_mut_eq_sized` fire on
//      any ptr@ atom in scope — these are the cascade lemmas named
//      in the memory note; no extra broadcast is added here.
//   4. An outer `assert forall|i| ...` quantifier to multiply
//      instantiations against.
//
// See the plan at .claude/plans/port-overlaid-list-structure-moonlit-muffin.md
// for the measurement matrix.

use crate::block::*;
use crate::ovlist::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

impl<'pool> OVList<'pool> {
    /// BASELINE: all 4 ingredients ON.
    pub fn touch_and_reprove_list2(&mut self, p: *mut BlockHdr, b: int)
        requires
            old(self).wf(),
            p@.addr < b,
        ensures self.wf(),
    {
        proof {
            lemma_ptr_addr_below_intro(p, b);

            assert forall|i: int|
                0 <= i < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, i)
            by { }
        }
    }

    /// Knob 1 OFF: only list2.wf is in scope (list1 invariant not
    /// exposed).  Compared to baseline this kills the "two lists in
    /// same context" structural prerequisite.
    pub fn variant_no_list1(&mut self, p: *mut BlockHdr, b: int)
        requires
            old(self).list2.wf(old(self).perms@),
            p@.addr < b,
        ensures self.list2.wf(self.perms@),
    {
        proof {
            lemma_ptr_addr_below_intro(p, b);

            assert forall|i: int|
                0 <= i < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, i)
            by { }
        }
    }

    /// Knob 2 OFF: no intro-lemma call, so no raw `ptr@.addr` atom
    /// is dropped into the SMT context.  Compared to baseline this
    /// kills the broadcast trigger source.
    pub fn variant_no_intro(&mut self, p: *mut BlockHdr, b: int)
        requires
            old(self).wf(),
            p@.addr < b,
        ensures self.wf(),
    {
        proof {
            assert forall|i: int|
                0 <= i < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, i)
            by { }
        }
    }

    /// Knob 4 OFF: single concrete assert instead of `assert forall|i|`.
    /// Compared to baseline this kills the outer quantifier that
    /// instantiations multiply against.
    pub fn variant_no_forall(&mut self, p: *mut BlockHdr, b: int)
        requires
            old(self).wf(),
            p@.addr < b,
        ensures self.wf(),
    {
        proof {
            lemma_ptr_addr_below_intro(p, b);
        }
    }

    /// SCALED baseline: 5 fresh ptr@.addr atoms in scope (mirrors the
    /// "many lemma_wf_structural_facts calls" pattern in allocate.rs).
    /// Both list invariants exposed via OVList::wf.
    pub fn cascade_both(
        &mut self,
        p1: *mut BlockHdr, b1: int,
        p2: *mut BlockHdr, b2: int,
        p3: *mut BlockHdr, b3: int,
        p4: *mut BlockHdr, b4: int,
        p5: *mut BlockHdr, b5: int,
    )
        requires
            old(self).wf(),
            p1@.addr < b1, p2@.addr < b2, p3@.addr < b3,
            p4@.addr < b4, p5@.addr < b5,
        ensures self.wf(),
    {
        proof {
            lemma_ptr_addr_below_intro(p1, b1);
            lemma_ptr_addr_below_intro(p2, b2);
            lemma_ptr_addr_below_intro(p3, b3);
            lemma_ptr_addr_below_intro(p4, b4);
            lemma_ptr_addr_below_intro(p5, b5);

            assert forall|i: int|
                0 <= i < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, i)
            by { }
        }
    }

    /// SCALED, ingredient 1 OFF: same 5 ptr@.addr atoms, but only
    /// list2.wf is in scope (no list1 invariant).  If the cascade is
    /// driven by "two list invariants in same context" the count
    /// here should be visibly lower than `cascade_both`.
    pub fn cascade_list2_only(
        &mut self,
        p1: *mut BlockHdr, b1: int,
        p2: *mut BlockHdr, b2: int,
        p3: *mut BlockHdr, b3: int,
        p4: *mut BlockHdr, b4: int,
        p5: *mut BlockHdr, b5: int,
    )
        requires
            old(self).list2.wf(old(self).perms@),
            p1@.addr < b1, p2@.addr < b2, p3@.addr < b3,
            p4@.addr < b4, p5@.addr < b5,
        ensures self.list2.wf(self.perms@),
    {
        proof {
            lemma_ptr_addr_below_intro(p1, b1);
            lemma_ptr_addr_below_intro(p2, b2);
            lemma_ptr_addr_below_intro(p3, b3);
            lemma_ptr_addr_below_intro(p4, b4);
            lemma_ptr_addr_below_intro(p5, b5);

            assert forall|i: int|
                0 <= i < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, i)
            by { }
        }
    }

    /// SCALED, ingredient 2 OFF: both lists in scope, 5 ptr params
    /// but no intro-lemma calls.  If the cascade is driven by ptr@
    /// atom exposure this should drop sharply versus `cascade_both`.
    pub fn cascade_no_intro(
        &mut self,
        p1: *mut BlockHdr, b1: int,
        p2: *mut BlockHdr, b2: int,
        p3: *mut BlockHdr, b3: int,
        p4: *mut BlockHdr, b4: int,
        p5: *mut BlockHdr, b5: int,
    )
        requires
            old(self).wf(),
            p1@.addr < b1, p2@.addr < b2, p3@.addr < b3,
            p4@.addr < b4, p5@.addr < b5,
        ensures self.wf(),
    {
        proof {
            assert forall|i: int|
                0 <= i < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, i)
            by { }
        }
    }

    // =====================================================================
    // PORTED VARIANTS — mirror the allocate.rs brittleness pattern.
    // Each variant uses 3 (p, q) pairs / 3 ptrs to keep signatures
    // compact.  Cascade sizes are proportionally smaller than at 10
    // pairs but the cost-product profile and quantifier ranking are
    // preserved.
    // =====================================================================

    /// Property (1): multi-atom intro lemma.  3 (p, q) pairs; each
    /// `lemma_structural_facts_intro` call drops 4 ptr@ atoms into
    /// scope → 12 atoms total.  Compare against `cascade_both` (5
    /// atoms) to attribute count growth to per-call atom width.
    pub fn port_multi_atom_intro(
        &mut self,
        p1: *mut BlockHdr, q1: *mut BlockHdr, o1: int,
        p2: *mut BlockHdr, q2: *mut BlockHdr, o2: int,
        p3: *mut BlockHdr, q3: *mut BlockHdr, o3: int,
    )
        requires
            old(self).wf(),
            q1@.addr == p1@.addr + o1, q1@.provenance == p1@.provenance,
            q2@.addr == p2@.addr + o2, q2@.provenance == p2@.provenance,
            q3@.addr == p3@.addr + o3, q3@.provenance == p3@.provenance,
        ensures self.wf(),
    {
        proof {
            lemma_structural_facts_intro(p1, q1, o1);
            lemma_structural_facts_intro(p2, q2, o2);
            lemma_structural_facts_intro(p3, q3, o3);

            assert forall|i: int|
                0 <= i < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, i)
            by { }
        }
    }

    /// Property (3): case analysis on shared concrete ptrs.  Three
    /// ptrs (`block`, `next_phys`, `new_free`) reused across three
    /// `if`-arms; each arm calls intro on all three.  Mirrors the
    /// `assert(self.all_blocks.wf()) by { ... }` case split in
    /// allocate.rs lines 1002–1316.
    pub fn port_case_split(
        &mut self,
        block: *mut BlockHdr, next_phys: *mut BlockHdr, new_free: *mut BlockHdr,
        o_bn: int, o_bf: int, o_nf: int,
        which: u8,
    )
        requires
            old(self).wf(),
            next_phys@.addr == block@.addr + o_bn,
            next_phys@.provenance == block@.provenance,
            new_free@.addr == block@.addr + o_bf,
            new_free@.provenance == block@.provenance,
            new_free@.addr == next_phys@.addr + o_nf,
            new_free@.provenance == next_phys@.provenance,
        ensures self.wf(),
    {
        proof {
            if which == 0 {
                lemma_structural_facts_intro(block, next_phys, o_bn);
                lemma_structural_facts_intro(block, new_free, o_bf);
                lemma_structural_facts_intro(next_phys, new_free, o_nf);
            } else if which == 1 {
                lemma_structural_facts_intro(block, next_phys, o_bn);
                lemma_structural_facts_intro(block, new_free, o_bf);
                lemma_structural_facts_intro(next_phys, new_free, o_nf);
            } else {
                lemma_structural_facts_intro(block, next_phys, o_bn);
                lemma_structural_facts_intro(block, new_free, o_bf);
                lemma_structural_facts_intro(next_phys, new_free, o_nf);
            }

            assert forall|i: int|
                0 <= i < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, i)
            by { }
        }
    }

    /// Property (4): cross-firing of both lists' `contains`-foralls.
    /// 3 ptrs required to be in BOTH list1.ptrs@ AND list2.ptrs@.
    /// Asserting `p_k@.addr != 0` for each forces both lists' wf
    /// `forall|p| ptrs.contains(p) ==> ... p@.addr != 0` to
    /// instantiate against the same ptrs.  This is the user's
    /// original hypothesis under direct test.
    pub fn port_cross_firing(
        &mut self,
        p1: *mut BlockHdr, p2: *mut BlockHdr, p3: *mut BlockHdr,
    )
        requires
            old(self).wf(),
            old(self).list1.ptrs@.contains(p1),
            old(self).list2.ptrs@.contains(p1),
            old(self).list1.ptrs@.contains(p2),
            old(self).list2.ptrs@.contains(p2),
            old(self).list1.ptrs@.contains(p3),
            old(self).list2.ptrs@.contains(p3),
        ensures self.wf(),
    {
        proof {
            assert(p1@.addr != 0);
            assert(p2@.addr != 0);
            assert(p3@.addr != 0);

            assert forall|i: int|
                0 <= i < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, i)
            by { }
        }
    }

    /// Combined: properties (1), (2), (4) together — multi-atom
    /// intro × 3 calls, both lists in scope, cross-firing.
    pub fn port_combined(
        &mut self,
        p1: *mut BlockHdr, q1: *mut BlockHdr, o1: int,
        p2: *mut BlockHdr, q2: *mut BlockHdr, o2: int,
        p3: *mut BlockHdr, q3: *mut BlockHdr, o3: int,
    )
        requires
            old(self).wf(),
            old(self).list1.ptrs@.contains(p1), old(self).list2.ptrs@.contains(p1),
            old(self).list1.ptrs@.contains(p2), old(self).list2.ptrs@.contains(p2),
            old(self).list1.ptrs@.contains(p3), old(self).list2.ptrs@.contains(p3),
            q1@.addr == p1@.addr + o1, q1@.provenance == p1@.provenance,
            q2@.addr == p2@.addr + o2, q2@.provenance == p2@.provenance,
            q3@.addr == p3@.addr + o3, q3@.provenance == p3@.provenance,
        ensures self.wf(),
    {
        proof {
            lemma_structural_facts_intro(p1, q1, o1);
            lemma_structural_facts_intro(p2, q2, o2);
            lemma_structural_facts_intro(p3, q3, o3);

            assert forall|i: int|
                0 <= i < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, i)
            by { }
        }
    }

    /// Property (5): two outer `assert forall|i|` blocks — one per
    /// list — in the same proof.  Mirrors the actual shape of
    /// `assert(self.wf()) by { ... }` in `src/allocate.rs:3024,3247`,
    /// where re-proving `wf` requires re-establishing BOTH lists'
    /// per-index `wf_node` clauses simultaneously.
    pub fn port_two_foralls(
        &mut self,
        p1: *mut BlockHdr, q1: *mut BlockHdr, o1: int,
        p2: *mut BlockHdr, q2: *mut BlockHdr, o2: int,
        p3: *mut BlockHdr, q3: *mut BlockHdr, o3: int,
    )
        requires
            old(self).wf(),
            old(self).list1.ptrs@.contains(p1), old(self).list2.ptrs@.contains(p1),
            old(self).list1.ptrs@.contains(p2), old(self).list2.ptrs@.contains(p2),
            old(self).list1.ptrs@.contains(p3), old(self).list2.ptrs@.contains(p3),
            q1@.addr == p1@.addr + o1, q1@.provenance == p1@.provenance,
            q2@.addr == p2@.addr + o2, q2@.provenance == p2@.provenance,
            q3@.addr == p3@.addr + o3, q3@.provenance == p3@.provenance,
        ensures self.wf(),
    {
        proof {
            lemma_structural_facts_intro(p1, q1, o1);
            lemma_structural_facts_intro(p2, q2, o2);
            lemma_structural_facts_intro(p3, q3, o3);

            assert forall|i: int|
                0 <= i < self.list1.ptrs@.len()
                implies self.list1.wf_node(self.perms@, i)
            by { }

            assert forall|j: int|
                0 <= j < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, j)
            by { }
        }
    }

    /// Property (6): coupled-index 2D-style quantification.  ONE
    /// `assert forall|i|` whose body asserts BOTH `list1.wf_node(i)`
    /// AND `list2.wf_node(i)` under a common Skolem `i`.  Now both
    /// `list1.ptrs@[i]` and `list2.ptrs@[i]` enter the same body —
    /// vstd broadcasts can fire on both within one quantifier
    /// instantiation, which `port_two_foralls` could not.
    pub fn port_coupled_forall(
        &mut self,
        p1: *mut BlockHdr, q1: *mut BlockHdr, o1: int,
        p2: *mut BlockHdr, q2: *mut BlockHdr, o2: int,
        p3: *mut BlockHdr, q3: *mut BlockHdr, o3: int,
    )
        requires
            old(self).wf(),
            old(self).list1.ptrs@.len() <= old(self).list2.ptrs@.len(),
            old(self).list1.ptrs@.contains(p1), old(self).list2.ptrs@.contains(p1),
            old(self).list1.ptrs@.contains(p2), old(self).list2.ptrs@.contains(p2),
            old(self).list1.ptrs@.contains(p3), old(self).list2.ptrs@.contains(p3),
            q1@.addr == p1@.addr + o1, q1@.provenance == p1@.provenance,
            q2@.addr == p2@.addr + o2, q2@.provenance == p2@.provenance,
            q3@.addr == p3@.addr + o3, q3@.provenance == p3@.provenance,
        ensures self.wf(),
    {
        proof {
            lemma_structural_facts_intro(p1, q1, o1);
            lemma_structural_facts_intro(p2, q2, o2);
            lemma_structural_facts_intro(p3, q3, o3);

            assert forall|i: int|
                0 <= i < self.list1.ptrs@.len()
                implies
                    self.list1.wf_node(self.perms@, i)
                    && self.list2.wf_node(self.perms@, i)
            by { }

            assert forall|j: int|
                self.list1.ptrs@.len() <= j < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, j)
            by { }
        }
    }

    /// Scale = 5 ptrs.  Same shape as port_coupled_forall, larger
    /// ptr@-atom budget.  Confirms that instantiation count grows
    /// superlinearly in the ptr count.
    pub fn port_coupled_forall_5(
        &mut self,
        p1: *mut BlockHdr, q1: *mut BlockHdr, o1: int,
        p2: *mut BlockHdr, q2: *mut BlockHdr, o2: int,
        p3: *mut BlockHdr, q3: *mut BlockHdr, o3: int,
        p4: *mut BlockHdr, q4: *mut BlockHdr, o4: int,
        p5: *mut BlockHdr, q5: *mut BlockHdr, o5: int,
    )
        requires
            old(self).wf(),
            old(self).list1.ptrs@.len() <= old(self).list2.ptrs@.len(),
            old(self).list1.ptrs@.contains(p1), old(self).list2.ptrs@.contains(p1),
            old(self).list1.ptrs@.contains(p2), old(self).list2.ptrs@.contains(p2),
            old(self).list1.ptrs@.contains(p3), old(self).list2.ptrs@.contains(p3),
            old(self).list1.ptrs@.contains(p4), old(self).list2.ptrs@.contains(p4),
            old(self).list1.ptrs@.contains(p5), old(self).list2.ptrs@.contains(p5),
            q1@.addr == p1@.addr + o1, q1@.provenance == p1@.provenance,
            q2@.addr == p2@.addr + o2, q2@.provenance == p2@.provenance,
            q3@.addr == p3@.addr + o3, q3@.provenance == p3@.provenance,
            q4@.addr == p4@.addr + o4, q4@.provenance == p4@.provenance,
            q5@.addr == p5@.addr + o5, q5@.provenance == p5@.provenance,
        ensures self.wf(),
    {
        proof {
            lemma_structural_facts_intro(p1, q1, o1);
            lemma_structural_facts_intro(p2, q2, o2);
            lemma_structural_facts_intro(p3, q3, o3);
            lemma_structural_facts_intro(p4, q4, o4);
            lemma_structural_facts_intro(p5, q5, o5);

            assert forall|i: int|
                0 <= i < self.list1.ptrs@.len()
                implies
                    self.list1.wf_node(self.perms@, i)
                    && self.list2.wf_node(self.perms@, i)
            by { }

            assert forall|j: int|
                self.list1.ptrs@.len() <= j < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, j)
            by { }
        }
    }

    /// Scale = 8 ptrs.
    pub fn port_coupled_forall_8(
        &mut self,
        p1: *mut BlockHdr, q1: *mut BlockHdr, o1: int,
        p2: *mut BlockHdr, q2: *mut BlockHdr, o2: int,
        p3: *mut BlockHdr, q3: *mut BlockHdr, o3: int,
        p4: *mut BlockHdr, q4: *mut BlockHdr, o4: int,
        p5: *mut BlockHdr, q5: *mut BlockHdr, o5: int,
        p6: *mut BlockHdr, q6: *mut BlockHdr, o6: int,
        p7: *mut BlockHdr, q7: *mut BlockHdr, o7: int,
        p8: *mut BlockHdr, q8: *mut BlockHdr, o8: int,
    )
        requires
            old(self).wf(),
            old(self).list1.ptrs@.len() <= old(self).list2.ptrs@.len(),
            old(self).list1.ptrs@.contains(p1), old(self).list2.ptrs@.contains(p1),
            old(self).list1.ptrs@.contains(p2), old(self).list2.ptrs@.contains(p2),
            old(self).list1.ptrs@.contains(p3), old(self).list2.ptrs@.contains(p3),
            old(self).list1.ptrs@.contains(p4), old(self).list2.ptrs@.contains(p4),
            old(self).list1.ptrs@.contains(p5), old(self).list2.ptrs@.contains(p5),
            old(self).list1.ptrs@.contains(p6), old(self).list2.ptrs@.contains(p6),
            old(self).list1.ptrs@.contains(p7), old(self).list2.ptrs@.contains(p7),
            old(self).list1.ptrs@.contains(p8), old(self).list2.ptrs@.contains(p8),
            q1@.addr == p1@.addr + o1, q1@.provenance == p1@.provenance,
            q2@.addr == p2@.addr + o2, q2@.provenance == p2@.provenance,
            q3@.addr == p3@.addr + o3, q3@.provenance == p3@.provenance,
            q4@.addr == p4@.addr + o4, q4@.provenance == p4@.provenance,
            q5@.addr == p5@.addr + o5, q5@.provenance == p5@.provenance,
            q6@.addr == p6@.addr + o6, q6@.provenance == p6@.provenance,
            q7@.addr == p7@.addr + o7, q7@.provenance == p7@.provenance,
            q8@.addr == p8@.addr + o8, q8@.provenance == p8@.provenance,
        ensures self.wf(),
    {
        proof {
            lemma_structural_facts_intro(p1, q1, o1);
            lemma_structural_facts_intro(p2, q2, o2);
            lemma_structural_facts_intro(p3, q3, o3);
            lemma_structural_facts_intro(p4, q4, o4);
            lemma_structural_facts_intro(p5, q5, o5);
            lemma_structural_facts_intro(p6, q6, o6);
            lemma_structural_facts_intro(p7, q7, o7);
            lemma_structural_facts_intro(p8, q8, o8);

            assert forall|i: int|
                0 <= i < self.list1.ptrs@.len()
                implies
                    self.list1.wf_node(self.perms@, i)
                    && self.list2.wf_node(self.perms@, i)
            by { }

            assert forall|j: int|
                self.list1.ptrs@.len() <= j < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, j)
            by { }
        }
    }

    /// Scale = 10 ptrs.
    pub fn port_coupled_forall_10(
        &mut self,
        p1: *mut BlockHdr, q1: *mut BlockHdr, o1: int,
        p2: *mut BlockHdr, q2: *mut BlockHdr, o2: int,
        p3: *mut BlockHdr, q3: *mut BlockHdr, o3: int,
        p4: *mut BlockHdr, q4: *mut BlockHdr, o4: int,
        p5: *mut BlockHdr, q5: *mut BlockHdr, o5: int,
        p6: *mut BlockHdr, q6: *mut BlockHdr, o6: int,
        p7: *mut BlockHdr, q7: *mut BlockHdr, o7: int,
        p8: *mut BlockHdr, q8: *mut BlockHdr, o8: int,
        p9: *mut BlockHdr, q9: *mut BlockHdr, o9: int,
        p10: *mut BlockHdr, q10: *mut BlockHdr, o10: int,
    )
        requires
            old(self).wf(),
            old(self).list1.ptrs@.len() <= old(self).list2.ptrs@.len(),
            old(self).list1.ptrs@.contains(p1), old(self).list2.ptrs@.contains(p1),
            old(self).list1.ptrs@.contains(p2), old(self).list2.ptrs@.contains(p2),
            old(self).list1.ptrs@.contains(p3), old(self).list2.ptrs@.contains(p3),
            old(self).list1.ptrs@.contains(p4), old(self).list2.ptrs@.contains(p4),
            old(self).list1.ptrs@.contains(p5), old(self).list2.ptrs@.contains(p5),
            old(self).list1.ptrs@.contains(p6), old(self).list2.ptrs@.contains(p6),
            old(self).list1.ptrs@.contains(p7), old(self).list2.ptrs@.contains(p7),
            old(self).list1.ptrs@.contains(p8), old(self).list2.ptrs@.contains(p8),
            old(self).list1.ptrs@.contains(p9), old(self).list2.ptrs@.contains(p9),
            old(self).list1.ptrs@.contains(p10), old(self).list2.ptrs@.contains(p10),
            q1@.addr == p1@.addr + o1, q1@.provenance == p1@.provenance,
            q2@.addr == p2@.addr + o2, q2@.provenance == p2@.provenance,
            q3@.addr == p3@.addr + o3, q3@.provenance == p3@.provenance,
            q4@.addr == p4@.addr + o4, q4@.provenance == p4@.provenance,
            q5@.addr == p5@.addr + o5, q5@.provenance == p5@.provenance,
            q6@.addr == p6@.addr + o6, q6@.provenance == p6@.provenance,
            q7@.addr == p7@.addr + o7, q7@.provenance == p7@.provenance,
            q8@.addr == p8@.addr + o8, q8@.provenance == p8@.provenance,
            q9@.addr == p9@.addr + o9, q9@.provenance == p9@.provenance,
            q10@.addr == p10@.addr + o10, q10@.provenance == p10@.provenance,
        ensures self.wf(),
    {
        proof {
            lemma_structural_facts_intro(p1, q1, o1);
            lemma_structural_facts_intro(p2, q2, o2);
            lemma_structural_facts_intro(p3, q3, o3);
            lemma_structural_facts_intro(p4, q4, o4);
            lemma_structural_facts_intro(p5, q5, o5);
            lemma_structural_facts_intro(p6, q6, o6);
            lemma_structural_facts_intro(p7, q7, o7);
            lemma_structural_facts_intro(p8, q8, o8);
            lemma_structural_facts_intro(p9, q9, o9);
            lemma_structural_facts_intro(p10, q10, o10);

            assert forall|i: int|
                0 <= i < self.list1.ptrs@.len()
                implies
                    self.list1.wf_node(self.perms@, i)
                    && self.list2.wf_node(self.perms@, i)
            by { }

            assert forall|j: int|
                self.list1.ptrs@.len() <= j < self.list2.ptrs@.len()
                implies self.list2.wf_node(self.perms@, j)
            by { }
        }
    }
}

} // verus!
