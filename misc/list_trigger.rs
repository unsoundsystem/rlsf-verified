use vstd::prelude::*;
use vstd::raw_ptr::{expose_provenance, ptr_mut_write, ptr_ref, with_exposed_provenance, PointsTo};

verus! {
    struct ListGroup {
        l1: Ghost<Seq<*mut Val>>,
        l2: Ghost<Seq<*mut Val>>,
        m: Tracked<Map<*mut Val, PointsTo<Val>>>
    }

    impl ListGroup {
        spec fn wf(self) -> bool {
            &&& self.wf_l1()
            &&& self.wf_l2()
            &&& forall|i: int| 0 <= i < self.l1@.len()
                ==> {
                    let k = #[trigger] self.l1@[i];
                    &&& self.m@.contains_key(k)
                    &&& self.l1@[i] == self.m@[k].ptr()
                    &&& self.m@[k].is_init()
                }
            &&& forall|i: int, j: int|
                    0 <= i < self.l1@.len() &&
                    0 <= j < self.l1@.len() && i < j
                ==> (self.l1@[i] as usize) < (self.l1@[j] as usize)
        }

        spec fn wf_l1(self) -> bool {
            forall|i: int| 0 <= i < self.l1@.len()
                ==> self.wf_node_l1(i)
        }
        spec fn wf_l2(self) -> bool {
            &&& self.wf_l1()
            &&& forall|i: int| 0 <= i < self.l2@.len()
                ==> self.wf_node_l2(i)
        }

        spec fn wf_node_l1(self, i: int) -> bool
            recommends 0 <= i < self.l1@.len()
        {
            (self.m@[self.l1@[i]].value().x as usize) % 2 == 0
        }

        spec fn wf_node_l2(self, i: int) -> bool
            recommends 0 <= i < self.l2@.len()
        {
            &&& self.l1@.contains(self.l2@[i])
            &&& (self.m@[self.l2@[i]].value().y as usize) % 3 ==  0
            &&& (self.m@[self.l2@[i]].value().x as usize) % 4 ==  0
        }
        proof fn l1_contains_implies_map_contains(&self, node: *mut Val)
            requires self.wf(), self.l1@.contains(node)
            ensures self.m@.contains_key(node)
        {
            assert(self.wf_l1());
            let i = choose|i: int| node == self.l1@[i];
        }

        fn update(&mut self, node: *mut Val)
            requires
                old(self).wf(),
                old(self).l1@.contains(node)
        {
            let ghost idx_l1 = choose|i: int| 0 <= i < self.l1@.len()
                && self.l1@[i] == node;
            assert(self.wf());
            assert(self.wf_l1());
            assert(self.wf_node_l1(idx_l1));

            // modify list
            let tracked node_perm = self.m.tracked_remove(node);

            let old_x = ptr_ref(node, Tracked(&node_perm)).x;
            let old_y = ptr_ref(node, Tracked(&node_perm)).y;
            let prov  = expose_provenance(old_y);
            assume((old_y as usize) + 3 < usize::MAX);
            let new_y = with_exposed_provenance((old_y as usize) + 3, prov);
            ptr_mut_write(node, Tracked(&mut node_perm), Val {
                x: old_x,
                y: new_y
            });

            proof {
                self.m.tracked_insert(node, node_perm);
            }

            assert forall|i: int| 0 <= i < self.l1.len()
                implies self.wf_node_l1(i) by
            {
                if i == idx_l1 {
                    assert((old_x as usize) % 2 == 0);
                    //assert((new_y as usize) % 3 == 0);
                } else {
                    assert(old(self).wf_node_l1(i))
                }
            }
            assert(self.wf_l1());

            assert forall|i: int| 0 <= i < self.l2.len()
                implies self.wf_node_l2(i) by
            {
                if idx_l1 != i {
                    assert(old(self).wf_node_l2(i));
                }
            }

            assert(self.wf_l2());
        }

        proof fn probe(self)
            requires
                self.wf(),
                self.l1@.len() >= 4,
                forall |i: int, j: int|
                    0 <= i < j < self.l1@.len()
                    ==> (self.l1@[i] as usize) < (self.l1@[j] as usize),
        {
            assert((self.l1@[0] as usize) < self.l1@[1] as usize);
            assert((self.l1@[1] as usize) < self.l1@[2] as usize);
            assert((self.l1@[2] as usize) < self.l1@[3] as usize);
            assert((self.l1@[0] as usize) < self.l1@[3] as usize);
            assert((self.l1@[0] as usize) < self.l1@[2] as usize);
        }
    }

    struct Val {
        x: *mut u8,
        y: *mut u8,
    }

}
