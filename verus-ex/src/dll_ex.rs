#![feature(strict_provenance)]

use vstd::prelude::*;
use vstd::raw_ptr::*;
verus! {

proof fn ex<T>(tracked p: PointsTo<T>)
    requires p.is_uninit()
{
    let r = Tracked(p.into_raw());
    assert(r@.is_range(p.ptr() as usize as int, vstd::layout::size_of::<T>() as int))
}

struct DLL {
    first: *mut Node
}

use vstd::map::*;

struct GhostDLL {
    perms: Map<int /* addr */, PointsTo<Node>>,
    ptrs: Seq<int> // node addrs ordered by list order
}

struct Node {
    next: Option<*mut Node>,
    prev: Option<*mut Node>
}

impl GhostDLL {
    spec fn wf(self) -> bool {
        forall |i: int| #![trigger self.ptrs[i]] 0 <= i && i < self.ptrs.len() ==> self.wf_node(i) &&
        ({
            let node_addr = self.ptrs[i];
            node_addr == self.perms[node_addr].ptr() as usize as int
        })
    }

    spec fn next_of(self, i: int) -> Option<int> {
        if i + 1 == self.ptrs.len() {
            None
        } else {
            Some(self.ptrs[i + 1])
        }
    }

    spec fn prev_of(self, i: int) -> Option<int> {
        if i == 0 || self.ptrs.len() <= i - 1 {
            None
        } else {
            Some(self.ptrs[i-1])
        }
    }

    spec fn wf_node(self, i: int) -> bool {
        let node_addr = self.ptrs[i];
        &&& self.perms.contains_key(node_addr)
        // header must be initialized
        &&& self.perms[node_addr].opt_value() matches MemContents::Init(node)
            // just asserting that the addresses are same i.e. except provenance etc.
            //&& (self.next_of(i) == node.next.map(|p: *mut Node| p as usize as int))
            && (node.next matches Some(ptr) && self.next_of(i) == Some(ptr as usize as int))
            && (node.next == <Option<*mut Node>>::None && self.next_of(i) == <Option<int>>::None)
            && (node.prev matches Some(ptr) && self.prev_of(i) == Some(ptr as usize as int))
            && (node.prev == <Option<*mut Node>>::None && self.prev_of(i) == <Option<int>>::None)
            // TODO: assert that free block has approprate region by e.g. PointsToRaw
    }

    spec fn wf_node_ptr(self, p: *mut Node) -> bool {
        let node_addr = p as usize as int;
        exists|i: int| self.ptrs[i] == p as usize as int && self.wf_node(i)
    }

    spec fn is_contiguous_nodes(self, n1: *mut Node, n2: *mut Node, n3: *mut Node) -> bool
        recommends
            self.wf_node_ptr(n1),
            self.wf_node_ptr(n2),
            self.wf_node_ptr(n3),
    {
        let n1_idx = choose|i: int| self.ptrs[i] == n1 as usize as int && self.wf_node(i);
        let n2_idx = choose|i: int| self.ptrs[i] == n2 as usize as int && self.wf_node(i);
        let n3_idx = choose|i: int| self.ptrs[i] == n3 as usize as int && self.wf_node(i);

        true
        //&&& self.next_of(n1_idx) == Some(n2_idx) &&
                //self.next_of(n2_idx) == Some(n3_idx)
        //&&& self.prev_of(n3_idx) == Some(n2_idx) &&
                //self.prev_of(n2_idx) == Some(n1_idx)
    }

    fn insert(&mut self, n1: *mut Node, n2: *mut Node, new_node: *mut Node,
                Tracked(perm_n1): Tracked<PointsToRaw>,
                Tracked(perm_new_node): Tracked<PointsToRaw>,
                Tracked(perm_n2): Tracked<PointsToRaw>)
        requires old(self).wf(), old(self).wf_node_ptr(n1), old(self).wf_node_ptr(n2),
                 n1@.provenance == perm_n1.provenance(),
                 new_node@.provenance == perm_new_node.provenance(),
                 n2@.provenance == perm_n2.provenance(),
        ensures self.wf(),
            self.wf_node_ptr(n1),
            self.wf_node_ptr(n2),
            self.wf_node_ptr(new_node),
            self.is_contiguous_nodes(n1, new_node, n2)
    {

        let tracked mut perm_n1 = perm_n1.into_typed::<Node>(n1.addr());
        let tracked mut perm_new_node = perm_new_node.into_typed::<Node>(new_node.addr());
        let tracked mut perm_n2 = perm_n2.into_typed::<Node>(n2.addr());
        assert(false)

        //// n1 <-> new_node
        //{
        //    let n1_prev = {
        //        ptr_mut_read(n1, Tracked(&mut perm_n1)).prev
        //    };
        //    let new_node_next = {
        //        ptr_mut_read(new_node, Tracked(&mut perm_new_node)).next
        //    };
        //    ptr_mut_write(n1, Tracked(&mut perm_n1), Node { prev: n1_prev, next: Some(new_node) });
        //    ptr_mut_write(new_node, Tracked(&mut perm_new_node), Node { prev: Some(n1), next: new_node_next });
        //}

        //// new_node <-> n2
        //{
        //    let new_node_prev = {
        //        ptr_mut_read(new_node, Tracked(&mut perm_new_node)).prev
        //    };
        //    let n2_prev = {
        //        ptr_mut_read(n2, Tracked(&mut perm_n2)).next
        //    };
        //    ptr_mut_write(n2, Tracked(&mut perm_n1), Node { prev: Some(new_node), next: n2_prev });
        //    ptr_mut_write(new_node, Tracked(&mut perm_new_node), Node { prev: new_node_prev, next: Some(n2) });
        //}
        //proof {
        //    // FIXME: ???
        //    //      * reproducing when wf_node_ptr in requires
        //    assert(false)
        //}
    }

    //fn insert_x(&mut self, n1: *mut Node, n2: *mut Node, new_node: *mut Node,
                //Tracked(perm_n1): Tracked<PointsToRaw>,
                //Tracked(perm_new_node): Tracked<PointsToRaw>,
                //Tracked(perm_n2): Tracked<PointsToRaw>)
        //ensures false
    //{
        //let tracked mut perm_n1 = perm_n1.into_typed::<Node>(n1.addr());
        //let tracked mut perm_new_node = perm_new_node.into_typed::<Node>(new_node.addr());
        //let tracked mut perm_n2 = perm_n2.into_typed::<Node>(n2.addr());
    //}
}

} // verus!
