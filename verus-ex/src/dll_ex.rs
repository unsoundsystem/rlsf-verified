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
    // TODO: add more information about managed region to perms
    perms: Tracked<Map<int /* addr */, PointsTo<Node>>>,
    ptrs: Seq<int> // node addrs ordered by list order
}

struct Node {
    next: Option<*mut Node>,
    prev: Option<*mut Node>
}

global layout Node is size == 32, align == 8;


pub proof fn size_of_node()
    ensures size_of::<Node>() == 32
        && align_of::<Node>() == 8
{
}


impl GhostDLL {
    spec fn wf(self) -> bool {
        forall |i: int| 0 <= i && i < self.ptrs.len()
            ==> #[trigger] self.wf_node(i) &&
        ({
            let node_addr = self.ptrs[i];
            node_addr == self.perms@[node_addr].ptr() as usize as int
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
        &&& self.perms@.contains_key(node_addr)
        // header must be initialized
        &&& self.perms@[node_addr].opt_value() matches MemContents::Init(node)
            // just asserting that the addresses are same i.e. except provenance etc.
            && (node.next matches Some(ptr) ==> self.next_of(i) == Some(ptr as usize as int))
            && (node.next == <Option<*mut Node>>::None ==> self.next_of(i) == <Option<int>>::None)
            && (node.prev matches Some(ptr) ==> self.prev_of(i) == Some(ptr as usize as int))
            && (node.prev == <Option<*mut Node>>::None ==> self.prev_of(i) == <Option<int>>::None)
            // TODO: assert that free block has approprate region by e.g. PointsToRaw
    }

    spec fn wf_node_ptr(self, p: *mut Node) -> bool {
        let node_addr = p as usize as int;
        exists|i: int| 0 <= i < self.ptrs.len()
            && self.ptrs[i] == p as usize as int && self.wf_node(i)
    }

    spec fn is_next_ptr_of(self, n1: *mut Node, n2: *mut Node) -> bool
        recommends
            self.wf_node_ptr(n1),
            self.wf_node_ptr(n2),
    {
        let n1_idx = choose|i: int| self.ptrs[i] == n1 as usize as int && self.wf_node(i);
        let n2_idx = choose|i: int| self.ptrs[i] == n2 as usize as int && self.wf_node(i);

        &&& Some(n2_idx) == self.next_of(n1_idx)
        &&& Some(n1_idx) == self.prev_of(n2_idx)
    }

    proof fn contains_key_if_wf_node_ptr(self, n: *mut Node)
        requires self.wf_node_ptr(n)
        ensures self.perms@.contains_key(n as usize as int)
    {}

    fn insert(&mut self, n1: *mut Node, n2: *mut Node, new_node: *mut Node,
                Tracked(perm_new_node): Tracked<PointsToRaw>)
        requires ({
            let perm_n1 = old(self).perms@[n1 as usize as int];
            let perm_n2 = old(self).perms@[n2 as usize as int];
            &&& old(self).wf()
            &&& old(self).wf_node_ptr(n1)
            &&& old(self).wf_node_ptr(n2)
            &&& old(self).is_next_ptr_of(n1, n2)
            &&& n1 != n2 && n1 != new_node && n2 != new_node
            &&& n1@.provenance == perm_n1.ptr()@.provenance
            &&& n2@.provenance == perm_n2.ptr()@.provenance
            //&&& new_node@.provenance == perm_new_node.ptr()@.provenance
        })
        ensures self.wf(),
            self.wf_node_ptr(n1),
            self.wf_node_ptr(n2),
            self.wf_node_ptr(new_node),
            self.is_next_ptr_of(n1, new_node),
            self.is_next_ptr_of(new_node, n2)
    {
        proof {
            assert(self.perms@.contains_key(n1 as usize as int));
            assert(self.perms@.contains_key(n2 as usize as int));
            assert(n1 != n2);
        }
        let tracked mut perm_n1 = self.perms.borrow_mut().tracked_remove(n1 as usize as int);
        let tracked mut perm_n2 = self.perms.borrow_mut().tracked_remove(n2 as usize as int);

        let tracked perm_new_node = perm_new_node.into_typed::<Node>(new_node.addr());
        //// n1 <-> new_node
        {
            let n1_prev = {
                ptr_mut_read(n1, Tracked(&mut perm_n1)).prev
            };
            let new_node_next = {
                ptr_mut_read(new_node, Tracked(&mut perm_new_node)).next
            };
            ptr_mut_write(n1, Tracked(&mut perm_n1), Node { prev: n1_prev, next: Some(new_node) });
            ptr_mut_write(new_node, Tracked(&mut perm_new_node), Node { prev: Some(n1), next: new_node_next });
        }

        //// new_node <-> n2
        {
            let new_node_prev = {
                ptr_mut_read(new_node, Tracked(&mut perm_new_node)).prev
            };
            let n2_prev = {
                ptr_mut_read(n2, Tracked(&mut perm_n2)).next
            };
            ptr_mut_write(n2, Tracked(&mut perm_n1), Node { prev: Some(new_node), next: n2_prev });
            ptr_mut_write(new_node, Tracked(&mut perm_new_node), Node { prev: new_node_prev, next: Some(n2) });
        }
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
