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
    perms: Tracked<Map<*mut Node, PointsTo<Node>>>,
    ptrs: Ghost<Seq<*mut Node>> // node addrs ordered by list order
    // NOTE: first tried using int as ID for each pointer,
    //       but this wasn't work because equality issue when used it with Map
    //       i.e. different pointers not necessarily have distinct addresses.
    //
    //       current approach is,
    //
    //       * all managed region should have same provenance -- propagated from given pool
    //       * we will tweak that provenance won't change e.g. avoid ptr_ref*
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
        forall |i: int| 0 <= i && i < self.ptrs@.len()
            ==> #[trigger] self.wf_node(i) &&
        ({
            let node_addr = self.ptrs@[i];
            // NOTE: following condition states two,
            // * if ptrs[i] exists then perms[ptrs[i]] is present
            // * moreover, PointsTo<Node> in perms[ptrs[i]] is about
            //   the pointer contained in ptrs[i]
            node_addr == self.perms@[node_addr].ptr()
        })
        //TODO: all elements of ptrs[...] are distinct
    }

    spec fn next_of(self, i: int) -> Option<*mut Node> {
        if i + 1 == self.ptrs@.len() {
            None
        } else {
            Some(self.ptrs@[i + 1])
        }
    }

    spec fn prev_of(self, i: int) -> Option<*mut Node> {
        if i == 0 || self.ptrs@.len() <= i - 1 {
            None
        } else {
            Some(self.ptrs@[i-1])
        }
    }

    spec fn wf_node(self, i: int) -> bool {
        let node_addr = self.ptrs@[i];
        &&& 0 <= i < self.ptrs@.len()
        &&& self.perms@.contains_key(node_addr)
        // header must be initialized
        &&& self.perms@[node_addr].opt_value() matches MemContents::Init(node)
            // just asserting that the addresses are same i.e. except provenance etc.
            && (node.next matches Some(ptr) ==> self.next_of(i) == Some(ptr))
            && (node.next == <Option<*mut Node>>::None ==> self.next_of(i) == <Option<*mut Node>>::None)
            && (node.prev matches Some(ptr) ==> self.prev_of(i) == Some(ptr))
            && (node.prev == <Option<*mut Node>>::None ==> self.prev_of(i) == <Option<*mut Node>>::None)
            // TODO: assert that free block has approprate region by e.g. PointsToRaw
    }

    spec fn wf_node_ptr(self, p: *mut Node) -> bool {
        let node_addr = p as usize as int;
        exists|i: int| 0 <= i < self.ptrs@.len()
            && self.ptrs@[i] == p && self.wf_node(i)
    }

    spec fn is_next_ptr_of(self, n1: *mut Node, n2: *mut Node) -> bool
        recommends
            self.wf_node_ptr(n1),
            self.wf_node_ptr(n2),
    {
        let n1_idx = choose|i: int| self.ptrs@[i] == n1 && self.wf_node(i);
        let n2_idx = choose|i: int| self.ptrs@[i] == n2 && self.wf_node(i);

        &&& Some(n2) == self.next_of(n1_idx)
        &&& Some(n1) == self.prev_of(n2_idx)
    }

    proof fn contains_key_if_wf_node_ptr(self, n: *mut Node)
        requires self.wf_node_ptr(n)
        ensures self.perms@.contains_key(n)
    {}

    // TODO: proof
    fn insert(&mut self, n1: *mut Node, n2: *mut Node, new_node: *mut Node,
                Tracked(perm_new_node): Tracked<PointsToRaw>)
        requires
            old(self).wf(),
            old(self).wf_node_ptr(n1),
            old(self).wf_node_ptr(n2),
            old(self).is_next_ptr_of(n1, n2),
            n1.addr() != n2.addr() && n1.addr() != new_node.addr(),
            && n2.addr() != new_node.addr(),
            new_node.addr() % align_of::<Node>() == 0,
            perm_new_node.is_range(new_node.addr() as usize as int, size_of::<Node>() as int),
            n1 == old(self).perms@[n1].ptr(),
            n2 == old(self).perms@[n2].ptr(),
            new_node@.metadata == vstd::raw_ptr::Metadata::Thin,
            new_node@.provenance == perm_new_node.provenance(),
        ensures self.wf(),
            self.wf_node_ptr(n1),
            self.wf_node_ptr(n2),
            self.wf_node_ptr(new_node),
            self.is_next_ptr_of(n1, new_node),
            self.is_next_ptr_of(new_node, n2)
    {
        proof {
            assert(self.perms@.contains_key(n1));
            assert(self.perms@.contains_key(n2));
        }
        let tracked mut perm_n1 = self.perms.borrow_mut().tracked_remove(n1);
        let tracked mut perm_n2 = self.perms.borrow_mut().tracked_remove(n2);

        let tracked perm_new_node = perm_new_node.into_typed::<Node>(new_node.addr());
        assert(perm_new_node@.ptr == new_node);
        //// n1 <-> new_node <-> n2
        {
            let n2_next = {
                ptr_mut_read(n2, Tracked(&mut perm_n2)).next
            };
            let n1_prev = {
                ptr_mut_read(n1, Tracked(&mut perm_n1)).prev
            };
            ptr_mut_write(n1, Tracked(&mut perm_n1), Node { prev: n1_prev, next: Some(new_node) });
            ptr_mut_write(n2, Tracked(&mut perm_n2), Node { prev: Some(new_node), next: n2_next });
            ptr_mut_write(new_node, Tracked(&mut perm_new_node), Node { prev: Some(n1), next: Some(n2) });
        }

        proof {
            self.perms.borrow_mut().tracked_insert(n1, perm_n1);
            self.perms.borrow_mut().tracked_insert(n2, perm_n2);
            self.perms.borrow_mut().tracked_insert(new_node, perm_new_node);

            let n2_idx = choose|i: int| 0 <= i < self.ptrs@.len() && self.ptrs@[i] == n2 && self.wf_node(i);
            self.ptrs@ = self.ptrs@.insert(n2_idx, new_node);

            //assert forall|i: int| 0 <= i < self.ptrs@.len()
                //implies self.ptrs@[i] == self.perms@[self.ptrs@[i]].ptr() by
            //{
                //admit()
                ////assert(self.ptrs@[n2_idx] == self.perms@
            //};

            assert(self.perms@[n1].opt_value() matches MemContents::Init(node) &&
                node.next matches Some(new_node));
            assert(self.perms@[n2].opt_value() matches MemContents::Init(node) &&
                node.prev matches Some(new_node));
            assert(self.perms@[new_node].opt_value() matches MemContents::Init(node) &&
                node.prev matches Some(n1) && node.next matches Some(n2));
            self.ptrs@.insert_ensures(n2_idx, new_node);
            assert(self.next_of(n2_idx) == Some(n2));
            assert(self.wf_node(n2_idx));
        }

    }
}

} // verus!
