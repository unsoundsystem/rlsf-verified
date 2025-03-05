use vstd::prelude::*;
use crate::FreeBlockHdr;
use vstd::raw_ptr::{MemContents, PointsTo, PointsToRaw};

verus! {
    pub struct GhostFreeList {
        perms: Tracked<Map<*mut FreeBlockHdr, PointsTo<FreeBlockHdr>>>,
        ptrs: Ghost<Seq<*mut FreeBlockHdr>>,
    }

    impl GhostFreeList {

        pub closed spec fn wf(self) -> bool {
            &&& forall |i: int| 0 <= i && i < self.ptrs@.len()
                ==> #[trigger] self.wf_node(i)
                &&& self.ptrs@.no_duplicates()
        }

        spec fn next_of(self, i: int) -> Option<*mut FreeBlockHdr>
            recommends 0 <= i < self.ptrs@.len() - 1
        {
            if i + 1 == self.ptrs@.len() {
                None
            } else {
                Some(self.ptrs@[i + 1])
            }
        }

        spec fn prev_of(self, i: int) -> Option<*mut FreeBlockHdr> {
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
            // NOTE: following condition states two,
            // * if ptrs[i] exists then perms[ptrs[i]] is present
            // * moreover, domain of PointsTo<FreeBlockHdr> in perms[ptrs[i]] is
            //   the pointer contained in ptrs[i]
            &&& self.ptrs@[i] == self.perms@[self.ptrs@[i]].ptr()
            // header must be initialized
            &&& self.perms@[node_addr].opt_value() matches MemContents::Init(node)
                // just asserting that the addresses are same i.e. except provenance etc.
                && (node.next_free matches Some(ptr) ==> self.next_of(i) == Some(ptr))
                && (node.next_free == <Option<*mut FreeBlockHdr>>::None ==> self.next_of(i) == <Option<*mut FreeBlockHdr>>::None)
                && (node.prev_free matches Some(ptr) ==> self.prev_of(i) == Some(ptr))
                && (node.prev_free == <Option<*mut FreeBlockHdr>>::None ==> self.prev_of(i) == <Option<*mut FreeBlockHdr>>::None)
                // TODO: assert that free block has approprate region by e.g. PointsToRaw
        }
    }
}
