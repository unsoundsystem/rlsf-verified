use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::raw_ptr::ptr_mut_write;

verus! {
    #[derive(Clone, Copy)]
    struct Node {
        next: Option<*mut Node>,
    }

    struct LList {
        first: Option<PPtr<Node>>,
        perms: Tracked<Map<nat, PointsTo<Node>>>,
        ptrs: Ghost<Seq<PPtr<Node>>>
    }

    impl LList {
        fn link(&mut self, node: PPtr<Node>, Tracked(pointsto_node): Tracked<&mut PointsTo<Node>>) {
            if let Some(old_first) = self.first {
                node.write(Tracked(&mut pointsto_node.points_to), Node { next: Some(old_first.clone()) });
            } else {
                node.write(Tracked(&mut pointsto_node), Node { next: None });
                self.first = Some(node);
            }
        }
    }
}
