use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {
    #[derive(Clone, Copy)]
    struct Node {
        next: Option<PPtr<Node>>,
        prev: Option<PPtr<Node>>
    }

    struct LList {
        first: Option<PPtr<Node>>,
        perms: Tracked<Map<nat, PointsTo<Node>>>,
        ptrs: Ghost<Seq<PPtr<Node>>>
    }

    impl LList {
        fn link(&mut self, node: PPtr<Node>, pointsto_node: Tracked<&mut PointsTo<Node>>) {
            if let Some(old_first_ptr) = self.first {
                let tracked old_first_perm = self.perms.borrow_mut().tracked_remove((self.ptrs@.len() - 1) as nat);
                let old_first = old_first_ptr.read(Tracked(&old_first_perm));
                let old_first_prev = old_first.prev;
                old_first_ptr.write(Tracked(&mut old_first_perm), Node { prev: Some(node.clone()), next: old_first.next });
                node.write(Tracked(pointsto_node.borrow_mut()), Node { prev: None, next: Some(node.clone()) });
            } else {
                // list is empty
                node.write(Tracked(pointsto_node.borrow_mut()), Node { prev: None, next: None });
                self.first = Some(node);
            }
        }
    }

    fn main() {}
}
