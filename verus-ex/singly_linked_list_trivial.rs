use vstd::prelude::*;
use vstd::simple_pptr::*;
use vstd::assert_by_contradiction;

verus! {
    #[derive(Clone, Copy)]
    struct Node {
        next: Option<PPtr<Node>>,
        x: usize
    }

    impl Node {

    }

    struct LList {
        first: Option<PPtr<Node>>,
        perms: Tracked<Map<nat, PointsTo<Node>>>,
        ptrs: Ghost<Seq<PPtr<Node>>>
    }

    impl LList {
        pub closed spec fn view(&self) -> Seq<usize> {
            Seq::<usize>::new(
                self.ptrs@.len(),
                |i: int| { self.perms@[i as nat].value().x },
            )
        }

        spec fn next_of(&self, i: nat) -> Option<PPtr<Node>> {
            if i + 1 == self.ptrs@.len() {
                None
            } else {
                Some(self.ptrs@[i as int + 1])
            }
        }

        spec fn wf_node(&self, i: nat) -> bool {
            &&& self.perms@.dom().contains(i)
            &&& self.perms@[i].pptr() == self.ptrs@[i as int]
            &&& self.perms@[i].mem_contents() matches MemContents::Init(node)
                  && node.next == self.next_of(i)
        }

        spec fn wf(&self) -> bool {
            &&& forall|i: nat| 0 <= i && i < self.ptrs@.len() ==> self.wf_node(i)
            &&& if self.ptrs@.len() == 0 {
                self.first.is_none()
            } else {
                self.first == Some(self.ptrs@[self.ptrs@.len() - 1])
            }
        }

        fn push_front(&mut self, v: usize)
            requires old(self).wf(),
            ensures
                self.wf(),
                //self@ == old(self)@.push(v),
        {
            let (node, Tracked(mut perm)) = PPtr::<Node>::empty();
            if let Some(old_first) = self.first {
                assert(self.wf_node((self.ptrs@.len() - 1) as nat));
                node.write(Tracked(&mut perm),
                    Node { next: Some(old_first.clone()) , x: v});
            } else {
                proof {
                    assert_by_contradiction!(self.ptrs@.len() == 0,
                        {
                            assert(self.wf_node((self.ptrs@.len() - 1) as nat)); // trigger
                        });
                }
                node.write(Tracked(&mut perm), Node { next: None, x: v });
                self.first = Some(node);
                proof {
                    self.ptrs@ = self.ptrs@.push(node);
                    self.perms.borrow_mut().tracked_insert(
                        0,
                        perm,
                    );
                }
            }
            proof {
                self.perms.borrow_mut().tracked_insert(self.ptrs@.len(), perm);
                self.ptrs@ = self.ptrs@.push(node);
            }

            proof {
                assert(self.wf_node((self.ptrs@.len() - 2) as nat));
                assert(self.wf_node((self.ptrs@.len() - 1) as nat));
                assert(forall|i: nat| i < self.ptrs@.len() && old(self).wf_node(i)
                    ==> self.wf_node(i));
                assert forall|i: int| 0 <= i && i < self.ptrs@.len() as int - 1
                    implies old(self)@[i] == self@[i]
                by {
                    assert(old(self).wf_node(i as nat));  // trigger
                }
                assert(self@ =~= old(self)@.push(v));

                assert(self.wf());
            }
        }
    }

    fn main() {}
}
