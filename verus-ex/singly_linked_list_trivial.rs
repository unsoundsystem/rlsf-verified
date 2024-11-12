use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {
    #[derive(Clone, Copy)]
    pub struct Node {
        next: Option<PPtr<Node>>,
        x: usize
    }

    pub struct LList {
        first: Option<PPtr<Node>>,
        gs: Tracked<GhostState>
    }

    pub struct GhostState {
        tracked perms: Map<nat, PointsTo<Node>>,
        ghost ptrs: Seq<PPtr<Node>>
    }

    impl LList {
        pub closed spec fn view(&self) -> Seq<usize> {
            Seq::<usize>::new(
                self.gs@.ptrs.len(),
                |i: int| { self.gs@.perms[i as nat].value().x },
            )
        }

        pub closed spec fn next_of(&self, i: nat) -> Option<PPtr<Node>> {
            if i == 0 {
                None
            } else {
                Some(self.gs@.ptrs[i as int - 1])
            }
        }

        pub closed spec fn wf_node(&self, i: nat) -> bool {
            &&& self.gs@.perms.dom().contains(i)
            &&& self.gs@.perms[i].pptr() == self.gs@.ptrs[i as int]
            &&& self.gs@.perms[i].mem_contents() matches MemContents::Init(node)
                  && node.next == self.next_of(i)
        }

        pub closed spec fn wf(&self) -> bool {
            &&& forall|i: nat| 0 <= i && i < self.gs@.ptrs.len() ==> self.wf_node(i)
            &&& if self.gs@.ptrs.len() == 0 {
                self.first.is_none()
            } else {
                self.first == Some(self.gs@.ptrs[self.gs@.ptrs.len() - 1])
            }
        }

        pub fn push_front(&mut self, v: usize)
            requires old(self).wf(),
            ensures
                self.wf(),
                self@ =~= seq![v].add(old(self)@)
        {
            if let Some(old_first) = self.first {
                assert(self.wf_node((self.gs@.ptrs.len() - 1) as nat));
                let (node, Tracked(mut perm)) = PPtr::<Node>::new(Node { next: Some(old_first.clone()) , x: v});
                self.first = Some(node);

                proof {
                    assert(self.gs@.ptrs.len() != 0);
                    self.gs.borrow_mut().perms.tracked_insert(self.gs@.ptrs.len(), perm);
                    self.gs@.ptrs = self.gs@.ptrs.push(node);
                    assert(self.first == Some(self.gs@.ptrs[self.gs@.ptrs.len() - 1]));

                    assert(self.wf_node((self.gs@.ptrs.len() - 2) as nat));
                    assert(self.wf_node((self.gs@.ptrs.len() - 1) as nat));
                    assert(forall|i: nat| i < self.gs@.ptrs.len() && old(self).wf_node(i)
                        ==> self.wf_node(i));
                    assert(self@ =~= seq![v].add(old(self)@));

                    //assume(!(self.gs@.ptrs.len() == 0) ==> self.first == Some(self.gs@.ptrs.index(self.gs@.ptrs.len() - 1)));
                    //assert(self.wf());
                }
            } else {
                proof {
                    assert(self.gs@.ptrs.len() == 0);
                    assert(old(self)@ =~= Seq::empty());
                }
                let (node, Tracked(mut perm)) = PPtr::<Node>::new(Node { next: None, x: v });
                self.first = Some(node);
                proof {
                    self.gs.borrow_mut().perms.tracked_insert(
                        self.gs@.ptrs.len(),
                        perm,
                    );
                    self.gs@.ptrs = self.gs@.ptrs.push(node);
                    assert(self.wf_node((self.gs@.ptrs.len() - 1) as nat));
                    assert(self.wf());
                    assert(self@ =~= seq![v].add(old(self)@));
                }
            }
        }
    }

    fn main() {}
}
