use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {
pub mod llist {
    use vstd::prelude::*;
    use vstd::simple_pptr::*;
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
        pub fn new() -> (ls: Self)
            ensures
            ls.wf(),
            ls@.len() == 0
        {
            Self {
                first: None,
                gs: Tracked(GhostState {
                    ptrs: Seq::empty(),
                    perms: Map::tracked_empty(),
                }),
            }
        }
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
                self@ =~= old(self)@.push(v)
        {
            if let Some(old_first) = self.first {
                proof {
                    //assert(!(old(self)@ =~= Seq::empty()));
                    assert(self.wf_node((self.gs@.ptrs.len() - 1) as nat));
                }
                let (node, Tracked(mut perm)) = PPtr::<Node>::new(Node { next: Some(old_first.clone()) , x: v});
                self.first = Some(node);

                proof {
                    //assert(self.gs@.ptrs.len() != 0);
                    self.gs@.ptrs = self.gs@.ptrs.push(node);
                    self.gs.borrow_mut().perms.tracked_insert((self.gs@.ptrs.len() - 1) as nat, perm);
                    //assert(self.first == Some(self.gs@.ptrs[self.gs@.ptrs.len() - 1]));
                    //assert(self.gs@.perms[(self.gs@.ptrs.len() - 1) as nat].value().x == v);

                    //assert(self.wf_node((self.gs@.ptrs.len() - 2) as nat));
                    //assert(self.wf_node((self.gs@.ptrs.len() - 1) as nat));
                    assert(forall|i: nat| i < self.gs@.ptrs.len() && old(self).wf_node(i)
                        ==> self.wf_node(i));
                    assert forall|i: int| 0 <= i && i  < old(self)@.len()
                        implies old(self)@[i] == self@[i]
                    by {
                        assert(old(self).wf_node(i as nat));  // trigger
                    }

                    //assert(self@.len() == old(self)@.push(v).len());
                    //assert(self@[self@.len() - 1] == perm.value().x);
                    assert(self@ =~= old(self)@.push(v));

                    //assume(!(self.gs@.ptrs.len() == 0) ==> self.first == Some(self.gs@.ptrs.index(self.gs@.ptrs.len() - 1)));
                    //assert(self.wf());
                }
            } else {
                //proof {
                    //assert(self.gs@.ptrs.len() == 0);
                    //assert(old(self)@ =~= Seq::empty());
                //}
                let (node, Tracked(mut perm)) = PPtr::<Node>::new(Node { next: None, x: v });
                self.first = Some(node);
                proof {
                    self.gs@.ptrs = self.gs@.ptrs.push(node);
                    self.gs.borrow_mut().perms.tracked_insert(
                        (self.gs@.ptrs.len() - 1) as nat,
                        perm,
                    );
                    //assert(self.wf_node((self.gs@.ptrs.len() - 1) as nat));
                    //assert(self.wf());
                    //assert(self@ =~= old(self)@.push(v));
                }
            }
        }

        pub fn pop_front(&mut self) -> (r: Option<usize>)
            requires
                old(self).wf()
            ensures
                self.wf(),
                old(self)@.len() == 0 ==> r == None::<usize>,
                old(self)@.len() > 0 ==> r == Some(old(self)@.last())
                    && self@ =~= old(self)@.drop_last()
        {
            if let Some(old_first) = self.first {
                //assert(self.gs@.ptrs.len() > 0);
                //assert(old(self).gs@.ptrs.len() > 0);
                //assert(self@.len() > 0);
                proof {
                    assert(self.wf_node((self.gs@.ptrs.len() - 1) as nat));
                }
                let tracked old_first_perm = self.gs.borrow_mut()
                    .perms.tracked_remove((self.gs@.ptrs.len() - 1) as nat);
                let old_first_node = old_first.into_inner(Tracked(old_first_perm));
                self.first = old_first_node.next;
                proof {
                    //assert(self.gs@.ptrs.drop_last().len() + 1 == old(self).gs@.ptrs.len());
                    self.gs@.ptrs = self.gs@.ptrs.drop_last();
                    //assert(self.gs@.ptrs =~= old(self).gs@.ptrs.drop_last());
                    //assert(self.first.is_none() ==> self@.len() == 0);
                    //assert(self.first.is_some() ==> self.gs@.ptrs.len() != 0);

                    //if self.gs@.ptrs.len() == 0 {
                        //assert(self.wf());
                    //}
                    assert(forall|i: nat|
                        i < self@.len() && old(self).wf_node(i) ==> self.wf_node(i));

                    assert forall|i: int| 0 <= i && i  < self@.len()
                        implies old(self)@[i] == self@[i]
                    by {
                        assert(old(self).wf_node(i as nat));  // trigger
                    }
                    
                }

                //assert(self.gs@.ptrs.len() < old(self).gs@.ptrs.len());
                //assert(self.wf());

                Some(old_first_node.x)
            } else {
                //assert(old(self)@.len() == 0);
                None
            }
        }
    }
}

mod main {
    use super::llist;
    pub fn run() {
        let mut ls = llist::LList::new();
        ls.push_front(1);
        ls.push_front(2);
        ls.push_front(3);

        let x = ls.pop_front();
        let y = ls.pop_front();
        let z = ls.pop_front();
        assert(x == Some(3usize));
        assert(y == Some(2usize));
        assert(z == Some(1usize));
    }
}


fn main() {
    main::run();
}
}
