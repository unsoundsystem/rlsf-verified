use vstd::prelude::*;

verus! {
mod llist {
    use vstd::prelude::*;
    use vstd::simple_pptr::*;
    #[derive(Clone, Copy)]
    pub struct Node {
        next: Option<PPtr<Node>>,
        x: usize
    }

    pub struct LList {
        first: Option<PPtr<Node>>,
        // すべてのノードへのポインタとトークンを追跡
        gs: Tracked<GhostState>
    }

    pub struct GhostState {
        // 追加時のリストの長さをキーにして各ノードへのポインタのトークンを格納している
        tracked perms: Map<nat, PointsTo<Node>>,
        // 追加された順に各ノードへのポインタが格納されている
        ghost ptrs: Seq<PPtr<Node>>
    }

    impl LList {
        // リンクリストのノードをself.firstから辿っていったときの要素のリストを*逆順にしたもの*
        pub closed spec fn view(&self) -> Seq<usize> {
            // Seqを添字を引数に取るクロージャで生成する
            Seq::<usize>::new(
                self.gs@.ptrs.len(), // 長さ
                // permsはノードの追加時のリストの長さがキーなため､最後に追加した要素が先頭になる
                |i: int| { self.gs@.perms[i as nat].value().x },
            )
        }

        // ノードへのポインタを追跡しているSeqで､与えられた添字から次のノードを返す
        pub closed spec fn next_of(&self, i: nat) -> Option<PPtr<Node>> {
            if i == 0 {
                None
            } else {
                Some(self.gs@.ptrs[i as int - 1])
            }
        }

        // 与えられた添字に対して対応するノードのGhostState内の状態とメモリ上の表現が
        // 整合していることを示す
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
            // 実行の前後で内部構造の整合性が保たれること､
            // viewによる表現が期待通り更新されることを保証する
            requires old(self).wf(),
            ensures
                self.wf(),
                self@ =~= old(self)@.push(v)
        {
            if let Some(old_first) = self.first {
                proof {
                    assert(self.wf_node((self.gs@.ptrs.len() - 1) as nat));
                }
                let (node, Tracked(mut perm)) = PPtr::<Node>::new(Node { next: Some(old_first.clone()) , x: v});
                self.first = Some(node);

                proof {
                    self.gs@.ptrs = self.gs@.ptrs.push(node);
                    self.gs.borrow_mut().perms.tracked_insert((self.gs@.ptrs.len() - 1) as nat, perm);
                    assert(forall|i: nat| i < self.gs@.ptrs.len() && old(self).wf_node(i)
                        ==> self.wf_node(i));
                    assert forall|i: int| 0 <= i && i  < old(self)@.len()
                        implies old(self)@[i] == self@[i]
                    by {
                        assert(old(self).wf_node(i as nat));
                    }
                    assert(self@ =~= old(self)@.push(v));
                }
            } else {
                let (node, Tracked(mut perm)) = PPtr::<Node>::new(Node { next: None, x: v });
                self.first = Some(node);
                proof {
                    self.gs@.ptrs = self.gs@.ptrs.push(node);
                    self.gs.borrow_mut().perms.tracked_insert(
                        (self.gs@.ptrs.len() - 1) as nat,
                        perm,
                    );
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
                assert(self.wf_node((self.gs@.ptrs.len() - 1) as nat));
                let tracked old_first_perm = self.gs.borrow_mut()
                    .perms.tracked_remove((self.gs@.ptrs.len() - 1) as nat);
                let old_first_node = old_first.into_inner(Tracked(old_first_perm));
                self.first = old_first_node.next;
                proof {
                    self.gs@.ptrs = self.gs@.ptrs.drop_last();
                    assert(forall|i: nat|
                        i < self@.len() && old(self).wf_node(i) ==> self.wf_node(i));

                    assert forall|i: int| 0 <= i && i  < self@.len()
                        implies old(self)@[i] == self@[i]
                    by {
                        assert(old(self).wf_node(i as nat));
                    }
                }
                Some(old_first_node.x)
            } else {
                None
            }
        }
    }
    }
}

fn main() {}
}
