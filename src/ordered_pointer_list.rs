use crate::block::BlockHdr;
use vstd::prelude::*;

verus! {

    pub(crate) open spec fn pointer_leq<T>() -> spec_fn(*mut T, *mut T) -> bool {
        |x: *mut T, y: *mut T| {
            let xi = x as usize as int;
            let yi = y as usize as int;
            xi <= yi
        }
    }

    pub(crate) closed spec fn ghost_pointer_ordered(ls: Seq<*mut BlockHdr>) -> bool {
        forall|i: int, j: int|
            0 <= i < ls.len() && 0 <= j < ls.len() && i < j ==>
                (ls[i] as usize as int) <= (ls[j] as usize as int)
    }

    pub(crate) closed spec fn ptrs_no_duplicates(ls: Seq<*mut BlockHdr>) -> bool {
        ls.no_duplicates()
    }

    pub(crate) proof fn lemma_ptrs_no_duplicates_index_neq(
        ls: Seq<*mut BlockHdr>,
        i: int,
        j: int,
    )
        requires
            ptrs_no_duplicates(ls),
            0 <= i < ls.len(),
            0 <= j < ls.len(),
            i != j,
        ensures
            ls[i] != ls[j],
    {
        reveal(ptrs_no_duplicates);
        assert(ls.no_duplicates());
        assert(ls[i] != ls[j]);
    }

    pub(crate) proof fn lemma_ptrs_no_duplicates_eq_index(
        ls: Seq<*mut BlockHdr>,
        i: int,
        j: int,
    )
        requires
            ptrs_no_duplicates(ls),
            0 <= i < ls.len(),
            0 <= j < ls.len(),
            ls[i] == ls[j],
        ensures
            i == j,
    {
        if i != j {
            lemma_ptrs_no_duplicates_index_neq(ls, i, j);
            assert(false);
        }
    }

    pub(crate) proof fn lemma_ghost_pointer_ordered_index(ls: Seq<*mut BlockHdr>, i: int, j: int)
        requires
            ghost_pointer_ordered(ls),
            0 <= i < ls.len(),
            0 <= j < ls.len(),
            i < j,
        ensures
            (ls[i] as usize as int) <= (ls[j] as usize as int)
    {
        assert(ghost_pointer_ordered(ls));
        assert(0 <= i < ls.len() && 0 <= j < ls.len() && i < j);
    }

    pub(crate) closed spec fn add_ghost_pointer(ls: Seq<*mut BlockHdr>, p: *mut BlockHdr) -> Seq<*mut BlockHdr>
        recommends ghost_pointer_ordered(ls)
        decreases ls.len()
    {
        if ls.len() == 0 {
            seq![p]
        } else {
            if (p as usize as int) <= ls.first() as usize as int {
                seq![p].add(ls)
            } else {
                seq![ls.first()].add(add_ghost_pointer(ls.drop_first(), p))
            }
        }
    }

    pub(crate) proof fn lemma_ghost_pointer_first_is_least(ls: Seq<*mut BlockHdr>)
        requires ghost_pointer_ordered(ls), ls.len() > 0
        ensures ls.all(|e: *mut BlockHdr| (ls.first() as usize as int) <= e as usize as int)
    {
    }

    pub(crate) proof fn lemma_ghost_pointer_add_least(ls: Seq<*mut BlockHdr>, p: *mut BlockHdr)
        requires ghost_pointer_ordered(ls),
            (p as usize as int) <= ls.first() as usize as int
        ensures ghost_pointer_ordered(seq![p].add(ls)),
    {
        if ls.len() > 0 {
            lemma_ghost_pointer_first_is_least(ls);
        }
    }

    pub(crate) proof fn lemma_add_ghost_pointer_ensures(ls: Seq<*mut BlockHdr>, p: *mut BlockHdr)
        requires ghost_pointer_ordered(ls)
        ensures
            ghost_pointer_ordered(add_ghost_pointer(ls, p)),
            add_ghost_pointer(ls, p).contains(p),
            forall|e: *mut BlockHdr| ls.contains(e) ==> add_ghost_pointer(ls, p).contains(e),
        decreases ls.len()
    {
        reveal(add_ghost_pointer);
        if ls.len() > 0 {
            lemma_add_ghost_pointer_ensures(ls.drop_first(), p);
            assert(ls.drop_first().len() < ls.len());
            assert(ghost_pointer_ordered(add_ghost_pointer(ls.drop_first(), p)));
            if (p as usize as int) <= ls.first() as usize as int {
                assert(ghost_pointer_ordered(seq![p, ls.first()].add(ls.drop_first())));
                assert(add_ghost_pointer(ls, p) == seq![p, ls.first()].add(ls.drop_first()));
                assert(seq![p, ls.first()].add(ls.drop_first())[0] == p);
                assert forall|e: *mut BlockHdr| ls.contains(e)
                    implies add_ghost_pointer(ls, p).contains(e)
                by {
                    let i = choose|i: int| 0 <= i < ls.len() && ls[i] == e;
                    assert(seq![p, ls.first()].add(ls.drop_first()) == seq![p].add(ls));
                    lemma_list_add_contains(ls, seq![p], e);
                }
            } else {
                assert((p as usize as int) > ls.first() as usize as int);
                assert(add_ghost_pointer(ls.drop_first(), p).contains(p));
                assert(add_ghost_pointer(ls, p) == seq![ls.first()].add(add_ghost_pointer(ls.drop_first(), p)));
                lemma_list_add_contains(add_ghost_pointer(ls.drop_first(), p), seq![ls.first()], p);
                lemma_ghost_pointer_add_least(add_ghost_pointer(ls.drop_first(), p), ls.first());

                assert(forall|e: *mut BlockHdr| ls.drop_first().contains(e)
                    ==> add_ghost_pointer(ls.drop_first(), p).contains(e));
                assert forall|e: *mut BlockHdr| ls.contains(e)
                    implies add_ghost_pointer(ls, p).contains(e)
                by {
                    let i = choose|i: int| 0 <= i < ls.len() && ls[i] == e;
                    if i > 0 {
                        lemma_drop_first_elements(ls);
                        lemma_list_add_contains(add_ghost_pointer(ls.drop_first(), p),
                            seq![ls.first()], e);
                    } else {
                        assert(i == 0);
                        assert(e == ls[0]);
                        assert(ls[0] == ls.first());
                        assert(add_ghost_pointer(ls, p) == seq![ls.first()].add(add_ghost_pointer(ls.drop_first(), p)));
                        assert(0 <= 0 < add_ghost_pointer(ls, p).len());
                        assert(add_ghost_pointer(ls, p)[0] == ls.first());
                        assert(add_ghost_pointer(ls, p)[0] == e);
                        assert(add_ghost_pointer(ls, p).contains(e));
                    }
                }
            }
        } else {
            assert(add_ghost_pointer(ls, p)[0] == p);
        }
    }

    pub(crate) proof fn lemma_add_ghost_pointer_contains_reverse(
        ls: Seq<*mut BlockHdr>,
        p: *mut BlockHdr,
    )
        requires
            ghost_pointer_ordered(ls),
        ensures
            forall|e: *mut BlockHdr| add_ghost_pointer(ls, p).contains(e)
                ==> e == p || ls.contains(e),
        decreases ls.len()
    {
        reveal(add_ghost_pointer);
        if ls.len() > 0 {
            lemma_add_ghost_pointer_contains_reverse(ls.drop_first(), p);
            if (p as usize as int) <= ls.first() as usize as int {
                assert(add_ghost_pointer(ls, p) == seq![p].add(ls));
                assert forall|e: *mut BlockHdr| add_ghost_pointer(ls, p).contains(e)
                    implies e == p || ls.contains(e)
                by {
                    if add_ghost_pointer(ls, p).contains(e) {
                        let i = choose|i: int| 0 <= i < add_ghost_pointer(ls, p).len()
                            && add_ghost_pointer(ls, p)[i] == e;
                        if i == 0 {
                            assert(add_ghost_pointer(ls, p)[0] == p);
                        } else {
                            assert(add_ghost_pointer(ls, p)[i] == ls[i - 1]);
                            assert(ls.contains(e));
                        }
                    }
                };
            } else {
                assert(add_ghost_pointer(ls, p) == seq![ls.first()].add(add_ghost_pointer(ls.drop_first(), p)));
                assert forall|e: *mut BlockHdr| add_ghost_pointer(ls, p).contains(e)
                    implies e == p || ls.contains(e)
                by {
                    if add_ghost_pointer(ls, p).contains(e) {
                        let i = choose|i: int| 0 <= i < add_ghost_pointer(ls, p).len()
                            && add_ghost_pointer(ls, p)[i] == e;
                        if i == 0 {
                            assert(add_ghost_pointer(ls, p)[0] == ls.first());
                            assert(ls.contains(e));
                        } else {
                            assert(add_ghost_pointer(ls, p)[i] == add_ghost_pointer(ls.drop_first(), p)[i - 1]);
                            assert(add_ghost_pointer(ls.drop_first(), p).contains(e));
                            assert(e == p || ls.drop_first().contains(e));
                            if ls.drop_first().contains(e) {
                                let j = choose|j: int| 0 <= j < ls.drop_first().len()
                                    && ls.drop_first()[j] == e;
                                assert(ls[j + 1] == e);
                                assert(ls.contains(e));
                            }
                        }
                    }
                };
            }
        } else {
            assert(add_ghost_pointer(ls, p) == seq![p]);
            assert forall|e: *mut BlockHdr| add_ghost_pointer(ls, p).contains(e)
                implies e == p || ls.contains(e)
            by {
                if add_ghost_pointer(ls, p).contains(e) {
                    let i = choose|i: int| 0 <= i < add_ghost_pointer(ls, p).len()
                        && add_ghost_pointer(ls, p)[i] == e;
                    assert(i == 0);
                    assert(add_ghost_pointer(ls, p)[0] == p);
                }
            };
        }
    }

    /// When adding to an empty list, the result is [p].
    pub(crate) proof fn lemma_add_ghost_pointer_empty(p: *mut BlockHdr)
        ensures
            add_ghost_pointer(Seq::empty(), p).len() == 1,
            add_ghost_pointer(Seq::empty(), p)[0] == p,
    {
        reveal(add_ghost_pointer);
    }

    /// When adding to a single-element list [q] where q < p, result is [q, p].
    pub(crate) proof fn lemma_add_ghost_pointer_append_to_singleton(
        q: *mut BlockHdr, p: *mut BlockHdr)
        requires
            (q as usize as int) < (p as usize as int),
        ensures
            add_ghost_pointer(seq![q], p).len() == 2,
            add_ghost_pointer(seq![q], p)[0] == q,
            add_ghost_pointer(seq![q], p)[1] == p,
    {
        reveal(add_ghost_pointer);
        // After one unfolding: since (p as usize) > (q as usize) = seq![q].first(),
        // result = seq![q].add(add_ghost_pointer(seq![q].drop_first(), p))
        // Need to connect seq![q].drop_first() to Seq::empty()
        assert(seq![q].drop_first() =~= Seq::<*mut BlockHdr>::empty());
        // Now handle the recursive call via the empty lemma
        lemma_add_ghost_pointer_empty(p);
    }

    pub(crate) proof fn lemma_add_ghost_pointer_insert_after_index(
        ls: Seq<*mut BlockHdr>,
        p: *mut BlockHdr,
        ins: int,
    )
        requires
            ghost_pointer_ordered(ls),
            0 <= ins < ls.len(),
            (ls[ins] as usize as int) < (p as usize as int),
            ins + 1 < ls.len() ==> (p as usize as int) <= (ls[ins + 1] as usize as int),
        ensures
            add_ghost_pointer(ls, p).len() == ls.len() + 1,
            forall|k: int| 0 <= k <= ins ==> add_ghost_pointer(ls, p)[k] == ls[k],
            add_ghost_pointer(ls, p)[ins + 1] == p,
            forall|k: int| ins + 1 < k < add_ghost_pointer(ls, p).len()
                ==> add_ghost_pointer(ls, p)[k] == ls[k - 1],
        decreases ls.len()
    {
        reveal(add_ghost_pointer);
        if ls.len() == 1 {
            assert(ins == 0);
            assert(add_ghost_pointer(ls, p) == seq![ls[0], p]);
            assert forall|k: int| 0 <= k <= ins implies add_ghost_pointer(ls, p)[k] == ls[k] by {
                assert(k == 0);
            };
            assert(add_ghost_pointer(ls, p)[ins + 1] == p);
            assert forall|k: int| ins + 1 < k < add_ghost_pointer(ls, p).len()
                implies add_ghost_pointer(ls, p)[k] == ls[k - 1] by {
            };
        } else if ins == 0 {
            assert((ls[0] as usize as int) < (p as usize as int));
            assert((p as usize as int) > (ls.first() as usize as int));
            assert(add_ghost_pointer(ls, p) == seq![ls.first()].add(add_ghost_pointer(ls.drop_first(), p)));
            assert((p as usize as int) <= (ls[1] as usize as int));
            assert((p as usize as int) <= (ls.drop_first().first() as usize as int));
            assert(add_ghost_pointer(ls.drop_first(), p) == seq![p].add(ls.drop_first()));
            assert(add_ghost_pointer(ls, p) == seq![ls[0], p].add(ls.drop_first()));
            assert forall|k: int| 0 <= k <= ins implies add_ghost_pointer(ls, p)[k] == ls[k] by {
                assert(k == 0);
            };
            assert(add_ghost_pointer(ls, p)[ins + 1] == p);
            assert forall|k: int| ins + 1 < k < add_ghost_pointer(ls, p).len()
                implies add_ghost_pointer(ls, p)[k] == ls[k - 1] by {
                assert(1 < k < add_ghost_pointer(ls, p).len());
                assert(add_ghost_pointer(ls, p)[k] == ls.drop_first()[k - 2]);
                assert(ls.drop_first()[k - 2] == ls[k - 1]);
            };
        } else {
            lemma_ghost_pointer_first_is_least(ls);
            assert((ls.first() as usize as int) <= (ls[ins] as usize as int));
            assert((ls.first() as usize as int) < (p as usize as int));
            assert((p as usize as int) > (ls.first() as usize as int));
            assert(add_ghost_pointer(ls, p) == seq![ls.first()].add(add_ghost_pointer(ls.drop_first(), p)));
            assert(0 <= ins - 1 < ls.drop_first().len());
            assert(ls.drop_first()[ins - 1] == ls[ins]);
            if ins < ls.len() - 1 {
                assert((p as usize as int) <= (ls[ins + 1] as usize as int));
                assert((p as usize as int) <= (ls.drop_first()[ins] as usize as int));
            }
            lemma_add_ghost_pointer_insert_after_index(ls.drop_first(), p, ins - 1);
            assert(add_ghost_pointer(ls, p).len() == ls.len() + 1);
            assert forall|k: int| 0 <= k <= ins implies add_ghost_pointer(ls, p)[k] == ls[k] by {
                if k == 0 {
                    assert(add_ghost_pointer(ls, p)[0] == ls[0]);
                } else {
                    assert(0 <= k - 1 <= ins - 1);
                    assert(add_ghost_pointer(ls.drop_first(), p)[k - 1] == ls.drop_first()[k - 1]);
                    assert(add_ghost_pointer(ls, p)[k] == add_ghost_pointer(ls.drop_first(), p)[k - 1]);
                    assert(ls.drop_first()[k - 1] == ls[k]);
                }
            };
            assert(add_ghost_pointer(ls.drop_first(), p)[ins] == p);
            assert(add_ghost_pointer(ls, p)[ins + 1] == p);
            assert forall|k: int| ins + 1 < k < add_ghost_pointer(ls, p).len()
                implies add_ghost_pointer(ls, p)[k] == ls[k - 1] by {
                assert(ins < k - 1 < add_ghost_pointer(ls.drop_first(), p).len());
                assert(add_ghost_pointer(ls.drop_first(), p)[k - 1] == ls.drop_first()[k - 2]);
                assert(add_ghost_pointer(ls, p)[k] == add_ghost_pointer(ls.drop_first(), p)[k - 1]);
                assert(ls.drop_first()[k - 2] == ls[k - 1]);
            };
        }
    }

    pub(crate) proof fn lemma_add_ghost_pointer_insert_point(
        ls: Seq<*mut BlockHdr>,
        p: *mut BlockHdr,
        ins: int,
    )
        requires
            ghost_pointer_ordered(ls),
            0 <= ins < ls.len(),
            (ls[ins] as usize as int) < (p as usize as int),
            ins + 1 < ls.len() ==> (p as usize as int) <= (ls[ins + 1] as usize as int),
        ensures
            add_ghost_pointer(ls, p)[ins + 1] == p,
    {
        lemma_add_ghost_pointer_insert_after_index(ls, p, ins);
        assert(add_ghost_pointer(ls, p)[ins + 1] == p);
    }

    pub(crate) proof fn lemma_add_ghost_pointer_index_map(
        ls: Seq<*mut BlockHdr>,
        p: *mut BlockHdr,
        ins: int,
        i: int,
    )
        requires
            ghost_pointer_ordered(ls),
            0 <= ins < ls.len(),
            (ls[ins] as usize as int) < (p as usize as int),
            ins + 1 < ls.len() ==> (p as usize as int) <= (ls[ins + 1] as usize as int),
            0 <= i < add_ghost_pointer(ls, p).len(),
            i != ins + 1,
        ensures
            i <= ins ==> add_ghost_pointer(ls, p)[i] == ls[i],
            ins + 1 < i ==> add_ghost_pointer(ls, p)[i] == ls[i - 1],
    {
        lemma_add_ghost_pointer_insert_after_index(ls, p, ins);
        if i <= ins {
            assert(0 <= i <= ins);
            assert(add_ghost_pointer(ls, p)[i] == ls[i]);
        } else {
            assert(!(i <= ins));
            assert(ins + 1 < i);
            assert(ins + 1 < i < add_ghost_pointer(ls, p).len());
            assert(add_ghost_pointer(ls, p)[i] == ls[i - 1]);
        }
    }

    pub(crate) proof fn lemma_add_ghost_pointer_contains_old(
        ls: Seq<*mut BlockHdr>,
        p: *mut BlockHdr,
        e: *mut BlockHdr,
    )
        requires
            ghost_pointer_ordered(ls),
            !ls.contains(p),
            add_ghost_pointer(ls, p).contains(e),
            e != p,
        ensures
            ls.contains(e),
    {
        lemma_add_ghost_pointer_contains_reverse(ls, p);
        assert(forall|x: *mut BlockHdr| add_ghost_pointer(ls, p).contains(x)
            ==> x == p || ls.contains(x));
        assert(e == p || ls.contains(e));
        if e == p {
            assert(false);
        }
    }

    proof fn lemma_consecutive_ordering_implies_allpairs(
        ls: Seq<*mut BlockHdr>, i: int, j: int)
        requires
            forall|k: int| 0 <= k < ls.len() - 1
                ==> (#[trigger] (ls[k] as int)) < (ls[k + 1] as int),
            0 <= i < j < ls.len(),
        ensures
            (ls[i] as int) < (ls[j] as int)
        decreases j - i
    {
        if j == i + 1 {
        } else {
            lemma_consecutive_ordering_implies_allpairs(ls, i, j - 1);
        }
    }

    pub(crate) proof fn lemma_ptrs_no_duplicates_from_ordered(ls: Seq<*mut BlockHdr>)
        requires
            forall|i: int|
                0 <= i < ls.len() - 1
                ==> (#[trigger] (ls[i] as int)) < (ls[i + 1] as int)
        ensures
            ptrs_no_duplicates(ls)
    {
        reveal(ptrs_no_duplicates);
        assert forall|i: int, j: int|
            0 <= i < ls.len() && 0 <= j < ls.len() && i != j
            implies ls[i] != ls[j]
        by {
            if i < j {
                lemma_consecutive_ordering_implies_allpairs(ls, i, j);
            } else {
                lemma_consecutive_ordering_implies_allpairs(ls, j, i);
            }
        };
    }

    pub(crate) proof fn lemma_ptrs_no_duplicates_preserved_by_add_ghost_pointer(
        ls: Seq<*mut BlockHdr>,
        p: *mut BlockHdr,
        ins: int,
    )
        requires
            ptrs_no_duplicates(ls),
            ghost_pointer_ordered(ls),
            !ls.contains(p),
            0 <= ins < ls.len(),
            (ls[ins] as usize as int) < (p as usize as int),
            ins + 1 < ls.len() ==> (p as usize as int) <= (ls[ins + 1] as usize as int),
        ensures
            ptrs_no_duplicates(add_ghost_pointer(ls, p))
    {
        reveal(ptrs_no_duplicates);
        lemma_add_ghost_pointer_insert_after_index(ls, p, ins);
        let new_ls = add_ghost_pointer(ls, p);
        assert(new_ls.no_duplicates()) by {
            assert forall|i: int, j: int|
                0 <= i < new_ls.len() && 0 <= j < new_ls.len() && i != j
                implies new_ls[i] != new_ls[j]
            by {
                if i == ins + 1 {
                    // new_ls[ins+1] == p
                    assert(new_ls[ins + 1] == p);
                    // the other element new_ls[j] maps to some ls[k]
                    if j <= ins {
                        assert(new_ls[j] == ls[j]);
                        // ls[j] is in ls, p is not in ls
                        assert(ls.contains(ls[j]));
                        assert(new_ls[i] != new_ls[j]);
                    } else {
                        // j > ins + 1
                        assert(j != ins + 1);
                        assert(ins + 1 < j);
                        assert(new_ls[j] == ls[j - 1]);
                        assert(ls.contains(ls[j - 1]));
                        assert(new_ls[i] != new_ls[j]);
                    }
                } else if j == ins + 1 {
                    // symmetric
                    assert(new_ls[ins + 1] == p);
                    if i <= ins {
                        assert(new_ls[i] == ls[i]);
                        assert(ls.contains(ls[i]));
                        assert(new_ls[i] != new_ls[j]);
                    } else {
                        assert(ins + 1 < i);
                        assert(new_ls[i] == ls[i - 1]);
                        assert(ls.contains(ls[i - 1]));
                        assert(new_ls[i] != new_ls[j]);
                    }
                } else {
                    // both i and j are not ins+1, map back to ls indices
                    let mi = if i <= ins { i } else { i - 1 };
                    let mj = if j <= ins { j } else { j - 1 };
                    assert(new_ls[i] == ls[mi]);
                    assert(new_ls[j] == ls[mj]);
                    assert(mi != mj);
                    lemma_ptrs_no_duplicates_index_neq(ls, mi, mj);
                    assert(ls[mi] != ls[mj]);
                }
            };
        };
    }

    // =========================================
    // remove_ghost_pointer: inverse of add_ghost_pointer
    // =========================================

    /// Removes p from an ordered sequence. Inverse of add_ghost_pointer.
    /// Equivalent to ls.remove(idx) where ls[idx] == p.
    pub(crate) closed spec fn remove_ghost_pointer(
        ls: Seq<*mut BlockHdr>, p: *mut BlockHdr
    ) -> Seq<*mut BlockHdr>
        recommends ghost_pointer_ordered(ls), ls.contains(p)
    {
        let idx = choose|i: int| 0 <= i < ls.len() && ls[i] == p;
        ls.remove(idx)
    }

    pub(crate) proof fn lemma_remove_ghost_pointer_index(
        ls: Seq<*mut BlockHdr>, p: *mut BlockHdr,
    )
        requires
            ghost_pointer_ordered(ls),
            ptrs_no_duplicates(ls),
            ls.contains(p),
        ensures ({
            let idx = choose|i: int| 0 <= i < ls.len() && ls[i] == p;
            &&& 0 <= idx < ls.len()
            &&& ls[idx] == p
            &&& remove_ghost_pointer(ls, p) == ls.remove(idx)
            &&& remove_ghost_pointer(ls, p).len() == ls.len() - 1
        })
    {
        reveal(remove_ghost_pointer);
        let idx = choose|i: int| 0 <= i < ls.len() && ls[i] == p;
        assert(0 <= idx < ls.len());
    }

    pub(crate) proof fn lemma_remove_ghost_pointer_ensures(
        ls: Seq<*mut BlockHdr>, p: *mut BlockHdr,
    )
        requires
            ghost_pointer_ordered(ls),
            ptrs_no_duplicates(ls),
            ls.contains(p),
        ensures
            ghost_pointer_ordered(remove_ghost_pointer(ls, p)),
            !remove_ghost_pointer(ls, p).contains(p),
            remove_ghost_pointer(ls, p).len() == ls.len() - 1,
    {
        reveal(remove_ghost_pointer);
        reveal(ptrs_no_duplicates);
        let idx = choose|i: int| 0 <= i < ls.len() && ls[i] == p;
        let result = ls.remove(idx);

        // Ordered preserved: elements before idx keep their order,
        // elements after idx shift down but keep their relative order
        assert(ghost_pointer_ordered(result)) by {
            reveal(ghost_pointer_ordered);
            assert forall|i: int, j: int|
                0 <= i < result.len() && 0 <= j < result.len() && i < j
                implies (result[i] as usize as int) <= (result[j] as usize as int)
            by {
                let oi = if i < idx { i } else { i + 1 };
                let oj = if j < idx { j } else { j + 1 };
                assert(result[i] == ls[oi]);
                assert(result[j] == ls[oj]);
                assert(oi < oj);
                assert((ls[oi] as usize as int) <= (ls[oj] as usize as int));
            };
        };

        // !contains(p): since ls had no duplicates, removing the one occurrence removes p
        assert(!result.contains(p)) by {
            if result.contains(p) {
                let j = choose|j: int| 0 <= j < result.len() && result[j] == p;
                let oj = if j < idx { j } else { j + 1 };
                assert(ls[oj] == p);
                assert(ls[idx] == p);
                assert(oj != idx);
                assert(ls.no_duplicates());
                assert(false);
            }
        };
    }

    pub(crate) proof fn lemma_remove_ghost_pointer_contains_old(
        ls: Seq<*mut BlockHdr>, p: *mut BlockHdr, e: *mut BlockHdr,
    )
        requires
            ghost_pointer_ordered(ls),
            ptrs_no_duplicates(ls),
            ls.contains(p),
            ls.contains(e),
            e != p,
        ensures
            remove_ghost_pointer(ls, p).contains(e),
    {
        reveal(remove_ghost_pointer);
        let idx = choose|i: int| 0 <= i < ls.len() && ls[i] == p;
        let ei = choose|i: int| 0 <= i < ls.len() && ls[i] == e;
        let result = ls.remove(idx);
        if ei < idx {
            assert(result[ei] == ls[ei]);
            assert(result[ei] == e);
        } else {
            assert(ei != idx);
            assert(ei > idx);
            assert(result[ei - 1] == ls[ei]);
            assert(result[ei - 1] == e);
        }
    }

    pub(crate) proof fn lemma_remove_ghost_pointer_contains_reverse(
        ls: Seq<*mut BlockHdr>, p: *mut BlockHdr, e: *mut BlockHdr,
    )
        requires
            ghost_pointer_ordered(ls),
            ptrs_no_duplicates(ls),
            ls.contains(p),
            remove_ghost_pointer(ls, p).contains(e),
        ensures
            ls.contains(e),
    {
        reveal(remove_ghost_pointer);
        let idx = choose|i: int| 0 <= i < ls.len() && ls[i] == p;
        let result = ls.remove(idx);
        let j = choose|j: int| 0 <= j < result.len() && result[j] == e;
        let oj = if j < idx { j } else { j + 1 };
        assert(ls[oj] == result[j]);
        assert(ls[oj] == e);
    }

    pub(crate) proof fn lemma_remove_ghost_pointer_index_map(
        ls: Seq<*mut BlockHdr>, p: *mut BlockHdr, i: int,
    )
        requires
            ghost_pointer_ordered(ls),
            ptrs_no_duplicates(ls),
            ls.contains(p),
            0 <= i < remove_ghost_pointer(ls, p).len(),
        ensures ({
            let idx = choose|j: int| 0 <= j < ls.len() && ls[j] == p;
            &&& i < idx ==> remove_ghost_pointer(ls, p)[i] == ls[i]
            &&& i >= idx ==> remove_ghost_pointer(ls, p)[i] == ls[i + 1]
        })
    {
        reveal(remove_ghost_pointer);
        let idx = choose|j: int| 0 <= j < ls.len() && ls[j] == p;
        let result = ls.remove(idx);
        if i < idx {
            assert(result[i] == ls[i]);
        } else {
            assert(result[i] == ls[i + 1]);
        }
    }

    pub(crate) proof fn lemma_remove_ghost_pointer_insert_point(
        ls: Seq<*mut BlockHdr>, p: *mut BlockHdr,
    )
        requires
            ghost_pointer_ordered(ls),
            ptrs_no_duplicates(ls),
            ls.contains(p),
        ensures ({
            let idx = choose|j: int| 0 <= j < ls.len() && ls[j] == p;
            &&& 0 <= idx < ls.len()
            &&& ls[idx] == p
        })
    {
        reveal(remove_ghost_pointer);
    }

    pub(crate) proof fn lemma_ptrs_no_duplicates_preserved_by_remove(
        ls: Seq<*mut BlockHdr>, p: *mut BlockHdr,
    )
        requires
            ptrs_no_duplicates(ls),
            ghost_pointer_ordered(ls),
            ls.contains(p),
        ensures
            ptrs_no_duplicates(remove_ghost_pointer(ls, p))
    {
        reveal(ptrs_no_duplicates);
        reveal(remove_ghost_pointer);
        let idx = choose|i: int| 0 <= i < ls.len() && ls[i] == p;
        let result = ls.remove(idx);
        assert(result.no_duplicates()) by {
            assert forall|i: int, j: int|
                0 <= i < result.len() && 0 <= j < result.len() && i != j
                implies result[i] != result[j]
            by {
                let oi = if i < idx { i } else { i + 1 };
                let oj = if j < idx { j } else { j + 1 };
                assert(result[i] == ls[oi]);
                assert(result[j] == ls[oj]);
                assert(oi != oj);
                assert(ls.no_duplicates());
            };
        };
    }

    pub(crate) proof fn lemma_drop_first_elements<T>(x: Seq<T>)
        requires x.len() > 0
        ensures forall|i: int| 0 < i < x.len() ==> x.drop_first().contains(x[i])
    {
        assert forall|i: int| 0 < i < x.len()
            implies x.drop_first().contains(x[i]) by {
                if x.len() == 1 {
                    assert(false);
                } else {
                    assert(x.drop_first()[i - 1] == x[i]);
                }
            }
    }

    pub(crate) proof fn lemma_list_add_contains<T>(x: Seq<T>, y: Seq<T>, e: T)
        requires x.contains(e)
        ensures y.add(x).contains(e)
    {
        assert(forall|i: int| 0 <= i < x.len() ==>
            y.add(x)[i + y.len()] == x[i]);
    }
}
