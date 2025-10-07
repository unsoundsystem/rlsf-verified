use vstd::pcm::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {
    trait Node: Sized {}
    #[verifier::reject_recursive_types(N)]
    struct PartialGraph<T, N: Node> {
        adj_map: Map<N, (T, Seq<N>)>
    }

    impl<T, N: Node> PartialGraph<T, N> {
        spec fn decomp(self, rhs: Self) -> Self
            recommends self.adj_map.dom().disjoint(rhs.adj_map.dom())
        {
            if self.adj_map.dom().disjoint(rhs.adj_map.dom()) {
                Self { adj_map: self.adj_map.union_prefer_right(rhs.adj_map) }
            } else { arbitrary() }
        }

        spec fn is_empty(self) -> bool { self.adj_map.is_empty() }
    }

    spec fn list_pred<T>(seq: Seq<T>, i: *mut T, j: *mut T) -> bool
        decreases seq.len()
    {
        if seq.len() == 0 {
            i == j
        } else {
            exists|k: *mut T| {
                &&& exists|pt: PointsTo<(T, *mut T)>| pt.value() == (seq.first(), k)
                &&& list_pred(seq.drop_first(), k, j)
            }
        }
    }

    spec fn graph_pred<T, N: Node>(pg: PartialGraph<T, N>) -> bool
        decreases pg.adj_map.len()
            when pg.adj_map.dom().finite()
    {
        if pg.is_empty() {
            true
        } else {
            let node = choose|n: N| pg.adj_map.contains_key(n);
            let (contents, adj_seq) = pg.adj_map[node];
            exists|i: *mut N| {
                &&& exists|pt: PointsTo<(T, *mut N)>| pt.value() == (contents, i)
                &&& list_pred(adj_seq, i, vstd::raw_ptr::ptr_null::<N>() as *mut N)
                &&& graph_pred(PartialGraph { adj_map: pg.adj_map.remove(node) })
            }
        }
    }

    proof fn graph_pred_distr<T, N: Node>(pg1: PartialGraph<T, N>, pg2: PartialGraph<T, N>)
        ensures graph_pred(pg1.decomp(pg2)) <==> graph_pred(pg1) && graph_pred(pg2)
    {}

    spec fn dlist<T>(seq: Seq<T>, i_0: *mut T, i_1: *mut T, j_0: *mut T, j_1: *mut T) -> bool
        decreases seq.len()
    {
        if seq.len() == 0 {
            i_0 == i_1 && j_0 == j_1
        } else {
            exists|k: *mut T| {
                &&& exists|pt: PointsTo<(T, *mut T, *mut T)>| pt.value() == (seq.first(), i_0, k)
                &&& dlist(seq.drop_first(), k, i_0, j_0, j_1)
            }
        }
    }
}
