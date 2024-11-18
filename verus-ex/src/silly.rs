use vstd::prelude::*;

verus! {

spec fn gt_any(x: nat, ls: Seq<nat>) -> bool
{ 
    forall|i: int| 0 <= i && i < ls.len() ==> x >= ls[i]
}

mod X {
    use vstd::prelude::*;
    pub closed spec fn max(x: int, y: int) -> int
    {
        if x <= y {
            y
        } else {
            x
        }

    }

    pub proof fn lemma_max(x: int, y: int) 
    ensures
        max(x, y) >= x,
        max(x, y) >= y,
        max(x, y) == x || max(x, y) == y
    {}
}

fn max(x: usize, y: usize) -> (r: usize)
    ensures
        r == x || r == y,
        r >= x && r >= y
{
    if x <= y {
        y
    } else {
        x
    }
}

struct S { x: usize }

impl S {
    fn safe_inc(&mut self) -> (r: usize)
        requires 0 <= old(self).x, old(self).x < usize::MAX
        ensures r == self.x == old(self).x + 1
    {
        self.x = self.x + 1; self.x
    }
}
fn main() {
    assert(!gt_any(1, seq![1, 2, 3]));
    assert(gt_any(3, seq![1, 2, 3]));

    proof {
        X::lemma_max(1, 2);
        X::lemma_max(100, 200);
    }
    assert(X::max(1, 2) == 2);
    assert(X::max(100, 200) == 200);
}
}
