use vstd::prelude::*;

verus! {
    proof fn chain(x: int,
        p0: spec_fn(int) -> bool,
        p1: spec_fn(int) -> bool,
        p2: spec_fn(int) -> bool,
        p3: spec_fn(int) -> bool,
        p4: spec_fn(int) -> bool,
        p5: spec_fn(int) -> bool,
        p6: spec_fn(int) -> bool,
        p7: spec_fn(int) -> bool,
        p8: spec_fn(int) -> bool,
        p9: spec_fn(int) -> bool,
        p10: spec_fn(int) -> bool,
        p11: spec_fn(int) -> bool,
        p12: spec_fn(int) -> bool,
        p13: spec_fn(int) -> bool,
        p14: spec_fn(int) -> bool,
        p15: spec_fn(int) -> bool,
        p16: spec_fn(int) -> bool,
        )
        requires
            forall|i: int| p0(i) ==> #[trigger] p1(i),
            forall|i: int| p1(i) ==> #[trigger] p2(i),
            forall|i: int| p2(i) ==> #[trigger] p3(i),
            forall|i: int| p3(i) ==> #[trigger] p4(i),
            forall|i: int| p4(i) ==> #[trigger] p5(i),
            forall|i: int| p5(i) ==> #[trigger] p6(i),
            forall|i: int| p6(i) ==> #[trigger] p7(i),
            forall|i: int| p7(i) ==> #[trigger] p8(i),
            forall|i: int| p8(i) ==> #[trigger] p9(i),
            forall|i: int| p9(i) ==> #[trigger] p10(i),
            forall|i: int| p10(i) ==> #[trigger] p11(i),
            forall|i: int| p11(i) ==> #[trigger] p12(i),
            forall|i: int| p12(i) ==> #[trigger] p13(i),
            forall|i: int| p13(i) ==> #[trigger] p14(i),
            forall|i: int| p14(i) ==> #[trigger] p15(i),
            forall|i: int| p15(i) ==> #[trigger] p16(i),
        ensures
            p0(x) ==> p16(x)
    {}
}
