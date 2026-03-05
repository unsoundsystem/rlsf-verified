use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::relations::injective;

verus! {
    trait AsBoolSeq<const W: u32> {
        spec fn wf(&self) -> bool {
            self.as_seq().len() == W
        }

        spec fn as_seq(self) -> Seq<bool>;
            ensures self.wf();
    }
    trait AsInteger<const W: u32> {
        spec fn wf(&self) -> bool {
            self.as_int() < pow2(W as nat) as int
        }

        spec fn as_int(self) -> int;
        proof fn as_int_ensures(self)
            ensures self.wf();
    }

    impl AsBoolSeq<{ u64::BITS }> for u64 {
        spec fn as_seq(self) -> Seq<bool> {
            Seq::new(u64::BITS as nat, |i: int| self & (1u64 << i) == 1)
        }
    }

    impl AsInteger<{ u64::BITS }> for u64 {
        spec fn as_int(self) -> int {
            self as int
        }
    }
}
