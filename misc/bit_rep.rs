use vstd::arithmetic::power::pow;
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::relations::injective;

verus! {
macro_rules! nth_bit_macro {
    ($a:expr, $b:expr) => {{
        (0x1 & ($a >> $b)) == 1
    }};
}

macro_rules! nth_bit {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(nth_bit_macro!($($a)*))
    }
}

    trait AsBoolSeq<const W: u32>: core::ops::Shr<Output = Self> + core::ops::BitAnd<Self> {
        spec fn wf(&self) -> bool {
            self.as_seq().len() == W
        }

        spec fn as_seq(self) -> Seq<bool>;

        proof fn as_seq_ensures(self)
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

        proof fn as_seq_ensures(self)
            ensures AsBoolSeq::wf(&self)
        {
        }

    }

    impl AsInteger<{ u64::BITS }> for u64 {
        spec fn as_int(self) -> int {
            self as int
        }
        proof fn as_int_ensures(self)
            ensures AsInteger::wf(&self)
        {
            assert(self.as_int() <= u64::MAX);
            reveal(pow2);
            reveal(pow);
            assert(u64::MAX < pow2(u64::BITS as nat)) by (compute);
        }
    }

    proof fn lemma_nth_bit_list<const W: u32, B: AsBoolSeq<W>>(x: B, n: u32)
        requires x.wf(), nth_bit!(x, n), 0 <= n < W
        ensures 0 <= n < x.as_seq().len(), x.as_seq()[n]
    {
    }




}
