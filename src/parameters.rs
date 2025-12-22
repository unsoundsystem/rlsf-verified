use vstd::prelude::*;

verus! {

    use crate::Tlsf;
use vstd::calc_macro::calc;
use vstd::arithmetic::{logarithm::log, power2::pow2, power::pow};
use vstd::std_specs::bits::u64_trailing_zeros;
use crate::bits::{
    lemma_pow2_values,
    lemma_log2_values,
    usize_trailing_zeros, is_power_of_two,
    usize_trailing_zeros_is_log2_when_pow2_given
};



/// Hardcoding the result of `size_of::<usize>()` to use `GRANULARITY` in both spec/exec modes
// the following doesn't work
//pub const GRANULARITY: usize = core::mem::size_of::<usize>() * 4;
//pub const GRANULARITY: usize = vstd::layout::size_of::<usize>() as usize * 4;
#[cfg(target_pointer_width = "64")]
pub const GRANULARITY: usize = 8 * 4;

//pub const GRANULARITY_LOG2: u32 = ex_usize_trailing_zeros(GRANULARITY);

pub const SIZE_USED: usize = 1;
pub const SIZE_SENTINEL: usize = 2;
// FIXME: cannot call function `lib::bits::ex_usize_trailing_zeros` with mode exec
// https://verus-lang.github.io/verus/guide/const.html#specexec-consts
pub spec const SPEC_SIZE_SIZE_MASK: usize =
    !(((1usize << usize_trailing_zeros(GRANULARITY)) as usize - 1usize) as usize);
#[verifier::when_used_as_spec(SPEC_SIZE_SIZE_MASK)]
pub exec const SIZE_SIZE_MASK: usize =  !((1 << GRANULARITY.trailing_zeros()) - 1);


impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    // workaround: verus doesn't support constants definitions in impl.
    //const SLI: u32 = SLLEN.trailing_zeros();
    #[verifier::when_used_as_spec(sli_spec_usize)]
    pub const fn sli() -> (r: u32)
        requires Self::parameter_validity()
        ensures
            r == Self::sli_spec(),
            r == Self::sli_spec_usize()
    {
        proof {
            let i = choose|i: nat| pow2(i) == SLLEN;
            usize_trailing_zeros_is_log2_when_pow2_given(SLLEN, i);

            calc! {
                (==)
                pow2(Self::sli_spec() as nat); {}
                pow2(log(2, SLLEN as int) as nat); {}
                pow2(log(2, pow2(i) as int) as nat); {
                assert(log(2, pow2(i) as int) == i) by {
                    vstd::arithmetic::power2::lemma_pow2(i);
                    vstd::arithmetic::logarithm::lemma_log_pow(2, i);
                };
            }
                pow2(i); {}
                SLLEN as nat;
            }
        }
        SLLEN.trailing_zeros()
    }

    pub open spec fn sli_spec_usize() -> (r: u32) {
        usize_trailing_zeros(SLLEN)
    }

    pub open spec fn sli_spec() -> int {
        log(2, SLLEN as int)
    }

    pub proof fn sli_pow2_is_sllen()
        requires Self::parameter_validity()
        ensures pow2(Self::sli_spec() as nat) == SLLEN
    {
        let i = choose|i: nat| pow2(i) == SLLEN;
        calc! {
            (==)
            pow2(Self::sli_spec() as nat); {}
            pow2(log(2, SLLEN as int) as nat); {}
            pow2(log(2, pow2(i) as int) as nat); {
                assert(log(2, pow2(i) as int) == i) by {
                    vstd::arithmetic::power2::lemma_pow2(i);
                    vstd::arithmetic::logarithm::lemma_log_pow(2, i);
                };
            }
            pow2(i); {}
            SLLEN as nat;
        }
    }

    #[verifier::when_used_as_spec(granularity_log2_spec_usize)]
    pub const fn granularity_log2() -> (r: u32)
        requires
            Self::parameter_validity()
        // is_power_of_two(GRANULARITY as int)
        ensures r == Self::granularity_log2_spec_usize()
                  == Self::granularity_log2_spec()
    {
        proof {
            lemma_pow2_values();
            lemma_log2_values();
            if GRANULARITY == 32 {
                reveal(usize_trailing_zeros);
                reveal(u64_trailing_zeros);
                assert(log(2, GRANULARITY as int) == 5);
                assert(usize_trailing_zeros(32) == 5) by (compute);
            } else if GRANULARITY == 16 {
                reveal(usize_trailing_zeros);
                reveal(u64_trailing_zeros);
                assert(log(2, GRANULARITY as int) == 4);
                assert(usize_trailing_zeros(16) == 4) by (compute);
            }
        }
        GRANULARITY.trailing_zeros()
    }

    pub proof fn granularity_basics()
        requires Self::parameter_validity()
        ensures
            Self::granularity_log2_spec_usize() == Self::granularity_log2_spec(),
            is_power_of_two(GRANULARITY as int),
            GRANULARITY == pow2(Self::granularity_log2_spec() as nat),
            GRANULARITY == 16 ==>
                Self::granularity_log2_spec() == 4
                && SLLEN <= 32,
            GRANULARITY == 32 ==>
                Self::granularity_log2_spec() == 5
                && SLLEN <= 64,

    {
        Self::plat_basics();
        usize_trailing_zeros_is_log2_when_pow2_given(
            GRANULARITY,
            Self::granularity_log2_spec() as nat
        );
    }


    pub open spec fn granularity_log2_spec_usize() -> (r: u32) {
        usize_trailing_zeros(GRANULARITY)
    }

    pub open spec fn granularity_log2_spec() -> int {
        log(2, GRANULARITY as int)
    }

    pub open spec fn parameter_validity() -> bool {
        &&& 0 < FLLEN <= usize::BITS
        &&& 0 < SLLEN <= usize::BITS
            && is_power_of_two(SLLEN as int)
        &&& usize::BITS == 64 ==> GRANULARITY == 32 // 64bit platform
        &&& usize::BITS == 32 ==> GRANULARITY == 16 // 32bit platform
    }

}
}
