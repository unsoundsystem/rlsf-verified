use vstd::prelude::*;

verus! {
use vstd::raw_ptr::PointsToRaw;
use std::marker::PhantomData;
use vstd::std_specs::bits::{u64_trailing_zeros, u64_leading_zeros, u32_leading_zeros, u32_trailing_zeros,
    ex_u64_leading_zeros, ex_u64_trailing_zeros, ex_u32_leading_zeros, ex_u32_trailing_zeros};
use vstd::{seq::*, seq_lib::*};
use vstd::arithmetic::logarithm::log;


// for codes being executed
macro_rules! get_bit {
    ($a:expr, $b:expr) => {{
        (0x1usize & ($a >> $b)) == 1
    }};
}

// for spec/proof codes
macro_rules! nth_bit {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bit!($($a)*))
    }
}

pub struct Tlsf<'pool, const FLLEN: usize, const SLLEN: usize> {
    fl_bitmap: usize,
    /// `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
    sl_bitmap: [usize; FLLEN],
    first_free: [[Option<*mut FreeBlockHdr>; SLLEN]; FLLEN],
    _phantom: PhantomData<&'pool ()>,
}

//pub const GRANULARITY: usize = core::mem::size_of::<usize>() * 4;

#[cfg(target_pointer_width = "64")]
global size_of usize == 8;

#[cfg(target_pointer_width = "64")]
pub const GRANULARITY: usize = 8 * 4;

//pub const GRANULARITY_LOG2: u32 = ex_usize_trailing_zeros(GRANULARITY);

//const SIZE_USED: usize = 1;
//const SIZE_SENTINEL: usize = 2;
//const SIZE_SIZE_MASK: usize = !((1 << ex_usize_trailing_zeros(GRANULARITY)) - 1);

struct BlockHdr {
    /// The size of the whole memory block, including the header.
    ///
    ///  - `bit[0]` ([`SIZE_USED`]) indicates whether the block is a used memory
    ///    block or not.
    ///
    ///  - `bit[1]` ([`SIZE_LAST_IN_POOL`]) indicates whether the block is the
    ///    last one of the pool or not.
    ///
    ///  - `bit[GRANULARITY_LOG2..]` ([`SIZE_SIZE_MASK`]) represents the size.
    ///
    size: usize,
    prev_phys_block: Option<*mut BlockHdr>,
}
//impl BlockHdr {
    ///// Get the next block, assuming it exists.
    /////
    ///// # Safety
    /////
    ///// `self` must have a next block (it must not be the sentinel block in a
    ///// pool).
    //#[inline]
    //unsafe fn next_phys_block(&self) -> *mut BlockHdr {
        //((self as *const _ as *mut u8).add(self.size & SIZE_SIZE_MASK)).cast()
    //}
//}

#[repr(C)]
struct UsedBlockHdr {
    common: BlockHdr,
}

#[repr(C)]
struct UsedBlockPad {
    block_hdr: *mut UsedBlockHdr,
}

#[repr(C)]
struct FreeBlockHdr {
    common: BlockHdr,
    next_free: Option<*mut FreeBlockHdr>,
    prev_free: Option<*mut FreeBlockHdr>,
}


//impl UsedBlockPad {
    //#[inline]
    //fn get_for_allocation(ptr: *mut u8) -> *mut Self {
        //ptr.cast::<Self>().wrapping_sub(1)
    //}
//}

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    // workaround: verus doesn't support constants definitions in impl.
    //const SLI: u32 = SLLEN.trailing_zeros();
    const fn sli() -> u32
    { ex_usize_trailing_zeros(SLLEN) }

    const fn granularity_log2() -> (r: u32)
        ensures r == usize_trailing_zeros(GRANULARITY)
    {
        ex_usize_trailing_zeros(GRANULARITY)
    }

    spec fn granularity_log2_spec() -> int {
        usize_trailing_zeros(GRANULARITY)
    }

    spec fn wf() -> bool {
        true
    }

    pub const fn new() -> Self {
        Self {
            fl_bitmap: 0,
            sl_bitmap: [0; FLLEN],
            first_free: [[None; SLLEN]; FLLEN],
            _phantom: PhantomData
        }
    }

    //pub fn allocate(&mut self) -> (r: *mut u8) { unimplemented!() }
    pub fn insert_block(x: *mut u8, size: usize, Tracked(pointsto): Tracked<PointsToRaw>)
    {}

    pub fn map_ceil(size: usize) -> (r: Option<(usize, usize)>)
        requires Self::valid_block_size(size),
        ensures
            r matches Some(idx) && Self::valid_block_index(idx)
            || r.is_none()
    {
        assert(size >= GRANULARITY);
        //assert(size % GRANULARITY == 0);
        assert(usize::BITS == 64);
        assert(GRANULARITY < usize::BITS);
        let mut fl = usize::BITS - Self::granularity_log2() - 1 - ex_usize_leading_zeros(size);
        assert(fl == log(2, size as int) - log(2, GRANULARITY as int)); // TODO

        // The shift amount can be negative, and rotation lets us handle both
        // cases without branching.
        // negative case can occur when SLLEN > core::mem::size_of::<usize>() * 4
        // (on 64bit platform SLLEN > 32, FIXME: is this unusual case?)
        let mut sl = size.rotate_right((fl + Self::granularity_log2()).wrapping_sub(Self::sli()));

        // The most significant one of `size` should be now at `sl[SLI]`
        //debug_assert!(((sl >> Self::sli()) & 1) == 1);

        // Underflowed digits appear in `sl[SLI + 1..USIZE-BITS]`. They should
        // be rounded up
        sl = (sl & (SLLEN - 1)) + bool_to_usize(sl >= (1 << (Self::sli() + 1)));

        // if sl[SLI] { fl += 1; sl = 0; }
        fl += (sl >> Self::sli()) as u32;

        // `fl` must be in a valid range
        if fl as usize >= FLLEN {
            return None;
        }

        Some((fl as usize, sl & (SLLEN - 1)))
    }

    pub closed spec fn valid_block_size(size: usize) -> bool {
        GRANULARITY <= size && size < (1 << FLLEN + Self::granularity_log2_spec())
    }

    pub closed spec fn valid_block_index(idx: (usize, usize)) -> bool {
        let (fl, sl) = idx;
        &&& 0 <= fl < FLLEN
        &&& 0 <= sl < SLLEN
    }
    spec fn bitmap_wf(&self) -> bool {
        // `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
        forall|fl: usize, sl: usize|  Self::valid_block_index((fl,sl)) ==>
            nth_bit!(self.sl_bitmap[fl as int], sl)
                <==> self.first_free[fl as int][sl as int].is_some()
    }
}

#[inline]
#[verifier::external_body]
fn bool_to_usize(b: bool) -> (r: usize)
    ensures
        b ==> r == 1,
        !b ==> r == 0
{
    b as usize
}

// NOTE: vstd's interface returns u32 for u(64|32)_(leading|trailing)_zeros,
//       except for u64_leading_zeros (this returns int).
//       Thus, aligned the return type at int for spec functions here.

#[cfg(target_pointer_width = "32")]
pub open spec fn usize_leading_zeros(x: usize) -> int
{
    u32_leading_zeros(x as u32) as int
}

#[cfg(target_pointer_width = "64")]
pub open spec fn usize_leading_zeros(x: usize) -> int
{
    u64_leading_zeros(x as u64)
}


#[cfg(target_pointer_width = "32")]
pub open spec fn usize_trailing_zeros(x: usize) -> int
{
    u32_trailing_zeros(x as u32) as int
}

#[cfg(target_pointer_width = "64")]
pub open spec fn usize_trailing_zeros(x: usize) -> int
{
    u64_trailing_zeros(x as u64) as int
}


#[cfg(target_pointer_width = "32")]
pub const fn ex_usize_leading_zeros(x: usize) -> (r: u32)
    ensures
        0 <= r <= usize::BITS,
        r == u32_leading_zeros(x as u32)
{
    ex_u32_leading_zeros(x as u32)
}

#[cfg(target_pointer_width = "64")]
pub const fn ex_usize_leading_zeros(x: usize) -> (r: u32)
    ensures
        0 <= r <= usize::BITS,
        r == u64_leading_zeros(x as u64)
{
    //ex_u64_leading_zeros(x as u64)
    (x as u64).leading_zeros()
}


#[cfg(target_pointer_width = "32")]
pub const fn ex_usize_trailing_zeros(x: usize) -> (r: u32)
    ensures
        0 <= r <= usize::BITS,
        r == u32_trailing_zeros(x as u32)
{
    //ex_u32_trailing_zeros(x as u32)
    (x as u32).trailing_zeros()
}

#[cfg(target_pointer_width = "64")]
pub const fn ex_usize_trailing_zeros(x: usize) -> (r: u32)
    ensures
        0 <= r <= usize::BITS,
        r == u64_trailing_zeros(x as u64)
{
    //ex_u64_trailing_zeros(x as u64)
    (x as u64).trailing_zeros()
}
use core::cmp::Ordering;
use builtin::*;
use vstd::math::abs;
/// TODO: External specification for usize::rotate_right
pub open spec fn is_usize_rotate_right(x: usize, r: usize, n: int) -> bool {
    let sa: nat = abs(n) as nat % usize::BITS as nat;
    let sa_ctr: nat = abs(usize::BITS - sa);
    // TODO: justification
    &&& (n == 0) ==> (r == x)
    &&& (n > 0) ==> r == ((x & high_mask(sa)) >> sa | ((x & low_mask(sa)) << (sa_ctr)))
    &&& (n < 0) ==> r == ((x & low_mask(sa_ctr)) << sa | ((x & high_mask(sa_ctr)) >> (sa_ctr)))
}
use vstd::bits::low_bits_mask;
// masks n or higher bits
pub open spec fn high_mask(n: nat) -> usize {
    !(low_bits_mask(n) as usize)
}

pub open spec fn low_mask(n: nat) -> usize {
    low_bits_mask(n) as usize
}

#[verifier::external_fn_specification]
pub fn usize_rotate_right(x: usize, n: u32) -> (r: usize)
    ensures is_usize_rotate_right(x, r, n as int)
{ x.rotate_right(n) }

//pub open spec fn usize_view(x: usize) -> Seq<bool> {
    //Seq::new(8*vstd::layout::size_of::<usize>(), |i: int| nth_bit!(x, i as usize))
//}

//pub open spec fn seq_rotate_right_pos(x: int, bs: Seq<bool>) -> Seq<bool>
    //recommends x > 0
//{
    //let rot = x % bs.len();
    //bs.drop_first(rot).add(bs.subrange(bs.len() - rot, bs.len()))
//}

//pub open spec fn seq_rotate_right_neg(x: int, bs: Seq<bool>) -> Seq<bool>
    //recommends x > 0
//{
    //let rot = x % bs.len();
    //bs.subrange(bs.len() - rot, bs.len()).add(bs.drop(rot))
//}
}

