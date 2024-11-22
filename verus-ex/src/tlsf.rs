use vstd::prelude::*;

verus! {
use vstd::raw_ptr::PointsToRaw;
use std::marker::PhantomData;
use vstd::std_specs::bits::{u64_trailing_zeros, u64_leading_zeros};
pub struct Tlsf<'pool, const FLLEN: usize, const SLLEN: usize, Bitmap> {
    fl_bitmap: Bitmap,
    /// `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
    sl_bitmap: [Bitmap; FLLEN],
    first_free: [[Option<*mut FreeBlockHdr>; SLLEN]; FLLEN],
    _phantom: PhantomData<&'pool ()>,
}

pub const GRANULARITY: usize = core::mem::size_of::<usize>() * 4;

const GRANULARITY_LOG2: u32 = u64_trailing_zeros(GRANULARITY as u64);

const SIZE_USED: usize = 1;
const SIZE_SENTINEL: usize = 2;
const SIZE_SIZE_MASK: usize = !((1 << GRANULARITY_LOG2) - 1);

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

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN, u64> {
    //const SLI: u32 = SLLEN.trailing_zeros();
    const fn sli() -> u32 { u64_trailing_zeros(SLLEN as u64) }
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

    pub fn map_ceil(size: u64) -> (r: Option<(usize, usize)>)
        requires Self::valid_block_size(size),
        ensures
            r matches Some(idx) && Self::valid_block_index(idx)
            || r.is_none()
    {
        //debug_assert!(size >= GRANULARITY);
        //debug_assert!(size % GRANULARITY == 0);
        let mut fl = usize::BITS - GRANULARITY_LOG2 - 1 - u64_leading_zeros(size);

        // The shift amount can be negative, and rotation lets us handle both
        // cases without branching.
        // negative case can occur when SLLEN > core::mem::size_of::<usize>() * 4
        // (on 64bit platform SLLEN > 32, FIXME: is this unusual case?)
        let mut sl = size.rotate_right((fl + GRANULARITY_LOG2).wrapping_sub(Self::sli()));

        // The most significant one of `size` should be now at `sl[SLI]`
        //debug_assert!(((sl >> Self::sli()) & 1) == 1);

        // Underflowed digits appear in `sl[SLI + 1..USIZE-BITS]`. They should
        // be rounded up
        sl = (sl & (SLLEN as u64 - 1)) + bool_to_usize(sl >= (1 << (Self::sli() + 1)));

        // if sl[SLI] { fl += 1; sl = 0; }
        fl += (sl >> Self::sli()) as u32;

        // `fl` must be in a valid range
        if fl as usize >= FLLEN {
            return None;
        }

        Some((fl as usize, sl & (SLLEN - 1)))
    }

    pub closed spec fn valid_block_size(size: usize) -> bool {
        GRANULARITY <= size && size < (1 << FLLEN+GRANULARITY_LOG2)
    }

    pub closed spec fn valid_block_index(idx: (usize, usize)) -> bool {
        let (fl, sl) = idx;
        &&& 0 <= fl < FLLEN
        &&& 0 <= sl < SLLEN
    }
    spec fn bitmap_wf(&self) -> bool {
        // `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
        forall|fl: usize, sl: usize|  Self::valid_block_index((fl,sl)) ==>
            get_bit(self.sl_bitmap[fl as int], sl)
                <==> self.first_free[fl as int][sl as int].is_some()
    }
}

fn get_bit(x: u64, nth: usize) -> bool
    requires
        nth < usize::BITS
{
    x & (1 << nth) == 1
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
}

