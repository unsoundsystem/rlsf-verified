use vstd::prelude::*;

verus! {
use vstd::raw_ptr::PointsToRaw;
use std::marker::PhantomData;

pub struct Tlsf<'pool, const FLLEN: usize, const SLLEN: usize> {
    fl_bitmap: usize,
    /// `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
    sl_bitmap: [usize; FLLEN],
    first_free: [[Option<*mut FreeBlockHdr>; SLLEN]; FLLEN],
    _phantom: PhantomData<&'pool ()>,
}

pub const GRANULARITY: usize = core::mem::size_of::<usize>() * 4;

const GRANULARITY_LOG2: u32 = GRANULARITY.trailing_zeros();

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
impl BlockHdr {
    /// Get the next block, assuming it exists.
    ///
    /// # Safety
    ///
    /// `self` must have a next block (it must not be the sentinel block in a
    /// pool).
    #[inline]
    unsafe fn next_phys_block(&self) -> *mut BlockHdr {
        ((self as *const _ as *mut u8).add(self.size & SIZE_SIZE_MASK)).cast()
    }
}

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


impl UsedBlockPad {
    #[inline]
    fn get_for_allocation(ptr: *mut u8) -> *mut Self {
        ptr.cast::<Self>().as_ptr().wrapping_sub(1)
    }
}

const FLLEN: usize = 8;
const SLLEN: usize = 8;
impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    spec fn wf() -> bool {

    }

    pub const fn new() {
        Self {
            fl_bitmap: 0,
            sl_bitmap: 0,
            first_free: [[None; SLLEN]; FLLEN],
            _phantom: PhantomData
        }
    }

    pub fn allocate(&mut self) -> (r: *mut u8) {}
    pub fn insert_block(x: *mut u8, size: usize, Tracked(pointsto): Tracked<PointsToRaw>)
    {}
    pub fn map_ceil(size: usize) -> (r: Option<(usize, usize)>)
        requires Self::valid_block_size(size),
        ensures
            r matches Some(idx) && Self::valid_block_index(idx)
            || r.is_none()
    {
        debug_assert!(size >= GRANULARITY);
        debug_assert!(size % GRANULARITY == 0);
        let mut fl = usize::BITS - GRANULARITY_LOG2 - 1 - size.leading_zeros();

        // The shift amount can be negative, and rotation lets us handle both
        // cases without branching.
        let mut sl = size.rotate_right((fl + GRANULARITY_LOG2).wrapping_sub(Self::SLI));

        // The most significant one of `size` should be now at `sl[SLI]`
        debug_assert!(((sl >> Self::SLI) & 1) == 1);

        // Underflowed digits appear in `sl[SLI + 1..USIZE-BITS]`. They should
        // be rounded up
        sl = (sl & (SLLEN - 1)) + (sl >= (1 << (Self::SLI + 1))) as usize;

        // if sl[SLI] { fl += 1; sl = 0; }
        fl += (sl >> Self::SLI) as u32;

        // `fl` must be in a valid range
        if fl as usize >= FLLEN {
            return None;
        }

        Some((fl as usize, sl & (SLLEN - 1)))
    }

    spec fn valid_block_size(size: usize) -> bool {
        GRANULARITY <= size && size < (1 << FLLEN+GRANULARITY_LOG2)
    }

    spec fn valid_block_index(idx: (usize, usize)) -> bool {
        let (fl, sl) = idx;
        &&& 0 <= fl < FLLEN
        &&& 0 <= sl < SLLEN
    }
    spec fn bitmap_wf(&self) -> bool {
        // `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
        forall|fl: usize, sl: usize|  Self::valid_block_index((fl,sl)) ==>
            self.sl_bitmap[fl].get_bit(sl) <==> self.first_free[fl][sl].is_some()
    }
}
}
