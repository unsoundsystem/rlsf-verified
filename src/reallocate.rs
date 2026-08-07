use vstd::prelude::*;

use crate::bits::*;
use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::{logarithm::log, power::pow, power2::pow2};
use vstd::calc_macro::calc;
#[cfg(verus_keep_ghost)]
use vstd::pervasive::arbitrary;
use vstd::pervasive::*;
use vstd::raw_ptr::{
    expose_provenance, ptr_mut_write, ptr_ref, with_exposed_provenance, IsExposed, Metadata,
    PointsTo, PointsToRaw, Provenance,
};
#[cfg(verus_keep_ghost)]
use vstd::raw_ptr::{ptr_from_data, PtrData};
#[cfg(verus_keep_ghost)]
use vstd::set_lib::set_int_range;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::u64_trailing_zeros;
use vstd::{bytes::*, seq::*, seq_lib::*};
//#[cfg(verus_keep_ghost)]
//use crate::bits::bit_scan_forward;
use crate::block_index::BlockIndex;
//use crate::rational_numbers::{Rational, rational_number_facts, rational_number_properties};
use core::hint::unreachable_unchecked;
use vstd::array::*;
//use ghost_tlsf::{UsedInfo, Block, BlockPerm};
use crate::all_blocks::*;
use crate::block::*;
use crate::ordered_pointer_list::*;
use crate::parameters::*;
use crate::unverified_api::*;
use crate::*;
use core::ptr::null;

verus! {

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
        pub unsafe fn reallocate(
            &mut self,
            ptr: *mut u8,
            size: usize,
            align: usize,
            new_size: usize,
            perm: Tracked<PointsToRaw>
        ) -> (r: (Option<*mut u8>, PointsToRaw))
            requires
                self.wf(),
                perm@.is_range(ptr as int, size)
            ensures
                r.0 matches Some(p) ==> {
                    // ownership of ptr is left to the allocator
                    // same contents
                    //  - (p as int)..(p + min(size, new_size))
                    //  - (p as int)..(p + size)
                    r.1.is_range(p as int, size)
                },
        {
        }
    }

}
