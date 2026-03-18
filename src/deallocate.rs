use vstd::pervasive::*;
use vstd::prelude::*;
use vstd::raw_ptr::{ptr_mut_write, ptr_ref, PointsToRaw};

use crate::block::*;
use crate::*;

verus! {

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    // TODO: refactor use Layout as an argument (external type?)
    // TODO: refactor array access to unchecked operations e.g. arr.get_unchecked_mut(i)
    //#[verifier::external_body] // for spec debug
    pub fn deallocate(&mut self,
        ptr: *mut u8, align: usize,
        Tracked(token): Tracked<DeallocToken>, //NOTE: pattern matching to move out token
        Tracked(points_to): Tracked<PointsToRaw>, // permssion to previously allocated region
    )
    requires old(self).wf(), old(self).wf_dealloc(token)
    ensures self.wf()
    {
        // Safety: `ptr` is a previously allocated memory block with the same
        //         alignment as `align`. This is upheld by the caller.
        let block = unsafe { self.used_block_hdr_for_allocation(ptr, align) };

        let tracked ubh_perm = None.tracked_unwrap();
        unsafe { self.deallocate_block(block, Tracked(ubh_perm)) };
    }

    #[inline]
    //#[verifier::external_body] // debug
    unsafe fn deallocate_block(&mut self, mut block: *mut BlockHdr,
        Tracked(block_perm): Tracked<BlockPerm>) {
        let tracked mut block_perm = block_perm;
        let mut size = ptr_ref(block, Tracked(&block_perm.points_to)).size & !SIZE_USED;
        //debug_assert!((block.as_ref().size & SIZE_USED) != 0);

        // This variable tracks whose `prev_phys_block` we should update.
        let mut new_next_phys_block;
        let tracked mut new_next_phys_block_perm: BlockPerm;

        // Merge the created hole with the next block if the next block is a
        // free block
        // Safety: `block.common` should be fully up-to-date and valid
        let mut next_phys_block = BlockHdr::next_phys_block(block, Tracked(&block_perm));
        let tracked next_phys_block_perm: BlockPerm = {
            let i = choose|i: int| self.all_blocks.ptrs@[i] == block;
            self.all_blocks.perms.borrow_mut()
                .tracked_remove(self.all_blocks.phys_next_of(i).unwrap())
        };
        let next_phys_block_size_and_flags =
            ptr_ref(next_phys_block,
                    Tracked(&next_phys_block_perm.points_to)).size;
        if (next_phys_block_size_and_flags & SIZE_USED) == 0 {
            let next_phys_block_size = next_phys_block_size_and_flags;
            //debug_assert_eq!(
                //next_phys_block_size_and_flags & SIZE_SIZE_MASK,
                //next_phys_block_size
            //);

            // It's coalescable. Add its size to `size`.
            size += next_phys_block_size;

            // Safety: `next_phys_block` is a free block and therefore is not a
            // sentinel block
            new_next_phys_block = BlockHdr::next_phys_block(next_phys_block, Tracked(&next_phys_block_perm));
            proof {
                new_next_phys_block_perm = {
                    let ghost i: int = choose|i: int| self.all_blocks.ptrs@[i] == next_phys_block;
                    self.all_blocks.perms.borrow_mut()
                        .tracked_remove(self.all_blocks.phys_next_of(i).unwrap())
                };
            }

            // Unlink `next_phys_block`.
            let idx = Self::map_floor(next_phys_block_size).unwrap();
            self.unlink_free_block(next_phys_block, idx, Ghost(Set::empty()));
        } else {
            new_next_phys_block = next_phys_block;
            proof {
                new_next_phys_block_perm = next_phys_block_perm;
            }
        }

        // Merge with the previous block if it's a free block.
        if ptr_ref(block, Tracked(&block_perm.points_to)).prev_phys_block.addr() != 0 {
            let prev_phys_block = ptr_ref(block, Tracked(&block_perm.points_to)).prev_phys_block;
            let tracked prev_phys_block_perm = {
                let i = choose|i: int| self.all_blocks.ptrs@[i] == prev_phys_block;
                self.all_blocks.perms.borrow_mut()
                    .tracked_remove(self.all_blocks.phys_prev_of(i).unwrap())
            };
            let prev_phys_block_size_and_flags = ptr_ref(prev_phys_block, Tracked(&prev_phys_block_perm.points_to)).size;

            if (prev_phys_block_size_and_flags & SIZE_USED) == 0 {
                let prev_phys_block_size = prev_phys_block_size_and_flags;
                //debug_assert_eq!(
                    //prev_phys_block_size_and_flags & SIZE_SIZE_MASK,
                    //prev_phys_block_size
                //);

                // It's coalescable. Add its size to `size`.
                size += prev_phys_block_size;

                // Unlink `prev_phys_block`.
                let idx = Self::map_floor(prev_phys_block_size).unwrap();
                self.unlink_free_block(prev_phys_block, idx, Ghost(Set::empty()));

                // Move `block` to where `prev_phys_block` is located. By doing
                // this, `block` will implicitly inherit `prev_phys_block.
                // as_ref().prev_phys_block`.
                block = prev_phys_block;
            }
        }

        // Write the new free block's size and flags.
        //debug_assert!((size & SIZE_USED) == 0);
        let prev_phys_block = ptr_ref(block, Tracked(&block_perm.points_to)).prev_phys_block;
        ptr_mut_write(block, Tracked(&mut block_perm.points_to), BlockHdr {
            size,
            prev_phys_block,
        });

        // Link this free block to the corresponding free list
        let new_block_idx = Self::map_floor(size).unwrap();
        {
            let tracked freelink_perm = block_perm.free_link_perm.tracked_unwrap();

            self.link_free_block(new_block_idx, block);
        }

        // Link `new_next_phys_block.prev_phys_block` to `block`
        //debug_assert_eq!(
            //new_next_phys_block,
            //BlockHdr::next_phys_block(nn_field!(block, common))
        //);
        let new_next_phys_block_size = ptr_ref(new_next_phys_block,
                          Tracked(&new_next_phys_block_perm.points_to)).size;
        ptr_mut_write(new_next_phys_block,
            Tracked(&mut new_next_phys_block_perm.points_to),
            BlockHdr {
                size: new_next_phys_block_size,
                prev_phys_block: block
        });
        //new_next_phys_block.as_mut().prev_phys_block = Some(block.cast());
    }


    /// Validity of blocks being deallocated
    ///
    /// allocated region and headers,
    /// - Must have same provenance with PointsToRaw that we got when called insert_free_block_ptr*
    ///
    ///TODO: Check equlity with `PtrData { ptr: tok.ptr, provenance: /* root provenance */, Thin }`
    /// TODO: formalize assumptions on the header of blocks being deallocated
    ///
    /// Assumption about deallocation
    ///
    /// - Given pointer must be previously allocated one
    ///     - NOTE: In Verus world, it's assured because `deallocate` requires PointsToRaw
    /// - Header of the previously allocated pointer which going to deallocated, must have same size/flags as when it allocated
    ///     (NOTE: header integrity is assumed)
    pub closed spec fn wf_dealloc(&self, tok: DeallocToken) -> bool {
        true
    }

    pub proof fn lemma_wf_dealloc_token(&self)
        ensures
            self.wf_dealloc(DeallocToken),
    {
        assert(self.wf_dealloc(DeallocToken));
    }


    //#[verifier::external_body] //debug
    #[inline]
    unsafe fn used_block_hdr_for_allocation(
        &mut self,
        ptr: *mut u8,
        align: usize,
    ) -> *mut UsedBlockHdr
    {
        if align >= GRANULARITY {
            // Read the header pointer
            //(*UsedBlockPad::get_for_allocation(ptr)).block_hdr
            //TODO: wf_dealloc(.., token) -->
            //      token.pad.ptr() == get_for_allocation(PTR_BEEN_DEALLOCATED)
            //      or in precondition?
            let tracked mut pad_perm: PointsTo<UsedBlockPad> = self.used_info.pad_perms.borrow_mut().tracked_remove(ptr);
            let ptr =
                UsedBlockPad::get_for_allocation(ptr);
            ptr_ref(ptr, Tracked(&pad_perm)).block_hdr
        } else {
            let is_exposed = expose_provenance(ptr);
            let ptr = ptr as usize - (GRANULARITY / 2);
            with_exposed_provenance(ptr, is_exposed)
        }
    }

}

} // verus!
