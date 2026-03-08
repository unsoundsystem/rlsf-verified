use vstd::prelude::*;
use vstd::pervasive::*;
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
    requires old(self).wf(), old(self).wf_dealloc(Ghost(token))
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
            self.unlink_free_block(next_phys_block, idx);
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
                self.unlink_free_block(prev_phys_block, idx);

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
}

} // verus!
