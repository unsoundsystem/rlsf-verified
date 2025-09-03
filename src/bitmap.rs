use vstd::prelude::*;

verus! {

use crate::{
    Tlsf, GRANULARITY
};
use crate::bits::nth_bit;
use crate::block_index::BlockIndex;

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {
    #[inline(always)]
    pub fn set_bit_for_index(&mut self, idx: BlockIndex<FLLEN, SLLEN>)
        requires old(self).wf(), idx.wf(),
        ensures ({ let BlockIndex(fl, sl) = idx;
                &&& self.fl_bitmap == (old(self).fl_bitmap | (1usize << fl as int))
                &&& self.sl_bitmap[fl as int] == (old(self).sl_bitmap[fl as int] | (1usize << sl as int))
                &&& self.wf() })
                // NOTE: this function should be used to fix the inconsistency bitween
                //       freelist & bitmaps (thus the postcondition)

    {
        let BlockIndex(fl, sl) = idx;
        self.fl_bitmap = self.fl_bitmap | (1usize << fl);
        // TODO: Confirm that this workaround not needed anymore
        //let tmp = self.sl_bitmap[fl] | (1usize << sl);
        //self.sl_bitmap.set(fl, tmp);
        self.sl_bitmap[fl] = self.sl_bitmap[fl] | (1usize << sl);
    }

    #[inline(always)]
    pub fn clear_bit_for_index(&mut self, idx: BlockIndex<FLLEN, SLLEN>)
        requires old(self).wf(), idx.wf()
        ensures ({ let BlockIndex(fl, sl) = idx;
                &&& self.sl_bitmap[fl as int]
                    == (old(self).sl_bitmap[fl as int] ^ (1usize << sl as int))
                &&& self.wf() })
                // NOTE: this function should be used to fix the inconsistency bitween
                //       freelist & bitmaps (thus the postcondition)
    {}

    pub closed spec fn bitmap_wf(&self) -> bool {
        // TODO: state that self.fl_bitmap[0..GRANULARITY_LOG2] is zero?

        // `sl_bitmap[fl].get_bit(sl)` is set iff `first_free[fl][sl].is_some()`
        &&& forall|idx: BlockIndex<FLLEN, SLLEN>|  idx.wf() ==>
            nth_bit(self.sl_bitmap[idx.0 as int], idx.1 as usize)
                <==> !self.first_free[idx.0 as int][idx.1 as int].is_empty()
        // state *inner bitmap consistency*
        //      fl_bitmap[i] == fold(true, |j,k| fl_bitmap[i][j] || fl_bitmap[i][k])
        &&& forall|idx: BlockIndex<FLLEN, SLLEN>|  idx.wf() &&
                self.sl_bitmap[idx.0 as int] == 0 ==> !(nth_bit(self.fl_bitmap, idx.0))
    }

}
}
