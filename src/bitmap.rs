use vstd::prelude::*;

verus! {

#[macro_use]
use crate::*;
use crate::{
    Tlsf, GRANULARITY
};

use crate::block_index::BlockIndex;

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {

    #[verifier::bit_vector]
    pub proof fn lemma_bitmap_or(b: usize, i: usize)
        requires
            0 <= i < usize::BITS,
        ensures
            nth_bit!(b | (1usize << i), i),
            forall|j: usize|
                0 <= j < usize::BITS && i != j ==>
                    nth_bit!(b | (1usize << i), j) == nth_bit!(b, j)
    {}

    #[inline(always)]
    pub fn set_bit_for_index(&mut self, idx: BlockIndex<FLLEN, SLLEN>)
        requires Self::parameter_validity(), idx.wf(), old(self).bitmap_wf()
        ensures self.bitmap_wf(),
            idx matches BlockIndex(fl, sl)
                && nth_bit!(self.sl_bitmap[fl as int], sl)

    {
        let BlockIndex(fl, sl) = idx;
        self.fl_bitmap = self.fl_bitmap | (1usize << fl);
        // TODO: Confirm that this workaround not needed anymore
        //let tmp = self.sl_bitmap[fl] | (1usize << sl);
        //self.sl_bitmap.set(fl, tmp);
        self.sl_bitmap[fl] = self.sl_bitmap[fl] | (1usize << sl);
        proof {
            assert(nth_bit!(self.fl_bitmap, fl)) by {
                Self::lemma_bitmap_or(old(self).fl_bitmap, fl);
            };
            assert(nth_bit!(self.sl_bitmap[fl as int], sl)) by {
                Self::lemma_bitmap_or(old(self).sl_bitmap[fl as int], sl);
            };
            Self::lemma_bitmap_or(old(self).sl_bitmap[fl as int], sl);
            Self::lemma_bitmap_or(old(self).fl_bitmap, fl);
            assert(self.fl_bitmap == old(self).fl_bitmap | (1usize << fl));
            assert(self.sl_bitmap[fl as int] == old(self).sl_bitmap[fl as int] | (1usize << sl));
            //assert(old(self).bitmap_wf());
            //assert(nth_bit!(self.sl_bitmap[fl as int], sl) <==> nth_bit!(self.fl_bitmap, fl));

            //assert(forall|b1: usize, b2: usize, i: usize| 0 <= i < usize::BITS ==>
                //b1 & (1usize << i) == b2 & (1usize << i) ==> b1 == b2) by (bit_vector);
            //assert(forall|b1: usize, b2: usize, i: usize| 0 <= i < usize::BITS ==>
                //b1 & (1usize << i) != 0 && b2 & (1usize << i) != 0
                //==>  b1 & (1usize << i) == b2 & (1usize << i)) by (bit_vector);
            //assert(forall|b1: usize, b2: usize, i: usize| 0 <= i < usize::BITS ==>
                //nth_bit!(b1, i) == nth_bit!(b2, i) ==> b1 == b2);

            //assert(forall|b: usize, i: usize, j: usize|
                //0 <= i < usize::BITS && 0 <= j < usize::BITS && i != j
                //==> ((b | (1usize << i)) & 1usize << j) == b & 1usize << j) by (bit_vector);
            //assert(forall|b: usize, i: usize, j: usize|
                //0 <= i < usize::BITS && 0 <= j < usize::BITS && i != j
                //==> nth_bit!(b | (1usize << i), j) == nth_bit!(b, j));

            //assert(forall|f: usize|
                //0 <= f < usize::BITS && f != fl
                //==> nth_bit!(self.fl_bitmap, f) == nth_bit!(old(self).fl_bitmap, f));

            //admit()
            assert(old(self).bitmap_wf());
            assert forall|idx: BlockIndex<FLLEN, SLLEN>|
                idx.wf() implies idx matches BlockIndex(f, s) &&
                    (self.sl_bitmap[f as int] == 0 <==> !nth_bit!(self.fl_bitmap, f))
            by {
                let BlockIndex(f, s) = idx;
                if f == fl && s == sl {
                    admit()
                } else {
                    //admit();
                    assert(old(self).bitmap_wf());
                    assert(nth_bit!(self.sl_bitmap[f as int], s) == nth_bit!(old(self).sl_bitmap[f as int], s));
                    assert(nth_bit!(self.fl_bitmap, f) == nth_bit!(old(self).fl_bitmap, f));
                }
            }
        }
    }

    // NOTE: this function should be used to fix the inconsistency bitween
    //       freelist & bitmaps (thus the postcondition)
    #[inline(always)]
    pub fn clear_bit_for_index(&mut self, idx: BlockIndex<FLLEN, SLLEN>)
        requires idx.wf(), old(self).bitmap_wf()
        ensures self.bitmap_wf(),
            idx matches BlockIndex(fl, sl)
                && !nth_bit!(self.sl_bitmap[fl as int], sl)
    {}

    /// State *inner bitmap consistency*
    ///      fl_bitmap[i] == fold(true, |j,k| fl_bitmap[i][j] || fl_bitmap[i][k])
    pub closed spec fn bitmap_wf(&self) -> bool {
        // TODO: state that self.fl_bitmap[0..GRANULARITY_LOG2] is zero?
        forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf() ==>
            (self.sl_bitmap[idx.0 as int] == 0 <==> !(nth_bit!(self.fl_bitmap, idx.0)))
    }

    /// Bitmap kept sync with segregated free lists.
    pub closed spec fn bitmap_sync(self) -> bool {
        forall|idx: BlockIndex<FLLEN, SLLEN>|  idx.wf() ==>
            (nth_bit!(self.sl_bitmap[idx.0 as int], idx.1 as usize)
                <==> !self.first_free[idx.0 as int][idx.1 as int].is_empty())
    }
}
}
