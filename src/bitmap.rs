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
            assert(old(self).bitmap_wf());

            assert forall|idx: BlockIndex<FLLEN, SLLEN>|
                idx.wf() implies idx matches BlockIndex(f, s) &&
                    (self.sl_bitmap[f as int] == 0 <==> !nth_bit!(self.fl_bitmap, f))
            by {
                let BlockIndex(f, s) = idx;
                if f == fl && s == sl {
                    // we modified f-th and s-th bits
                    assert(forall|x: usize, s: usize| 0 <= s < usize::BITS ==> (x | (1usize << s)) != 0) by (bit_vector);
                    assert((old(self).sl_bitmap[fl as int] | (1usize << sl)) != 0);
                    assert(nth_bit!(old(self).fl_bitmap | (1usize << fl), f));
                } else {
                    // other bits are same as in old(self)
                    if f != fl {
                        assert(old(self).sl_bitmap[f as int] == self.sl_bitmap[f as int]);
                        assert(nth_bit!(old(self).fl_bitmap, fl) ==> nth_bit!(self.fl_bitmap, fl));
                    }
                    if s != sl {
                        if f == fl {
                            assert(nth_bit!(self.fl_bitmap, fl));
                            assert(self.sl_bitmap[f as int] == old(self).sl_bitmap[f as int] | (1usize << sl));
                            assert(0 <= sl < usize::BITS);
                            assert(forall|x: usize, s: usize| 0 <= s < usize::BITS ==> (x | (1usize << s)) != 0) by (bit_vector);
                            assert(self.sl_bitmap[f as int] != 0);
                        }

                        assert(self.sl_bitmap[f as int] == 0 ==> !(1 & self.fl_bitmap >> f == 1));
                        assert(nth_bit!(old(self).sl_bitmap[f as int], sl) ==> nth_bit!(self.sl_bitmap[f as int], sl));
                    }
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
