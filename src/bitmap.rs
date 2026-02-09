use vstd::prelude::*;

verus! {

#[macro_use]
use crate::*;
use crate::{
    Tlsf, GRANULARITY
};

#[cfg(verus_keep_ghost)]
use crate::bits::{lemma_bitmap_or, lemma_bit_clear_zero, lemma_bit_or_nonzero, lemma_bitmap_clear};

use crate::block_index::BlockIndex;

impl<'pool, const FLLEN: usize, const SLLEN: usize> Tlsf<'pool, FLLEN, SLLEN> {

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
                lemma_bitmap_or(old(self).fl_bitmap, fl);
            };
            assert(nth_bit!(self.sl_bitmap[fl as int], sl)) by {
                lemma_bitmap_or(old(self).sl_bitmap[fl as int], sl);
            };
            lemma_bitmap_or(old(self).sl_bitmap[fl as int], sl);
            lemma_bitmap_or(old(self).fl_bitmap, fl);
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
                    lemma_bit_or_nonzero();
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
                            lemma_bit_or_nonzero();
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
        requires Self::parameter_validity(), idx.wf(), old(self).bitmap_wf()
        ensures self.bitmap_wf(),
            idx matches BlockIndex(fl, sl)
                && !nth_bit!(self.sl_bitmap[fl as int], sl)
                && !nth_bit!(self.fl_bitmap, fl)
    {
        let BlockIndex(fl, sl) = idx;
        self.fl_bitmap = self.fl_bitmap & !(1usize << fl);
        self.sl_bitmap[fl] = self.sl_bitmap[fl] & !(1usize << sl);

        proof {
            assert(self.fl_bitmap == old(self).fl_bitmap & !(1usize << fl));
            assert(self.sl_bitmap[fl as int] == old(self).sl_bitmap[fl as int] & !(1usize << sl));
            assert(!nth_bit!(self.fl_bitmap, fl)) by {
                lemma_bitmap_clear(old(self).fl_bitmap, fl);
            };
            assert(!nth_bit!(self.sl_bitmap[fl as int], sl)) by {
                lemma_bitmap_clear(old(self).sl_bitmap[fl as int], sl);
            };
            lemma_bitmap_clear(old(self).sl_bitmap[fl as int], sl);
            lemma_bitmap_clear(old(self).fl_bitmap, fl);
            assert forall|idx: BlockIndex<FLLEN, SLLEN>|
                idx.wf() implies idx matches BlockIndex(f, s) &&
                    (self.sl_bitmap[f as int] == 0 <==> !nth_bit!(self.fl_bitmap, f))
            by {
                let BlockIndex(f, s) = idx;
                if f == fl && s == sl {
                    // we modified f-th and s-th bits
                    lemma_bit_clear_zero();
                } else {
                    // other bits are same as in old(self)
                    if s != sl && f == fl {
                            lemma_bit_clear_zero();
                    }
                }
            }
        }
    }

    #[inline]
    pub fn clear_bit_for_sl(&mut self, idx: BlockIndex<FLLEN, SLLEN>)
        requires Self::parameter_validity(), idx.wf(), old(self).bitmap_wf()
        ensures self.bitmap_wf(),
            idx matches BlockIndex(fl, sl)
                && !nth_bit!(self.sl_bitmap[fl as int], sl)
    {
        let BlockIndex(fl, sl) = idx;
        self.sl_bitmap[fl] = self.sl_bitmap[fl] & !(1usize << sl);
        if self.sl_bitmap[fl] == 0 {
            self.fl_bitmap = self.fl_bitmap & !(1usize << fl);
        }
    }

    /// State *inner bitmap consistency*
    ///      fl_bitmap[i] == fold(true, |j,k| fl_bitmap[i][j] || fl_bitmap[i][k])
    pub open spec fn bitmap_wf(&self) -> bool {
        // TODO: state that self.fl_bitmap[0..GRANULARITY_LOG2] is zero?
        &&& forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf() ==>
            (self.sl_bitmap[idx.0 as int] == 0 <==> !(nth_bit!(self.fl_bitmap, idx.0)))
        &&& forall|f: usize| f >= FLLEN ==> !(nth_bit!(self.fl_bitmap, f))
        &&& forall|f: usize, s: usize| s >= SLLEN ==> !(nth_bit!(self.sl_bitmap[f as int], s))
    }

    /// Bitmap kept sync with shadow segregated free lists.
    /// NOTE: this def only depends on sl_bitmap
    pub(crate) closed spec fn bitmap_sync(self) -> bool
        recommends
            self.all_blocks.wf(),
            self.all_freelist_wf(),
            self.bitmap_wf()
    {
        forall|idx: BlockIndex<FLLEN, SLLEN>|  idx.wf() ==>
        {
            nth_bit!(self.sl_bitmap[idx.0 as int], idx.1 as usize)
                <==> self.shadow_freelist@.m[idx].len() > 0
        }
    }
}
}
