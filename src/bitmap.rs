use vstd::prelude::*;

verus! {

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
        ensures
            self.bitmap_wf(),
            idx matches BlockIndex(fl, sl)
                && nth_bit!(self.sl_bitmap[fl as int], sl),
            forall|i: BlockIndex<FLLEN, SLLEN>| i.wf() && i != idx
                ==> nth_bit!(self.sl_bitmap[i.0 as int], i.1 as usize)
                    == nth_bit!(old(self).sl_bitmap[i.0 as int], i.1 as usize),
            forall|i: BlockIndex<FLLEN, SLLEN>| i.wf() && i != idx
                ==> (1 & self.sl_bitmap[i.0 as int] >> i.1 as usize)
                    == (1 & old(self).sl_bitmap[i.0 as int] >> i.1 as usize),
            self.first_free == old(self).first_free,
            self.shadow_freelist == old(self).shadow_freelist,
            self.all_blocks == old(self).all_blocks,
            self.user_block_map == old(self).user_block_map,
            self.valid_range == old(self).valid_range,
            self.root_provenances == old(self).root_provenances,
    {
        //#[cfg(feature = "std")]
        //{
            //use std::println;
            //println!("set bitmap {}, {}, {:b}", idx.0, idx.1, self.fl_bitmap);
        //}
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

            assert forall|i: BlockIndex<FLLEN, SLLEN>| i.wf() && i != idx
                implies nth_bit!(self.sl_bitmap[i.0 as int], i.1 as usize)
                    == nth_bit!(old(self).sl_bitmap[i.0 as int], i.1 as usize)
            by {
                let BlockIndex(f, s) = i;
                let BlockIndex(fl, sl) = idx;
                if f == fl {
                    assert(s != sl);
                    lemma_bitmap_or(old(self).sl_bitmap[fl as int], sl);
                } else {
                    assert(self.sl_bitmap[f as int] == old(self).sl_bitmap[f as int]);
                }
            };
            assert forall|i: BlockIndex<FLLEN, SLLEN>| i.wf() && i != idx
                implies (1 & self.sl_bitmap[i.0 as int] >> i.1 as usize)
                    == (1 & old(self).sl_bitmap[i.0 as int] >> i.1 as usize)
            by {
                assert(nth_bit!(self.sl_bitmap[i.0 as int], i.1 as usize)
                    == nth_bit!(old(self).sl_bitmap[i.0 as int], i.1 as usize));
            };
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
                && !nth_bit!(self.fl_bitmap, fl),
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
            self.all_blocks == old(self).all_blocks,
            self.first_free == old(self).first_free,
            self.shadow_freelist == old(self).shadow_freelist,
            self.user_block_map == old(self).user_block_map,
            self.valid_range == old(self).valid_range,
            self.root_provenances == old(self).root_provenances,
            forall|i: BlockIndex<FLLEN, SLLEN>| i.wf() && i != idx
                ==> nth_bit!(self.sl_bitmap[i.0 as int], i.1 as usize)
                    == nth_bit!(old(self).sl_bitmap[i.0 as int], i.1 as usize),
            idx matches BlockIndex(fl, sl)
                && !nth_bit!(self.sl_bitmap[fl as int], sl)
    {
        let BlockIndex(fl, sl) = idx;
        proof {
            assert(fl < FLLEN);
            assert(sl < SLLEN);
            Self::plat_basics();
            if usize::BITS == 64 {
                assert(Self::granularity_log2_spec() == 5);
                assert(FLLEN < 64 - 5);
                assert(FLLEN < usize::BITS as usize);
            } else {
                assert(usize::BITS == 32);
                assert(Self::granularity_log2_spec() == 4);
                assert(FLLEN < 32 - 4);
                assert(FLLEN < usize::BITS as usize);
            }
            assert(fl < usize::BITS as usize);
            assert(sl < usize::BITS as usize);
        }
        self.sl_bitmap[fl] = self.sl_bitmap[fl] & !(1usize << sl);
        if self.sl_bitmap[fl] == 0 && fl < usize::BITS as usize {
            self.fl_bitmap = self.fl_bitmap & !(1usize << fl);
        }
        proof {
            assert(old(self).bitmap_wf());
            let ghost old_fl = old(self).fl_bitmap;
            let ghost old_row = old(self).sl_bitmap[fl as int];
            let ghost new_row = self.sl_bitmap[fl as int];
            let ghost new_fl = self.fl_bitmap;

            assert(new_row == old_row & !(1usize << sl));
            lemma_bitmap_clear(old_row, sl);

            if new_row == 0 && fl < usize::BITS as usize {
                assert(new_fl == old_fl & !(1usize << fl));
                lemma_bitmap_clear(old_fl, fl);
            } else {
                assert(new_fl == old_fl);
            }

            assert forall|i: BlockIndex<FLLEN, SLLEN>| i.wf() && i != idx
                implies nth_bit!(self.sl_bitmap[i.0 as int], i.1 as usize)
                    == nth_bit!(old(self).sl_bitmap[i.0 as int], i.1 as usize)
            by {
                let BlockIndex(f, s) = i;
                if f == fl {
                    assert(s != sl);
                    assert(nth_bit!(new_row, s) == nth_bit!(old_row, s));
                } else {
                    assert(self.sl_bitmap[f as int] == old(self).sl_bitmap[f as int]);
                }
            };

            assert forall|i: BlockIndex<FLLEN, SLLEN>| i.wf() implies
                i matches BlockIndex(f, s) &&
                    (self.sl_bitmap[f as int] == 0 <==> !nth_bit!(self.fl_bitmap, f))
            by {
                let BlockIndex(f, s) = i;
                if f == fl {
                    assert(self.sl_bitmap[f as int] == new_row);
                    if new_row == 0 {
                        if fl < usize::BITS as usize {
                            assert(new_fl == old_fl & !(1usize << fl));
                            lemma_bitmap_clear(old_fl, fl);
                            assert(!nth_bit!(new_fl, fl));
                        } else {
                            assert(!nth_bit!(new_fl, fl));
                        }
                    } else {
                        assert(old_row != 0) by {
                            if old_row == 0 {
                                assert(new_row == old_row & !(1usize << sl));
                                assert(0usize & !(1usize << sl) == 0usize) by (bit_vector);
                                assert(new_row == 0usize & !(1usize << sl));
                                assert(new_row == 0usize);
                                assert(false);
                            }
                        };
                        assert(old_row == 0 <==> !nth_bit!(old_fl, fl));
                        assert(nth_bit!(old_fl, fl));
                        assert(new_fl == old_fl);
                        assert(nth_bit!(new_fl, fl));
                    }
                } else {
                    assert(self.sl_bitmap[f as int] == old(self).sl_bitmap[f as int]);
                    if new_row == 0 && fl < usize::BITS as usize {
                        assert(f != fl);
                        lemma_bitmap_clear_preserve(old_fl, fl, f);
                        assert(nth_bit!(new_fl, f) == nth_bit!(old_fl, f));
                    } else {
                        assert(new_fl == old_fl);
                    }
                    assert(old(self).sl_bitmap[f as int] == 0 <==> !nth_bit!(old_fl, f));
                }
            };

            assert forall|f: usize| f >= FLLEN implies !nth_bit!(self.fl_bitmap, f) by {
                assert(!nth_bit!(old_fl, f));
                if new_row == 0 && fl < usize::BITS as usize {
                    assert(f != fl);
                    lemma_bitmap_clear_preserve(old_fl, fl, f);
                    assert(nth_bit!(new_fl, f) == nth_bit!(old_fl, f));
                } else {
                    assert(new_fl == old_fl);
                }
            };

            assert forall|f: usize, s: usize| f < FLLEN && s >= SLLEN implies !nth_bit!(self.sl_bitmap[f as int], s) by {
                if f == fl {
                    assert(s != sl);
                    assert(!nth_bit!(old_row, s));
                    lemma_bitmap_clear_preserve(old_row, sl, s);
                    assert(nth_bit!(new_row, s) == nth_bit!(old_row, s));
                    assert(!nth_bit!(new_row, s));
                    assert(!nth_bit!(old_row, s));
                } else {
                    assert(self.sl_bitmap[f as int] == old(self).sl_bitmap[f as int]);
                    assert(!nth_bit!(old(self).sl_bitmap[f as int], s));
                }
            };
        }
    }

    /// State *inner bitmap consistency*
    ///      fl_bitmap[i] == fold(true, |j,k| fl_bitmap[i][j] || fl_bitmap[i][k])
    pub open spec fn bitmap_wf(&self) -> bool
        recommends Self::parameter_validity()
    {
        // TODO: state that self.fl_bitmap[0..GRANULARITY_LOG2] is zero?
        &&& forall|idx: BlockIndex<FLLEN, SLLEN>| idx.wf() ==>
            (self.sl_bitmap[idx.0 as int] == 0 <==> !(nth_bit!(self.fl_bitmap, idx.0)))
        &&& forall|f: usize| f >= FLLEN ==> !(nth_bit!(self.fl_bitmap, f))
        &&& forall|f: usize, s: usize| f < FLLEN && s >= SLLEN ==> !(nth_bit!(self.sl_bitmap[f as int], s))
    }

    /// Bitmap kept sync with shadow segregated free lists.
    /// NOTE: this def only depends on sl_bitmap
    pub(crate) open spec fn bitmap_sync(self) -> bool
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
