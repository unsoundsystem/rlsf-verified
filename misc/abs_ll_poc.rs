// PoC: single-file copy of AllBlocks / ShadowFreelist specs and definitions.
// proof fns are omitted; exec/const fns are marked external_body since their
// supporting lemmas are not included.
//
// Sources: src/{all_blocks,block,block_index,half_open_range,
//              ordered_pointer_list,parameters,bits}.rs

use vstd::arithmetic::logarithm::log;
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::set::Set;
use vstd::std_specs::bits::u64_trailing_zeros;

verus! {

// ---------- bits.rs ----------

#[cfg(target_pointer_width = "64")]
pub open spec fn usize_trailing_zeros(x: usize) -> u32
{
    u64_trailing_zeros(x as u64) as u32
}

pub open spec fn is_power_of_two(n: int) -> bool
{
    exists|p: nat| n == pow2(p) as int
}

// ---------- parameters.rs / block_index.rs constants ----------

#[cfg(target_pointer_width = "64")]
pub const GRANULARITY: usize = 8 * 4;

pub const SIZE_USED: usize = 1;
pub const SIZE_SENTINEL: usize = 2;

pub spec const SPEC_SIZE_SIZE_MASK: usize =
    !(((1usize << usize_trailing_zeros(GRANULARITY)) as usize - 1usize) as usize);
#[verifier::external_body]
#[verifier::when_used_as_spec(SPEC_SIZE_SIZE_MASK)]
pub exec const SIZE_SIZE_MASK: usize ensures SIZE_SIZE_MASK == SPEC_SIZE_SIZE_MASK
{
    !((1 << GRANULARITY.trailing_zeros()) - 1)
}

// ---------- half_open_range.rs ----------

pub struct HalfOpenRange(int, int);

impl HalfOpenRange {
    #[verifier::type_invariant]
    pub open spec fn wf(self) -> bool {
        self.start() <= self.end()
    }

    pub closed spec fn new(start: int, size: int) -> Self
        recommends size >= 0
    {
        HalfOpenRange(start, start + size)
    }

    pub open spec fn contains(self, e: int) -> bool
        recommends self.wf()
    {
        self.start() <= e < self.end()
    }

    pub closed spec fn start(self) -> int {
        self.0
    }

    pub closed spec fn end(self) -> int {
        self.1
    }

    pub open spec fn is_empty(self) -> bool
        recommends self.wf()
    {
        self.start() == self.end()
    }

    pub open spec fn disjoint(self, rhs: Self) -> bool
        recommends self.wf(), rhs.wf()
    {
        if self.is_empty() || rhs.is_empty() {
            true
        } else {
            &&& self.wf()
            &&& rhs.wf()
            &&& self.end() <= rhs.start() || rhs.end() <= self.start()
        }
    }

    pub open spec fn to_set(self) -> Set<int>
        recommends self.wf()
    {
        Set::new(|p: int| self.start() <= p < self.end())
    }

    pub open spec fn lt(self, rhs: Self) -> bool {
        &&& self.wf()
        &&& self.end() <= rhs.start()
    }
}

// ---------- block.rs ----------

#[repr(C)]
#[derive(Debug)]
pub struct BlockHdr {
    pub size: usize,
    pub prev_phys_block: *mut BlockHdr,
}

impl BlockHdr {
    pub open spec fn is_sentinel(self) -> bool {
        self.size & SIZE_SENTINEL != 0
    }
    pub open spec fn is_free(self) -> bool {
        self.size & SIZE_USED == 0
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn next_phys_block(block: *mut Self, Tracked(perm): Tracked<&BlockPerm>) -> (r: *mut Self)
        requires
            perm.points_to.is_init(),
            perm.points_to.ptr() == block,
            !perm.points_to.value().is_sentinel(),
            (block as usize as int) + (perm.points_to.value().size as int) < usize::MAX as int,
        ensures
            r@.provenance == block@.provenance,
            r@.addr == block@.addr + ((perm.points_to.value().size & SIZE_SIZE_MASK) as int),
    {
        let size = ptr_ref(block, Tracked(&perm.points_to)).size;
        let mask: usize = !31usize;
        let masked_size = size & mask;
        let prov = expose_provenance(block);
        let r = with_exposed_provenance((block as usize) + masked_size, prov);
        r
    }
}

#[repr(C)]
pub struct FreeLink {
    pub next_free: *mut BlockHdr,
    pub prev_free: *mut BlockHdr,
}

pub struct BlockPerm {
    pub points_to: PointsTo<BlockHdr>,
    pub free_link_perm: Option<PointsTo<FreeLink>>,
    pub mem: PointsToRaw,
    pub overhead_mem: PointsToRaw,
    pub pad_perm: Option<PointsTo<UsedBlockPad>>,
}

impl BlockPerm {
    pub open spec fn wf(self) -> bool {
        &&& self.points_to.is_init()
        &&& self.mem.provenance() == self.points_to.ptr()@.provenance
        &&& self.points_to.value().is_free() ==> {
                let size = self.points_to.value().size;
                &&& self.free_link_perm matches Some(pt) &&
                        get_freelink_ptr_spec(self.points_to.ptr()) == pt.ptr()
                            && pt.is_init()
                &&& size == size & SIZE_SIZE_MASK
                &&& self.mem.is_range(
                    self.points_to.ptr() as int + size_of::<BlockHdr>() as int + size_of::<FreeLink>() as int,
                    size as int - size_of::<BlockHdr>() as int - size_of::<FreeLink>() as int)
                &&& self.overhead_mem.dom().is_empty()
                &&& self.pad_perm is None
            }
    }
}

pub type UsedBlockHdr = BlockHdr;

#[repr(C)]
pub struct UsedBlockPad {
    pub block_hdr: *mut UsedBlockHdr,
}

impl UsedBlockPad {
    #[verifier::external_body]
    #[inline(always)]
    pub fn get_for_allocation(ptr: *mut u8) -> (r: *mut Self)
        ensures
            r@.provenance == ptr@.provenance,
            r@.addr == ((ptr as usize).wrapping_sub(core::mem::size_of::<Self>()) as int),
            ptr@.addr >= core::mem::size_of::<Self>() as int
                ==> r@.addr == ptr@.addr - core::mem::size_of::<Self>() as int,
    {
        let Tracked(is_exposed) = expose_provenance(ptr);
        let ptr = with_exposed_provenance(
            (ptr as usize).wrapping_sub(core::mem::size_of::<Self>()),
            Tracked(is_exposed));
        ptr
    }
}

pub closed spec fn get_freelink_ptr_spec(ptr: *mut BlockHdr) -> *mut FreeLink {
    ptr_from_data(PtrData::<FreeLink> {
        provenance: ptr@.provenance,
        addr: (ptr as usize + size_of::<BlockHdr>()) as usize,
        metadata: ()
    }) as *mut _
}

#[verifier::external_body]
#[inline(always)]
pub fn get_freelink_ptr(ptr: *mut BlockHdr) -> (r: *mut FreeLink)
    requires
        (ptr as usize as int) + (size_of::<BlockHdr>() as int) <= usize::MAX as int,
    ensures
        r == get_freelink_ptr_spec(ptr),
        r@.provenance == ptr@.provenance,
        r as usize == ptr as usize + size_of::<BlockHdr>(),
{
    let prov = expose_provenance(ptr);
    with_exposed_provenance(ptr as usize + size_of::<BlockHdr>(), prov)
}

#[verifier::external_body]
pub const fn null_bhdr() -> (r: *mut BlockHdr)
    ensures r@.addr == 0
{
    core::ptr::null::<BlockHdr>() as *mut _
}

// ---------- block_index.rs ----------

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct BlockIndex<const FLLEN: usize, const SLLEN: usize>(pub usize, pub usize);

impl<const FLLEN: usize, const SLLEN: usize> BlockIndex<FLLEN, SLLEN> {

    pub open spec fn view(self) -> (int, int) {
        (self.0 as int, self.1 as int)
    }

    #[verifier::external_body]
    const fn granularity_log2() -> (r: u32)
        requires is_power_of_two(GRANULARITY as int)
        ensures r == Self::granularity_log2_spec()
    {
        GRANULARITY.trailing_zeros()
    }

    pub open spec fn granularity_log2_spec() -> int {
        log(2, GRANULARITY as int)
    }

    pub open spec fn parameter_validity() -> bool {
        &&& 0 < FLLEN <= usize::BITS
        &&& 0 < SLLEN <= usize::BITS
            && is_power_of_two(SLLEN as int)
        &&& usize::BITS == 64 ==> GRANULARITY == 32
        &&& usize::BITS == 32 ==> GRANULARITY == 16
    }

    pub open spec fn valid_block_index(idx: (int, int)) -> bool {
        let (fl, sl) = idx;
        &&& 0 <= fl < FLLEN as int
        &&& 0 <= sl < SLLEN as int
    }

    spec fn from_int(idx: (int, int)) -> Self
    {
        BlockIndex(idx.0 as usize, idx.1 as usize)
    }

    pub open spec fn wf(self) -> bool {
        Self::valid_block_index(self@)
    }

    pub open spec fn block_size_range_set(self) -> Set<int>
        recommends self.wf(), Self::parameter_validity()
    {
        self.block_size_range().to_set()
    }

    pub open spec fn block_size_range(self) -> HalfOpenRange
        recommends self.wf(), Self::parameter_validity()
    {
        let BlockIndex(fl, sl) = self;
        let fl_block_bytes = pow2((fl + Self::granularity_log2_spec()) as nat) as int;

        if fl_block_bytes < SLLEN {
            HalfOpenRange::new(GRANULARITY as int, GRANULARITY as int)
        } else {
            let sl_block_bytes = fl_block_bytes / SLLEN as int;

            let start = fl_block_bytes + sl_block_bytes * (sl as int);
            let size = sl_block_bytes;
            HalfOpenRange::new(start, size)
        }
    }

    pub open spec fn valid_block_size(size: int) -> bool {
        &&& GRANULARITY <= size && size < (pow2(FLLEN as nat) * GRANULARITY)
        &&& size % (GRANULARITY as int) == 0
    }

    pub open spec fn block_index_lt(self, rhs: Self) -> bool
        recommends self.wf(), rhs.wf(), Self::parameter_validity()
    {
        let (fl1, sl1) = self@;
        let (fl2, sl2) = rhs@;
        if fl1 == fl2 {
            sl1 < sl2
        } else {
            fl1 < fl2
        }
    }

    pub closed spec fn suc(self) -> Self
        recommends self.wf()
    {
        let BlockIndex(fl, sl) = self;
        if sl < SLLEN - 1 {
            BlockIndex(fl, (sl + 1) as usize)
        } else if sl == SLLEN - 1 {
            if fl < FLLEN - 1 {
                BlockIndex((fl + 1) as usize, 0)
            } else {
                self
            }
        } else {
            self
        }
    }

    pub open spec fn fl_zero_cond(self) -> bool
        recommends Self::parameter_validity()
    {
        pow2((self.0 + Self::granularity_log2_spec()) as nat) < SLLEN
    }

    pub open spec fn mapping(size: int) -> Self {
        let fl = log(2, size as int / GRANULARITY as int);
        let flb = pow2((fl + Self::granularity_log2_spec()) as nat) as int;
        let slb = flb / SLLEN as int;
        let sl = ((size as int) / slb) % SLLEN as int;
        Self(fl as usize, sl as usize)
    }
}

// ---------- ordered_pointer_list.rs ----------

pub open spec fn pointer_leq<T>() -> spec_fn(*mut T, *mut T) -> bool {
    |x: *mut T, y: *mut T| {
        let xi = x as usize as int;
        let yi = y as usize as int;
        xi <= yi
    }
}

pub closed spec fn ghost_pointer_ordered(ls: Seq<*mut BlockHdr>) -> bool {
    forall|i: int, j: int|
        0 <= i < ls.len() && 0 <= j < ls.len() && i < j ==>
            (ls[i] as usize as int) <= (ls[j] as usize as int)
}

pub closed spec fn ptrs_no_duplicates(ls: Seq<*mut BlockHdr>) -> bool {
    ls.no_duplicates()
}

pub closed spec fn add_ghost_pointer(ls: Seq<*mut BlockHdr>, p: *mut BlockHdr) -> Seq<*mut BlockHdr>
    recommends ghost_pointer_ordered(ls)
    decreases ls.len()
{
    if ls.len() == 0 {
        seq![p]
    } else {
        if (p as usize as int) <= ls.first() as usize as int {
            seq![p].add(ls)
        } else {
            seq![ls.first()].add(add_ghost_pointer(ls.drop_first(), p))
        }
    }
}

// ---------- all_blocks.rs: AllBlocks ----------

/// Tracks global structure of the header linkage and memory states
pub struct AllBlocks<const FLLEN: usize, const SLLEN: usize> {
    pub ptrs: Ghost<Seq<*mut BlockHdr>>,
    pub perms: Tracked<Map<*mut BlockHdr, BlockPerm>>,
}

impl<const FLLEN: usize, const SLLEN: usize> AllBlocks<FLLEN, SLLEN> {
    pub open spec fn value_at(self, ptr: *mut BlockHdr) -> BlockHdr
        recommends
        self.contains(ptr),
        self.perms@[ptr].points_to.is_init()
    {
        self.perms@[ptr].points_to.value()
    }

    pub open spec fn contains(self, ptr: *mut BlockHdr) -> bool {
        self.ptrs@.contains(ptr)
    }

    #[verifier::opaque]
    pub open spec fn ptr_is_null<T>(p: *mut T) -> bool {
        p@.addr == 0
    }

    #[verifier::opaque]
    pub open spec fn wf_node_ptr(ptr: *mut BlockHdr) -> bool {
        &&& ptr@.addr != 0
        &&& 0 <= ptr@.addr
        &&& (ptr@.addr as int) % (GRANULARITY as int) == 0
    }

    pub closed spec fn phys_next_matches(
        next_ptr: *mut BlockHdr,
        cur_ptr: *mut BlockHdr,
        size: usize,
    ) -> bool {
        &&& next_ptr@.addr == cur_ptr@.addr + (size & SIZE_SIZE_MASK)
        &&& next_ptr@.provenance == cur_ptr@.provenance
    }

    pub closed spec fn wf_node_glue(self, i: int) -> bool
        recommends 0 <= i < self.ptrs@.len()
    {
        let ptr = self.ptrs@[i];
        &&& self.value_at(ptr).prev_phys_block@.addr != 0 ==> (self.phys_prev_of(i)
                matches Some(p) && p == self.value_at(ptr).prev_phys_block)
        &&& self.value_at(ptr).prev_phys_block@.addr == 0 ==> self.phys_prev_of(i) is None
        &&& if self.value_at(ptr).is_sentinel() {
            &&& i == self.ptrs@.len() - 1
            &&& (self.value_at(ptr).size & SIZE_SIZE_MASK) == 0
            &&& (ptr as int) + (size_of::<BlockHdr>() as int) < usize::MAX
        } else {
            &&& BlockIndex::<FLLEN, SLLEN>::valid_block_size((self.value_at(ptr).size & SIZE_SIZE_MASK) as int)
            &&& (self.value_at(ptr).size as int) + (ptr as int) < usize::MAX
            &&& self.phys_next_of(i) is Some
        }
        &&& if self.value_at(ptr).is_free() {
            self.perms@[ptr].free_link_perm matches Some(p)
                && p.ptr() == get_freelink_ptr_spec(ptr)
        } else { true }
    }

    pub closed spec fn wf_node_structural(self, i: int) -> bool
        recommends 0 <= i < self.ptrs@.len()
    {
        let ptr = self.ptrs@[i];
        &&& self.phys_next_of(i) matches Some(next_ptr) ==> {
            &&& next_ptr@.addr == ptr@.addr + (self.value_at(ptr).size & SIZE_SIZE_MASK)
            &&& next_ptr@.provenance == ptr@.provenance
        }
        &&& if self.value_at(ptr).is_free() {
            self.phys_next_of(i) matches Some(next_ptr)
                && !self.value_at(next_ptr).is_free()
        } else { true }
    }

    pub open spec fn wf_node(self, i: int) -> bool
        recommends 0 <= i < self.ptrs@.len()
    {
        let ptr = self.ptrs@[i];
        &&& Self::wf_node_ptr(ptr)
        &&& self.perms@.contains_key(ptr)
        &&& ptr == self.perms@[ptr].points_to.ptr()
        &&& self.perms@[ptr].wf()
        &&& self.wf_node_glue(i)
        &&& self.wf_node_structural(i)
    }

    pub open spec fn phys_next_of(self, i: int) -> Option<*mut BlockHdr> {
        if self.ptrs@.len() - 1 == i {
            None
        } else {
            Some(self.ptrs@[i + 1])
        }
    }

    pub open spec fn phys_prev_of(self, i: int) -> Option<*mut BlockHdr> {
        if i == 0 {
            None
        } else {
            Some(self.ptrs@[i - 1])
        }
    }

    pub open spec fn is_sentinel_pointer(self, ptr: *mut BlockHdr) -> bool
        recommends self.wf(), self.contains(ptr)
    {
        self.value_at(ptr).is_sentinel()
    }

    pub closed spec fn all_nodes_wf(self) -> bool {
        forall|i: int| 0 <= i < self.ptrs@.len() ==> self.wf_node(i)
    }

    pub closed spec fn pool_size_bounded(self) -> bool {
        self.ptrs@.len() >= 2 ==>
            (self.ptrs@.last() as usize as int) - (self.ptrs@[0] as usize as int)
                < pow2(FLLEN as nat) * GRANULARITY as int
    }

    pub open spec fn wf(self) -> bool {
        &&& self.all_nodes_wf()
        &&& ghost_pointer_ordered(self.ptrs@)
        &&& self.pool_size_bounded()
    }

    pub open spec fn get_ptr_internal_index(self, x: *mut BlockHdr) -> int
        recommends exists|i: int| self.ptrs@[i] == x && 0 <= i < self.ptrs@.len()
    {
        choose|i: int| self.ptrs@[i] == x && 0 <= i < self.ptrs@.len()
    }

    #[verifier::external_body]
    pub const fn empty() -> Self {
        Self {
            ptrs: Ghost(Seq::empty()),
            perms: Tracked(Map::tracked_empty()),
        }
    }
}

// ---------- all_blocks.rs: ShadowFreelist ----------

pub type Pi<const FLLEN: usize, const SLLEN: usize> = Map<(BlockIndex<FLLEN, SLLEN>, int), int>;

#[verifier::reject_recursive_types(FLLEN)]
#[verifier::reject_recursive_types(SLLEN)]
pub struct ShadowFreelist<const FLLEN: usize, const SLLEN: usize> {
    pub m: Map<BlockIndex<FLLEN, SLLEN>, Seq<*mut BlockHdr>>,
    pub pi: Pi<FLLEN, SLLEN>,
}

impl<const FLLEN: usize, const SLLEN: usize> ShadowFreelist<FLLEN, SLLEN> {
    pub open spec fn ii_push_for_index(self,
        all_blocks: AllBlocks<FLLEN, SLLEN>,
        new_node_bi: BlockIndex<FLLEN, SLLEN>,
        new_node_ai: int
    ) -> Self
    recommends
        is_identity_injection(self, all_blocks.ptrs@),
        !self.pi.values().contains(new_node_ai)
    {
        let old_len = self.m[new_node_bi].len();
        Self {
            m: self.m.insert(new_node_bi, seq![all_blocks.ptrs@[new_node_ai]].add(self.m[new_node_bi])),
            pi: Map::new(
                |k: (BlockIndex<FLLEN, SLLEN>, int)| {
                    if k.0 == new_node_bi {
                        0 <= k.1 < old_len + 1
                    } else {
                        self.pi.contains_key(k)
                    }
                },
                |k: (BlockIndex<FLLEN, SLLEN>, int)| {
                    if k.0 == new_node_bi {
                        if k.1 == 0 {
                            new_node_ai
                        } else {
                            self.pi[(new_node_bi, k.1 - 1)]
                        }
                    } else {
                        self.pi[k]
                    }
                }
            )
        }
    }

    pub open spec fn ii_remove_for_index(self,
        all_blocks: AllBlocks<FLLEN, SLLEN>,
        rm_bi: BlockIndex<FLLEN, SLLEN>,
        rm_pos: int
    ) -> Self
    recommends
        rm_bi.wf(),
        is_identity_injection(self, all_blocks.ptrs@),
        0 <= rm_pos < self.m[rm_bi].len()
    {
        let new_m_idx = self.m[rm_bi].remove(rm_pos);
        let old_len = self.m[rm_bi].len();
        let last_key = (rm_bi, old_len - 1);
        Self {
            m: self.m.insert(rm_bi, new_m_idx),
            pi: self.pi.map_entries(|k: (BlockIndex<FLLEN, SLLEN>, int), v: int|
                if k.0 == rm_bi {
                    if k.1 < rm_pos {
                        self.pi[(rm_bi, k.1)]
                    } else if rm_pos <= k.1 < old_len - 1 {
                        self.pi[(rm_bi, k.1 + 1)]
                    } else {
                        arbitrary()
                    }
                } else { v }
            ).remove(last_key)
        }
    }

    pub open spec fn ii_shift_after_insert(self, insert_ai: int) -> Self {
        Self {
            m: self.m,
            pi: self.pi.map_values(|ai: int| if insert_ai + 1 <= ai { ai + 1 } else { ai }),
        }
    }

    pub open spec fn ii_shift_after_remove(self, remove_ai: int) -> Self {
        Self {
            m: self.m,
            pi: self.pi.map_values(|ai: int| if ai > remove_ai { (ai - 1) as int } else { ai }),
        }
    }

    pub open spec fn contains(self, node: *mut BlockHdr) -> bool {
        exists|i: BlockIndex<FLLEN, SLLEN>| i.wf()
            && self.m[i].contains(node)
    }

    pub open spec fn shadow_freelist_has_all_wf_index(self) -> bool {
        forall|idx: BlockIndex<FLLEN, SLLEN>|
            self.m.contains_key(idx) <==> idx.wf()
    }
}

pub open spec fn is_identity_injection<const FLLEN: usize, const SLLEN: usize>(
    sfl: ShadowFreelist<FLLEN, SLLEN>,
    all_block_ptrs: Seq<*mut BlockHdr>) -> bool
    recommends
        ptrs_no_duplicates(all_block_ptrs),
        sfl.shadow_freelist_has_all_wf_index()
{
    &&& sfl.pi.is_injective()
    &&& forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
        sfl.pi.contains_key((idx, m)) <==> idx.wf() && 0 <= m < sfl.m[idx].len()

    &&& forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
        idx.wf() && 0 <= m < sfl.m[idx].len() ==> {
            &&& 0 <= #[trigger] sfl.pi[(idx, m)] < all_block_ptrs.len()
            &&& sfl.m[idx][m] == all_block_ptrs[sfl.pi[(idx, m)]]
        }
}

trait Perm {}

struct GlobalStore<T: Sized, P: Perm> {
    ptrs: Seq<*mut T>,
    perms: Map<*mut T, P>
}

impl GlobalStore {

    pub open spec fn is_identity_injection<const FLLEN: usize, const SLLEN: usize>(
        self,
        ls: ListView,
        ) -> bool
        recommends
            ls.wf(),
    {
        &&& sfl.pi.is_injective()
        &&& forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
            sfl.pi.contains_key((idx, m)) <==> idx.wf() && 0 <= m < sfl.m[idx].len()

        &&& forall|idx: BlockIndex<FLLEN, SLLEN>, m: int|
            idx.wf() && 0 <= m < sfl.m[idx].len() ==> {
                &&& 0 <= #[trigger] sfl.pi[(idx, m)] < all_block_ptrs.len()
                &&& sfl.m[idx][m] == all_block_ptrs[sfl.pi[(idx, m)]]
            }
    }
}

struct ListView<T: Sized> {
    ptrs: Seq<*mut T>,
    pi: Map<*mut T, *mut T>
}

impl ListView {

}

} // verus!
