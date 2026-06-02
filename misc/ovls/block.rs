// Minimal block types for the overlaid list port.
//
// BlockHdr  - one-pointer header carrying the singly-linked OVList1 chain.
// FreeLink  - two-pointer overlay carrying the doubly-linked OVList2 chain.
//             Stored at offset size_of::<BlockHdr>() inside the same block.
// BlockPerm - permissions bundle: PointsTo<BlockHdr> + Option<PointsTo<FreeLink>>.
//
// Adapted from src/block.rs.  Stripped: size, prev_phys_block, is_sentinel,
// is_free, next_phys_block, mem/overhead_mem/pad_perm, UsedBlockHdr,
// UsedBlockPad.
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

#[repr(C)]
pub struct BlockHdr {
    pub next: *mut BlockHdr,
}

#[repr(C)]
pub struct FreeLink {
    pub next_free: *mut BlockHdr,
    pub prev_free: *mut BlockHdr,
}

pub struct BlockPerm {
    pub points_to: PointsTo<BlockHdr>,
    pub free_link_perm: Option<PointsTo<FreeLink>>,
}

impl BlockPerm {
    /// Well-formedness for use by OVList1 (header-only access).
    pub open spec fn wf(self, ptr: *mut BlockHdr) -> bool {
        &&& self.points_to.is_init()
        &&& self.points_to.ptr() == ptr
    }

    /// Well-formedness for use by OVList2 (header + FreeLink access).
    pub open spec fn wf_freelink(self, ptr: *mut BlockHdr) -> bool {
        &&& self.wf(ptr)
        &&& self.free_link_perm matches Some(pt)
        &&& self.free_link_perm.unwrap().ptr() == get_freelink_ptr_spec(ptr)
        &&& self.free_link_perm.unwrap().is_init()
    }
}

pub closed spec fn get_freelink_ptr_spec(ptr: *mut BlockHdr) -> *mut FreeLink {
    ptr_from_data(PtrData::<FreeLink> {
        provenance: ptr@.provenance,
        addr: (ptr as usize + size_of::<BlockHdr>()) as usize,
        metadata: (),
    }) as *mut _
}

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

pub const fn null_bhdr() -> (r: *mut BlockHdr)
    ensures r@.addr == 0
{
    core::ptr::null::<BlockHdr>() as *mut _
}

/// Returns true iff `p` has address 0 (i.e. is null).
#[inline(always)]
pub fn ptr_eq_null(p: *mut BlockHdr) -> (r: bool)
    ensures r == (p@.addr == 0)
{
    p as usize == 0
}

/// Closed wrapper that hides a raw `ptr@.addr` atom.  Stands in for
/// the `wf_node_structural` shape in `src/all_blocks.rs`: a closed
/// spec whose intro lemma is the only way to put the `ptr@.addr`
/// atom into a proof context.
pub closed spec fn ptr_addr_below(p: *mut BlockHdr, bound: int) -> bool {
    p@.addr < bound
}

/// Intro lemma for `ptr_addr_below`.  Calling this drops a raw
/// `ptr@.addr` term into the surrounding SMT context — exactly the
/// ignition pattern documented in the project memory
/// `project_ptrs_mut_eq_cascade`.
pub proof fn lemma_ptr_addr_below_intro(p: *mut BlockHdr, bound: int)
    requires p@.addr < bound,
    ensures ptr_addr_below(p, bound),
{
    reveal(ptr_addr_below);
}

/// Four-atom closed wrapper, mirroring the shape of
/// `src/all_blocks.rs`'s `wf_node_structural`: hides
/// `p@.addr`, `p@.provenance`, `q@.addr`, `q@.provenance`.
pub closed spec fn structural_atoms(
    p: *mut BlockHdr, q: *mut BlockHdr, off: int,
) -> bool {
    &&& q@.addr == p@.addr + off
    &&& q@.provenance == p@.provenance
}

/// Intro lemma for `structural_atoms`.  Mirrors the ensures shape of
/// `lemma_wf_structural_facts`: a single call exposes FOUR raw
/// `ptr@` atoms (two addrs, two provenances) into the caller's SMT
/// context.  This is the multi-atom intro lemma the minimal
/// reproduction was missing.
pub proof fn lemma_structural_facts_intro(
    p: *mut BlockHdr, q: *mut BlockHdr, off: int,
)
    requires
        q@.addr == p@.addr + off,
        q@.provenance == p@.provenance,
    ensures
        structural_atoms(p, q, off),
        q@.addr == p@.addr + off,
        q@.provenance == p@.provenance,
{
    reveal(structural_atoms);
}

} // verus!
