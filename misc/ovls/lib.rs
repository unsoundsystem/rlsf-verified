// Minimal standalone Verus port of the overlaid list structure.
//
// Two first-class list types:
//   OVList1 - singly-linked list; nodes are BlockHdr.  The list owns the
//             ghost pointer sequence AND a tracked map of BlockPerm.
//   OVList2 - doubly-linked list; the link pointers live in a FreeLink
//             struct overlaid at offset size_of::<BlockHdr>() inside each
//             node.  Owns the ghost pointer sequence + head pointer; the
//             perms map is supplied by the caller (typically borrowed from
//             the corresponding OVList1).
//
// Source: src/{block,linked_list,all_blocks}.rs (refactored, simplified).
#![allow(unused_imports)]
#![no_std]

mod block;
mod ovlist1;
mod ovlist2;
mod ovlist;
mod brittle;

use vstd::prelude::*;

verus! {

use vstd::raw_ptr::{
    ptr_mut_read, ptr_mut_write, ptr_ref, PointsTo,
    expose_provenance, with_exposed_provenance, ptr_from_data, PtrData,
};
use core::marker::PhantomData;
use vstd::{seq::*, seq_lib::*};
use crate::block::*;

#[cfg(target_pointer_width = "64")]
global layout BlockHdr is size == 8, align == 8;

#[cfg(target_pointer_width = "64")]
global layout FreeLink is size == 16, align == 8;

} // verus!
