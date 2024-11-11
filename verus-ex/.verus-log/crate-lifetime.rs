#![feature(box_patterns)]
#![feature(ptr_metadata)]
#![feature(never_type)]
#![feature(allocator_api)]
#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(unused_parens)]
#![allow(unused_braces)]
#![allow(dead_code)]
#![allow(unreachable_code)]
#![allow(unconditional_recursion)]
#![allow(unused_mut)]
#![allow(unused_labels)]
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::Arc;
use std::alloc::Allocator;
use std::alloc::Global;
use std::mem::ManuallyDrop;
use std::ptr::Pointee;
use std::ptr::Thin;
fn op<A, B>(a: A) -> B { panic!() }
fn static_ref<T>(t: T) -> &'static T { panic!() }
fn tracked_new<T>(t: T) -> Tracked<T> { panic!() }
fn tracked_exec_borrow<'a, T>(t: &'a T) -> &'a Tracked<T> { panic!() }
fn clone<T>(t: &T) -> T { panic!() }
fn rc_new<T>(t: T) -> std::rc::Rc<T> { panic!() }
fn arc_new<T>(t: T) -> std::sync::Arc<T> { panic!() }
fn box_new<T>(t: T) -> Box<T> { panic!() }
struct Tracked<A> { a: PhantomData<A> }
impl<A> Tracked<A> {
    pub fn get(self) -> A { panic!() }
    pub fn borrow(&self) -> &A { panic!() }
    pub fn borrow_mut(&mut self) -> &mut A { panic!() }
}
struct Ghost<A> { a: PhantomData<A> }
impl<A> Clone for Ghost<A> { fn clone(&self) -> Self { panic!() } }
impl<A> Copy for Ghost<A> { }
impl<A: Copy> Clone for Tracked<A> { fn clone(&self) -> Self { panic!() } }
impl<A: Copy> Copy for Tracked<A> { }
#[derive(Clone, Copy)] struct int;
#[derive(Clone, Copy)] struct nat;
struct FnSpec<Args, Output> { x: PhantomData<(Args, Output)> }
struct InvariantBlockGuard;
fn open_atomic_invariant_begin<'a, X, V>(_inv: &'a X) -> (InvariantBlockGuard, V) { panic!(); }
fn open_local_invariant_begin<'a, X, V>(_inv: &'a X) -> (InvariantBlockGuard, V) { panic!(); }
fn open_invariant_end<V>(_guard: InvariantBlockGuard, _v: V) { panic!() }
fn index<'a, V, Idx, Output>(v: &'a V, index: Idx) -> &'a Output { panic!() }
struct C<const N: usize, A: ?Sized>(Box<A>);
struct Arr<A: ?Sized, const N: usize>(Box<A>);
fn use_type_invariant<A>(a: A) -> A { a }
fn main() {}



trait T82_Clone {
}

enum D35_Option<A2_T, > where A2_T: ,  {
    C43_None(
    ),
    C36_Some(
        A2_T,
    ),
}

impl<A2_T, > Clone for D35_Option<A2_T, > where A2_T: Clone,  { fn clone(&self) -> Self { panic!() } }

impl<A2_T, > Copy for D35_Option<A2_T, > where A2_T: Copy,  {}

struct D30_PointsTo<A23_V, > where A23_V: ,  {
    y55_points_to: D56_PointsTo<A23_V, >,
    y57_exposed: D58_IsExposed,
    y59_dealloc: D35_Option<D60_Dealloc, >,
}

struct D60_Dealloc(
);

struct D58_IsExposed(
);

impl Clone for D58_IsExposed { fn clone(&self) -> Self { panic!() } }

impl Copy for D58_IsExposed {}

struct D56_PointsTo<A2_T, >(
    PhantomData<A2_T>,
) where A2_T: , ;

struct D29_PPtr<A23_V, >(
    usize,
    PhantomData<A23_V, >,
) where A23_V: , ;

impl<A23_V, > Clone for D29_PPtr<A23_V, > { fn clone(&self) -> Self { panic!() } }

impl<A23_V, > Copy for D29_PPtr<A23_V, > {}

struct D47_LList {
    y34_first: D35_Option<D29_PPtr<D28_Node, >, >,
    y61_perms: Tracked<D62_Map<nat, D30_PointsTo<D28_Node, >, >, >,
    y63_ptrs: Ghost<D64_Seq<D29_PPtr<D28_Node, >, >, >,
}

struct D64_Seq<A25_A, >(
    PhantomData<A25_A>,
) where A25_A: , ;

struct D62_Map<A22_K, A23_V, >(
    PhantomData<A22_K>,
    PhantomData<A23_V>,
) where A22_K: , A23_V: , ;

struct D28_Node {
    y38_next: D35_Option<D29_PPtr<D28_Node, >, >,
    y40_x: usize,
}

impl Clone for D28_Node { fn clone(&self) -> Self { panic!() } }

impl Copy for D28_Node {}

struct D66_Option<A65_V, >(
    Box<A65_V, >,
) where A65_V : ?Sized, ;

struct D67_PhantomData<A65_V, >(
    Box<A65_V, >,
) where A65_V : ?Sized, ;

struct D69_Map<A68_K, A65_V, >(
    Box<A68_K, >,
    Box<A65_V, >,
) where A68_K : ?Sized, A65_V : ?Sized, ;

struct D71_PointsTo<A70_T, >(
    Box<A70_T, >,
) where A70_T : ?Sized, ;

struct D72_MemContents<A70_T, >(
    Box<A70_T, >,
) where A70_T : ?Sized, ;

struct D73_IsExposed(
);

struct D74_Dealloc(
);

struct D76_Seq<A75_A, >(
    Box<A75_A, >,
) where A75_A : ?Sized, ;

struct D77_Set<A75_A, >(
    Box<A75_A, >,
) where A75_A : ?Sized, ;

struct D78_PPtr<A65_V, >(
    Box<A65_V, >,
) where A65_V : ?Sized, ;

struct D79_PointsTo<A65_V, >(
    Box<A65_V, >,
) where A65_V : ?Sized, ;

struct D80_Node(
);

struct D81_LList(
);

impl T82_Clone for D73_IsExposed {
}

impl<A65_V, > T82_Clone for D78_PPtr<A65_V, > where A65_V : ?Sized,  {
}

impl T82_Clone for usize {
}

impl<A70_T, > T82_Clone for D67_PhantomData<A70_T, > where A70_T : ?Sized,  {
}

impl<A70_T, > T82_Clone for C<4, (Box<A70_T, >, ), > where A70_T : ?Sized,  {
}

impl T82_Clone for bool {
}

impl<A70_T, > T82_Clone for D66_Option<A70_T, > where A70_T: T82_Clone, A70_T : ?Sized,  {
}

impl<A75_A, > T82_Clone for C<10, (Box<A75_A, >, ), > where A75_A : ?Sized,  {
}

impl<A75_A, > T82_Clone for C<9, (Box<A75_A, >, ), > where A75_A : ?Sized,  {
}

impl T82_Clone for D80_Node {
}

fn f45_push_front<'a46__, >(
    x33_self: &'a46__  mut D47_LList,
    x41_v: usize,
) where 
{
    let (x26_node, x27_verus_tmp_perm, ): (D29_PPtr<D28_Node, >, Tracked<D30_PointsTo<D28_Node, >, >, ) = f31_empty::<D28_Node, >();
    let mut x32_perm: D30_PointsTo<D28_Node, >;
    {
        (x32_perm) = (x27_verus_tmp_perm.get());
    };
    match (x33_self).y34_first {
        D35_Option::C36_Some(x37_old_first, ) => 
        {
            f42_write::<D28_Node, >(x26_node, tracked_new::<& mut D30_PointsTo<D28_Node, >, >(&mut(x32_perm), ), D28_Node { y38_next: D35_Option::C36_Some::<D29_PPtr<D28_Node, >, >(f39_clone::<D28_Node, >(&(x37_old_first), ), ), y40_x: x41_v,  } , );
        }
        _ => 
        {
            f42_write::<D28_Node, >(x26_node, tracked_new::<& mut D30_PointsTo<D28_Node, >, >(&mut(x32_perm), ), D28_Node { y38_next: D35_Option::C43_None::<D29_PPtr<D28_Node, >, >(), y40_x: x41_v,  } , );
            ((x33_self).y34_first) = (D35_Option::C36_Some::<D29_PPtr<D28_Node, >, >(x26_node, ));
        }
    }
}

fn f49_main(
)
{
}

fn f39_clone<'a46__, A23_V, >(
    x33_self: &'a46__ D29_PPtr<A23_V, >,
) -> D29_PPtr<A23_V, > where A23_V: , 
{
    panic!()
}

fn f42_write<'a46__, A23_V, >(
    x33_self: D29_PPtr<A23_V, >,
    x52_verus_tmp_perm: Tracked<&'a46__  mut D30_PointsTo<A23_V, >, >,
    x53_in_v: A23_V,
) -> () where A23_V: , A23_V: Copy, 
{
    panic!()
}

fn f31_empty<A23_V, >(
) -> (D29_PPtr<A23_V, >, Tracked<D30_PointsTo<A23_V, >, >, ) where A23_V: , 
{
    panic!()
}
