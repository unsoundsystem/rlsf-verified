// Copyright 2021 yvt
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software
// and associated documentation files (the "Software"), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge, publish, distribute,
// sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
use core::{mem::MaybeUninit, ptr::NonNull};

/// Polyfill for <https://github.com/rust-lang/rust/issues/71941>
#[inline]
pub fn nonnull_slice_from_raw_parts<T>(ptr: NonNull<T>, len: usize) -> NonNull<[T]> {
    unsafe { NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(ptr.as_ptr(), len)) }
}

/// Polyfill for  <https://github.com/rust-lang/rust/issues/71146>
#[inline]
pub fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
    // Safety: We are just reading the slice length embedded in the fat
    //         pointer and not dereferencing the pointer. We also convert it
    //         to `*mut [MaybeUninit<u8>]` just in case because the slice
    //         might be uninitialized.
    unsafe { (*(ptr.as_ptr() as *const [MaybeUninit<T>])).len() }
}

// Polyfill for <https://github.com/rust-lang/rust/issues/74265>
#[inline]
pub fn nonnull_slice_start<T>(ptr: NonNull<[T]>) -> NonNull<T> {
    unsafe { NonNull::new_unchecked(ptr.as_ptr() as *mut T) }
}

#[inline]
pub fn nonnull_slice_end<T>(ptr: NonNull<[T]>) -> *mut T {
    (ptr.as_ptr() as *mut T).wrapping_add(nonnull_slice_len(ptr))
}
