use std::mem::MaybeUninit;
use std::ptr;

/// Copied from std btree node.rs
///
/// Inserts a value into a slice of initialized elements followed by one uninitialized element.
///
/// # Safety
/// The slice has more than `idx` elements.
pub(crate) unsafe fn slice_insert<T>(slice: &mut [MaybeUninit<T>], idx: usize, val: T) {
    unsafe {
        let len = slice.len();
        debug_assert!(len > idx);
        let slice_ptr = slice.as_mut_ptr();
        if len > idx + 1 {
            ptr::copy(slice_ptr.add(idx), slice_ptr.add(idx + 1), len - idx - 1);
        }
        (*slice_ptr.add(idx)).write(val);
    }
}

/// Removes and returns a value from a slice of all initialized elements, leaving behind one
/// trailing uninitialized element.
///
/// # Safety
/// The slice has more than `idx` elements.
pub(crate) unsafe fn slice_remove<T>(slice: &mut [MaybeUninit<T>], idx: usize) -> T {
    unsafe {
        let len = slice.len();
        debug_assert!(idx < len);
        let slice_ptr = slice.as_mut_ptr();
        let ret = (*slice_ptr.add(idx)).assume_init_read();
        ptr::copy(slice_ptr.add(idx + 1), slice_ptr.add(idx), len - idx - 1);
        ret
    }
}

/// Moves all values from a slice of initialized elements to a slice
/// of uninitialized elements, leaving behind `src` as all uninitialized.
/// Works like `dst.copy_from_slice(src)` but does not require `T` to be `Copy`.
pub(crate) fn move_to_slice<T>(src: &mut [MaybeUninit<T>], dst: &mut [MaybeUninit<T>]) {
    assert!(src.len() == dst.len());
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
    }
}
