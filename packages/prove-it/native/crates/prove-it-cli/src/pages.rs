//! Huge pages for the binary's large allocations, on Linux.
//!
//! The search's tables (the memo tables, the seen-set, the store's arrays) grow to hundreds of
//! megabytes and are read at random, so on 4 KiB pages nearly every read misses the TLB too. Where
//! transparent huge pages are on only for memory that asks for them (`madvise`, a common default),
//! this allocator asks for them on every allocation of at least [`LARGE`] bytes. What it allocates
//! is what the system allocator does; a failed request is ignored.

use std::alloc::{GlobalAlloc, Layout, System};
use std::ffi::{c_int, c_void};

/// The size of a huge page on x86_64 and on arm64 with 4 KiB pages.
const HUGE_PAGE: usize = 2 << 20;
/// The smallest allocation that asks for huge pages: one that spans at least one whole huge page
/// wherever it starts.
const LARGE: usize = 2 * HUGE_PAGE;
/// `MADV_HUGEPAGE`, the same on every Linux architecture.
const MADV_HUGEPAGE: c_int = 14;

unsafe extern "C" {
    fn madvise(address: *mut c_void, length: usize, advice: c_int) -> c_int;
}

pub struct HugePages;

// Asks for huge pages under the whole huge pages an allocation spans.
fn advise(pointer: *mut u8, size: usize) {
    if pointer.is_null() || size < LARGE {
        return;
    }
    let start = (pointer as usize).next_multiple_of(HUGE_PAGE);
    let end = (pointer as usize + size) / HUGE_PAGE * HUGE_PAGE;
    // SAFETY: madvise with MADV_HUGEPAGE changes no memory's contents. The range is page-aligned
    // and lies inside an allocation this process owns, and a failure only leaves 4 KiB pages.
    unsafe {
        madvise(start as *mut c_void, end - start, MADV_HUGEPAGE);
    }
}

// SAFETY: every method forwards to the system allocator with the same arguments, and advising
// a block changes neither its address, its size nor its contents.
unsafe impl GlobalAlloc for HugePages {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's contract for `alloc`.
        let pointer = unsafe { System.alloc(layout) };
        advise(pointer, layout.size());
        pointer
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's contract for `alloc_zeroed`.
        let pointer = unsafe { System.alloc_zeroed(layout) };
        advise(pointer, layout.size());
        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        // SAFETY: the caller's contract for `dealloc`.
        unsafe { System.dealloc(pointer, layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        // SAFETY: the caller's contract for `realloc`.
        let pointer = unsafe { System.realloc(pointer, layout, size) };
        advise(pointer, size);
        pointer
    }
}
