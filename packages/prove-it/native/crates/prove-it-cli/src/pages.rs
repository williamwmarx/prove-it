//! How the binary backs the search's large regions of memory.

use tla_engine::search::Advice;

/// On Linux, huge pages, where transparent huge pages are on for regions that ask for them.
#[cfg(target_os = "linux")]
pub const LARGE_REGION_ADVICE: Option<Advice> = Some(advise_huge_pages);

#[cfg(not(target_os = "linux"))]
pub const LARGE_REGION_ADVICE: Option<Advice> = None;

// Asks the kernel to back the region's whole 2 MB pages with huge pages. A probe anywhere in a
// large table then misses the TLB far less often, and growing the table faults it in 2 MB at a
// time. Where the kernel refuses, the region keeps small pages.
#[cfg(target_os = "linux")]
fn advise_huge_pages(address: *const u8, length: usize) {
    const HUGE_PAGE: usize = 1 << 21;
    const MADV_HUGEPAGE: i32 = 14;
    unsafe extern "C" {
        fn madvise(address: *mut std::ffi::c_void, length: usize, advice: i32) -> i32;
    }
    let start = (address as usize).next_multiple_of(HUGE_PAGE);
    let end = (address as usize + length) / HUGE_PAGE * HUGE_PAGE;
    if start < end {
        // SAFETY: the range lies inside the region the search allocated and keeps alive through
        // the call, and the advice changes only how the kernel backs its pages, not what they
        // hold. A failure leaves the pages as they were, so its result is ignored.
        unsafe {
            madvise(start as *mut std::ffi::c_void, end - start, MADV_HUGEPAGE);
        }
    }
}
