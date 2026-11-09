//! Executable memory, written while it is writable and run only once it is executable and no longer
//! writable (native/design/native-backend.md 5). Linux x86-64 only for now; elsewhere there is
//! none, and the engine runs its closures.

/// Machine code in a sealed mapping of its own, unmapped when dropped.
pub struct Code {
    address: *mut u8,
    length: usize,
}

impl Code {
    /// Copies the bytes into a fresh mapping and seals it, or None where executable memory isn't
    /// available or the system refuses it.
    pub fn new(bytes: &[u8]) -> Option<Code> {
        if bytes.is_empty() {
            return None;
        }
        system::map(bytes.len()).and_then(|address| {
            let code = Code {
                address,
                length: bytes.len(),
            };
            // SAFETY: the mapping is fresh, writable and `length` bytes long, and nothing else
            // refers to it yet.
            unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), code.address, code.length) };
            system::seal(code.address, code.length).then_some(code)
        })
    }

    /// The address of the first byte, which a caller turns into a function of the signature the
    /// code was emitted for.
    pub fn entry(&self) -> *const u8 {
        self.address
    }
}

impl Drop for Code {
    fn drop(&mut self) {
        system::unmap(self.address, self.length);
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod system {
    use std::ffi::c_void;

    const PROT_READ: i32 = 1;
    const PROT_WRITE: i32 = 2;
    const PROT_EXEC: i32 = 4;
    const MAP_PRIVATE: i32 = 2;
    const MAP_ANONYMOUS: i32 = 0x20;

    // From the C library std already links.
    unsafe extern "C" {
        fn mmap(
            address: *mut c_void,
            length: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: i64,
        ) -> *mut c_void;
        fn mprotect(address: *mut c_void, length: usize, prot: i32) -> i32;
        fn munmap(address: *mut c_void, length: usize) -> i32;
    }

    pub(super) fn map(length: usize) -> Option<*mut u8> {
        // SAFETY: an anonymous private mapping at an address the kernel picks touches no memory
        // the program owns. MAP_FAILED is -1.
        let address = unsafe {
            mmap(
                std::ptr::null_mut(),
                length,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS,
                -1,
                0,
            )
        };
        (address as isize != -1).then_some(address.cast())
    }

    pub(super) fn seal(address: *mut u8, length: usize) -> bool {
        // SAFETY: the range is a mapping `map` made, so changing its protection affects nothing
        // else; x86-64's instruction cache needs no flush.
        unsafe { mprotect(address.cast(), length, PROT_READ | PROT_EXEC) == 0 }
    }

    pub(super) fn unmap(address: *mut u8, length: usize) {
        // SAFETY: the range is a mapping `map` made, and its `Code`, the only owner, is dropping.
        unsafe { munmap(address.cast(), length) };
    }
}

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
mod system {
    pub(super) fn map(_: usize) -> Option<*mut u8> {
        None
    }

    pub(super) fn seal(_: *mut u8, _: usize) -> bool {
        false
    }

    pub(super) fn unmap(_: *mut u8, _: usize) {}
}

#[cfg(all(test, target_os = "linux", target_arch = "x86_64"))]
mod tests {
    use super::Code;
    use crate::native::x86_64::{Assembler, Condition, Gpr, Memory, Scale, Width};

    #[test]
    fn runs_code_once_sealed() {
        // lea rax, [rdi + 1]; ret
        let code = Code::new(&[0x48, 0x8d, 0x47, 0x01, 0xc3]).expect("executable memory");
        // SAFETY: the bytes are a complete System V function of one integer argument.
        let increment: extern "C" fn(u64) -> u64 = unsafe { std::mem::transmute(code.entry()) };
        assert_eq!(increment(41), 42);
    }

    // Run alone by `refuses_writes_once_sealed`, in a process of its own, which the write kills.
    #[test]
    #[ignore = "faults by design; run as a child process"]
    fn writes_to_sealed_code() {
        let code = Code::new(&[0xc3]).expect("executable memory");
        // SAFETY: none; the write must fault, since the mapping is no longer writable.
        unsafe { code.entry().cast_mut().write_volatile(0x90) };
    }

    #[test]
    fn refuses_writes_once_sealed() {
        let status = std::process::Command::new(std::env::current_exe().expect("the test binary"))
            .args([
                "--exact",
                "native::memory::tests::writes_to_sealed_code",
                "--ignored",
            ])
            .args(["--test-threads", "1", "--nocapture"])
            .stderr(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .status()
            .expect("the child test");
        assert_eq!(
            std::os::unix::process::ExitStatusExt::signal(&status),
            Some(11)
        );
    }

    // The encoder's forms, run: a loop with both kinds of jump, indexed loads and a call out.
    #[test]
    fn runs_assembled_code() {
        // How many of `length` u32s at `values` equal `value`.
        let mut assembler = Assembler::new();
        let (top, skip, end) = (assembler.label(), assembler.label(), assembler.label());
        assembler.mov_immediate(Gpr::Rax, 0);
        assembler.mov_immediate(Gpr::Rcx, 0);
        assembler.bind(top);
        assembler.cmp(Width::W64, Gpr::Rcx, Gpr::Rsi);
        assembler.jump_if(Condition::AboveOrEqual, end);
        let element = Memory::indexed(Gpr::Rdi, Gpr::Rcx, Scale::Four, 0);
        assembler.cmp_memory(Width::W32, Gpr::Rdx, element);
        assembler.jump_if(Condition::NotEqual, skip);
        assembler.add_immediate(Width::W64, Gpr::Rax, 1);
        assembler.bind(skip);
        assembler.add_immediate(Width::W64, Gpr::Rcx, 1);
        assembler.jump(top);
        assembler.bind(end);
        assembler.ret();
        let code = Code::new(&assembler.finish()).expect("executable memory");
        // SAFETY: the bytes are a complete System V function of a pointer, a length and a u32,
        // which reads only the `length` u32s the pointer points at.
        let count: extern "C" fn(*const u32, u64, u32) -> u64 =
            unsafe { std::mem::transmute(code.entry()) };
        let values = [3, 1, 3, 3, 2];
        assert_eq!(count(values.as_ptr(), values.len() as u64, 3), 3);
        assert_eq!(count(values.as_ptr(), 0, 3), 0);

        // `callee(41) + 1`, keeping the stack 16-byte aligned across the call.
        extern "C" fn double(value: u64) -> u64 {
            value * 2
        }
        let mut assembler = Assembler::new();
        assembler.push(Gpr::Rbx);
        assembler.mov(Width::W64, Gpr::Rax, Gpr::Rdi);
        assembler.mov_immediate(Gpr::Rdi, 41);
        assembler.call(Gpr::Rax);
        assembler.lea(Gpr::Rax, Memory::at(Gpr::Rax, 1));
        assembler.pop(Gpr::Rbx);
        assembler.ret();
        let code = Code::new(&assembler.finish()).expect("executable memory");
        // SAFETY: the bytes are a complete System V function of one function pointer, which it
        // calls with one integer argument.
        let call: extern "C" fn(extern "C" fn(u64) -> u64) -> u64 =
            unsafe { std::mem::transmute(code.entry()) };
        assert_eq!(call(double), 83);
    }

    #[test]
    fn maps_no_empty_code() {
        assert!(Code::new(&[]).is_none());
    }
}
