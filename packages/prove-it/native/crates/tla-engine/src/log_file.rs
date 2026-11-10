//! The file the search writes its state log to. WebAssembly has no files of its own, so there the
//! host writes what the search hands it.

use std::io::Write;

/// A writer of the file at `path`, which it creates, or `None` where it can't.
#[cfg(not(target_arch = "wasm32"))]
pub fn create(path: &str) -> Option<impl Write> {
    let file = std::fs::File::create(path).ok()?;
    Some(std::io::BufWriter::with_capacity(1 << 20, file))
}

/// A writer of the file at `path`, which the host creates as it takes the first bytes.
#[cfg(target_arch = "wasm32")]
pub fn create(path: &str) -> Option<impl Write> {
    Some(HostFile {
        path: path.to_owned(),
        is_created: false,
    })
}

#[cfg(target_arch = "wasm32")]
struct HostFile {
    path: String,
    is_created: bool,
}

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "env")]
unsafe extern "C" {
    /// Writes bytes to the file the path names, creating it unless `is_appended` is 1.
    fn prove_it_write(
        path: *const u8,
        path_length: usize,
        bytes: *const u8,
        length: usize,
        is_appended: u32,
    );
}

#[cfg(target_arch = "wasm32")]
impl Write for HostFile {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        let path = self.path.as_bytes();
        let is_appended = u32::from(self.is_created);
        unsafe {
            prove_it_write(
                path.as_ptr(),
                path.len(),
                bytes.as_ptr(),
                bytes.len(),
                is_appended,
            )
        };
        self.is_created = true;
        Ok(bytes.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
