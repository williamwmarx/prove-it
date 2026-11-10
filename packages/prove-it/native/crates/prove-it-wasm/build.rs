// WebAssembly has one thread, so the search and deeply nested values run on the module's stack,
// which the linker sets: as deep as the search thread's in a release build of the addon would
// cost every instance that much memory, so it is a quarter of it.
fn main() {
    if std::env::var("CARGO_CFG_TARGET_ARCH").as_deref() == Ok("wasm32") {
        println!(
            "cargo:rustc-link-arg-cdylib=-zstack-size={}",
            64 * 1024 * 1024
        );
    }
}
