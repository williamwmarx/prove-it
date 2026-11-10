//! The native `prove-it` binary (native/DESIGN.md 13): checks a TLA+ spec as the TypeScript CLI
//! does and prints exactly what TLC prints.

mod args;
mod check;
mod failure;
mod files;
mod front;
mod messages;
mod summary;
mod time;
mod trace;
mod zone;

/// The stack of the run's thread: the front end recurses as deep as TLC's translation of a
/// formula does before it reports TLC's stack overflow, which a main thread's stack, 1 MiB on
/// Windows, doesn't hold.
const RUN_STACK_BYTES: usize = 64 * 1024 * 1024;

fn main() {
    let args: Vec<String> = std::env::args_os()
        .skip(1)
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect();
    let status = std::thread::Builder::new()
        .stack_size(RUN_STACK_BYTES)
        .spawn(move || check::run(&args))
        .expect("a thread for the run")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
    std::process::exit(status);
}
