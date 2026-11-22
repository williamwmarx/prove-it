//! The native `prove-it` binary (native/DESIGN.md 13): checks a TLA+ spec as the TypeScript CLI
//! does and prints exactly what TLC prints.

mod pages;

use prove_it_check::{Outcome, Output, SystemHost};

/// The stack of the run's thread: the front end recurses as deep as TLC's translation of a
/// formula does before it reports TLC's stack overflow or declines, which a main thread's stack,
/// 1 MiB on Windows, doesn't hold; its level analysis of a chain of 2,250 definitions, where the
/// expansion of a formula through them declines, takes more than 64 MiB in a debug build. It is
/// reserved, not committed, as the search's is.
const RUN_STACK_BYTES: usize = 256 * 1024 * 1024;

fn main() {
    let args: Vec<String> = std::env::args_os()
        .skip(1)
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect();
    // A user who stops the run while its output is held gets what TLC would have printed.
    prove_it_check::flush_held_on_interrupt();
    let status = std::thread::Builder::new()
        .stack_size(RUN_STACK_BYTES)
        .spawn(move || {
            let (mut out, mut err) = (std::io::stdout(), std::io::stderr());
            prove_it_check::run(
                &args,
                &mut Output {
                    out: &mut out,
                    err: &mut err,
                    host: &SystemHost::new(pages::LARGE_REGION_ADVICE),
                    outcome: Outcome::default(),
                },
            )
        })
        .expect("a thread for the run")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
    std::process::exit(status);
}
