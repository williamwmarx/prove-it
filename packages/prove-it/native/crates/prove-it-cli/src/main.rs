//! The native `prove-it` binary (native/DESIGN.md 13): checks a TLA+ spec as the TypeScript CLI
//! does and prints exactly what TLC prints.

mod pages;

use prove_it_check::{Outcome, Output, RUN_STACK_BYTES, SystemHost};

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
