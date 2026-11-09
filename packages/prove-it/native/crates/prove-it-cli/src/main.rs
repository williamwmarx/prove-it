//! The native `prove-it` binary (native/DESIGN.md 13): checks a TLA+ spec as the TypeScript CLI
//! does and prints exactly what TLC prints.

mod args;
mod check;
// HACK: the search reports a run-time error stop to print (`ViolationKind::Error`) once the
// gaps session lands it; until then nothing calls the module.
#[allow(dead_code)]
mod failure;
mod front;
mod messages;
mod summary;
mod time;
mod trace;
mod zone;

fn main() {
    let args: Vec<String> = std::env::args_os()
        .skip(1)
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect();
    std::process::exit(check::run(&args));
}
