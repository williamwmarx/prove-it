//! The check TLC's command line asks for (native/DESIGN.md 13): the front end, the engine, and the
//! trace and liveness printers, writing what TLC prints to an `Output`. The `prove-it` binary runs
//! it on stdout and stderr.

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

pub use check::run;
pub use messages::Output;
