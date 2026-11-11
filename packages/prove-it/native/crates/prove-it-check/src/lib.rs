//! The check TLC's command line asks for (native/DESIGN.md 13): the front end, the engine, and the
//! trace and liveness printers, writing what TLC prints to an `Output`. The `prove-it` binary runs
//! it on stdout and stderr.

mod args;
mod check;
mod coverage;
mod dump_trace;
mod failure;
mod files;
mod front;
mod host;
mod inflate;
mod jar;
mod messages;
mod stack;
mod summary;
mod time;
mod trace;
mod xml_exporter;
mod zip;
pub mod zone;

pub use check::run;
pub use host::{FileDescription, Files, Host, Machine, SystemHost};
pub use messages::Output;
pub use zone::Zone;
