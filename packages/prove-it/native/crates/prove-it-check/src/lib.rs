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
pub mod host_path;
mod inflate;
mod jar;
mod messages;
mod outcome;
mod plain;
pub mod resolve;
mod simulation;
mod stack;
mod summary;
mod te_spec;
mod time;
mod trace;
mod xml_exporter;
mod zip;
pub mod zone;

pub use check::run;
pub use files::FileDescriber;
pub use host::{FileDescription, FileKind, Files, Host, Machine, SystemHost, is_directory_there};
pub use messages::Output;
pub use outcome::{Counts, Outcome, Reported, ReportedState, Thrown};
pub use plain::Variable;
pub use zone::Zone;
