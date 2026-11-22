//! A native decline is a decision not to run: hold a run's output until that decision is known.
//! Nested scopes isolate each specification in a batch. A scope records declines explicitly,
//! rather than inferring them from an exit code or from the contents of stderr.
//!
//! The engine can decline at any point of a search, so no run is known to be native before it
//! ends. TLC prints each line as it goes, though, and a check runs until it finishes or the user
//! stops it: a user watching a long check must see its progress, and stopping it must leave what
//! TLC would have printed so far. So the hold lasts [`HOLD`] from the start of the outermost
//! scope. After that every scope streams, and a later decline follows what was printed, as the
//! binary did before it held its output.

use std::cell::{Cell, RefCell};
use std::io::{self, Write};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use tla_engine::clock::Instant;

use crate::messages::Output;

/// How long a run's output is held back before it streams. A decline within it prints nothing
/// but the decline; the front end and the startup take milliseconds, as most declining searches do.
const HOLD: Duration = Duration::from_secs(2);

enum Decline {
    Message(String),
    Thrown,
}

#[derive(Default)]
struct ScopeState {
    decline: Option<Decline>,
}

thread_local! {
    static DECLINES: RefCell<Vec<ScopeState>> = const { RefCell::new(Vec::new()) };
    /// When the outermost scope started to hold its output, until the hold ends.
    static HELD_SINCE: Cell<Option<Instant>> = const { Cell::new(None) };
    /// How many lowerings of a model are under way, through which output is held however long
    /// they take.
    static LOWERING: Cell<u32> = const { Cell::new(0) };
}

#[cfg(test)]
thread_local! {
    /// Whether a lowering ends past the hold, as a slow one does, for the tests.
    static IS_LOWERING_SLOW: Cell<bool> = const { Cell::new(false) };
}

/// Runs `lower`, the front end's lowering of a model, with the run's output held however long it
/// takes: the front end declines as it lowers, before the search prints anything of its own, so
/// a decline there never follows what the run printed. The hold then lasts as it would have, so
/// output streams at the first write once [`HOLD`] has passed.
pub(crate) fn holding_through<T>(lower: impl FnOnce() -> T) -> T {
    struct Lowering;
    impl Drop for Lowering {
        fn drop(&mut self) {
            LOWERING.with(|lowering| lowering.set(lowering.get() - 1));
        }
    }
    LOWERING.with(|lowering| lowering.set(lowering.get() + 1));
    let _lowering = Lowering;
    let lowered = lower();
    #[cfg(test)]
    if IS_LOWERING_SLOW.with(Cell::get) {
        let past = Instant::now()
            .checked_sub(HOLD)
            .expect("a moment before the hold");
        HELD_SINCE.with(|since| since.set(Some(past)));
    }
    lowered
}

struct Scope {
    active: bool,
}

impl Scope {
    fn new() -> Self {
        DECLINES.with(|stack| {
            let mut stack = stack.borrow_mut();
            if stack.is_empty() {
                HELD_SINCE.with(|since| since.set(Some(Instant::now())));
            }
            stack.push(ScopeState::default());
        });
        Self { active: true }
    }

    fn finish(mut self) -> ScopeState {
        self.active = false;
        pop()
    }
}

fn pop() -> ScopeState {
    DECLINES.with(|stack| {
        let mut stack = stack.borrow_mut();
        let state = stack.pop().unwrap_or_default();
        if stack.is_empty() {
            HELD_SINCE.with(|since| since.set(None));
        }
        state
    })
}

impl Drop for Scope {
    fn drop(&mut self) {
        if self.active {
            pop();
        }
    }
}

/// How much longer output is held, or `None` where it streams already.
pub(crate) fn get_hold_left() -> Option<Duration> {
    // WebAssembly hands the output over only as the run ends.
    if cfg!(target_arch = "wasm32") {
        return None;
    }
    if LOWERING.with(Cell::get) > 0 {
        return HELD_SINCE.with(Cell::get).map(|_| HOLD);
    }
    HELD_SINCE
        .with(Cell::get)
        .map(|since| HOLD.saturating_sub(since.elapsed()))
        .filter(|left| !left.is_zero())
}

// Whether output streams now: true once the hold has lasted [`HOLD`], from then on, unless the
// run has declined before it streamed, whose output then goes with the decline, however late.
fn is_streaming() -> bool {
    if cfg!(target_arch = "wasm32") {
        return false;
    }
    if LOWERING.with(Cell::get) > 0
        || DECLINES.with(|stack| {
            stack
                .borrow()
                .last()
                .is_some_and(|scope| scope.decline.is_some())
        })
    {
        return false;
    }
    match HELD_SINCE.with(Cell::get) {
        Some(since) => since.elapsed() >= HOLD,
        None => false,
    }
}

pub(crate) fn mark_declined(reason: &str) {
    DECLINES.with(|stack| {
        if let Some(current) = stack.borrow_mut().last_mut() {
            current.decline = Some(Decline::Message(reason.to_string()));
        }
    });
}

pub(crate) fn mark_thrown() {
    DECLINES.with(|stack| {
        if let Some(current) = stack.borrow_mut().last_mut() {
            current.decline = Some(Decline::Thrown);
        }
    });
}

// The CLI does not retain prints in Outcome. Spill a long run's provisional output to a private
// temporary file rather than making its memory proportional to the transcript. Hosts that cannot
// create a temporary file, including WebAssembly, keep the bytes in memory instead. Once the hold
// ends, the spool hands what it holds to `parent` and passes everything after it straight on.
//
// What a spool holds sits where the binary's interrupt handler finds it
// (`flush_held_on_interrupt`): a user who stops a run while the hold lasts gets what TLC would
// have printed so far, as after it.
struct Spool<'p> {
    parent: &'p mut dyn Write,
    is_streaming: bool,
    held: Arc<Mutex<Held>>,
}

// The bytes a spool holds, in memory or in its temporary file, and whether they are the run's
// standard error.
#[derive(Default)]
struct Held {
    #[cfg(unix)]
    is_error: bool,
    memory: Vec<u8>,
    #[cfg(not(target_arch = "wasm32"))]
    file: Option<(std::fs::File, std::path::PathBuf)>,
}

impl Held {
    // Writes what it holds to `out`, and empties it, removing its temporary file.
    fn drain(&mut self, out: &mut dyn Write) -> io::Result<()> {
        #[cfg(not(target_arch = "wasm32"))]
        if let Some((mut file, path)) = self.file.take() {
            use std::io::{Seek, SeekFrom};
            let copied = file
                .flush()
                .and_then(|()| file.seek(SeekFrom::Start(0)))
                .and_then(|_| io::copy(&mut file, out));
            drop(file);
            let _ = std::fs::remove_file(path);
            copied?;
        }
        let held = std::mem::take(&mut self.memory);
        out.write_all(&held)
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn discard(&mut self) {
        if let Some((file, path)) = self.file.take() {
            drop(file);
            let _ = std::fs::remove_file(path);
        }
    }
}

/// The spools that hold output, outermost first, which an interrupt prints in that order: an
/// inner scope's spool takes every write while it lasts, and hands what it holds to the spool
/// around it only as it ends.
static SPOOLS: Mutex<Vec<Arc<Mutex<Held>>>> = Mutex::new(Vec::new());

/// Held while a spool changes, so the interrupt handler sees no write half done.
static SPOOLING: Mutex<()> = Mutex::new(());

thread_local! {
    static SPOOLING_DEPTH: Cell<u32> = const { Cell::new(0) };
}

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

// Runs a change to the spools, holding `SPOOLING`; a spool that writes to the spool around it
// changes both in one hold.
fn spooling<R>(change: impl FnOnce() -> R) -> R {
    struct Depth;
    impl Drop for Depth {
        fn drop(&mut self) {
            SPOOLING_DEPTH.with(|depth| depth.set(depth.get() - 1));
        }
    }
    let outer = SPOOLING_DEPTH.with(|depth| {
        let outer = depth.get();
        depth.set(outer + 1);
        outer
    });
    let _depth = Depth;
    let _guard = (outer == 0).then(|| lock(&SPOOLING));
    change()
}

impl<'p> Spool<'p> {
    #[cfg(not(target_arch = "wasm32"))]
    const MEMORY_LIMIT: usize = 4 * 1024 * 1024;

    fn new(parent: &'p mut dyn Write, is_error: bool) -> Self {
        #[cfg(unix)]
        let held = Held {
            is_error,
            ..Held::default()
        };
        #[cfg(not(unix))]
        let held = {
            let _ = is_error;
            Held::default()
        };
        let held = Arc::new(Mutex::new(held));
        spooling(|| lock(&SPOOLS).push(Arc::clone(&held)));
        Self {
            parent,
            is_streaming: false,
            held,
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    fn spill(held: &mut Held) {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        for _ in 0..32 {
            let id = NEXT.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("prove-it-output-{}-{id}", std::process::id()));
            let mut options = std::fs::OpenOptions::new();
            options.read(true).write(true).create_new(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt;
                options.mode(0o600);
            }
            match options.open(&path) {
                Ok(mut file) => {
                    if file.write_all(&held.memory).is_ok() {
                        held.memory.clear();
                        held.file = Some((file, path));
                    } else {
                        drop(file);
                        let _ = std::fs::remove_file(path);
                    }
                    return;
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(_) => return,
            }
        }
    }

    /// Hands what the spool holds to `parent`, and empties it.
    fn commit(&mut self) -> io::Result<()> {
        spooling(|| lock(&self.held).drain(self.parent))
    }

    // Starts to stream once the hold is over, with what the spool held first.
    fn is_streamed(&mut self) -> io::Result<bool> {
        if !self.is_streaming && is_streaming() {
            self.is_streaming = true;
            self.commit()?;
        }
        Ok(self.is_streaming)
    }

    fn hold(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let mut held = lock(&self.held);
        #[cfg(not(target_arch = "wasm32"))]
        {
            if held.file.is_none()
                && held.memory.len().saturating_add(bytes.len()) > Self::MEMORY_LIMIT
            {
                Self::spill(&mut held);
            }
            if let Some((file, _)) = &mut held.file {
                match file.write(bytes) {
                    Ok(written) => return Ok(written),
                    Err(_) => {
                        // An exhausted temporary filesystem must not turn a supported run into a
                        // decline. Recover the bytes already staged and continue in memory.
                        use std::io::{Read, Seek, SeekFrom};
                        file.seek(SeekFrom::Start(0))?;
                        let mut recovered = Vec::new();
                        file.read_to_end(&mut recovered)?;
                        held.discard();
                        held.memory = recovered;
                    }
                }
            }
        }
        held.memory.extend_from_slice(bytes);
        Ok(bytes.len())
    }
}

impl Write for Spool<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        spooling(|| {
            if self.is_streamed()? {
                return self.parent.write(bytes);
            }
            self.hold(bytes)
        })
    }

    fn flush(&mut self) -> io::Result<()> {
        spooling(|| {
            if self.is_streamed()? {
                return self.parent.flush();
            }
            #[cfg(not(target_arch = "wasm32"))]
            if let Some((file, _)) = &mut lock(&self.held).file {
                return file.flush();
            }
            Ok(())
        })
    }
}

impl Drop for Spool<'_> {
    fn drop(&mut self) {
        spooling(|| {
            lock(&SPOOLS).retain(|held| !Arc::ptr_eq(held, &self.held));
            #[cfg(not(target_arch = "wasm32"))]
            lock(&self.held).discard();
        });
    }
}

/// Prints what the spools hold to the process's standard output and error, outermost first, and
/// leaves `SPOOLING` held, so that nothing changes them after: for the binary's interrupt handler,
/// which then ends the process. Each write it makes counts its bytes in `printed`, so the handler
/// can tell a print that goes on from one that waits.
#[cfg(unix)]
fn print_held(printed: &std::sync::atomic::AtomicU64) {
    // Counts what passes through to the process's output.
    struct Counted<'a, W: Write>(W, &'a std::sync::atomic::AtomicU64);
    impl<W: Write> Write for Counted<'_, W> {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            let written = self.0.write(bytes)?;
            self.1
                .fetch_add(written as u64, std::sync::atomic::Ordering::Relaxed);
            Ok(written)
        }
        fn flush(&mut self) -> io::Result<()> {
            self.0.flush()
        }
    }
    let guard = lock(&SPOOLING);
    let spools = lock(&SPOOLS);
    for is_error in [false, true] {
        for held in spools.iter() {
            let mut held = lock(held);
            if held.is_error != is_error {
                continue;
            }
            let _ = if is_error {
                held.drain(&mut Counted(io::stderr().lock(), printed))
            } else {
                held.drain(&mut Counted(io::stdout().lock(), printed))
            };
        }
    }
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::mem::forget(guard);
}

/// Has an interrupt (SIGINT) or a termination request (SIGTERM) first print what the run holds,
/// as TLC, which prints each line as it goes, has printed it by then, and then end the process
/// as the signal does by default. The binary calls this once, before the run, whose standard
/// output and error are the process's.
#[cfg(unix)]
pub fn flush_held_on_interrupt() {
    use std::io::Read;
    use std::os::unix::io::AsRawFd;
    use std::os::unix::net::UnixStream;
    use std::sync::atomic::{AtomicI32, Ordering};

    const SIGINT: i32 = 2;
    const SIGTERM: i32 = 15;
    const SIG_DFL: usize = 0;
    static NOTIFY: AtomicI32 = AtomicI32::new(-1);

    unsafe extern "C" {
        fn signal(signal: i32, handler: usize) -> usize;
        fn raise(signal: i32) -> i32;
        fn write(descriptor: i32, bytes: *const std::ffi::c_void, length: usize) -> isize;
    }

    // Runs in the signal's context: it only writes the signal's number to the watcher's socket,
    // which `write` may do there.
    extern "C" fn on_signal(number: i32) {
        let descriptor = NOTIFY.load(Ordering::Relaxed);
        if descriptor >= 0 {
            let byte = number as u8;
            // SAFETY: `write` is async-signal-safe, and the byte outlives the call.
            unsafe {
                write(descriptor, (&raw const byte).cast(), 1);
            }
        }
    }

    let Ok((sender, mut receiver)) = UnixStream::pair() else {
        return;
    };
    NOTIFY.store(sender.as_raw_fd(), Ordering::Relaxed);
    // The sender stays open for the process's life, for the handler.
    std::mem::forget(sender);
    let watcher = std::thread::Builder::new()
        .name("interrupt".into())
        .spawn(move || {
            let mut number = [0u8];
            if receiver.read_exact(&mut number).is_err() {
                return;
            }
            // The run's own thread may be blocked writing to an output nobody reads, holding
            // `SPOOLING` or the output's lock, and the print may block on such an output too.
            // TLC's process ends on the signal whatever it is writing, as the binary did before
            // it held its output, so the print runs on a thread of its own, and the process ends
            // once it is done or as soon as it has printed nothing for a while.
            let printed = Arc::new(std::sync::atomic::AtomicU64::new(0));
            let (done, is_done) = std::sync::mpsc::channel::<()>();
            let printer = Arc::clone(&printed);
            let printing = std::thread::Builder::new()
                .name("interrupt-print".into())
                .spawn(move || {
                    print_held(&printer);
                    let _ = done.send(());
                });
            if printing.is_ok() {
                let mut seen = 0;
                while let Err(std::sync::mpsc::RecvTimeoutError::Timeout) =
                    is_done.recv_timeout(Duration::from_secs(1))
                {
                    let now = printed.load(Ordering::Relaxed);
                    if now == seen {
                        break;
                    }
                    seen = now;
                }
            }
            // SAFETY: restoring the default action and raising the signal again ends the
            // process as the signal would have without the handler.
            unsafe {
                signal(i32::from(number[0]), SIG_DFL);
                raise(i32::from(number[0]));
            }
        });
    if watcher.is_err() {
        return;
    }
    const SIG_IGN: usize = 1;
    let handler = on_signal as extern "C" fn(i32) as usize;
    for number in [SIGINT, SIGTERM] {
        // SAFETY: the handler only calls `write`, which is async-signal-safe. A signal the
        // process was started ignoring, as a shell starts a background job ignoring SIGINT,
        // stays ignored.
        unsafe {
            if signal(number, handler) == SIG_IGN {
                signal(number, SIG_IGN);
            }
        }
    }
}

#[cfg(not(unix))]
pub fn flush_held_on_interrupt() {}

pub(crate) fn run(output: &mut Output<'_>, action: impl FnOnce(&mut Output<'_>) -> i32) -> i32 {
    run_scoped(output, action).0
}

/// Runs `action` in a scope of its own: its exit code, whether it declined, and whether it
/// printed anything (what streamed before a decline, or all of a run that didn't decline).
pub(crate) fn run_scoped(
    output: &mut Output<'_>,
    action: impl FnOnce(&mut Output<'_>) -> i32,
) -> (i32, bool, bool) {
    let scope = Scope::new();
    let written = tla_values::written::mark();
    let mut stdout = Spool::new(&mut *output.out, false);
    let mut stderr = Spool::new(&mut *output.err, true);
    let mut staged = Output {
        out: &mut stdout,
        err: &mut stderr,
        host: output.host,
        outcome: output.outcome.clone(),
    };
    let status = action(&mut staged);
    let outcome = staged.outcome;
    let scope = scope.finish();
    let is_streamed = stdout.is_streaming || stderr.is_streaming;
    // A run that declines hands the model to another checker, which must find the files as the
    // run found them. One that doesn't lets go of what it kept, unless an outer scope may still
    // decline and put back what it wrote.
    let unrestored = match scope.decline {
        Some(_) => tla_values::written::restore(written),
        None => {
            tla_values::written::release(written);
            Vec::new()
        }
    };
    // A decline that leaves a file otherwise than the run found it isn't one another checker may
    // take up: it says what it couldn't put back, and not that it declined.
    if let (Some(decline), false) = (&scope.decline, unrestored.is_empty()) {
        let reason = match decline {
            Decline::Message(reason) => reason.as_str(),
            Decline::Thrown => "a decline of the host's",
        };
        for failure in &unrestored {
            let _ = writeln!(
                stderr.parent,
                "prove-it: a run that wasn't native ({reason}) couldn't put back {} as it found it: {}",
                failure.path.display(),
                failure.error
            );
        }
        return (status, false, true);
    }
    match &scope.decline {
        // What streamed stays, as TLC printed it, the decline's own note among it; what is held
        // goes with the decline.
        Some(Decline::Message(_)) if stderr.is_streaming => {}
        Some(Decline::Message(reason)) => {
            let _ = writeln!(stderr.parent, "prove-it: not native yet: {reason}");
        }
        Some(Decline::Thrown) => {
            // SourcesHost communicates this decline through Outcome rather than stderr.
            output.outcome = outcome;
        }
        None => {
            let _ = stdout.commit();
            let _ = stderr.commit();
            output.outcome = outcome;
        }
    }
    (
        status,
        scope.decline.is_some(),
        is_streamed || scope.decline.is_none(),
    )
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use super::{Spool, mark_declined, run};
    use crate::{Outcome, Output, SystemHost};

    #[test]
    fn nested_decline_drops_only_that_specs_output() {
        let host = SystemHost::new(None);
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let mut output = Output {
            out: &mut stdout,
            err: &mut stderr,
            host: &host,
            outcome: Outcome::default(),
        };
        let status = run(&mut output, |outer| {
            writeln!(outer.out, "first").unwrap();
            let child = run(outer, |inner| {
                writeln!(inner.out, "discard").unwrap();
                writeln!(inner.err, "discard diagnostic").unwrap();
                mark_declined("unsupported model");
                1
            });
            assert_eq!(child, 1);
            writeln!(outer.out, "third").unwrap();
            1
        });
        assert_eq!(status, 1);
        assert_eq!(stdout, b"first\nthird\n");
        assert_eq!(stderr, b"prove-it: not native yet: unsupported model\n");
    }

    #[test]
    fn error_exit_and_diagnostic_text_do_not_imply_decline() {
        let host = SystemHost::new(None);
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let mut output = Output {
            out: &mut stdout,
            err: &mut stderr,
            host: &host,
            outcome: Outcome::default(),
        };
        let status = run(&mut output, |inner| {
            writeln!(inner.out, "TLC error").unwrap();
            writeln!(inner.err, "prove-it: not native yet: text from an error").unwrap();
            1
        });
        assert_eq!(status, 1);
        assert_eq!(stdout, b"TLC error\n");
        assert_eq!(stderr, b"prove-it: not native yet: text from an error\n");
    }

    #[test]
    fn source_host_thrown_decline_remains_typed_without_output() {
        let host = SystemHost::new(None);
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let mut output = Output {
            out: &mut stdout,
            err: &mut stderr,
            host: &host,
            outcome: Outcome::default(),
        };
        let status = run(&mut output, |outer| {
            let (status, declined, _) = super::run_scoped(outer, |inner| {
                writeln!(inner.out, "discard").unwrap();
                inner.outcome.thrown = Some(crate::Thrown::NotNative("source uncertainty"));
                super::mark_thrown();
                1
            });
            assert!(declined);
            status
        });
        assert_eq!(status, 1);
        assert!(matches!(
            output.outcome.thrown,
            Some(crate::Thrown::NotNative("source uncertainty"))
        ));
        assert!(stdout.is_empty());
        assert!(stderr.is_empty());
    }

    // A decline that can't put back a file it wrote says so, and doesn't decline: another checker
    // must not take up the model over files the run changed.
    #[cfg(unix)]
    #[test]
    fn a_decline_that_cannot_put_a_file_back_says_so() {
        let directory =
            std::env::temp_dir().join(format!("prove-it-unrestored-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).unwrap();
        let file = directory.join("out");
        let host = SystemHost::new(None);
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let mut output = Output {
            out: &mut stdout,
            err: &mut stderr,
            host: &host,
            outcome: Outcome::default(),
        };
        let (status, declined, printed) = super::run_scoped(&mut output, |inner| {
            tla_values::written::keep_file(&file).unwrap();
            // What the run made there, `remove_file` can't take away.
            std::fs::create_dir(&file).unwrap();
            writeln!(inner.out, "discard").unwrap();
            mark_declined("unsupported model");
            1
        });
        let _ = std::fs::remove_dir_all(&directory);
        assert_eq!((status, declined, printed), (1, false, true));
        assert!(stdout.is_empty());
        let stderr = String::from_utf8(stderr).unwrap();
        assert!(!stderr.contains("not native yet: "), "{stderr}");
        assert!(
            stderr.starts_with(
                "prove-it: a run that wasn't native (unsupported model) couldn't put back "
            ),
            "{stderr}"
        );
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn large_output_spills_and_removes_its_temporary_file() {
        let mut output = Vec::new();
        let mut spool = Spool::new(&mut output, false);
        let content = vec![b'x'; Spool::MEMORY_LIMIT + 1];
        spool.write_all(&content).unwrap();
        let path = spool
            .held
            .lock()
            .unwrap()
            .file
            .as_ref()
            .map(|(_, path)| path.clone());
        spool.commit().unwrap();
        if let Some(path) = &path {
            assert!(!path.exists());
        }
        drop(spool);
        assert_eq!(output, content);
    }

    // A model whose lowering declines, and takes longer than the hold, prints the decline alone:
    // the check reports it once the lowering has returned.
    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn a_slow_lowering_that_declines_prints_the_decline_alone() {
        let directory = std::env::temp_dir().join(format!("hold-lowering-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            directory.join("M.tla"),
            "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====\n",
        )
        .unwrap();
        std::fs::write(
            directory.join("M.cfg"),
            "INIT Init\nNEXT Next\nINVARIANT Nat\n",
        )
        .unwrap();
        let host = SystemHost::new(None);
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let mut output = Output {
            out: &mut stdout,
            err: &mut stderr,
            host: &host,
            outcome: Outcome::default(),
        };
        super::IS_LOWERING_SLOW.with(|slow| slow.set(true));
        let args = [
            "-workers".to_owned(),
            "1".to_owned(),
            directory.join("M.tla").to_string_lossy().into_owned(),
        ];
        let status = crate::check::run(&args, &mut output);
        super::IS_LOWERING_SLOW.with(|slow| slow.set(false));
        std::fs::remove_dir_all(&directory).unwrap();
        assert_eq!(status, 1, "{}", String::from_utf8_lossy(&stderr));
        assert_eq!(String::from_utf8_lossy(&stdout), "");
        assert_eq!(
            String::from_utf8_lossy(&stderr),
            "prove-it: not native yet: a name the configuration gives that is an operator of a standard module\n"
        );
    }

    // A lowering holds the output past the hold's end, so a decline in it prints nothing else.
    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn a_decline_as_the_model_lowers_prints_nothing_however_long_it_takes() {
        let host = SystemHost::new(None);
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let mut output = Output {
            out: &mut stdout,
            err: &mut stderr,
            host: &host,
            outcome: Outcome::default(),
        };
        let (status, declined, printed) = super::run_scoped(&mut output, |inner| {
            writeln!(inner.out, "held").unwrap();
            super::holding_through(|| {
                let past = tla_engine::clock::Instant::now()
                    .checked_sub(super::HOLD)
                    .expect("a moment before the hold");
                super::HELD_SINCE.with(|since| since.set(Some(past)));
                assert!(super::get_hold_left().is_some());
                writeln!(inner.out, "still held").unwrap();
                mark_declined("unsupported model");
                writeln!(inner.err, "prove-it: not native yet: unsupported model").unwrap();
            });
            1
        });
        assert_eq!((status, declined, printed), (1, true, false));
        assert_eq!(stdout, b"");
        assert_eq!(stderr, b"prove-it: not native yet: unsupported model\n");
    }

    // After the hold, what was held and everything after it goes straight through, and a decline
    // follows what streamed.
    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn output_streams_after_the_hold_and_a_later_decline_follows_it() {
        let host = SystemHost::new(None);
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let mut output = Output {
            out: &mut stdout,
            err: &mut stderr,
            host: &host,
            outcome: Outcome::default(),
        };
        let (status, declined, printed) = super::run_scoped(&mut output, |inner| {
            writeln!(inner.out, "held").unwrap();
            assert!(super::get_hold_left().is_some());
            let past = tla_engine::clock::Instant::now()
                .checked_sub(super::HOLD)
                .expect("a moment before the hold");
            super::HELD_SINCE.with(|since| since.set(Some(past)));
            assert!(super::get_hold_left().is_none());
            writeln!(inner.out, "streamed").unwrap();
            mark_declined("unsupported model");
            writeln!(inner.err, "prove-it: not native yet: unsupported model").unwrap();
            1
        });
        assert_eq!((status, declined, printed), (1, true, true));
        assert_eq!(stdout, b"held\nstreamed\n");
        assert_eq!(stderr, b"prove-it: not native yet: unsupported model\n");
        assert!(super::HELD_SINCE.with(std::cell::Cell::get).is_none());
    }
}
