//! A pool of threads the search keeps alive from the first level it shares to its end, so that a
//! level's rounds of work, its expansion, the state table's fill and the copy of its new states,
//! don't each start and join their threads: starting a thread costs tens of microseconds, and a
//! level makes six or seven rounds of them.
//!
//! A round gives each thread one job, or a few, and waits for every job to finish, as
//! `std::thread::scope` would, so a job may borrow what the round's caller holds: the jobs are
//! posted within a [`Pool::scope`], which joins every job before it returns, and a pool runs one
//! scope, and one round of it, at a time. Between rounds a thread spins briefly, since the rounds
//! of one level follow each other closely, and then parks until the next.

use std::cell::Cell;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, TryLockError};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// How long a thread spins for the next round before it parks: the rounds of one level follow
/// each other within this, and a thread that spins longer takes a core from the search's own
/// thread, which does the level's serial work between rounds.
const SPIN: Duration = Duration::from_micros(50);

type Job = Box<dyn FnOnce() + Send + 'static>;
/// Where a job leaves what it gave, or its panic.
type Slot<R> = Arc<Mutex<Option<std::thread::Result<R>>>>;

#[derive(Default)]
struct Posted {
    /// The jobs of the round, job `i` taken by thread `i % threads`; `None` once taken.
    jobs: Vec<Option<Job>>,
    is_stopping: bool,
}

struct Shared {
    posted: Mutex<Posted>,
    /// Which round `posted` holds, so a thread knows one it hasn't seen without the lock.
    number: AtomicU64,
    is_posted: Condvar,
    /// How many jobs of the current round are done; the caller waits for all of them.
    done: AtomicUsize,
    finished: Condvar,
    finished_lock: Mutex<()>,
}

pub struct Pool {
    shared: Arc<Shared>,
    threads: Vec<JoinHandle<()>>,
    /// Held by the scope that uses the pool, so that no two overlap.
    scoped: Mutex<()>,
}

impl Pool {
    /// Starts `threads` threads, each with a stack of `stack_bytes`.
    pub fn new(threads: usize, stack_bytes: usize) -> Self {
        let shared = Arc::new(Shared {
            posted: Mutex::new(Posted::default()),
            number: AtomicU64::new(0),
            is_posted: Condvar::new(),
            done: AtomicUsize::new(0),
            finished: Condvar::new(),
            finished_lock: Mutex::new(()),
        });
        let threads = (0..threads)
            .map(|index| {
                let shared = shared.clone();
                std::thread::Builder::new()
                    .stack_size(stack_bytes)
                    .spawn(move || serve(&shared, index, threads))
                    .expect("a thread for the search")
            })
            .collect();
        Self {
            shared,
            threads,
            scoped: Mutex::new(()),
        }
    }

    pub fn threads(&self) -> usize {
        self.threads.len()
    }

    /// Runs the jobs, job `i` on thread `i % threads`, and returns what each gave, in order, once
    /// every job is done. A job that panics makes this panic, after the round's other jobs are
    /// done. The jobs may borrow from the caller: none outlives this call.
    pub fn run<'env, R, F>(&self, jobs: impl IntoIterator<Item = F>) -> Vec<R>
    where
        R: Send + 'env,
        F: FnOnce() -> R + Send + 'env,
    {
        self.scope(|scope| scope.run(jobs))
    }

    /// Runs `f` with a scope that posts rounds of jobs to the pool, as `std::thread::scope` does
    /// with threads: every job is done before this returns, so a job may borrow anything that
    /// outlives the call, and a borrow of a value made inside `f` is rejected. A pool runs one
    /// scope at a time.
    pub fn scope<'env, F, T>(&self, f: F) -> T
    where
        F: for<'scope> FnOnce(&'scope Scope<'scope, 'env>) -> T,
    {
        let scoped = match self.scoped.try_lock() {
            Ok(scoped) => scoped,
            Err(TryLockError::Poisoned(poisoned)) => poisoned.into_inner(),
            Err(TryLockError::WouldBlock) => panic!("a pool runs one scope at a time"),
        };
        let scope = Scope {
            pool: self,
            posted: Cell::new(0),
            is_posting: Cell::new(false),
            _scoped: scoped,
            scope: PhantomData,
        };
        // The jobs are joined whether `f` returns or panics.
        let _joining = Joining(&scope);
        f(&scope)
    }
}

/// A scope that posts rounds of jobs to a pool ([`Pool::scope`]).
pub struct Scope<'scope, 'env: 'scope> {
    pool: &'scope Pool,
    /// How many jobs the round that was posted last has, which `done` counts to.
    posted: Cell<usize>,
    /// Whether a round is being installed, between the wait for the one before and the count.
    is_posting: Cell<bool>,
    _scoped: MutexGuard<'scope, ()>,
    scope: PhantomData<&'scope mut &'env ()>,
}

/// Joins a scope's round as the scope ends, on a return or a panic of its closure.
struct Joining<'s, 'scope, 'env>(&'s Scope<'scope, 'env>);

impl Drop for Joining<'_, '_, '_> {
    fn drop(&mut self) {
        self.0.wait();
    }
}

impl<'scope, 'env> Scope<'scope, 'env> {
    /// Runs the jobs, job `i` on thread `i % threads`, and returns what each gave, in order, once
    /// every job is done. A job that panics makes this panic, after the round's other jobs are
    /// done.
    pub fn run<R, F>(&'scope self, jobs: impl IntoIterator<Item = F>) -> Vec<R>
    where
        R: Send + 'env,
        F: FnOnce() -> R + Send + 'env,
    {
        self.post(jobs).join()
    }

    /// Starts a round of jobs, job `i` on thread `i % threads`, and returns it to join: the
    /// caller may do its own work while the jobs run. A round posted while the one before it
    /// still runs waits for it first, so a pool runs one round at a time, and the scope joins
    /// the round whether or not it is joined here. The jobs are all taken from the iterator
    /// before the wait, so an iterator that posts rounds of its own posts them before this one.
    pub fn post<R, F>(&'scope self, jobs: impl IntoIterator<Item = F>) -> Round<'scope, 'env, R>
    where
        R: Send + 'env,
        F: FnOnce() -> R + Send + 'env,
    {
        let mut results: Vec<Slot<R>> = Vec::new();
        let posted: Vec<Option<Job>> = jobs
            .into_iter()
            .map(|job| {
                let slot: Slot<R> = Arc::default();
                results.push(slot.clone());
                let job: Box<dyn FnOnce() + Send + 'env> = Box::new(move || {
                    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(job));
                    *slot
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(result);
                });
                // SAFETY: the job borrows only what lives for `'env`, which outlives the scope
                // (`Pool::scope`), and the scope waits for every job it posted before it ends,
                // on a return or a panic (`Joining`), so nothing a job borrows is dropped while
                // the job can run.
                Some(unsafe { erase(job) })
            })
            .collect();
        let count = posted.len();
        // From here to the round's installation no code of the caller's runs: the round before
        // is joined, and then the queue and the count are this round's.
        assert!(
            !self.is_posting.replace(true),
            "a round posted while another is installed"
        );
        self.wait();
        let shared = &self.pool.shared;
        shared.done.store(0, Ordering::Release);
        {
            let mut queue = shared
                .posted
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            queue.jobs = posted;
            shared.number.fetch_add(1, Ordering::Release);
        }
        shared.is_posted.notify_all();
        self.posted.set(count);
        self.is_posting.set(false);
        Round {
            scope: self,
            results,
        }
    }

    fn is_done(&self) -> bool {
        self.pool.shared.done.load(Ordering::Acquire) >= self.posted.get()
    }

    /// Waits for the round posted last, if any.
    fn wait(&self) {
        // The caller parks rather than spins: a round's jobs run for milliseconds on every core.
        let shared = &self.pool.shared;
        while !self.is_done() {
            let guard = shared
                .finished_lock
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if !self.is_done() {
                drop(
                    shared
                        .finished
                        .wait_timeout(guard, Duration::from_millis(1))
                        .unwrap_or_else(std::sync::PoisonError::into_inner),
                );
            }
        }
    }
}

/// A round of jobs a scope posted, joined for what they gave.
pub struct Round<'scope, 'env, R> {
    scope: &'scope Scope<'scope, 'env>,
    results: Vec<Slot<R>>,
}

impl<R> Round<'_, '_, R> {
    /// What each job gave, in order, once every job is done. A job that panicked makes this
    /// panic, after the round's other jobs are done.
    pub fn join(self) -> Vec<R> {
        self.scope.wait();
        self.results
            .into_iter()
            .map(|slot| {
                slot.lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .take()
                    .expect("a result of each job")
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            })
            .collect()
    }
}

/// Forgets a job's lifetime, for the queue the threads take jobs from; see `Scope::post`.
unsafe fn erase<'b>(job: Box<dyn FnOnce() + Send + 'b>) -> Job {
    unsafe { std::mem::transmute::<Box<dyn FnOnce() + Send + 'b>, Job>(job) }
}

impl Drop for Pool {
    fn drop(&mut self) {
        {
            let mut queue = self
                .shared
                .posted
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            queue.is_stopping = true;
            self.shared.number.fetch_add(1, Ordering::Release);
        }
        self.shared.is_posted.notify_all();
        for thread in self.threads.drain(..) {
            let _ = thread.join();
        }
    }
}

fn serve(shared: &Shared, index: usize, threads: usize) {
    let mut seen = 0u64;
    loop {
        let at = Instant::now();
        while shared.number.load(Ordering::Acquire) == seen {
            if at.elapsed() < SPIN {
                std::hint::spin_loop();
                continue;
            }
            let queue = shared
                .posted
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            drop(
                shared
                    .is_posted
                    .wait_while(queue, |_| shared.number.load(Ordering::Acquire) == seen)
                    .unwrap_or_else(std::sync::PoisonError::into_inner),
            );
        }
        seen = shared.number.load(Ordering::Acquire);
        for next in (index..).step_by(threads) {
            let job = {
                let mut queue = shared
                    .posted
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                if queue.is_stopping {
                    return;
                }
                match queue.jobs.get_mut(next) {
                    Some(job) => job.take(),
                    None => break,
                }
            };
            if let Some(job) = job {
                job();
                shared.done.fetch_add(1, Ordering::AcqRel);
                let _guard = shared
                    .finished_lock
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                shared.finished.notify_all();
            }
        }
    }
}

/// A job may borrow only what outlives the scope: a value made inside it is rejected.
///
/// ```compile_fail,E0597
/// let pool = tla_engine::pool::Pool::new(1, 1 << 20);
/// pool.scope(|scope| {
///     let local = vec![1u64];
///     let round = scope.post([()].map(|_| || local.len()));
///     round.join()
/// });
/// ```
///
/// A round may not leave its scope.
///
/// ```compile_fail
/// let pool = tla_engine::pool::Pool::new(1, 1 << 20);
/// let data = vec![1u64];
/// let round = pool.scope(|scope| scope.post([()].map(|_| || data.len())));
/// round.join();
/// ```
#[cfg(doctest)]
pub struct ScopeBorrows;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runs_each_job_on_its_thread_and_returns_in_order() {
        let pool = Pool::new(4, 1 << 20);
        let data = vec![10u64, 20, 30];
        assert_eq!(
            pool.run((0..3).map(|index| {
                let data = &data;
                move || data[index] * 2
            })),
            vec![20, 40, 60]
        );
        // Rounds of fewer jobs than threads, and many rounds, each borrowing anew.
        for round in 0..200u64 {
            let value = round;
            assert_eq!(
                pool.run([1, 2].map(|add| move || value + add)),
                vec![round + 1, round + 2]
            );
        }
    }

    #[test]
    fn runs_more_jobs_than_threads_in_order() {
        let pool = Pool::new(3, 1 << 20);
        let threads: Vec<std::thread::ThreadId> =
            pool.run((0..8).map(|_| || std::thread::current().id()));
        assert_eq!(threads.len(), 8);
        assert_eq!(threads[0], threads[3]);
        assert_eq!(threads[1], threads[7]);
        assert_ne!(threads[0], threads[1]);
        assert_eq!(
            pool.run((0..10u32).map(|i| move || i * i)),
            (0..10).map(|i| i * i).collect::<Vec<_>>()
        );
    }

    #[test]
    fn a_job_writes_through_a_borrow_the_scope_holds() {
        let pool = Pool::new(2, 1 << 20);
        let mut counts = vec![0usize; 2];
        {
            let (left, right) = counts.split_at_mut(1);
            pool.run([left, right].map(|count| move || count[0] += 5));
        }
        assert_eq!(counts, vec![5, 5]);
    }

    /// `cargo test -p tla-engine pool::tests::times -- --ignored --nocapture`: a round of the
    /// pool against a round of scoped threads, on this machine.
    #[test]
    #[ignore]
    fn times_a_round_against_scoped_threads() {
        for threads in [4, 16] {
            let pool = Pool::new(threads, 64 << 20);
            let rounds = 1000u32;
            let at = Instant::now();
            for _ in 0..rounds {
                pool.run((0..threads).map(|i| move || i));
            }
            let pool_round = at.elapsed() / rounds;
            let at = Instant::now();
            for _ in 0..rounds {
                std::thread::scope(|scope| {
                    let handles: Vec<_> = (0..threads)
                        .map(|i| {
                            std::thread::Builder::new()
                                .stack_size(64 << 20)
                                .spawn_scoped(scope, move || i)
                                .unwrap()
                        })
                        .collect();
                    for handle in handles {
                        handle.join().unwrap();
                    }
                });
            }
            let scope_round = at.elapsed() / rounds;
            eprintln!("{threads} threads: pool round {pool_round:?}, scoped round {scope_round:?}");
        }
    }

    #[test]
    fn a_posted_round_is_joined_after_the_caller_works() {
        let pool = Pool::new(2, 1 << 20);
        let counter = AtomicUsize::new(0);
        let (mut given, own) = pool.scope(|scope| {
            let counter = &counter;
            let round = scope
                .post([1usize, 10].map(|add| move || counter.fetch_add(add, Ordering::AcqRel)));
            let own: u64 = (0..1000).sum();
            (round.join(), own)
        });
        given.sort_unstable();
        assert_eq!(counter.load(Ordering::Acquire), 11);
        assert!(
            given == vec![0, 1] || given == vec![0, 10],
            "{given:?} after summing to {own}"
        );
    }

    #[test]
    fn sequential_scopes_and_rounds_each_complete_their_own_jobs() {
        let pool = Pool::new(2, 1 << 20);
        let mut totals = Vec::new();
        for scope_number in 0..3u64 {
            let base = scope_number * 100;
            let total = pool.scope(|scope| {
                // A round posted while the one before runs waits for it: every job of the first
                // is counted, and every result of the second is its own.
                let first = scope.post((0..4u64).map(|i| {
                    move || {
                        std::thread::sleep(Duration::from_millis(2));
                        base + i
                    }
                }));
                let second = scope.post((0..3u64).map(|i| move || base + 10 + i));
                let second = second.join();
                let first = first.join();
                assert_eq!(first, vec![base, base + 1, base + 2, base + 3]);
                assert_eq!(second, vec![base + 10, base + 11, base + 12]);
                first.iter().sum::<u64>() + second.iter().sum::<u64>()
            });
            totals.push(total);
        }
        assert_eq!(totals, vec![39, 739, 1439]);
    }

    #[test]
    fn an_iterator_that_posts_a_round_has_it_joined_before_its_own() {
        let pool = Pool::new(2, 1 << 20);
        let (inner_ran, outer_ran) = (AtomicUsize::new(0), AtomicUsize::new(0));
        pool.scope(|scope| {
            let (inner_ran, outer_ran) = (&inner_ran, &outer_ran);
            // The iterator of the outer round's jobs posts a round of its own, whose job is still
            // running when the iterator yields: the outer round waits for it.
            let jobs = std::iter::once(()).map(|()| {
                let inner = scope.post([()].map(|()| {
                    move || {
                        std::thread::sleep(Duration::from_millis(30));
                        inner_ran.fetch_add(1, Ordering::AcqRel);
                    }
                }));
                std::mem::forget(inner);
                move || {
                    outer_ran.fetch_add(1, Ordering::AcqRel);
                }
            });
            scope.run(jobs);
            assert_eq!(inner_ran.load(Ordering::Acquire), 1);
            assert_eq!(outer_ran.load(Ordering::Acquire), 1);
        });
        assert_eq!(inner_ran.load(Ordering::Acquire), 1);
    }

    #[test]
    fn a_forgotten_round_is_joined_as_its_scope_ends() {
        let pool = Pool::new(2, 1 << 20);
        let counter = AtomicUsize::new(0);
        pool.scope(|scope| {
            let round = scope.post((0..2).map(|_| {
                || {
                    std::thread::sleep(Duration::from_millis(5));
                    counter.fetch_add(1, Ordering::AcqRel);
                }
            }));
            std::mem::forget(round);
        });
        assert_eq!(counter.load(Ordering::Acquire), 2);
    }

    #[test]
    fn a_panic_in_a_job_reaches_the_caller_after_the_round() {
        let pool = Pool::new(2, 1 << 20);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            pool.run((0..2u32).map(|i| move || if i == 1 { panic!("a job's panic") } else { i }))
        }));
        assert!(result.is_err());
        // The pool still serves the next round.
        assert_eq!(pool.run([3u32].map(|i| move || i)), vec![3]);
    }
}
