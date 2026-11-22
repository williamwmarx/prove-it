//! A pool of threads the search keeps alive from the first level it shares to its end, so that a
//! level's rounds of work, its expansion, the state table's fill and the copy of its new states,
//! don't each start and join their threads: starting a thread costs tens of microseconds, and a
//! level makes six or seven rounds of them.
//!
//! A round gives each thread one job and waits for every job to finish, as `std::thread::scope`
//! would, so a job may borrow what the round's caller holds. Between rounds a thread spins briefly,
//! since the rounds of one level follow each other closely, and then parks until the next.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
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
    /// The jobs of the round, each taken by the thread of its index; `None` once taken.
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
                    .spawn(move || serve(&shared, index))
                    .expect("a thread for the search")
            })
            .collect();
        Self { shared, threads }
    }

    pub fn threads(&self) -> usize {
        self.threads.len()
    }

    /// Runs job `i` on thread `i` and returns what each gave, in order, once every job is done. A
    /// job that panics makes this panic, after the round's other jobs are done. The jobs may
    /// borrow from the caller: none outlives this call.
    pub fn run<'a, R: Send + 'a>(&self, jobs: Vec<Box<dyn FnOnce() -> R + Send + 'a>>) -> Vec<R> {
        self.post(jobs).join()
    }

    /// Starts a round of jobs, job `i` on thread `i`, and returns it to wait for: the caller may
    /// do its own work while the jobs run. The jobs may borrow from the caller: none outlives
    /// the round, which waits for every job as it is joined or dropped.
    pub fn post<'a, R: Send + 'a>(
        &self,
        jobs: Vec<Box<dyn FnOnce() -> R + Send + 'a>>,
    ) -> Round<'_, R> {
        assert!(jobs.len() <= self.threads.len(), "more jobs than threads");
        let count = jobs.len();
        let results: Vec<Slot<R>> = (0..count).map(|_| Arc::default()).collect();
        let posted: Vec<Option<Job>> = jobs
            .into_iter()
            .zip(&results)
            .map(|(job, slot)| {
                let slot = slot.clone();
                let job: Box<dyn FnOnce() + Send + 'a> = Box::new(move || {
                    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(job));
                    *slot
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(result);
                });
                // SAFETY: the job borrows from the caller for `'a`, and the round it belongs to
                // waits for every job to run to its end before it is joined or dropped
                // (`Round::wait`), so nothing a job borrows is dropped while it can run.
                Some(unsafe { erase(job) })
            })
            .collect();
        self.shared.done.store(0, Ordering::Release);
        {
            let mut queue = self
                .shared
                .posted
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            queue.jobs = posted;
            self.shared.number.fetch_add(1, Ordering::Release);
        }
        self.shared.is_posted.notify_all();
        Round {
            pool: self,
            count,
            results: Some(results),
        }
    }
}

/// A round of jobs a pool runs, joined for what they gave.
pub struct Round<'p, R> {
    pool: &'p Pool,
    count: usize,
    results: Option<Vec<Slot<R>>>,
}

impl<R> Round<'_, R> {
    /// Whether every job of the round is done.
    pub fn is_done(&self) -> bool {
        self.pool.shared.done.load(Ordering::Acquire) >= self.count
    }

    /// Waits for the round's jobs, at most `limit` before returning whether they are all done,
    /// for a caller with its own work to do meanwhile.
    pub fn wait_for(&self, limit: Duration) -> bool {
        let shared = &self.pool.shared;
        if self.is_done() {
            return true;
        }
        let guard = shared
            .finished_lock
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !self.is_done() {
            drop(
                shared
                    .finished
                    .wait_timeout(guard, limit)
                    .unwrap_or_else(std::sync::PoisonError::into_inner),
            );
        }
        self.is_done()
    }

    fn wait(&self) {
        // The caller parks rather than spins: a round's jobs run for milliseconds on every core.
        while !self.wait_for(Duration::from_millis(1)) {}
    }

    /// What each job gave, in order, once every job is done. A job that panicked makes this
    /// panic, after the round's other jobs are done.
    pub fn join(mut self) -> Vec<R> {
        self.wait();
        self.results
            .take()
            .expect("the round's results, joined once")
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

impl<R> Drop for Round<'_, R> {
    fn drop(&mut self) {
        if self.results.is_some() {
            self.wait();
        }
    }
}

/// Forgets a job's lifetime, for a round that outlives it; see `Pool::run`.
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

fn serve(shared: &Shared, index: usize) {
    let mut seen = 0u64;
    loop {
        let job = {
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
            let mut queue = shared
                .posted
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if queue.is_stopping {
                return;
            }
            seen = shared.number.load(Ordering::Acquire);
            queue.jobs.get_mut(index).and_then(Option::take)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runs_each_job_on_its_thread_and_returns_in_order() {
        let pool = Pool::new(4, 1 << 20);
        let data = vec![10u64, 20, 30];
        let jobs: Vec<Box<dyn FnOnce() -> u64 + Send + '_>> = (0..3)
            .map(|index| {
                let data = &data;
                Box::new(move || data[index] * 2) as Box<dyn FnOnce() -> u64 + Send + '_>
            })
            .collect();
        assert_eq!(pool.run(jobs), vec![20, 40, 60]);
        // Rounds of fewer jobs than threads, and many rounds, each borrowing anew.
        for round in 0..200u64 {
            let value = round;
            let jobs: Vec<Box<dyn FnOnce() -> u64 + Send + '_>> =
                vec![Box::new(|| value + 1), Box::new(|| value + 2)];
            assert_eq!(pool.run(jobs), vec![round + 1, round + 2]);
        }
    }

    #[test]
    fn a_job_writes_through_a_borrow_the_round_holds() {
        let pool = Pool::new(2, 1 << 20);
        let mut counts = vec![0usize; 2];
        {
            let (left, right) = counts.split_at_mut(1);
            let jobs: Vec<Box<dyn FnOnce() + Send + '_>> = vec![
                Box::new(move || left[0] += 5),
                Box::new(move || right[0] += 7),
            ];
            pool.run(jobs);
        }
        assert_eq!(counts, vec![5, 7]);
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
                let jobs: Vec<Box<dyn FnOnce() -> usize + Send + '_>> =
                    (0..threads).map(|i| Box::new(move || i) as _).collect();
                pool.run(jobs);
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
    fn a_posted_round_runs_while_the_caller_works() {
        let pool = Pool::new(2, 1 << 20);
        let counter = AtomicUsize::new(0);
        let round = {
            let counter = &counter;
            let jobs: Vec<Box<dyn FnOnce() -> usize + Send + '_>> = vec![
                Box::new(move || counter.fetch_add(1, Ordering::AcqRel) + 1),
                Box::new(move || counter.fetch_add(10, Ordering::AcqRel) + 10),
            ];
            pool.post(jobs)
        };
        let mut own = 0;
        while !round.wait_for(Duration::from_micros(100)) {
            own += 1;
        }
        let mut given = round.join();
        given.sort_unstable();
        assert_eq!(counter.load(Ordering::Acquire), 11);
        assert!(
            given == vec![1, 11] || given == vec![10, 11],
            "{given:?} after {own} waits"
        );
    }

    #[test]
    fn a_panic_in_a_job_reaches_the_caller_after_the_round() {
        let pool = Pool::new(2, 1 << 20);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let jobs: Vec<Box<dyn FnOnce() -> u32 + Send + '_>> =
                vec![Box::new(|| 1), Box::new(|| panic!("a job's panic"))];
            pool.run(jobs)
        }));
        assert!(result.is_err());
        // The pool still serves the next round.
        let jobs: Vec<Box<dyn FnOnce() -> u32 + Send + '_>> = vec![Box::new(|| 3)];
        assert_eq!(pool.run(jobs), vec![3]);
    }
}
