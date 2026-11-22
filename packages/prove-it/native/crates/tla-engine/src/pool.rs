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

#[derive(Default)]
struct Round {
    /// The jobs of the round, each taken by the thread of its index; `None` once taken.
    jobs: Vec<Option<Job>>,
    is_stopping: bool,
}

struct Shared {
    round: Mutex<Round>,
    /// Which round `round` holds, so a thread knows one it hasn't seen without the lock.
    number: AtomicU64,
    posted: Condvar,
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
            round: Mutex::new(Round::default()),
            number: AtomicU64::new(0),
            posted: Condvar::new(),
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
        assert!(jobs.len() <= self.threads.len(), "more jobs than threads");
        let count = jobs.len();
        let results: Vec<Mutex<Option<std::thread::Result<R>>>> =
            (0..count).map(|_| Mutex::new(None)).collect();
        let posted: Vec<Option<Job>> = jobs
            .into_iter()
            .zip(&results)
            .map(|(job, slot)| {
                let job: Box<dyn FnOnce() + Send + '_> = Box::new(move || {
                    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(job));
                    *slot
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(result);
                });
                // SAFETY: the job borrows from the caller and from this call's frame, and this
                // call doesn't return until every job of the round has run to its end (`done`
                // reaches `count` below), so nothing the job borrows is dropped while it can run.
                Some(unsafe { erase(job) })
            })
            .collect();
        self.shared.done.store(0, Ordering::Release);
        {
            let mut round = self
                .shared
                .round
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            round.jobs = posted;
            self.shared.number.fetch_add(1, Ordering::Release);
        }
        self.shared.posted.notify_all();
        // The caller parks rather than spins: a round's jobs run for milliseconds on every core.
        while self.shared.done.load(Ordering::Acquire) < count {
            let guard = self
                .shared
                .finished_lock
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if self.shared.done.load(Ordering::Acquire) < count {
                drop(
                    self.shared
                        .finished
                        .wait_timeout(guard, Duration::from_millis(1))
                        .unwrap_or_else(std::sync::PoisonError::into_inner),
                );
            }
        }
        results
            .into_iter()
            .map(|slot| {
                slot.into_inner()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .expect("a result of each job")
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            })
            .collect()
    }
}

/// Forgets a job's lifetime, for a round that outlives it; see `Pool::run`.
unsafe fn erase<'b>(job: Box<dyn FnOnce() + Send + 'b>) -> Job {
    unsafe { std::mem::transmute::<Box<dyn FnOnce() + Send + 'b>, Job>(job) }
}

impl Drop for Pool {
    fn drop(&mut self) {
        {
            let mut round = self
                .shared
                .round
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            round.is_stopping = true;
            self.shared.number.fetch_add(1, Ordering::Release);
        }
        self.shared.posted.notify_all();
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
                let round = shared
                    .round
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                drop(
                    shared
                        .posted
                        .wait_while(round, |_| shared.number.load(Ordering::Acquire) == seen)
                        .unwrap_or_else(std::sync::PoisonError::into_inner),
                );
            }
            let mut round = shared
                .round
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if round.is_stopping {
                return;
            }
            seen = shared.number.load(Ordering::Acquire);
            round.jobs.get_mut(index).and_then(Option::take)
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
