// Ported from Z3 (src/math/lp/nla_backoff.h), MIT license, see z3-license.txt. When the core runs
// its expensive engines.

// backoff: how many calls to skip before the next run of an expensive engine.
pub struct Backoff {
    delay: u64,
    delay_bound: u64,
}

impl Backoff {
    pub fn new(delay_bound: u64) -> Backoff {
        Backoff {
            delay: 0,
            delay_bound,
        }
    }

    pub fn should_run(&mut self) -> bool {
        if self.delay > 0 {
            self.delay -= 1;
        }
        self.delay < 2
    }

    pub fn update(&mut self, is_success: bool) {
        if is_success {
            self.delay_bound /= 2;
        } else if self.delay_bound < 1 << 20 {
            self.delay_bound = (2 * self.delay_bound).max(1);
        }
        self.delay = self.delay_bound;
    }
}

// squeeze_schedule: when to run the bounds optimization of the monomials.
#[derive(Default)]
pub struct SqueezeSchedule {
    fail_streak: u64,
    squeezes_since_sat_check: u64,
}

impl SqueezeSchedule {
    pub fn is_enabled(&self) -> bool {
        self.squeezes_since_sat_check < 50
    }

    pub fn is_eager(&self) -> bool {
        self.fail_streak < 3
    }

    pub fn on_squeeze(&mut self, is_improved: bool) {
        self.squeezes_since_sat_check += 1;
        self.fail_streak = if is_improved { 0 } else { self.fail_streak + 1 };
    }

    pub fn on_nothing_to_refine(&mut self) {
        self.squeezes_since_sat_check /= 2;
    }
}
