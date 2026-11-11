//! Ported from Z3 (src/smt/smt_case_split_queue.cpp, src/util/heap.h), MIT license, see
//! z3-license.txt, through `case-split-queue.ts`. Z3's default CS_ACTIVITY_DELAY_NEW queue: Boolean
//! variables ordered by activity, where variables created during the search wait in a delayed queue
//! until the main one runs dry. Without the delay, it is the CS_ACTIVITY queue of the model
//! checker's auxiliary context.

use super::literal::BoolVar;

/// heap<bool_var_act_lt>: a binary min-heap over activities negated, so the most active is first.
/// The activities are the context's, passed to each call that compares.
#[derive(Clone, Debug)]
struct ActivityHeap {
    /// The heap is 1-based, so the first slot is unused.
    values: Vec<BoolVar>,
    /// The position of each variable, or 0.
    indices: Vec<u32>,
}

/// A variable without an activity compares as JavaScript's `undefined` does: never greater.
fn is_less(activity: &[f64], first: BoolVar, second: BoolVar) -> bool {
    match (activity.get(first as usize), activity.get(second as usize)) {
        (Some(first), Some(second)) => first > second,
        _ => false,
    }
}

impl ActivityHeap {
    fn new() -> Self {
        ActivityHeap {
            values: vec![BoolVar::MAX],
            indices: vec![0; 1024],
        }
    }

    fn get_index(&self, value: BoolVar) -> usize {
        self.indices.get(value as usize).copied().unwrap_or(0) as usize
    }

    fn contains(&self, value: BoolVar) -> bool {
        self.get_index(value) != 0
    }

    fn is_empty(&self) -> bool {
        self.values.len() == 1
    }

    fn insert(&mut self, activity: &[f64], value: BoolVar) {
        if value as usize >= self.indices.len() {
            let length = (2 * self.indices.len()).max(value as usize + 1);
            self.indices.resize(length, 0);
        }
        self.values.push(value);
        self.indices[value as usize] = (self.values.len() - 1) as u32;
        self.move_up(activity, self.values.len() - 1);
    }

    /// The caller checks the heap is not empty.
    fn erase_min(&mut self, activity: &[f64]) -> BoolVar {
        let result = self.values[1];
        let last = self.values[self.values.len() - 1];
        self.values.pop();
        self.indices[result as usize] = 0;
        if self.values.len() > 1 {
            self.values[1] = last;
            self.indices[last as usize] = 1;
            self.move_down(activity, 1);
        }
        result
    }

    /// The caller checks the heap contains value.
    fn erase(&mut self, activity: &[f64], value: BoolVar) {
        let index = self.indices[value as usize] as usize;
        if index == self.values.len() - 1 {
            self.indices[value as usize] = 0;
            self.values.pop();
            return;
        }
        let last = self.values[self.values.len() - 1];
        self.values.pop();
        self.values[index] = last;
        self.indices[last as usize] = index as u32;
        self.indices[value as usize] = 0;
        let parent_index = index >> 1;
        if parent_index != 0 && is_less(activity, last, self.values[parent_index]) {
            self.move_up(activity, index);
        } else {
            self.move_down(activity, index);
        }
    }

    fn decreased(&mut self, activity: &[f64], value: BoolVar) {
        self.move_up(activity, self.indices[value as usize] as usize);
    }

    fn move_up(&mut self, activity: &[f64], start: usize) {
        let mut index = start;
        let value = self.values[index];
        loop {
            let parent_index = index >> 1;
            if parent_index == 0 || !is_less(activity, value, self.values[parent_index]) {
                break;
            }
            self.values[index] = self.values[parent_index];
            self.indices[self.values[index] as usize] = index as u32;
            index = parent_index;
        }
        self.values[index] = value;
        self.indices[value as usize] = index as u32;
    }

    fn move_down(&mut self, activity: &[f64], start: usize) {
        let mut index = start;
        let value = self.values[index];
        let size = self.values.len();
        loop {
            let left = index * 2;
            if left >= size {
                break;
            }
            let right = left + 1;
            let min_index =
                if right < size && is_less(activity, self.values[right], self.values[left]) {
                    right
                } else {
                    left
                };
            if !is_less(activity, self.values[min_index], value) {
                break;
            }
            self.values[index] = self.values[min_index];
            self.indices[self.values[index] as usize] = index as u32;
            index = min_index;
        }
        self.values[index] = value;
        self.indices[value as usize] = index as u32;
    }
}

/// What the queue reads of the context.
pub trait CaseSplitContext {
    fn activity(&self) -> &[f64];
    fn get_is_searching(&self) -> bool;
    fn get_random_value(&mut self) -> u32;
    fn get_num_bool_vars(&self) -> u32;
    fn is_unassigned(&self, bool_var: BoolVar) -> bool;
}

const RANDOM_VAR_FREQ: f64 = 0.01;
const RANDOM_MAX_VALUE: u32 = 0x7fff;

#[derive(Clone, Debug)]
pub struct CaseSplitQueue {
    queue: ActivityHeap,
    delayed_queue: ActivityHeap,
    is_delaying_new: bool,
}

impl CaseSplitQueue {
    pub fn new(is_delaying_new: bool) -> Self {
        CaseSplitQueue {
            queue: ActivityHeap::new(),
            delayed_queue: ActivityHeap::new(),
            is_delaying_new,
        }
    }

    pub fn activity_increased(&mut self, context: &impl CaseSplitContext, bool_var: BoolVar) {
        if self.queue.contains(bool_var) {
            self.queue.decreased(context.activity(), bool_var);
        }
        if self.delayed_queue.contains(bool_var) {
            self.delayed_queue.decreased(context.activity(), bool_var);
        }
    }

    pub fn mk_var(&mut self, context: &impl CaseSplitContext, bool_var: BoolVar) {
        if self.is_delaying_new && context.get_is_searching() {
            self.delayed_queue.insert(context.activity(), bool_var);
        } else {
            self.queue.insert(context.activity(), bool_var);
        }
    }

    pub fn del_var(&mut self, context: &impl CaseSplitContext, bool_var: BoolVar) {
        if self.queue.contains(bool_var) {
            self.queue.erase(context.activity(), bool_var);
        }
        if self.delayed_queue.contains(bool_var) {
            self.delayed_queue.erase(context.activity(), bool_var);
        }
    }

    pub fn unassign_var(&mut self, context: &impl CaseSplitContext, bool_var: BoolVar) {
        if !self.queue.contains(bool_var) {
            self.queue.insert(context.activity(), bool_var);
        }
    }

    /// Returns the next variable to split on, or `None` when every variable is assigned.
    pub fn next_case_split(&mut self, context: &mut impl CaseSplitContext) -> Option<BoolVar> {
        if f64::from(context.get_random_value())
            < (RANDOM_VAR_FREQ * f64::from(RANDOM_MAX_VALUE)).trunc()
        {
            let random = context.get_random_value();
            // With no variables, JavaScript's `% 0` is NaN, which is never unassigned.
            if let Some(next) = random.checked_rem(context.get_num_bool_vars())
                && context.is_unassigned(next)
            {
                return Some(next);
            }
        }
        while !self.queue.is_empty() {
            let next = self.queue.erase_min(context.activity());
            if context.is_unassigned(next) {
                return Some(next);
            }
        }
        std::mem::swap(&mut self.queue, &mut self.delayed_queue);
        while !self.queue.is_empty() {
            let next = self.queue.erase_min(context.activity());
            if context.is_unassigned(next) {
                return Some(next);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestContext {
        activity: Vec<f64>,
        is_searching: bool,
        assigned: Vec<bool>,
        // Above the random frequency, so no split is random.
        random_value: u32,
    }

    impl CaseSplitContext for TestContext {
        fn activity(&self) -> &[f64] {
            &self.activity
        }
        fn get_is_searching(&self) -> bool {
            self.is_searching
        }
        fn get_random_value(&mut self) -> u32 {
            self.random_value
        }
        fn get_num_bool_vars(&self) -> u32 {
            self.activity.len() as u32
        }
        fn is_unassigned(&self, bool_var: BoolVar) -> bool {
            !self.assigned[bool_var as usize]
        }
    }

    #[test]
    fn splits_on_the_most_active_variable_then_the_delayed_ones() {
        let mut context = TestContext {
            activity: vec![0.0, 3.0, 1.0, 5.0, 2.0, 4.0],
            is_searching: false,
            assigned: vec![true, false, false, false, false, false],
            random_value: 1000,
        };
        let mut queue = CaseSplitQueue::new(true);
        for bool_var in 0..4 {
            queue.mk_var(&context, bool_var);
        }
        context.is_searching = true;
        queue.mk_var(&context, 4);
        queue.mk_var(&context, 5);
        context.activity[2] = 6.0;
        queue.activity_increased(&context, 2);
        queue.del_var(&context, 1);
        let mut order = Vec::new();
        while let Some(next) = queue.next_case_split(&mut context) {
            order.push(next);
            context.assigned[next as usize] = true;
        }
        assert_eq!(order, [2, 3, 5, 4]);
        context.assigned[3] = false;
        queue.unassign_var(&context, 3);
        assert_eq!(queue.next_case_split(&mut context), Some(3));
    }

    #[test]
    fn splits_on_a_random_variable_now_and_then() {
        let mut context = TestContext {
            activity: vec![0.0, 3.0, 1.0],
            is_searching: false,
            assigned: vec![true, false, false],
            random_value: 5,
        };
        let mut queue = CaseSplitQueue::new(false);
        for bool_var in 0..3 {
            queue.mk_var(&context, bool_var);
        }
        // 5 is below 0.01 * 0x7fff, and 5 % 3 is 2.
        assert_eq!(queue.next_case_split(&mut context), Some(2));
    }
}
