//! TLC's check of one simulated behavior (`LiveCheck1.checkTrace`): for each solution in turn, a
//! behavior graph of the trace (`constructBEGraph`), Tarjan's search of its strongly connected
//! components from each initial node (`checkSccs`), the search within a component of the edges
//! that keep the solution's eventually-always actions (`checkSccs1`), and the check of each such
//! part (`checkSubcomponent`); the first part that satisfies the solution's checks is a
//! counterexample, which `printErrorTrace` prints from the trace itself.

use super::{Checker, Declined, Source, Step, edge_step};

/// `LiveCheck1.MAX_FIRST` and `MAX_SECOND`, which split a node's number between the searches.
const MAX_FIRST: i64 = 0x2000_0000_0000_0000;
const MAX_SECOND: i64 = 0x5000_0000_0000_0000;

/// What TLC prints of a counterexample it found on a trace: the first `length` states of the
/// trace, then the step back to the state at `loop_start` (counted from 0), or, where the last
/// state printed is the state of the node the cycle starts at, a stuttering step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TraceCounterexample {
    pub length: usize,
    pub loop_start: usize,
    pub is_stuttering: bool,
}

// A node of the behavior graph (`BEGraphNode`, `BTGraphNode`): a state of the trace, by its
// index in the graph, with a node of the tableau, the results of the solution's state checks, its
// transitions with the results of the action checks on each, and the numbers the searches give it.
struct Node {
    state: u32,
    tableau: u32,
    states: Vec<bool>,
    successors: Vec<usize>,
    actions: Vec<Vec<bool>>,
    number: i64,
    is_visited: bool,
    parent: Option<usize>,
}

struct Graph {
    nodes: Vec<Node>,
    initial: Vec<usize>,
}

impl Graph {
    fn add_node(&mut self, state: u32, tableau: u32, states: Vec<bool>) -> usize {
        self.nodes.push(Node {
            state,
            tableau,
            states,
            successors: Vec::new(),
            actions: Vec::new(),
            number: 0,
            is_visited: false,
            parent: None,
        });
        self.nodes.len() - 1
    }

    fn add_transition(&mut self, source: usize, target: usize, actions: Vec<bool>) {
        let node = &mut self.nodes[source];
        node.successors.push(target);
        node.actions.push(actions);
    }

    fn is_transition(&self, source: usize, target: usize) -> bool {
        self.nodes[source].successors.contains(&target)
    }
}

/// Why the search stopped: at a counterexample, or where it doesn't follow TLC.
enum Stop {
    Found(Found),
    Declined(Declined),
}

/// Where a check found the counterexample.
struct Found {
    node: usize,
    initial: usize,
    cycle: Vec<usize>,
}

// The checks of one solution on the trace.
struct Checks<'c, 's, 'g> {
    checker: &'c mut Checker,
    source: &'s Source<'g>,
    behavior: usize,
}

impl Checks<'_, '_, '_> {
    fn state(&mut self, state: u32) -> Result<Vec<bool>, Declined> {
        let solution = self.checker.behaviors[self.behavior].solution;
        let checks = self.checker.solutions[solution].state_checks.clone();
        checks
            .into_iter()
            .map(|check| {
                self.checker.start_evaluation();
                self.checker.evaluate_check(self.source, check, state, None)
            })
            .collect()
    }

    fn action(&mut self, state: u32, step: Step) -> Result<Vec<bool>, Declined> {
        let solution = self.checker.behaviors[self.behavior].solution;
        let checks = self.checker.solutions[solution].action_checks.clone();
        checks
            .into_iter()
            .map(|check| {
                self.checker.start_evaluation();
                self.checker
                    .evaluate_check(self.source, check, state, Some(step))
            })
            .collect()
    }

    // The step of the trace from one state to the next, which the graph holds as an edge.
    fn step(&self, state: u32, next: u32) -> Result<Step, Declined> {
        if state == next {
            return Ok(Checker::self_step(state, state));
        }
        let graph = self.source.graph;
        let start = graph.edge_offsets[state as usize] as usize;
        let end = graph.edge_offsets[state as usize + 1] as usize;
        (start..end)
            .find(|&edge| graph.edges[edge] == next)
            .map(|edge| edge_step(graph, state, edge))
            .ok_or_else(|| Declined::from("a step of the trace its graph lacks"))
    }

    fn is_consistent(&mut self, tableau: u32, state: u32) -> Result<bool, Declined> {
        self.checker
            .is_consistent(self.source, self.behavior, tableau, state)
    }

    // `LiveCheck1.constructBEGraph`.
    fn construct(&mut self, trace: &[u32]) -> Result<Graph, Declined> {
        let mut graph = Graph {
            nodes: Vec::new(),
            initial: Vec::new(),
        };
        let solution = self.checker.behaviors[self.behavior].solution;
        let tableau = self.checker.solutions[solution]
            .tableau
            .as_ref()
            .map(|tableau| {
                (
                    tableau.initial_count,
                    tableau
                        .nodes
                        .iter()
                        .map(|node| node.successors.clone())
                        .collect::<Vec<_>>(),
                )
            });
        let mut source_state = trace[0];
        let initial_states = self.state(source_state)?;
        let initial_stutter =
            self.action(source_state, Checker::self_step(source_state, source_state))?;
        let Some((initial_count, successors)) = tableau else {
            // Without a tableau, a node per state of the trace, keyed by the state.
            let mut nodes: Vec<Option<usize>> = Vec::new();
            let node_of = |nodes: &Vec<Option<usize>>, state: u32| {
                nodes.get(state as usize).copied().flatten()
            };
            let mut source = graph.add_node(source_state, 0, initial_states);
            graph.add_transition(source, source, initial_stutter);
            set_node(&mut nodes, source_state, source);
            graph.initial.push(source);
            for &state in &trace[1..] {
                match node_of(&nodes, state) {
                    None => {
                        let states = self.state(state)?;
                        let target = graph.add_node(state, 0, states);
                        let stutter = self.action(state, Checker::self_step(state, state))?;
                        graph.add_transition(target, target, stutter);
                        let step = self.step(source_state, state)?;
                        let actions = self.action(source_state, step)?;
                        graph.add_transition(source, target, actions);
                        set_node(&mut nodes, state, target);
                        source = target;
                    }
                    Some(target) => {
                        if !graph.is_transition(source, target) {
                            let step = self.step(source_state, state)?;
                            let actions = self.action(source_state, step)?;
                            graph.add_transition(source, target, actions);
                        }
                        source = target;
                    }
                }
                source_state = state;
            }
            return Ok(graph);
        };
        // With a tableau, a node per state of the trace and node of the tableau consistent with
        // it, keyed by both (`FP64.Extend`).
        let width = successors.len();
        let mut nodes: Vec<Option<usize>> = Vec::new();
        let key = |state: u32, tableau: u32| state as usize * width + tableau as usize;
        let mut sources = Vec::new();
        for tableau in 0..initial_count as u32 {
            if self.is_consistent(tableau, source_state)? {
                let node = graph.add_node(source_state, tableau, initial_states.clone());
                graph.initial.push(node);
                sources.push(node);
                set_node(&mut nodes, key(source_state, tableau) as u32, node);
            }
        }
        for &source in &sources {
            for &next in &successors[graph.nodes[source].tableau as usize] {
                if let Some(target) = nodes.get(key(source_state, next)).copied().flatten() {
                    graph.add_transition(source, target, initial_stutter.clone());
                }
            }
        }
        for &state in &trace[1..] {
            let mut targets: Vec<usize> = Vec::new();
            let states = self.state(state)?;
            let step = self.step(source_state, state)?;
            let actions = self.action(source_state, step)?;
            self.extend(
                &mut graph,
                &mut nodes,
                (&successors, width),
                &sources,
                &mut targets,
                (state, &states, &actions),
            )?;
            let stutter = self.action(state, Checker::self_step(state, state))?;
            // The nodes of the state each node made reaches by stuttering, which grow as it goes.
            let mut index = 0;
            while index < targets.len() {
                let source = targets[index];
                let mut added = Vec::new();
                self.extend(
                    &mut graph,
                    &mut nodes,
                    (&successors, width),
                    &[source],
                    &mut added,
                    (state, &states, &stutter),
                )?;
                targets.extend(added);
                index += 1;
            }
            sources = targets;
            source_state = state;
        }
        Ok(graph)
    }

    // The transitions from each of `sources` to the nodes of `state` its tableau node steps to:
    // a node consistent with the state that the graph lacks is made, and goes into `targets`.
    fn extend(
        &mut self,
        graph: &mut Graph,
        nodes: &mut Vec<Option<usize>>,
        (successors, width): (&[Vec<u32>], usize),
        sources: &[usize],
        targets: &mut Vec<usize>,
        (state, states, actions): (u32, &[bool], &[bool]),
    ) -> Result<(), Declined> {
        for &source in sources {
            let tableau = graph.nodes[source].tableau as usize;
            for &next in &successors[tableau] {
                let key = state as usize * width + next as usize;
                match nodes.get(key).copied().flatten() {
                    None => {
                        if self.is_consistent(next, state)? {
                            let target = graph.add_node(state, next, states.to_vec());
                            graph.add_transition(source, target, actions.to_vec());
                            targets.push(target);
                            set_node(nodes, key as u32, target);
                        }
                    }
                    Some(target) => {
                        if !graph.is_transition(source, target) {
                            graph.add_transition(source, target, actions.to_vec());
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

fn set_node(nodes: &mut Vec<Option<usize>>, key: u32, node: usize) {
    let key = key as usize;
    if nodes.len() <= key {
        nodes.resize(key + 1, None);
    }
    nodes[key] = Some(node);
}

// The search of one solution's graph for a counterexample, with `LiveCheck1`'s numbers.
struct Search<'s> {
    graph: Graph,
    checker: &'s Checker,
    solution: usize,
    model: usize,
    stack: Vec<usize>,
    first: i64,
    second: i64,
    third: i64,
    start_second: i64,
    start_third: i64,
    first_component: i64,
    second_component: i64,
    initial: usize,
}

impl Search<'_> {
    fn model(&self) -> &crate::tableau::Model {
        &self.checker.solutions[self.solution].models[self.model]
    }

    fn promises(&self) -> &[u32] {
        &self.checker.solutions[self.solution].promises
    }

    fn is_fulfilling(&self, node: usize, promise: u32) -> bool {
        let solution = &self.checker.solutions[self.solution];
        let Some(tableau) = &solution.tableau else {
            return false;
        };
        let particle = &tableau.nodes[self.graph.nodes[node].tableau as usize].particle;
        self.checker.terms.is_fulfilling(particle, promise)
    }

    // `getCheckAction` of the eventually-always actions: all of them hold on the transition.
    fn is_eventually_always(&self, node: usize, transition: usize) -> bool {
        let actions = &self.graph.nodes[node].actions[transition];
        self.model()
            .eventually_always
            .iter()
            .all(|&check| actions[check])
    }

    // `checkSccs`: the node's lowlink, or where the search stopped.
    fn check_components(&mut self, node: usize) -> Result<i64, Stop> {
        let mut lowlink = self.first;
        self.first += 1;
        self.graph.nodes[node].number = lowlink;
        self.stack.push(node);
        for index in 0..self.graph.nodes[node].successors.len() {
            let target = self.graph.nodes[node].successors[index];
            let mut number = self.graph.nodes[target].number;
            if number == 0 {
                number = self.check_components(target)?;
            }
            lowlink = lowlink.min(number);
        }
        if lowlink == self.graph.nodes[node].number {
            self.check_component(node)?;
        }
        Ok(lowlink)
    }

    fn pop(&mut self) -> Result<usize, Stop> {
        self.stack
            .pop()
            .ok_or_else(|| Stop::Declined(Declined::from("an empty stack of the search")))
    }

    // `checkComponent` and `extractComponent`.
    fn check_component(&mut self, node: usize) -> Result<(), Stop> {
        let mut popped = self.pop()?;
        if popped == node && !self.graph.is_transition(node, node) {
            self.graph.nodes[node].number = MAX_FIRST;
            return Ok(());
        }
        let mut members = Vec::new();
        self.first_component = self.second;
        self.second += 1;
        self.second_component = self.third;
        self.graph.nodes[popped].number = self.first_component;
        members.push(popped);
        while popped != node {
            popped = self.pop()?;
            self.graph.nodes[popped].number = self.first_component;
            members.push(popped);
        }
        for model in 0..self.checker.solutions[self.solution].models.len() {
            self.model = model;
            self.start_second = self.second;
            self.start_third = self.third;
            for &member in members.iter().rev() {
                if self.graph.nodes[member].number < self.start_third {
                    self.check_subcomponents(member)?;
                }
            }
        }
        Ok(())
    }

    // `checkSccs1`.
    fn check_subcomponents(&mut self, node: usize) -> Result<i64, Stop> {
        let mut lowlink = self.second;
        self.second += 1;
        self.graph.nodes[node].number = lowlink;
        self.stack.push(node);
        for index in 0..self.graph.nodes[node].successors.len() {
            let target = self.graph.nodes[node].successors[index];
            let mut number = self.graph.nodes[target].number;
            if self.first_component <= number && self.is_eventually_always(node, index) {
                if number < self.start_second
                    || (self.second_component <= number && number < self.start_third)
                {
                    number = self.check_subcomponents(target)?;
                }
                lowlink = lowlink.min(number);
            }
        }
        if lowlink == self.graph.nodes[node].number && self.extract_subcomponent(node)? {
            self.check_subcomponent(node)?;
        }
        Ok(lowlink)
    }

    // `extractComponent1`.
    fn extract_subcomponent(&mut self, node: usize) -> Result<bool, Stop> {
        let mut popped = self.pop()?;
        if popped == node && !self.can_stutter(node) {
            self.graph.nodes[node].number = self.third;
            self.third += 1;
            return Ok(false);
        }
        self.graph.nodes[popped].number = self.third;
        while popped != node {
            popped = self.pop()?;
            self.graph.nodes[popped].number = self.third;
        }
        Ok(true)
    }

    // `canStutter`: the node's first transition to itself keeps the eventually-always actions.
    fn can_stutter(&self, node: usize) -> bool {
        let successors = &self.graph.nodes[node].successors;
        match successors.iter().position(|&target| target == node) {
            Some(index) => {
                self.first_component <= self.graph.nodes[node].number
                    && self.is_eventually_always(node, index)
            }
            None => false,
        }
    }

    // `checkSubcomponent`: where the part satisfies every check, the search stops at the
    // counterexample it holds.
    fn check_subcomponent(&mut self, node: usize) -> Result<(), Stop> {
        let model = self.model();
        let states_checks = model.infinitely_often_states.clone();
        let action_checks = model.infinitely_often_actions.clone();
        let promises = self.promises().to_vec();
        let mut is_state = vec![false; states_checks.len()];
        let mut is_action = vec![false; action_checks.len()];
        let mut is_promise = vec![false; promises.len()];
        self.graph.nodes[node].number += 1;
        let mut pending = vec![node];
        while let Some(current) = pending.pop() {
            for (found, &check) in is_state.iter_mut().zip(&states_checks) {
                if !*found {
                    *found = self.graph.nodes[current].states[check];
                }
            }
            for index in 0..self.graph.nodes[current].successors.len() {
                let target = self.graph.nodes[current].successors[index];
                let number = self.graph.nodes[target].number;
                if number >= self.third {
                    for (found, &check) in is_action.iter_mut().zip(&action_checks) {
                        if !*found {
                            *found = self.graph.nodes[current].actions[index][check];
                        }
                    }
                }
                if number == self.third {
                    self.graph.nodes[target].number += 1;
                    pending.push(target);
                }
            }
            for (found, &promise) in is_promise.iter_mut().zip(&promises) {
                if self.is_fulfilling(current, promise) {
                    *found = true;
                }
            }
        }
        self.third += 2;
        if is_state.contains(&false) || is_action.contains(&false) || is_promise.contains(&false) {
            return Ok(());
        }
        Err(match self.find_cycle(node) {
            Ok(found) => Stop::Found(found),
            Err(declined) => Stop::Declined(declined),
        })
    }

    // The bad cycle `printErrorTrace` finds from the node, as the nodes on its cycle stack.
    fn find_cycle(&mut self, node: usize) -> Result<Found, Declined> {
        let lost = || Declined::from("a bad cycle TLC fails to print");
        let model = self.model();
        let states_checks = model.infinitely_often_states.clone();
        let action_checks = model.infinitely_often_actions.clone();
        let promises = self.promises().to_vec();
        let mut cycle: Vec<usize> = Vec::new();
        let low = self.third - 1;
        let mut is_state = vec![false; states_checks.len()];
        let mut is_action = vec![false; action_checks.len()];
        let mut is_promise = vec![false; promises.len()];
        let mut count = is_state.len() + is_action.len() + is_promise.len();
        let mut current = node;
        while count > 0 {
            self.graph.nodes[current].number = self.third;
            let count_before = count;
            'next: loop {
                for (index, &check) in states_checks.iter().enumerate() {
                    if !is_state[index] && self.graph.nodes[current].states[check] {
                        is_state[index] = true;
                        count -= 1;
                    }
                }
                for (index, &promise) in promises.iter().enumerate() {
                    if !is_promise[index] && self.is_fulfilling(current, promise) {
                        is_promise[index] = true;
                        count -= 1;
                    }
                }
                if count == 0 {
                    break;
                }
                let mut in_component = None;
                let mut unvisited = None;
                let count_actions = count;
                for index in 0..self.graph.nodes[current].successors.len() {
                    let target = self.graph.nodes[current].successors[index];
                    let number = self.graph.nodes[target].number;
                    if low <= number && number <= self.third {
                        in_component = Some(target);
                        for (position, &check) in action_checks.iter().enumerate() {
                            if !is_action[position]
                                && self.graph.nodes[current].actions[index][check]
                            {
                                is_action[position] = true;
                                count -= 1;
                            }
                        }
                    }
                    if count < count_actions {
                        cycle.push(current);
                        current = target;
                        self.third += 1;
                        break 'next;
                    }
                    if low <= number && number < self.third {
                        unvisited = Some(target);
                    }
                }
                if count < count_before {
                    cycle.push(current);
                    current = in_component.ok_or_else(lost)?;
                    self.third += 1;
                    break;
                }
                // Backtrack where no successor is left to visit.
                while unvisited.is_none() {
                    current = cycle.pop().ok_or_else(lost)?;
                    for &target in &self.graph.nodes[current].successors {
                        let number = self.graph.nodes[target].number;
                        if low <= number && number < self.third {
                            cycle.push(current);
                            unvisited = Some(target);
                            break;
                        }
                    }
                }
                cycle.push(current);
                current = unvisited.ok_or_else(lost)?;
                self.graph.nodes[current].number = self.third;
            }
        }
        // Close the path to form a cycle; `current` isn't on the stack.
        self.third += 1;
        self.graph.nodes[current].number = self.third;
        'done: while current != node {
            let mut is_found = false;
            for index in 0..self.graph.nodes[current].successors.len() {
                let target = self.graph.nodes[current].successors[index];
                let number = self.graph.nodes[target].number;
                if low <= number && number < self.third {
                    cycle.push(current);
                    if target == node {
                        break 'done;
                    }
                    is_found = true;
                    current = target;
                    self.graph.nodes[current].number = self.third;
                    break;
                }
            }
            if !is_found {
                current = cycle.pop().ok_or_else(lost)?;
            }
        }
        if cycle.is_empty() {
            cycle.push(current);
        }
        Ok(Found {
            node,
            initial: self.initial,
            cycle,
        })
    }

    // `BEGraph.getPath`: a breadth-first path from the initial node to the node.
    fn path(&mut self, start: usize, end: usize) -> Result<Vec<usize>, Declined> {
        if start == end {
            self.graph.nodes[start].parent = None;
        } else {
            let unseen = self.graph.nodes[start].is_visited;
            self.graph.nodes[start].is_visited = !unseen;
            let mut queue = std::collections::VecDeque::from([(start, None)]);
            let mut is_found = false;
            while !is_found {
                let Some((current, parent)) = queue.pop_front() else {
                    return Err(Declined::from("a behavior graph TLC fails to construct"));
                };
                for index in 0..self.graph.nodes[current].successors.len() {
                    let next = self.graph.nodes[current].successors[index];
                    if self.graph.nodes[next].is_visited == unseen {
                        if next == end {
                            self.graph.nodes[end].parent = Some(current);
                            is_found = true;
                            break;
                        }
                        self.graph.nodes[next].is_visited = !unseen;
                        queue.push_back((next, Some(current)));
                    }
                }
                self.graph.nodes[current].parent = parent;
            }
        }
        let mut path = Vec::new();
        let mut current = Some(end);
        while let Some(node) = current {
            path.push(node);
            current = self.graph.nodes[node].parent;
        }
        path.reverse();
        Ok(path)
    }
}

/// `LiveCheck1.checkTrace` of a trace, the state of the graph at each position: the first
/// counterexample of any solution, in their order, as `printErrorTrace` prints it, or none.
pub(crate) fn check_trace(
    checker: &mut Checker,
    source: &Source<'_>,
    trace: &[u32],
) -> Result<Option<TraceCounterexample>, Declined> {
    if trace.is_empty() {
        return Err(Declined::from("an empty trace"));
    }
    for behavior in 0..checker.behaviors.len() {
        let solution = checker.behaviors[behavior].solution;
        let graph = Checks {
            checker,
            source,
            behavior,
        }
        .construct(trace)?;
        let mut search = Search {
            graph,
            checker,
            solution,
            model: 0,
            stack: Vec::new(),
            first: 1,
            second: MAX_FIRST + 1,
            third: MAX_SECOND + 1,
            start_second: MAX_FIRST + 1,
            start_third: MAX_SECOND + 1,
            first_component: MAX_FIRST + 1,
            second_component: MAX_SECOND + 1,
            initial: 0,
        };
        let initial = search.graph.initial.clone();
        let mut found = None;
        for node in initial {
            search.initial = node;
            if search.graph.nodes[node].number == 0 {
                match search.check_components(node) {
                    Ok(_) => {}
                    Err(Stop::Found(lasso)) => {
                        found = Some(lasso);
                        break;
                    }
                    Err(Stop::Declined(declined)) => return Err(declined),
                }
            }
        }
        let Some(found) = found else {
            continue;
        };
        return Ok(Some(print_error_trace(&mut search, &found, trace)?));
    }
    Ok(None)
}

// What `printErrorTrace` prints of the counterexample: its states are the trace's, from the first,
// as many as the prefix to the node and the cycle change states (`StateTraceResolver`).
fn print_error_trace(
    search: &mut Search<'_>,
    found: &Found,
    trace: &[u32],
) -> Result<TraceCounterexample, Declined> {
    let prefix = search.path(found.initial, found.node)?;
    let state_of = |node: usize| search.graph.nodes[node].state;
    let mut length = 1;
    for pair in prefix.windows(2) {
        if state_of(pair[1]) != state_of(pair[0]) {
            length += 1;
        }
    }
    let loop_start = length - 1;
    for pair in found.cycle.windows(2) {
        if state_of(pair[1]) != state_of(pair[0]) {
            length += 1;
        }
    }
    if length > trace.len() {
        return Err(Declined::from("a counterexample longer than its trace"));
    }
    // TLC compares the node's state with the last state it printed, and else names the trace's
    // next state as the one it steps back by, which fails past the trace's end.
    let is_stuttering = state_of(found.node) == trace[length - 1];
    if !is_stuttering && length == trace.len() {
        return Err(Declined::from(
            "a step back into the cycle past the end of the trace",
        ));
    }
    Ok(TraceCounterexample {
        length,
        loop_start,
        is_stuttering,
    })
}
