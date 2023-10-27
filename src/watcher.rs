use std::collections::VecDeque;

use crate::formula::{Literal, Variable};

/// I haven't actually looked up how to implement two-watched literals,
/// so this might not be the best implementation...
pub struct TwoWatchedLiterals {
    lists: Vec<Vec<usize>>,
    watchers: Vec<(Literal, Literal)>,
    queue: VecDeque<Variable>,
    pub new_asserting_clauses: VecDeque<usize>,
}

impl TwoWatchedLiterals {
    pub fn new(variable_count: usize, clause_count: usize) -> Self {
        Self {
            lists: (0..(variable_count + 1)).map(|_| Vec::with_capacity(clause_count)).collect::<Vec<_>>(),
            watchers: Vec::with_capacity(clause_count),
            queue: VecDeque::new(),
            new_asserting_clauses: VecDeque::new(),
        }
    }

    pub fn add_clause(&mut self, clause: usize, literals: (Literal, Literal)) {
        debug_assert!(literals.0 != literals.1);
        self.lists[literals.0.variable().index()].push(clause);
        self.lists[literals.1.variable().index()].push(clause);
        self.watchers.push(literals);
    }

    pub fn add_dummy_clause(&mut self) {
        let dummy = Literal::try_from(i32::MAX).unwrap();
        self.watchers.push((dummy, dummy));
    }

    pub fn move_clause(&mut self, clause: usize, from: Literal, to: Literal) {
        let watchers = &mut self.watchers[clause];

        debug_assert!(watchers.0 != to);
        debug_assert!(watchers.1 != to);

        if watchers.0 == from {
            watchers.0 = to;
        } else if watchers.1 == from {
            watchers.1 = to;
        } else {
            unreachable!();
        }
        self.lists[to.variable().index()].push(clause);
    }

    pub fn get(&mut self, variable: Variable, index: usize) -> Option<(usize, Literal, Literal)> {
        let list = &mut self.lists[variable.index()];
        loop {
            let clause = *list.get(index)?;
            let watchers = &mut self.watchers[clause];
            if watchers.0.variable() == variable {
                return Some((clause, watchers.0, watchers.1));
            }
            if watchers.1.variable() == variable {
                return Some((clause, watchers.1, watchers.0));
            }
            list.swap_remove(index); // clause has been moved
        }
    }

    pub fn next_in_queue(&mut self) -> Option<Variable> {
        self.queue.pop_front()
    }

    pub fn enqueue(&mut self, v: Variable) {
        if !self.queue.contains(&v) {
            self.queue.push_back(v);
        }
    }
}


