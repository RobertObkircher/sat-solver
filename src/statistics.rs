use std::time::Duration;

#[derive(Debug, Default)]
pub struct Statistics {
    pub eliminated_x_or_not_x_clauses: usize,
    pub eliminated_x_or_x_literals: usize,
    pub parse_duration: Duration,
    pub pure_literals: usize,
}
