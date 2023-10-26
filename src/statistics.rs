use std::time::Duration;

#[derive(Debug, Default)]
pub struct Statistics {
    pub eliminated_x_or_not_x_clauses: usize,
    pub parse_duration: Duration,
}
