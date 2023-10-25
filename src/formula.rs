use std::iter::FusedIterator;
use std::num::{NonZeroI32, TryFromIntError};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Variable(NonZeroI32);

impl Variable {
    pub fn index(self) -> usize {
        self.0.get() as usize
    }

    pub fn literal(self, sign: bool) -> Literal {
        Literal(if sign { self.0 } else { -self.0 })
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Literal(NonZeroI32);

impl Literal {
    pub fn negated(self) -> Literal {
        Literal(-self.0)
    }

    pub fn variable(self) -> Variable {
        Variable(self.0.abs())
    }

    pub fn value(self) -> bool {
        self.0.is_positive()
    }
}

impl From<NonZeroI32> for Literal {
    fn from(value: NonZeroI32) -> Self {
        Self(value)
    }
}

impl TryFrom<i32> for Literal {
    type Error = TryFromIntError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        value.try_into().map(Literal)
    }
}

pub struct CnfFormula {
    pub comments: String,
    pub variable_count: usize,
    pub literals: Vec<Literal>,
    pub clauses: Vec<usize>,
}

impl CnfFormula {
    pub fn get_clause(&self, index: usize) -> &[Literal] {
        let start = if index > 0 { self.clauses[index - 1] } else { 0 };
        let end = self.clauses[index];
        return &self.literals[start..end];
    }
}

impl CnfFormula {
    pub fn clauses(&self) -> impl Iterator<Item=&[Literal]> + DoubleEndedIterator + ExactSizeIterator + FusedIterator {
        (0..self.clauses.len()).map(|c| self.get_clause(c))
    }
}
