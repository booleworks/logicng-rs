use crate::solver::minisat::sat::MsLit;

/// A MiniSAT clause
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, PartialEq, Debug)]
pub struct MsClause {
    pub data: Vec<MsLit>,
    pub learnt: bool,
    is_at_most: bool,
    pub activity: f64,
    sz_without_selectors: isize,
    seen: bool,
    lbd: i64,
    can_be_del: bool,
    one_watched: bool,
    at_most_watchers: isize,
}

impl MsClause {
    pub fn new(data: Vec<MsLit>, learnt: bool) -> Self {
        Self {
            data,
            learnt,
            is_at_most: false,
            activity: 0.0,
            sz_without_selectors: 0,
            seen: false,
            lbd: 0,
            can_be_del: true,
            one_watched: false,
            at_most_watchers: -1,
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn get(&self, i: usize) -> MsLit {
        self.data[i]
    }

    pub fn set(&mut self, i: usize, lit: MsLit) {
        self.data[i] = lit;
    }

    pub fn rescale_activity(&mut self) {
        self.activity *= 1e-20;
    }

    pub fn range_copy_from(&self, from: usize) -> Vec<MsLit> {
        self.data[from..].to_vec()
    }
}
