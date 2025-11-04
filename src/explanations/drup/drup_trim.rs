// Copyright (c) 2014-2015, Marijn Heule and Nathan Wetzler
// Last edit, March 4, 2015
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
// associated documentation files (the "Software"), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge, publish, distribute,
// sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
// NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
// OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#![allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)]

use std::collections::HashMap;
use std::num::Wrapping;

use crate::collections::LNG_VEC_INIT_SIZE;

pub struct DrupResult {
    pub trivial_unsat: bool,
    pub unsat_core: Vec<Vec<isize>>,
}

pub fn drup_compute(original_problem: Vec<Vec<isize>>, proof: Vec<Vec<isize>>) -> DrupResult {
    let mut s = Solver::new(original_problem, proof);
    if s.parse() {
        DrupResult { trivial_unsat: false, unsat_core: s.verify() }
    } else {
        DrupResult { trivial_unsat: true, unsat_core: vec![] }
    }
}

struct Solver {
    original_problem: Vec<Vec<isize>>,
    proof: Vec<Vec<isize>>,
    core: Vec<Vec<isize>>,
    delete: bool,
    db: Vec<isize>,
    n_vars: usize,
    n_clauses: usize,
    false_stack: Vec<isize>,
    reason: Vec<isize>,
    internal_false: Vec<isize>,
    forced_ptr: isize,
    processed_ptr: isize,
    assigned_ptr: isize,
    adlist: Vec<isize>,
    wlist: Vec<Vec<isize>>,
    count: isize,
    adlemmas: isize,
    lemmas: isize,
}

impl Solver {
    fn new(original_problem: Vec<Vec<isize>>, proof: Vec<Vec<isize>>) -> Self {
        let n_vars = original_problem.iter().map(|vector| vector.iter().map(|&i| i.abs()).max().unwrap_or(0)).max().unwrap_or(0) as usize;
        let n_clauses = original_problem.len();
        let mut wlist = Vec::with_capacity(2 * n_vars + 3);
        (0..(2 * n_vars + 3)).for_each(|_| wlist.push(Vec::with_capacity(LNG_VEC_INIT_SIZE)));
        Self {
            // explicitly initialized
            original_problem,
            proof,
            n_vars,
            n_clauses,
            core: Vec::new(),
            delete: true,
            false_stack: vec![0; n_vars + 1],
            reason: vec![0; n_vars + 1],
            internal_false: vec![0; 2 * n_vars + 3],
            adlist: Vec::new(),
            count: 1,
            wlist,
            db: Vec::new(),
            // default values -- computed later
            forced_ptr: 0,
            processed_ptr: 0,
            assigned_ptr: 0,
            adlemmas: 0,
            lemmas: 0,
        }
    }

    fn parse(&mut self) -> bool {
        let mut del = false;
        let mut n_zeros = self.n_clauses as isize;
        let mut buffer = Vec::with_capacity(LNG_VEC_INIT_SIZE);
        let mut marks = vec![0; 2 * self.n_vars + 3];
        let mut mark = 0;

        let mut hash_table: HashMap<isize, Vec<isize>> = HashMap::new();
        let mut current_file = &self.original_problem;
        let mut clause_nr = 0;

        loop {
            let mut file_switch_flag = n_zeros <= 0;
            let opt_clause = current_file.get(clause_nr);
            clause_nr += 1;
            let Some(clause) = opt_clause else {
                self.lemmas = self.db.len() as isize + 1;
                break;
            };
            if file_switch_flag && clause[0] == -1 {
                del = true;
            }
            for elem in clause.iter().skip(usize::from(file_switch_flag)) {
                buffer.push(*elem);
            }
            if clause_nr >= current_file.len() && !file_switch_flag {
                file_switch_flag = true;
                clause_nr = 0;
                current_file = &self.proof;
            }
            if clause_nr > current_file.len() && file_switch_flag && !current_file.is_empty() {
                break;
            }
            mark += 1;
            let hash = get_hash(&mut marks, mark, &buffer);
            if del {
                if self.delete {
                    let match_clause = self.match_clause(hash_table.get_mut(&hash).unwrap(), &marks, mark, &buffer);
                    hash_table.get_mut(&hash).unwrap().pop();
                    self.adlist.push((match_clause << 1) + 1);
                }
                del = false;
                buffer.clear();
                continue;
            }
            let clause_ptr = self.db.len() as isize + 1;
            self.db.push(2 * self.count);
            self.count += 1;
            self.db.extend_from_slice(&buffer);
            self.db.push(0);

            let vec = hash_table.entry(hash).or_insert_with(|| Vec::<isize>::with_capacity(LNG_VEC_INIT_SIZE));
            vec.push(clause_ptr);

            self.adlist.push(clause_ptr << 1);

            if n_zeros == 0 {
                self.lemmas = clause_ptr;
                self.adlemmas = self.adlist.len() as isize - 1;
            }
            if n_zeros > 0 {
                if buffer.is_empty() || (buffer.len() == 1 && self.internal_false[index(self.db[clause_ptr as usize])] != 0) {
                    return false;
                } else if buffer.len() == 1 {
                    let cls = self.db[clause_ptr as usize];
                    if self.internal_false[index(-cls)] == 0 {
                        self.reason[cls.unsigned_abs()] = clause_ptr + 1;
                        assign(cls, &mut self.internal_false, &mut self.false_stack, &mut self.assigned_ptr);
                    }
                } else {
                    add_watch(clause_ptr, 0, &self.db, &mut self.wlist);
                    add_watch(clause_ptr, 1, &self.db, &mut self.wlist);
                }
            } else if buffer.is_empty() {
                break;
            }
            buffer.clear();
            n_zeros -= 1;
        }
        true
    }

    #[allow(clippy::too_many_lines, clippy::cognitive_complexity)]
    fn verify(mut self) -> Vec<Vec<isize>> {
        let mut ad: isize;
        let mut flag = false;
        let mut clause_ptr = 0;
        let mut lemmas_ptr = self.lemmas;
        let last_ptr = self.lemmas;
        let mut checked = self.adlemmas;
        let mut buffer = Vec::<isize>::with_capacity(LNG_VEC_INIT_SIZE);
        let mut time: isize; // redundant according to IntelliJ = *self.db.get_unsafe(lemmas_ptr - 1);

        let goto_post_process = self.processed_ptr < self.assigned_ptr && !self.propagate();
        self.forced_ptr = self.processed_ptr;

        if !goto_post_process {
            let mut goto_verification = false;
            while !goto_verification {
                flag = false;
                buffer.clear();
                // redundant according to IntelliJ:  time = *self.db.get_unsafe(lemmas_ptr - 1);
                clause_ptr = lemmas_ptr;
                loop {
                    ad = self.adlist[checked as usize];
                    checked += 1;
                    let d = ad & 1;
                    let c_ptr = ad >> 1;
                    if d != 0 && self.db[(c_ptr + 1) as usize] != 0 {
                        if self.reason[self.db[c_ptr as usize].unsigned_abs()] - 1 == ad >> 1 {
                            continue;
                        }
                        remove_watch(c_ptr, 0, &self.db, &mut self.wlist);
                        remove_watch(c_ptr, 1, &self.db, &mut self.wlist);
                    }
                    if d == 0 {
                        break;
                    }
                }

                while self.db[lemmas_ptr as usize] != 0 {
                    let lit = self.db[lemmas_ptr as usize];
                    lemmas_ptr += 1;
                    if self.internal_false[index(-lit)] != 0 {
                        flag = true;
                    }
                    if self.internal_false[index(lit)] == 0 {
                        if buffer.len() <= 1 {
                            self.db[(lemmas_ptr - 1) as usize] = self.db[clause_ptr as usize + buffer.len()];
                            self.db[clause_ptr as usize + buffer.len()] = lit;
                        }
                        buffer.push(lit);
                    }
                }

                if self.db[(clause_ptr + 1) as usize] != 0 {
                    add_watch(clause_ptr, 0, &self.db, &mut self.wlist);
                    add_watch(clause_ptr, 1, &self.db, &mut self.wlist);
                }

                lemmas_ptr += EXTRA;

                if flag {
                    self.adlist[(checked - 1) as usize] = 0;
                    continue; // Clause is already satisfied
                }
                assert!(!buffer.is_empty(), "Conflict claimed, but not detected");

                if buffer.len() == 1 {
                    assign(buffer[0], &mut self.internal_false, &mut self.false_stack, &mut self.assigned_ptr);
                    self.reason[buffer[0].unsigned_abs()] = clause_ptr + 1;
                    self.forced_ptr = self.processed_ptr;
                    if !self.propagate() {
                        goto_verification = true;
                    }
                }

                if lemmas_ptr >= self.db.len() as isize {
                    break;
                }
            }
            assert!(goto_verification, "No conflict");

            self.forced_ptr = self.processed_ptr;
            lemmas_ptr = clause_ptr - EXTRA;

            loop {
                buffer.clear();
                clause_ptr = lemmas_ptr + EXTRA;
                loop {
                    checked -= 1;
                    ad = self.adlist[checked as usize];
                    let d = ad & 1;
                    let c_ptr = ad >> 1;
                    if d != 0 && self.db[(c_ptr + 1) as usize] != 0 {
                        if self.reason[self.db[c_ptr as usize].unsigned_abs()] - 1 == ad >> 1 {
                            continue;
                        }
                        add_watch(c_ptr, 0, &self.db, &mut self.wlist);
                        add_watch(c_ptr, 1, &self.db, &mut self.wlist);
                    }
                    if d == 0 {
                        break;
                    }
                }

                time = self.db[(clause_ptr - 1) as usize];

                if self.db[(clause_ptr + 1) as usize] != 0 {
                    remove_watch(clause_ptr, 0, &self.db, &mut self.wlist);
                    remove_watch(clause_ptr, 1, &self.db, &mut self.wlist);
                }

                let goto_next_lemma = ad == 0;

                if !goto_next_lemma {
                    while self.db[clause_ptr as usize] != 0 {
                        let lit = self.db[clause_ptr as usize];
                        clause_ptr += 1;
                        if self.internal_false[index(-lit)] != 0 {
                            flag = true;
                        }
                        if self.internal_false[index(lit)] == 0 {
                            buffer.push(lit);
                        }
                    }

                    if flag && buffer.len() == 1 {
                        loop {
                            self.forced_ptr -= 1;
                            self.internal_false[index(self.false_stack[self.forced_ptr as usize])] = 0;
                            if self.false_stack[self.forced_ptr as usize] == -buffer[0] {
                                break;
                            }
                        }
                        self.processed_ptr = self.forced_ptr;
                        self.assigned_ptr = self.forced_ptr;
                    }

                    if (time & 1) != 0 {
                        for &b in &buffer {
                            assign(-b, &mut self.internal_false, &mut self.false_stack, &mut self.assigned_ptr);
                            self.reason[b.unsigned_abs()] = 0;
                        }
                        assert!(!self.propagate(), "Formula is SAT");
                    }
                }

                if lemmas_ptr + EXTRA == last_ptr {
                    break;
                }
                lemmas_ptr -= 1;
                while self.db[lemmas_ptr as usize] != 0 {
                    lemmas_ptr -= 1;
                }
            }
        }

        lemmas_ptr = 0;
        while lemmas_ptr + EXTRA <= last_ptr {
            if (self.db[lemmas_ptr as usize] & 1) != 0 {
                self.count += 1;
            }
            lemmas_ptr += 1;
            while self.db[lemmas_ptr as usize] != 0 {
                lemmas_ptr += 1;
            }
        }
        lemmas_ptr = 0;

        while lemmas_ptr + EXTRA <= last_ptr {
            let mut core_vec = Vec::<isize>::with_capacity(LNG_VEC_INIT_SIZE);
            let marked = self.db[lemmas_ptr as usize] & 1;
            lemmas_ptr += 1;
            while self.db[lemmas_ptr as usize] != 0 {
                if marked != 0 {
                    core_vec.push(self.db[lemmas_ptr as usize]);
                }
                lemmas_ptr += 1;
            }
            if marked != 0 {
                self.core.push(core_vec);
            }
            lemmas_ptr += 1;
        }

        self.count = 0;
        while lemmas_ptr + EXTRA <= last_ptr {
            time = self.db[lemmas_ptr as usize];
            let marked = time & 1;
            lemmas_ptr += 1;
            if marked != 0 {
                self.count += 1;
            }
            while self.db[lemmas_ptr as usize] != 0 {
                lemmas_ptr += 1;
            }
            lemmas_ptr += 1;
        }

        self.core
    }

    fn match_clause(&self, clause_list: &mut [isize], marks: &[isize], mark: isize, input: &[isize]) -> isize {
        for i in 0..clause_list.len() {
            let mut match_size = 0;
            let mut aborted = false;
            let mut l = clause_list[i];
            while self.db[l as usize] != 0 {
                if marks[index(self.db[l as usize])] != mark {
                    aborted = true;
                    break;
                }
                match_size += 1;
                l += 1;
            }
            if !aborted && input.len() == match_size {
                let result = clause_list[i];
                clause_list[i] = *clause_list.last().unwrap();
                return result;
            }
        }
        panic!("Could not match deleted clause")
    }

    fn propagate(&mut self) -> bool {
        let mut check = 0;
        let mut lit: isize;
        let mut last_lit = 0;
        let mut last_watch_ptr = 0;
        let mut start = [self.processed_ptr, self.processed_ptr];
        let mut goto_flip_check = true;
        while goto_flip_check {
            goto_flip_check = false;
            check ^= 1;
            while !goto_flip_check && start[check] < self.assigned_ptr {
                // While unprocessed false literals
                lit = self.false_stack[start[check] as usize]; // Get first unprocessed literal
                start[check] += 1;
                let watch_lit = index(lit);
                let mut watch_ptr = if lit == last_lit { last_watch_ptr } else { 0 };

                // While there are watched clauses (watched by lit)
                while watch_ptr < self.wlist[watch_lit].len() {
                    if (self.wlist[watch_lit][watch_ptr] & 1) != check as isize {
                        watch_ptr += 1;
                        continue;
                    }
                    let clause_ptr = self.wlist[watch_lit][watch_ptr] / 2; // Get the clause from DB
                    if self.internal_false[index(-self.db[clause_ptr as usize])] != 0
                        || self.internal_false[index(-self.db[(clause_ptr + 1) as usize])] != 0
                    {
                        watch_ptr += 1;
                        continue;
                    }
                    if self.db[clause_ptr as usize] == lit {
                        // Ensure that the other watched literal is in front
                        self.db[clause_ptr as usize] = self.db[(clause_ptr + 1) as usize];
                    }
                    let mut goto_next_clause = false;
                    let mut i = 2;
                    // Scan the non-watched literals
                    while self.db[(clause_ptr + i) as usize] != 0 {
                        if self.internal_false[index(self.db[(clause_ptr + i) as usize])] == 0 {
                            // When clause[j] is not false, it is either true or unset
                            self.db[(clause_ptr + 1) as usize] = self.db[(clause_ptr + i) as usize];
                            self.db[(clause_ptr + i) as usize] = lit; // Swap literals
                            let to_push = self.wlist[watch_lit][watch_ptr];
                            self.wlist.get_mut(index(self.db[(clause_ptr + 1) as usize])).unwrap().push(to_push); // Add the watch to the list of clause[1]
                            let to_set = *self.wlist.get_mut(index(lit)).unwrap().last().unwrap();
                            self.wlist.get_mut(watch_lit).unwrap()[watch_ptr] = to_set; // Remove pointer
                            self.wlist.get_mut(index(lit)).unwrap().pop();
                            goto_next_clause = true;
                            break;
                        }
                        // go to the next watched clause
                        i += 1;
                    }
                    if !goto_next_clause {
                        self.db[(clause_ptr + 1) as usize] = lit;
                        watch_ptr += 1; // Set lit at clause[1] and set next watch
                        if self.internal_false[index(self.db[clause_ptr as usize])] == 0 {
                            // If the other watched literal is falsified,
                            // A unit clause is found, and the reason is set
                            assign(self.db[clause_ptr as usize], &mut self.internal_false, &mut self.false_stack, &mut self.assigned_ptr);
                            self.reason[self.db[clause_ptr as usize].unsigned_abs()] = clause_ptr + 1;
                            if check == 0 {
                                start[0] -= 1;
                                last_lit = lit;
                                last_watch_ptr = watch_ptr;
                                goto_flip_check = true;
                                break;
                            }
                        } else {
                            self.analyze(clause_ptr);
                            return false;
                        } // Found a root level conflict -> UNSAT
                    }
                }
            } // Set position for next clause
            if check != 0 {
                goto_flip_check = true;
            }
        }
        self.processed_ptr = self.assigned_ptr;
        true
    }

    fn analyze(&mut self, clause_ptr: isize) {
        self.mark_clause(clause_ptr, 0);
        while self.assigned_ptr > 0 {
            self.assigned_ptr -= 1;
            let lit = self.false_stack[self.assigned_ptr as usize];
            if self.internal_false[index(lit)] == MARK && self.reason[lit.unsigned_abs()] != 0 {
                self.mark_clause(self.reason[lit.unsigned_abs()], -1);
            }
            self.internal_false[index(lit)] = isize::from(self.assigned_ptr < self.forced_ptr);
        }
        self.processed_ptr = self.forced_ptr;
        self.assigned_ptr = self.forced_ptr;
    }

    fn mark_clause(&mut self, mut clause_ptr: isize, idx: isize) {
        if (self.db[(clause_ptr + idx - 1) as usize] & 1) == 0 {
            self.db[(clause_ptr + idx - 1) as usize] |= 1;
            if self.db[(clause_ptr + 1 + idx) as usize] == 0 {
                return;
            }
            self.mark_watch(clause_ptr, idx, -idx);
            self.mark_watch(clause_ptr, 1 + idx, -idx);
        }
        while self.db[clause_ptr as usize] != 0 {
            self.internal_false[index(self.db[clause_ptr as usize])] = MARK;
            clause_ptr += 1;
        }
    }

    fn mark_watch(&mut self, clause_ptr: isize, idx: isize, offset: isize) {
        let watch = self.wlist.get_mut(index(self.db[(clause_ptr + idx) as usize])).unwrap();
        let clause = self.db[(clause_ptr - offset - 1) as usize];
        let mut watch_ptr = 0;
        loop {
            let tmp_clause = self.db[((watch[watch_ptr] >> 1) - 1) as usize];
            if tmp_clause == clause {
                watch[watch_ptr] |= 1;
                return;
            }
            watch_ptr += 1;
        }
    }
}

const fn index(lit: isize) -> usize {
    if lit > 0 { lit as usize * 2 } else { ((-lit * 2) ^ 1) as usize }
}

fn get_hash(marks: &mut [isize], mark: isize, input: &Vec<isize>) -> isize {
    let mut sum = Wrapping(0);
    let mut xor = Wrapping(0);
    let mut prod = Wrapping(1);
    for &elem in input {
        sum += elem;
        xor ^= elem;
        prod *= elem;
        marks[index(elem)] = mark;
    }
    ((Wrapping(1023) * sum + prod) ^ ((Wrapping(31) * xor) % BIGINIT)).0.abs()
}

fn assign(a: isize, internal_false: &mut [isize], false_stack: &mut [isize], assigned_ptr: &mut isize) {
    internal_false[index(-a)] = 1;
    false_stack[*assigned_ptr as usize] = -a;
    *assigned_ptr += 1;
}

fn add_watch(c_ptr: isize, idx: isize, db: &[isize], wlist: &mut [Vec<isize>]) {
    let lit = db[(c_ptr + idx) as usize];
    wlist[index(lit)].push(c_ptr << 1);
}

fn remove_watch(c_ptr: isize, idx: isize, db: &[isize], wlist: &mut [Vec<isize>]) {
    let lit = db[(c_ptr + idx) as usize];
    let watch = wlist.get_mut(index(lit)).unwrap();
    let mut watch_ptr = 0;
    loop {
        if (watch[watch_ptr] >> 1) == c_ptr {
            let back = *watch.last().unwrap();
            watch[watch_ptr] = back;
            watch.pop();
            return;
        }
        watch_ptr += 1;
    }
}

const BIGINIT: Wrapping<isize> = Wrapping(1_000_000);
const EXTRA: isize = 2;
const MARK: isize = 3;
