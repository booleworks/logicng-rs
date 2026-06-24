#![allow(clippy::cast_possible_truncation)]
use num_bigint::{BigUint, ToBigUint};

use crate::handlers::NopHandler;

use super::bdd_kernel::{is_const, is_one, is_zero, BddKernel, BDD_FALSE, BDD_TRUE, MARKOFF, MARKON};

const CACHEID_SATCOU: usize = 0x2;
const CACHEID_PATHCOU_ONE: usize = 0x4;
const CACHEID_PATHCOU_ZERO: usize = 0x8;

/// Finds one satisfying variable assignment and returns it as BDD.
pub fn sat_one(r: usize, kernel: &mut BddKernel) -> usize {
    if r < 2 {
        return r;
    }
    kernel.init_ref();
    sat_one_rec(r, kernel)
}

/// Returns an arbitrary model for a given BDD which contains at least the given variables.
/// If a variable is a don't care variable, it will be assigned with the given default value.
pub fn sat_one_set(r: usize, var: usize, default: usize, kernel: &mut BddKernel) -> usize {
    if is_zero(r) {
        return r;
    }
    assert!(is_const(default), "Polarity for satOneSet must be a constant");
    kernel.init_ref();
    sat_one_set_rec(r, var, default, kernel)
}

/// Returns all nodes for a given root node in their internal representation.  The internal
/// representation is stored in an array: [node number, variable, low, high]
pub fn all_nodes(r: usize, kernel: &mut BddKernel) -> Vec<[usize; 4]> {
    let mut result = Vec::new();
    if r < 2 {
        return result;
    }
    kernel.mark(r);
    for n in 0..kernel.nodesize {
        if kernel.level(n) & MARKON != 0 {
            kernel.set_level(n, kernel.level(n) & MARKOFF);
            result.push([n, kernel.level2var[kernel.level(n)], kernel.low(n).unwrap(), kernel.high(n)]);
        }
    }
    result
}

/// Returns a full model in all variables for the given BDD.
pub fn full_sat_one(r: usize, kernel: &mut BddKernel) -> usize {
    if r == 0 {
        return BDD_FALSE;
    }
    kernel.init_ref();
    let mut res = full_sat_one_rec(r, kernel);
    for v in (0..kernel.level(r)).rev() {
        let node = kernel.make_node(v, res, BDD_FALSE);
        res = kernel.push_ref(node);
    }
    res
}

/// Returns all models for a given BDD.
pub fn all_sat(r: usize, kernel: &mut BddKernel) -> Vec<Vec<i8>> {
    let mut allsat_profile = vec![0; kernel.varnum];
    for v in (0..kernel.level(r)).rev() {
        allsat_profile[kernel.level2var[v]] = -1;
    }
    kernel.init_ref();
    let mut allsat = Vec::new();
    all_sat_rec(r, &mut allsat, &mut allsat_profile, kernel);
    allsat
}

/// Returns the number of nodes for a given BDD.
pub fn node_count(r: usize, kernel: &mut BddKernel) -> usize {
    let count = kernel.mark_count(r);
    kernel.unmark(r);
    count
}

///Returns the model count for the given BDD.
pub fn sat_count(r: usize, kernel: &mut BddKernel) -> BigUint {
    let size = 2.to_biguint().unwrap().pow(kernel.level(r) as u32);
    sat_count_rec(r, CACHEID_SATCOU, kernel) * size
}

/// Returns the number of paths to the terminal node 'one'.
pub fn path_count_one(r: usize, kernel: &mut BddKernel) -> BigUint {
    path_count_rec(r, CACHEID_PATHCOU_ONE, 1, 0, kernel)
}

/// Returns the number of paths to the terminal node 'zero'.
pub fn path_count_zero(r: usize, kernel: &mut BddKernel) -> BigUint {
    path_count_rec(r, CACHEID_PATHCOU_ZERO, 0, 1, kernel)
}

/// Returns all unsatisfiable assignments for a given BDD.
pub fn all_unsat(r: usize, kernel: &mut BddKernel) -> Vec<Vec<i8>> {
    let mut allunsat_profile = vec![0; kernel.varnum];
    for v in (0..kernel.level(r)).rev() {
        allunsat_profile[kernel.level2var[v]] = -1;
    }
    kernel.init_ref();
    let mut allunsat = Vec::new();
    all_unsat_rec(r, &mut allunsat, &mut allunsat_profile, kernel);
    allunsat
}

/// Returns how often each variable occurs in the given BDD.
pub fn var_profile(r: usize, kernel: &mut BddKernel) -> Vec<usize> {
    let mut varprofile = vec![0; kernel.varnum];
    var_profile_rec(r, &mut varprofile, kernel);
    kernel.unmark(r);
    varprofile
}

/// Returns all the variables that a given BDD depends on.
pub fn support(r: usize, kernel: &mut BddKernel) -> usize {
    if r < 2 || kernel.varnum == 0 {
        return BDD_FALSE;
    }
    let mut support = Vec::new();
    support_rec(r, &mut support, kernel);
    kernel.unmark(r);

    let mut res = 1;
    for n in support {
        kernel.add_ref(res, &mut NopHandler::new()).expect("Nop Handler never aborts.");
        let node = kernel.make_node(n, 0, res);
        kernel.del_ref(res);
        res = node;
    }
    res
}

fn sat_one_rec(r: usize, kernel: &mut BddKernel) -> usize {
    if is_const(r) {
        return r;
    }
    let node = if is_zero(kernel.low(r).unwrap()) {
        let res = sat_one_rec(kernel.high(r), kernel);
        kernel.make_node(kernel.level(r), BDD_FALSE, res)
    } else {
        let res = sat_one_rec(kernel.low(r).unwrap(), kernel);
        kernel.make_node(kernel.level(r), res, BDD_FALSE)
    };
    kernel.push_ref(node)
}

fn sat_one_set_rec(r: usize, var: usize, default: usize, kernel: &mut BddKernel) -> usize {
    if is_const(r) && is_const(var) {
        return r;
    }
    let r_level = kernel.level(r);
    let node = match r_level {
        _ if r_level < kernel.level(var) => {
            if is_zero(kernel.low(r).unwrap()) {
                let res = sat_one_set_rec(kernel.high(r), var, default, kernel);
                kernel.make_node(kernel.level(r), BDD_FALSE, res)
            } else {
                let res = sat_one_set_rec(kernel.low(r).unwrap(), var, default, kernel);
                kernel.make_node(kernel.level(r), res, BDD_FALSE)
            }
        }
        _ if r_level > kernel.level(var) => {
            let res = sat_one_set_rec(r, kernel.high(var), default, kernel);
            if default == BDD_TRUE {
                kernel.make_node(kernel.level(var), BDD_FALSE, res)
            } else {
                kernel.make_node(kernel.level(var), res, BDD_FALSE)
            }
        }
        _ => {
            if is_zero(kernel.low(r).unwrap()) {
                let res = sat_one_set_rec(kernel.high(r), kernel.high(var), default, kernel);
                kernel.make_node(kernel.level(r), BDD_FALSE, res)
            } else {
                let res = sat_one_set_rec(kernel.low(r).unwrap(), kernel.high(var), default, kernel);
                kernel.make_node(kernel.level(r), res, BDD_FALSE)
            }
        }
    };
    kernel.push_ref(node)
}

fn full_sat_one_rec(r: usize, kernel: &mut BddKernel) -> usize {
    if r < 2 {
        return r;
    }
    let node = if is_zero(kernel.low(r).unwrap()) {
        let mut res = full_sat_one_rec(kernel.high(r), kernel);
        let mut v = kernel.level(kernel.high(r)) - 1;
        while v > kernel.level(r) {
            let node = kernel.make_node(v, res, 0);
            res = kernel.push_ref(node);
            v -= 1;
        }
        kernel.make_node(kernel.level(r), 0, res)
    } else {
        let mut res = full_sat_one_rec(kernel.low(r).unwrap(), kernel);
        let mut v = kernel.level(kernel.low(r).unwrap()) - 1;
        while v > kernel.level(r) {
            let node = kernel.make_node(v, res, BDD_FALSE);
            res = kernel.push_ref(node);
            v -= 1;
        }
        kernel.make_node(kernel.level(r), res, 0)
    };
    kernel.push_ref(node)
}

fn all_sat_rec(r: usize, models: &mut Vec<Vec<i8>>, allsat_profile: &mut Vec<i8>, kernel: &mut BddKernel) {
    if is_one(r) {
        models.push(allsat_profile.clone());
        return;
    }
    if is_zero(r) {
        return;
    }
    if !is_zero(kernel.low(r).unwrap()) {
        allsat_profile[kernel.level2var[kernel.level(r)]] = 0;
        let mut v = kernel.level(kernel.low(r).unwrap()) - 1;
        while v > kernel.level(r) {
            allsat_profile[kernel.level2var[v]] = -1;
            v -= 1;
        }
        all_sat_rec(kernel.low(r).unwrap(), models, allsat_profile, kernel);
    }
    if !is_zero(kernel.high(r)) {
        allsat_profile[kernel.level2var[kernel.level(r)]] = 1;
        let mut v = kernel.level(kernel.high(r)) - 1;
        while v > kernel.level(r) {
            allsat_profile[kernel.level2var[v]] = -1;
            v -= 1;
        }
        all_sat_rec(kernel.high(r), models, allsat_profile, kernel);
    }
}

fn all_unsat_rec(r: usize, models: &mut Vec<Vec<i8>>, allunsat_profile: &mut Vec<i8>, kernel: &mut BddKernel) {
    if is_zero(r) {
        models.push(allunsat_profile.clone());
        return;
    }
    if is_one(r) {
        return;
    }
    if !is_one(kernel.low(r).unwrap()) {
        allunsat_profile[kernel.level2var[kernel.level(r)]] = 0;
        let mut v = kernel.level(kernel.low(r).unwrap()) - 1;
        while v > kernel.level(r) {
            allunsat_profile[kernel.level2var[v]] = -1;
            v -= 1;
        }
        all_unsat_rec(kernel.low(r).unwrap(), models, allunsat_profile, kernel);
    }
    if !is_one(kernel.high(r)) {
        allunsat_profile[kernel.level2var[kernel.level(r)]] = 1;
        let mut v = kernel.level(kernel.high(r)) - 1;
        while v > kernel.level(r) {
            allunsat_profile[kernel.level2var[v]] = -1;
            v -= 1;
        }
        all_unsat_rec(kernel.high(r), models, allunsat_profile, kernel);
    }
}

fn sat_count_rec(root: usize, miscid: usize, kernel: &mut BddKernel) -> BigUint {
    if root < 2 {
        return root.to_biguint().unwrap();
    }
    let cache_abc = kernel.misccache.lookup(root);
    if cache_abc.0 == Some(root) && cache_abc.2 == miscid {
        return kernel.misccache.lookup_bdres(root);
    }
    let mut size = 0.to_biguint().unwrap();
    let s = 2.to_biguint().unwrap().pow((kernel.level(kernel.low(root).unwrap()) - kernel.level(root) - 1) as u32);
    size += s * sat_count_rec(kernel.low(root).unwrap(), miscid, kernel);
    let s = 2.to_biguint().unwrap().pow((kernel.level(kernel.high(root)) - kernel.level(root) - 1) as u32);
    size += s * sat_count_rec(kernel.high(root), miscid, kernel);
    kernel.misccache.set_with_bdres(root, (root, 0, miscid), size.clone());
    size
}

fn path_count_rec(r: usize, miscid: usize, count_true: usize, count_false: usize, kernel: &mut BddKernel) -> BigUint {
    if is_zero(r) {
        return count_false.to_biguint().unwrap();
    }
    if is_one(r) {
        return count_true.to_biguint().unwrap();
    }
    let cache_abc = kernel.misccache.lookup(r);
    if cache_abc.0 == Some(r) && cache_abc.2 == miscid {
        return kernel.misccache.lookup_bdres(r);
    }
    let size = path_count_rec(kernel.low(r).unwrap(), miscid, count_true, count_false, kernel)
        + path_count_rec(kernel.high(r), miscid, count_true, count_false, kernel);
    kernel.misccache.set_with_bdres(r, (r, 0, miscid), size.clone());
    size
}

fn var_profile_rec(r: usize, varprofile: &mut Vec<usize>, kernel: &mut BddKernel) {
    if r < 2 {
        return;
    }
    if (kernel.level(r) & MARKON) != 0 {
        return;
    }
    varprofile[kernel.level2var[kernel.level(r)]] += 1;
    kernel.set_level(r, kernel.level(r) | MARKON);
    var_profile_rec(kernel.low(r).unwrap(), varprofile, kernel);
    var_profile_rec(kernel.high(r), varprofile, kernel);
}

fn support_rec(r: usize, support: &mut Vec<usize>, kernel: &mut BddKernel) {
    if r < 2 {
        return;
    }
    if (kernel.level(r) & MARKON) != 0 || kernel.low(r).is_none() {
        return;
    }
    support.push(kernel.level(r));
    kernel.set_level(r, kernel.level(r) | MARKON);
    support_rec(kernel.low(r).unwrap(), support, kernel);
    support_rec(kernel.high(r), support, kernel);
}
