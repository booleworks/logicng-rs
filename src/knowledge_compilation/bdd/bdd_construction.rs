use crate::knowledge_compilation::bdd::bdd_kernel::{is_const, BddKernel};

use super::bdd_kernel::{is_one, is_zero, pair, Operand, BDD_FALSE, BDD_TRUE, OPCODE_NOT};

const CACHEID_RESTRICT: usize = 0x1;
const CACHEID_FORALL: usize = 0x1;

/// Returns a BDD representing the i-th variable (one node with the children true and false).
pub fn ith_var(i: usize, kernel: &mut BddKernel) -> usize {
    assert!(i < kernel.varnum, "Illegal variable number: {i}");
    kernel.vars[i * 2]
}

/// Returns a BDD representing the negation of the i-th variable (one node with the children
/// true and false).
pub fn nith_var(i: usize, kernel: &mut BddKernel) -> usize {
    assert!(i < kernel.varnum, "Illegal variable number: {i}");
    kernel.vars[i * 2 + 1]
}

///Returns the variable index labeling the given root node.
pub fn bdd_var(root: usize, kernel: &mut BddKernel) -> usize {
    assert!(root >= 2, "Illegal node number: {root}");
    kernel.level2var[kernel.level(root)]
}

///Returns the false branch of the given root node.
pub fn bdd_low(root: usize, kernel: &mut BddKernel) -> usize {
    assert!(root >= 2, "Illegal node number: {root}");
    kernel.low(root).unwrap()
}

///Returns the true branch of the given root node.
pub fn bdd_high(root: usize, kernel: &mut BddKernel) -> usize {
    assert!(root >= 2, "Illegal node number: {root}");
    kernel.high(root)
}

/// Returns the conjunction of two BDDs.
pub fn and(l: usize, r: usize, kernel: &mut BddKernel) -> usize {
    kernel.apply(l, r, &Operand::and())
}

/// Returns the disjunction of two BDDs.
pub fn or(l: usize, r: usize, kernel: &mut BddKernel) -> usize {
    kernel.apply(l, r, &Operand::or())
}

/// Returns the implication of two BDDs.
pub fn implication(l: usize, r: usize, kernel: &mut BddKernel) -> usize {
    kernel.apply(l, r, &Operand::imp())
}

/// Returns the equivalence of two BDDs.
pub fn equivalence(l: usize, r: usize, kernel: &mut BddKernel) -> usize {
    kernel.apply(l, r, &Operand::equiv())
}

/// Returns the negation of a BDDs.
pub fn not(r: usize, kernel: &mut BddKernel) -> usize {
    not_rec(r, kernel)
}

/// Restricts the variables in the BDD {@code r} to constants true or false.  The restriction is submitted in the BDD
pub fn restrict(r: usize, var: usize, kernel: &mut BddKernel) -> usize {
    if var < 2 {
        return r;
    }
    varset2svartable(var, kernel);
    restrict_rec(r, (var << 3) | CACHEID_RESTRICT, kernel)
}

/// Existential quantifier elimination for the variables in var.
pub fn exists(r: usize, var: usize, kernel: &mut BddKernel) -> usize {
    if var < 2 {
        return r;
    }
    varset2vartable(var, kernel);
    quant_rec(r, &Operand::or(), var << 3, kernel)
}

/// Universal quantifier elimination for the variables in var.
pub fn for_all(r: usize, var: usize, kernel: &mut BddKernel) -> usize {
    if var < 2 {
        return r;
    }
    varset2vartable(var, kernel);
    quant_rec(r, &Operand::and(), (var << 3) | CACHEID_FORALL, kernel)
}

fn not_rec(r: usize, kernel: &mut BddKernel) -> usize {
    if is_zero(r) {
        return BDD_TRUE;
    }
    if is_one(r) {
        return BDD_FALSE;
    }
    let cache_abc = kernel.applycache.lookup(r);
    if cache_abc.0 == Some(r) && cache_abc.2 == OPCODE_NOT {
        return kernel.applycache.lookup_res(r);
    }
    let ref1 = not_rec(kernel.low(r).unwrap(), kernel);
    kernel.push_ref(ref1);
    let ref2 = not_rec(kernel.high(r), kernel);
    kernel.push_ref(ref2);
    let res = kernel.make_node(kernel.level(r), kernel.read_ref(2), kernel.read_ref(1));
    kernel.pop_ref(2);
    kernel.applycache.set_with_res(r, (r, 0, OPCODE_NOT), res);
    res
}

fn restrict_rec(r: usize, miscid: usize, kernel: &mut BddKernel) -> usize {
    if is_const(r) || kernel.level(r) > kernel.quantlast {
        return r;
    }
    let search_hash = pair(r, miscid);
    let cache_abc = kernel.misccache.lookup(search_hash);
    if cache_abc.0 == Some(r) && cache_abc.2 == miscid {
        return kernel.misccache.lookup_res(search_hash);
    }
    let res: usize;
    if kernel.insvarset(kernel.level(r)) {
        if kernel.quantvarset[kernel.level(r)] > 0 {
            res = restrict_rec(kernel.high(r), miscid, kernel);
        } else {
            res = restrict_rec(kernel.low(r).unwrap(), miscid, kernel);
        }
    } else {
        let ref1 = restrict_rec(kernel.low(r).unwrap(), miscid, kernel);
        kernel.push_ref(ref1);
        let ref2 = restrict_rec(kernel.high(r), miscid, kernel);
        kernel.push_ref(ref2);
        res = kernel.make_node(kernel.level(r), kernel.read_ref(2), kernel.read_ref(1));
        kernel.pop_ref(2);
    }
    kernel.misccache.set_with_res(search_hash, (r, 0, miscid), res);
    res
}

fn quant_rec(r: usize, op: &Operand, quantid: usize, kernel: &mut BddKernel) -> usize {
    if r < 2 || kernel.level(r) > kernel.quantlast {
        return r;
    }
    let cache_abc = kernel.quantcache.lookup(r);
    if cache_abc.0 == Some(r) && cache_abc.2 == quantid {
        return kernel.quantcache.lookup_res(r);
    }
    let ref1 = quant_rec(kernel.low(r).unwrap(), op, quantid, kernel);
    kernel.push_ref(ref1);
    let ref2 = quant_rec(kernel.high(r), op, quantid, kernel);
    kernel.push_ref(ref2);

    let res = if kernel.invarset(kernel.level(r)) {
        kernel.apply_rec(kernel.read_ref(2), kernel.read_ref(1), op)
    } else {
        kernel.make_node(kernel.level(r), kernel.read_ref(2), kernel.read_ref(1))
    };
    kernel.pop_ref(2);
    kernel.quantcache.set_with_res(r, (r, 0, quantid), res);
    res
}

#[allow(clippy::cast_possible_wrap)]
fn varset2svartable(r: usize, kernel: &mut BddKernel) {
    assert!(r >= 2, "Illegal variable: {r}");
    kernel.quantvarset_id += 1;
    if kernel.quantvarset_id == u32::MAX / 2 {
        kernel.quantvarset = vec![0; kernel.varnum];
        kernel.quantvarset_id = 1;
    }
    let mut n = r;
    while !is_const(n) {
        let id = kernel.quantvarset_id as i32;
        let level = kernel.level(n);
        if is_zero(kernel.low(n).unwrap()) {
            kernel.quantvarset[level] = id;
            n = kernel.high(n);
        } else {
            kernel.quantvarset[level] = -id;
            n = kernel.low(n).unwrap();
        }
        kernel.quantlast = kernel.level(n);
    }
}

#[allow(clippy::cast_possible_wrap)]
fn varset2vartable(r: usize, kernel: &mut BddKernel) {
    assert!(r >= 2, "Illegal variable: {r}");
    kernel.quantvarset_id += 1;
    if kernel.quantvarset_id == u32::MAX {
        kernel.quantvarset = vec![0; kernel.varnum];
        kernel.quantvarset_id = 1;
    }
    let mut n = r;
    while n > 1 {
        let level = kernel.level(n);
        kernel.quantvarset[level] = kernel.quantvarset_id as i32;
        kernel.quantlast = level;
        n = kernel.high(n);
    }
}

#[cfg(test)]
mod tests {
    use crate::knowledge_compilation::bdd::bdd_construction::{bdd_high, bdd_low, bdd_var, ith_var, nith_var};
    use crate::knowledge_compilation::bdd::bdd_kernel::BddKernel;

    #[test]
    fn test_simple_methods() {
        let mut kernel = BddKernel::new_with_num_vars(3, 1000, 1000);
        assert_eq!(ith_var(0, &mut kernel), 2);
        assert_eq!(nith_var(0, &mut kernel), 3);
        assert_eq!(bdd_var(2, &mut kernel), 0);
        assert_eq!(bdd_low(2, &mut kernel), 0);
        assert_eq!(bdd_high(2, &mut kernel), 1);
    }
}
