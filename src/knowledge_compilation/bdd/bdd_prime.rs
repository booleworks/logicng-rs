const CHECKTIMES: i32 = 20;

/// Returns the next prime greater than the given number
pub fn prime_gte(num: usize) -> usize {
    let mut n = num;
    if is_even(n) {
        n += 1;
    }
    while !is_prime(n) {
        n += 2;
    }
    n
}

/// Returns the next prime less than the given number
pub fn prime_lte(num: usize) -> usize {
    let mut n = num;
    if is_even(n) {
        n -= 1;
    }
    while !is_prime(n) {
        n -= 2;
    }
    n
}

const fn is_even(src: usize) -> bool {
    (src & 0x1) == 0
}

fn is_prime(src: usize) -> bool {
    !has_easy_factors(src) && is_miller_rabin_prime(src)
}

const fn has_easy_factors(src: usize) -> bool {
    has_factor(src, 3) || has_factor(src, 5) || has_factor(src, 7) || has_factor(src, 11) || has_factor(src, 13)
}

const fn has_factor(src: usize, n: usize) -> bool {
    src != n && src.is_multiple_of(n)
}

fn is_miller_rabin_prime(src: usize) -> bool {
    for _n in 0..CHECKTIMES {
        let witness = random(src - 1);
        if is_witness(witness, src) {
            return false;
        }
    }
    true
}

fn random(i: usize) -> usize {
    fastrand::usize(1..i)
}

fn is_witness(witness: usize, src: usize) -> bool {
    let bit_num = number_of_bits(src - 1) - 1;
    let mut d = 1;
    for i in (0..=bit_num).rev() {
        let x = d;
        d = mulmod(d, d, src);
        if d == 1 && x != 1 && x != src - 1 {
            return true;
        }
        if bit_is_set(src - 1, i) {
            d = mulmod(d, witness, src);
        }
    }
    d != 1
}

fn number_of_bits(src: usize) -> usize {
    if src == 0 {
        return 0;
    }
    for b in (0..31).rev() {
        if bit_is_set(src, b) {
            return b + 1;
        }
    }
    1
}

const fn bit_is_set(src: usize, b: usize) -> bool {
    (src & (1 << b)) != 0
}

const fn mulmod(a: usize, b: usize, c: usize) -> usize {
    a * b % c
}

#[cfg(test)]
mod tests {
    use crate::knowledge_compilation::bdd::bdd_prime::{number_of_bits, prime_gte, prime_lte};

    use super::is_prime;

    #[test]
    fn test_prime_lte() {
        assert_eq!(prime_lte(7558), 7549);
        assert_eq!(prime_lte(9), 7);
        assert_eq!(prime_lte(40), 37);
    }

    #[test]
    fn test_prime_gte() {
        assert_eq!(prime_gte(7560), 7561);
        assert_eq!(prime_gte(9), 11);
        assert_eq!(prime_gte(42), 43);
    }

    #[test]
    fn test_is_prime() {
        assert!(is_prime(13));
        assert!(is_prime(7561));
        assert!(!is_prime(42));
        assert!(!is_prime(7729));
    }

    #[test]
    fn test_numb_of_bits() {
        assert_eq!(number_of_bits(0), 0);
        assert_eq!(number_of_bits(1), 1);
        assert_eq!(number_of_bits(42), 6);
    }
}
