pub fn grow_to<T: Clone>(vec: &mut Vec<T>, size: usize, pad: T) {
    if vec.len() >= size {
        return;
    }
    vec.reserve(size - vec.len());
    for _ in vec.len()..size {
        vec.push(pad.clone());
    }
}

pub fn remove_elem<T, F>(vec: &mut Vec<T>, elem: &T, equality_function: F)
where F: Fn(&T, &T) -> bool {
    for i in 0..vec.len() {
        if equality_function(&vec[i], elem) {
            vec.remove(i);
            return;
        }
    }
}
