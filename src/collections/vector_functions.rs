pub fn grow_to<T: Clone>(vec: &mut Vec<T>, size: usize, pad: T) {
    if vec.len() >= size {
        return;
    }
    vec.reserve(size - vec.len());
    for _ in vec.len()..size {
        vec.push(pad.clone());
    }
}
