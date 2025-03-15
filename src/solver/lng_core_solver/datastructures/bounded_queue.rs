use std::ops::{Add, Div, Sub};

#[derive(Clone, Debug)]
pub struct BoundedQueue<E> {
    elems: Vec<E>,
    first: usize,
    last: usize,
    sum_of_queue: E,
    max_size: usize,
    queue_size: usize,
}

impl<E: Default> BoundedQueue<E> {
    pub fn new() -> Self {
        Self { elems: Vec::new(), first: 0, last: 0, sum_of_queue: E::default(), max_size: 0, queue_size: 0 }
    }

    pub fn init_size(&mut self, size: usize) {
        self.elems.resize_with(size, || E::default());
        self.first = 0;
        self.max_size = size;
        self.queue_size = 0;
        self.last = 0;
    }

    pub fn fast_clear(&mut self) {
        self.first = 0;
        self.last = 0;
        self.queue_size = 0;
        self.sum_of_queue = E::default();
    }
}

impl<E: Default> Default for BoundedQueue<E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E> BoundedQueue<E> {
    pub const fn valid(&self) -> bool {
        self.queue_size == self.max_size
    }

    pub const fn elements(&self) -> &Vec<E> {
        &self.elems
    }

    pub fn into_elements(self) -> Vec<E> {
        self.elems
    }

    pub const fn first(&self) -> usize {
        self.first
    }

    pub const fn last(&self) -> usize {
        self.last
    }

    pub const fn sum_of_queue(&self) -> &E {
        &self.sum_of_queue
    }

    pub const fn max_size(&self) -> usize {
        self.max_size
    }

    pub const fn queue_size(&self) -> usize {
        self.queue_size
    }
}

impl<E: Add<Output = E> + Sub<Output = E> + Copy> BoundedQueue<E> {
    pub fn push(&mut self, x: E) {
        if self.queue_size == self.max_size {
            assert_eq!(self.last, self.first);
            self.sum_of_queue = self.sum_of_queue - self.elems[self.last];
            self.last += 1;
            if self.last == self.max_size {
                self.last = 0;
            }
        } else {
            self.queue_size += 1;
        }
        self.sum_of_queue = self.sum_of_queue + x;
        self.elems[self.first] = x;
        self.first += 1;
        if self.first == self.max_size {
            self.first = 0;
            self.last = 0;
        }
    }
}

impl<A, E: Div<Output = A> + From<usize> + Copy> BoundedQueue<E> {
    pub fn avg(&self) -> A {
        self.sum_of_queue / self.queue_size.into()
    }
}

#[cfg(test)]
mod tests {
    use super::BoundedQueue;

    #[test]
    pub fn test_usize() {
        let mut queue = BoundedQueue::<usize>::new();
        queue.init_size(2);
        queue.push(64);
        queue.push(32);
        queue.push(8);
        queue.push(16);
        assert_eq!(
            "BoundedQueue { elems: [8, 16], first: 0, last: 0, sum_of_queue: 24, max_size: 2, queue_size: 2 }",
            &format!("{queue:?}")
        );
    }

    #[test]
    pub fn test_isize() {
        let mut queue = BoundedQueue::<isize>::new();
        queue.init_size(2);
        queue.push(64);
        queue.push(32);
        queue.push(8);
        queue.push(16);
        assert_eq!(
            "BoundedQueue { elems: [8, 16], first: 0, last: 0, sum_of_queue: 24, max_size: 2, queue_size: 2 }",
            &format!("{queue:?}")
        );
    }
}
