use std::ops::{Add, Div, Sub};

/// Fixed-capacity circular queue that tracks the sum of its current elements.
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
    /// Creates an uninitialized queue with zero capacity.
    pub fn new() -> Self {
        Self {
            elems: Vec::new(),
            first: 0,
            last: 0,
            sum_of_queue: E::default(),
            max_size: 0,
            queue_size: 0,
        }
    }

    /// Sets the queue capacity and clears all queued elements.
    pub fn init_size(&mut self, size: usize) {
        self.elems.resize_with(size, || E::default());
        self.first = 0;
        self.max_size = size;
        self.queue_size = 0;
        self.last = 0;
    }

    /// Clears the queue while retaining its allocated element storage.
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
    /// Returns whether the queue is filled to its configured capacity.
    pub const fn valid(&self) -> bool {
        self.queue_size == self.max_size
    }

    /// Returns the queue's backing element storage.
    pub const fn elements(&self) -> &Vec<E> {
        &self.elems
    }

    /// Consumes the queue and returns its backing element storage.
    pub fn into_elements(self) -> Vec<E> {
        self.elems
    }

    /// Returns the index at which the next element is written.
    pub const fn first(&self) -> usize {
        self.first
    }

    /// Returns the index of the oldest element when the queue is full.
    pub const fn last(&self) -> usize {
        self.last
    }

    /// Returns the sum of the elements currently in the queue.
    pub const fn sum_of_queue(&self) -> &E {
        &self.sum_of_queue
    }

    /// Returns the configured queue capacity.
    pub const fn max_size(&self) -> usize {
        self.max_size
    }

    /// Returns the number of elements currently in the queue.
    pub const fn queue_size(&self) -> usize {
        self.queue_size
    }
}

impl<E: Add<Output = E> + Sub<Output = E> + Copy> BoundedQueue<E> {
    /// Appends an element, replacing the oldest element when the queue is full.
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
    /// Returns the arithmetic mean of the queued elements.
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
