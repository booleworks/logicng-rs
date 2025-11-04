// This implementation is based on https://github.com/droundy/append-only-vec by
// David Roundy and Za Wilcox, released under Apache/MIT

use std::cell::UnsafeCell;
use std::ops::Index;
use std::sync::atomic::{AtomicUsize, Ordering};
pub struct AppendOnlyVec<T> {
    count: AtomicUsize,
    reserved: AtomicUsize,
    data: [UnsafeCell<*mut T>; BITS_USED - 1 - 3],
}

unsafe impl<T: Send> Send for AppendOnlyVec<T> {}
unsafe impl<T: Sync + Send> Sync for AppendOnlyVec<T> {}

const BITS: usize = std::mem::size_of::<usize>() * 8;

#[cfg(target_arch = "x86_64")]
const BITS_USED: usize = 48;
#[cfg(all(not(target_arch = "x86_64"), target_pointer_width = "64"))]
const BITS_USED: usize = 64;
#[cfg(target_pointer_width = "32")]
const BITS_USED: usize = 32;

// This takes an index into a vec, and determines which data array will hold it
// (the first return value), and what the index will be into that data array
// (second return value)
//
// The i-th data array holds 1<<i values.
#[allow(clippy::cast_possible_truncation)]
const fn indices(i: usize) -> (u32, usize) {
    let i = i + 8;
    let bin = BITS as u32 - 1 - i.leading_zeros();
    let bin = bin - 3;
    let offset = i - bin_size(bin);
    (bin, offset)
}
const fn bin_size(array: u32) -> usize {
    (1 << 3) << array
}

#[test]
fn test_indices() {
    for i in 0..32 {
        println!("{:3}: {} {}", i, indices(i).0, indices(i).1);
    }
    let mut array = 0;
    let mut offset = 0;
    let mut index = 0;
    while index < 1000 {
        index += 1;
        offset += 1;
        if offset >= bin_size(array) {
            offset = 0;
            array += 1;
        }
        assert_eq!(indices(index), (array, offset));
    }
}

fn layout<T>(array: u32) -> std::alloc::Layout {
    std::alloc::Layout::array::<T>(bin_size(array)).unwrap()
}

impl<T> AppendOnlyVec<T> {
    /// Return an `Iterator` over the elements of the vec.
    #[cfg(test)]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &T> + ExactSizeIterator {
        (0..self.len()).map(|i| unsafe { self.get_unchecked(i) })
    }

    /// Index the vec without checking the bounds.
    ///
    /// To use this correctly, you *must* first ensure that the `idx <
    /// self.len()`.  This not only prevents overwriting the bounds, but also
    /// creates the memory barriers to ensure that the data is visible to the
    /// current thread.  In single-threaded code, however, it is not needed to
    /// call `self.len()` explicitly (if e.g. you have counted the number of
    /// elements pushed).
    #[cfg(test)]
    unsafe fn get_unchecked(&self, idx: usize) -> &T {
        unsafe {
            let (array, offset) = indices(idx);
            // We use a Relaxed load of the pointer, because the length check (which
            // was supposed to be performed) should ensure that the data we want is
            // already visible, since self.len() used Ordering::Acquire on
            // `self.count` which synchronizes with the Ordering::Release write in
            // `self.push`.
            let ptr = *self.data[array as usize].get();
            &*ptr.add(offset)
        }
    }

    /// Find the length of the array.
    #[inline]
    pub fn len(&self) -> usize {
        self.count.load(Ordering::Acquire)
    }

    /// Append an element to the array
    pub fn push(&self, val: T) -> usize {
        let idx = self.reserved.fetch_add(1, Ordering::Relaxed);
        let (array, offset) = indices(idx);
        let ptr = if self.len() < 1 + idx - offset {
            // We are working on a new array, which may not have been allocated...
            if offset == 0 {
                // It is our job to allocate the array!  The size of the array
                // is determined in the layout method, which needs to be
                // consistent with the indices function.
                let layout = layout::<T>(array);
                let ptr = unsafe { std::alloc::alloc(layout) }.cast::<T>();
                unsafe {
                    *self.data[array as usize].get() = ptr;
                }
                ptr
            } else {
                // We need to wait for the array to be allocated.
                while self.len() < 1 + idx - offset {
                    std::hint::spin_loop();
                }
                // The Ordering::Acquire semantics of self.len() ensures that
                // this pointer read will get the non-null pointer allocated
                // above.
                unsafe { *self.data[array as usize].get() }
            }
        } else {
            // The Ordering::Acquire semantics of self.len() ensures that
            // this pointer read will get the non-null pointer allocated
            // above.
            unsafe { *self.data[array as usize].get() }
        };

        // The contents of this offset are guaranteed to be unused (so far)
        // because we got the idx from our fetch_add above, and ptr is
        // guaranteed to be valid because of the loop we used above, which used
        // self.len() which has Ordering::Acquire semantics.
        unsafe { (ptr.add(offset)).write(val) };

        // Now we need to increase the size of the vec, so it can get read.  We
        // use Release upon success, to ensure that the value which we wrote is
        // visible to any thread that has confirmed that the count is big enough
        // to read that element.  In case of failure, we can be relaxed, since
        // we don't do anything with the result other than try again.
        while self.count.compare_exchange(idx, idx + 1, Ordering::Release, Ordering::Relaxed).is_err() {
            // This means that someone else *started* pushing before we started,
            // but hasn't yet finished.  We have to wait for them to finish
            // pushing before we can update the count.  Note that using a
            // spinloop here isn't really ideal, but except when allocating a
            // new array, the window between reserving space and using it is
            // pretty small, so contention will hopefully be rare, and having a
            // context switch during that interval will hopefully be vanishingly
            // unlikely.
            std::hint::spin_loop();
        }
        idx
    }

    #[allow(clippy::declare_interior_mutable_const)] // this behavior is intended for initializing an array
    const EMPTY: UnsafeCell<*mut T> = UnsafeCell::new(std::ptr::null_mut());
    /// Allocate a new empty array
    pub const fn new() -> Self {
        Self { count: AtomicUsize::new(0), reserved: AtomicUsize::new(0), data: [Self::EMPTY; BITS_USED - 1 - 3] }
    }
}

impl<T> Index<usize> for AppendOnlyVec<T> {
    type Output = T;

    fn index(&self, idx: usize) -> &Self::Output {
        assert!(idx < self.len()); // this includes the required ordering memory barrier
        let (array, offset) = indices(idx);
        // The ptr value below is safe, because the length check above will
        // ensure that the data we want is already visible, since it used
        // Ordering::Acquire on `self.count` which synchronizes with the
        // Ordering::Release write in `self.push`.
        let ptr = unsafe { *self.data[array as usize].get() };
        unsafe { &*ptr.add(offset) }
    }
}

impl<T> Drop for AppendOnlyVec<T> {
    fn drop(&mut self) {
        // First we'll drop all the `T` in a slightly sloppy way.  FIXME this
        // could be optimized to avoid reloading the `ptr`.
        for idx in 0..self.len() {
            let (array, offset) = indices(idx);
            // We use a Relaxed load of the pointer, because the loop above (which
            // ends before `self.len()`) should ensure that the data we want is
            // already visible, since it Acquired `self.count` which synchronizes
            // with the write in `self.push`.
            let ptr = unsafe { *self.data[array as usize].get() };
            unsafe {
                std::ptr::drop_in_place(ptr.add(offset));
            }
        }
        // Now we will free all the arrays.
        #[allow(clippy::cast_possible_truncation)]
        for array in 0..self.data.len() as u32 {
            // This load is relaxed because no other thread can have a reference
            // to Self because we have a &mut self.
            let ptr = unsafe { *self.data[array as usize].get() };
            if ptr.is_null() {
                break;
            }
            let layout = layout::<T>(array);
            unsafe { std::alloc::dealloc(ptr.cast::<u8>(), layout) };
        }
    }
}

#[test]
fn test_pushing_and_indexing() {
    let v = AppendOnlyVec::<usize>::new();

    for n in 0..50 {
        v.push(n);
        assert_eq!(v.len(), n + 1);
        for i in 0..=n {
            assert_eq!(v[i], i);
        }
    }

    let vec: Vec<usize> = v.iter().copied().collect();
    let ve2: Vec<usize> = (0..50).collect();
    assert_eq!(vec, ve2);
}

#[test]
fn test_parallel_pushing() {
    use std::sync::Arc;
    const N: u64 = 100;
    let v = Arc::new(AppendOnlyVec::<u64>::new());
    let mut threads = Vec::new();
    for thread_num in 0..N {
        let v = v.clone();
        threads.push(std::thread::spawn(move || {
            let which1 = v.push(thread_num);
            let which2 = v.push(thread_num);
            assert_eq!(v[which1], thread_num);
            assert_eq!(v[which2], thread_num);
        }));
    }
    for t in threads {
        t.join().ok();
    }
    for thread_num in 0..N {
        assert_eq!(2, v.iter().copied().filter(|&x| x == thread_num).count());
    }
}
