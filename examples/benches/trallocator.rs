#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout};
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering::SeqCst;

use crate::PRINT_MEMORY;

pub struct Trallocator<A: GlobalAlloc>(pub A, AtomicU64);

unsafe impl<A: GlobalAlloc> GlobalAlloc for Trallocator<A> {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { unsafe {
        self.1.fetch_add(l.size() as u64, SeqCst);
        self.0.alloc(l)
    }}
    unsafe fn dealloc(&self, ptr: *mut u8, l: Layout) { unsafe {
        self.0.dealloc(ptr, l);
        self.1.fetch_sub(l.size() as u64, SeqCst);
    }}
}

impl<A: GlobalAlloc> Trallocator<A> {
    pub const fn new(a: A) -> Self {
        Self(a, AtomicU64::new(0))
    }

    pub fn reset(&self) {
        self.1.store(0, SeqCst);
    }

    pub fn get(&self) -> u64 {
        self.1.load(SeqCst)
    }

    pub fn print_memory(&self, prefix: &str) {
        if PRINT_MEMORY {
            println!("{}: {:.3} MB", prefix, self.get() as f64 / 1024_i32.pow(2) as f64);
        }
    }

    pub fn print_memory_bytes(&self, prefix: &str) {
        if PRINT_MEMORY {
            println!("{}: {} Bytes", prefix, self.get());
        }
    }

    pub fn measure<F>(&self, op: F) -> u64
    where F: FnOnce() {
        let start = self.get();
        op();
        let end = self.get();
        end - start
    }
}
