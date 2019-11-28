#![no_std]
extern crate evobox;

use evobox::{L, EvolveBox};

fn main() {
    let b: EvolveBox<L<u32, ()>> = EvolveBox::new(7);
    assert_eq!(7, b.into_inner());
}