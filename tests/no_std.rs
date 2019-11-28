#![no_std]
extern crate evobox;

use evobox::{EvolveBox, L};

fn main() {
    let b: EvolveBox<L<u32, ()>> = EvolveBox::new(7);
    assert_eq!(7, b.into_inner());
}
