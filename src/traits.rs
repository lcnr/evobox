use core::mem;

use crate::L;

unsafe impl ListLayout for () {
    fn size() -> usize {
        0
    }

    fn align() -> usize {
        1
    }
}

unsafe impl<E, C: ListLayout> ListLayout for L<E, C> {
    fn size() -> usize {
        mem::size_of::<E>().max(C::size())
    }
    fn align() -> usize {
        mem::align_of::<E>().max(C::align())
    }
}

pub unsafe trait ListLayout {
    fn size() -> usize;
    fn align() -> usize;
}

impl<E, C: ListLayout> List<()> for L<E, C> {
    type Value = E;
}

impl<E, B, C: List<B>> List<L<B>> for L<E, C> {
    type Value = C::Value;
}

pub trait List<V>: ListLayout {
    type Value;
}