//! T

extern crate alloc;

use core::{
    cmp::{Eq, PartialEq},
    fmt,
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
};

use alloc::alloc::{self as a, Layout};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct N<E, T> {
    _marker: PhantomData<(E, T)>,
}

unsafe impl TypeList for () {
    fn size() -> usize {
        0
    }

    fn align() -> usize {
        1
    }
}

unsafe impl<E, T: TypeList> TypeList for N<E, T> {
    fn size() -> usize {
        mem::size_of::<E>().max(T::size())
    }

    fn align() -> usize {
        mem::align_of::<E>().max(T::align())
    }
}

pub unsafe trait TypeList {
    fn size() -> usize;

    fn align() -> usize;
}

/// A pointer type which allows for safe transformations of its content without reallocation.
///
/// An `EvolveBox<P, C, N>` has the same size as a `Box<T>` and has exactly
/// the same size and alignment on the heap as its largest possible variant.
///
/// As the size and alignment of the allocated memory are required for deallocation.
/// This information is stored in the type signature across transformations.
/// All previous types are stored in `P` and all future types in `N`.
///
/// # Type parameters
///
/// - `C`: The type of the currently stored value
/// - `P`: A list of all previously used types
/// - `N`: A list of all possible future types
///
/// A list segment `L` of both `P` and `N` is either `N<T, L>` or `()`.
///
/// # Examples
///
/// ```rust
///
/// ```
pub struct EvolveBox<P: TypeList, C, N: TypeList> {
    _marker: PhantomData<(*const P, N, *const C)>,
    current: NonNull<C>,
}

unsafe impl<P: TypeList, C: Send, N: TypeList> Send for EvolveBox<P, C, N> {}
unsafe impl<P: TypeList, C: Sync, N: TypeList> Sync for EvolveBox<P, C, N> {}

impl<C, N: TypeList> EvolveBox<(), C, N> {
    /// Allocates memory on the heap and then places `x` into it.
    /// This does not actually allocate if all possible values `C` of this
    /// `EvolveBox` are zero-sized.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use evobox::EvolveBox;
    /// let value = EvolveBox::new(7).fin();
    ///
    /// assert_eq!(*value, 7);
    /// ```
    pub fn new(x: C) -> EvolveBox<(), C, N> {
        if let Some(layout) = Self::calculate_layout() {
            unsafe {
                let current: *mut C = a::alloc(layout).cast();
                if current.is_null() {
                    a::handle_alloc_error(layout);
                }
                ptr::write(current, x);

                Self {
                    _marker: PhantomData,
                    current: NonNull::new_unchecked(current),
                }
            }
        } else {
            Self {
                _marker: PhantomData,
                current: NonNull::dangling(),
            }
        }
    }
}

impl<P: TypeList, C, N: TypeList> EvolveBox<P, C, N> {
    fn calculate_layout() -> Option<Layout> {
        let size = P::size().max(N::size()).max(mem::size_of::<C>());
        let align = P::align().max(N::align()).max(mem::align_of::<C>());
        if size > 0 {
            debug_assert!(Layout::from_size_align(size, align).is_ok());
            unsafe { Some(Layout::from_size_align_unchecked(size, align)) }
        } else {
            None
        }
    }

    /// Consumes this pointer, returning the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use evobox::EvolveBox;
    /// let evolve_box = EvolveBox::new("hi").fin();
    /// assert_eq!("hi", evolve_box.into_inner());
    /// ```
    pub fn into_inner(self) -> C {
        let pointer = self.current.as_ptr();
        mem::forget(self);
        unsafe {
            let value = ptr::read(pointer);
            if let Some(layout) = Self::calculate_layout() {
                // SAFETY: self.current is valid and will not be
                // used after this function
                a::dealloc(pointer.cast(), layout);
            }
            value
        }
    }
}

impl<P: TypeList, C, V, R: TypeList> EvolveBox<P, C, N<V, R>> {
    /// Converts a pointer of type `C` to a pointer of type `V`
    /// without requiring a new allocation
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use evobox::EvolveBox;
    ///
    /// let int_box = EvolveBox::new(7);
    /// let str_box = int_box.evolve(|i| format!("{}", i)).fin();
    /// assert_eq!(str_box.as_str(), "7");
    /// ```
    pub fn evolve<F>(self, f: F) -> EvolveBox<N<C, P>, V, R>
    where
        F: FnOnce(C) -> V,
    {
        let pointer = self.current;
        // SAFETY: prevent `self` from being dropped
        mem::forget(self);
        unsafe {
            let value = ptr::read(pointer.as_ptr());
            let next = f(value);
            // SAFETY: thanks to `calculate_layout` the pointer must
            // support the type `V` as well. So this case is safe

            // As the pointer data of `C` is now added to `P`, `calculate_layout`
            // does not change its return value
            let mut pointer = pointer.cast::<V>();
            ptr::write(pointer.as_mut(), next);
            EvolveBox {
                _marker: PhantomData,
                current: pointer,
            }
        }
    }

    pub fn try_evolve<F, E>(self, f: F) -> Result<EvolveBox<N<C, P>, V, R>, E>
    where
        F: FnOnce(C) -> Result<V, E>,
    {
        let pointer = self.current;
        // SAFETY: prevent `self` from being dropped
        mem::forget(self);
        unsafe {
            let value = ptr::read(pointer.as_ptr());
            match f(value) {
                Ok(next) => {
                    // SAFETY: thanks to `calculate_layout` the pointer must
                    // support the type `V` as well. So this case is safe

                    // As the pointer data of `C` is now added to `P`, `calculate_layout`
                    // does not change its return value
                    let mut pointer = pointer.cast::<V>();
                    ptr::write(pointer.as_mut(), next);
                    Ok(EvolveBox {
                        _marker: PhantomData,
                        current: pointer,
                    })
                }
                Err(e) => {
                    if let Some(layout) = Self::calculate_layout() {
                        a::dealloc(pointer.as_ptr().cast(), layout);
                    }
                    Err(e)
                }
            }
        }
    }
}

impl<P: TypeList, C> EvolveBox<P, C, ()> {
    /// An identity function only implemented if `N` is empty,
    /// meaning that `C` is the final state.
    ///
    /// While this might seem quite useless at first, it does improve ergonomics
    /// by helping the compiler with type resolution.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use evobox::EvolveBox;
    /// let start = EvolveBox::new(7u32);
    /// // as there could still be some next evolutions,
    /// // we have to explicitly declare the type of `end`
    /// let end: EvolveBox<_, _, ()> = start.evolve(|i| i + 1);
    /// assert_eq!(end.as_ref(), &8);
    ///
    /// let start = EvolveBox::new(7u32);
    /// let end = start.evolve(|i| i + 1).fin();
    /// assert_eq!(end.as_ref(), &8);
    ///
    /// ```
    pub fn fin(self) -> Self {
        self
    }
}

impl<P: TypeList, C, N: TypeList> AsRef<C> for EvolveBox<P, C, N> {
    fn as_ref(&self) -> &C {
        self.deref()
    }
}

impl<P: TypeList, C, N: TypeList> AsMut<C> for EvolveBox<P, C, N> {
    fn as_mut(&mut self) -> &mut C {
        self.deref_mut()
    }
}

impl<P: TypeList, C, N: TypeList> Deref for EvolveBox<P, C, N> {
    type Target = C;

    fn deref(&self) -> &C {
        unsafe { self.current.as_ref() }
    }
}

impl<P: TypeList, C, N: TypeList> DerefMut for EvolveBox<P, C, N> {
    fn deref_mut(&mut self) -> &mut C {
        unsafe { self.current.as_mut() }
    }
}

impl<P1: TypeList, P2: TypeList, C, O, N1: TypeList, N2: TypeList> PartialEq<EvolveBox<P2, O, N2>>
    for EvolveBox<P1, C, N1>
where
    C: PartialEq<O>,
{
    fn eq(&self, other: &EvolveBox<P2, O, N2>) -> bool {
        self.deref() == other.deref()
    }
}

impl<P: TypeList, C, N: TypeList> Eq for EvolveBox<P, C, N> where C: Eq {}

impl<P: TypeList, C: fmt::Debug, N: TypeList> fmt::Debug for EvolveBox<P, C, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<P: TypeList, C, N: TypeList> Drop for EvolveBox<P, C, N> {
    fn drop(&mut self) {
        if let Some(layout) = Self::calculate_layout() {
            unsafe {
                // SAFETY: self.current is valid and will not be
                // used after this function
                let pointer = self.current.as_ptr();
                let value = ptr::read(pointer);
                a::dealloc(pointer.cast(), layout);
                mem::drop(value);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use alloc::rc::Rc;
    use core::{cell::Cell, convert::TryFrom};

    /// THE WELL KNOWN DOUBLE DROP DETECTOR STRIKES ONCE AGAIN.
    #[derive(Default, Clone)]
    struct DDT(Rc<Cell<bool>>);

    impl Drop for DDT {
        fn drop(&mut self) {
            if self.0.replace(true) {
                panic!("double drop");
            }
        }
    }

    #[test]
    fn simple() {
        let mut t = EvolveBox::new(7).fin();
        *t = 9;
        let r = t.as_mut();
        *r += 11;
        assert_eq!(20, *t);
    }

    #[test]
    fn zero_sized() {
        #[derive(Debug, PartialEq)]
        struct Empty;
        struct Foo;
        #[derive(Debug, PartialEq)]
        struct Bar;

        let mut t = EvolveBox::new(Empty);
        *t = Empty;

        assert_eq!(
            Bar,
            t.evolve(|t| {
                assert_eq!(Empty, t);
                Foo
            })
            .evolve(|_| Bar)
            .fin()
            .into_inner()
        );
    }

    #[test]
    fn evolve() {
        let int_box = EvolveBox::new(7);
        let str_box = int_box.evolve(|i| format!("{}", i)).fin();
        assert_eq!(str_box.as_str(), "7");
    }

    #[test]
    fn double_free() {
        let ddt = EvolveBox::new(DDT::default()).fin();
        ddt.into_inner();
    }

    #[test]
    fn sizes() {
        let evo = EvolveBox::new(7u8);
        assert_eq!(
            7,
            evo.evolve(u16::from)
                .evolve(u32::from)
                .evolve(u64::from)
                .try_evolve(u8::try_from)
                .unwrap()
                .evolve(u16::from)
                .fin()
                .into_inner()
        );
    }
}
