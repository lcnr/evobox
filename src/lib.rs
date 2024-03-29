//! A pointer type which allows for safe transformations of its content without reallocation.
//! This crate does not depend on the standard library, and can be used in `#![no_std]` contexts.
//! It does however require the `alloc` crate.
//!
//! For more details look at the documentation of [`EvolveBox`].
//!
//! [`EvolveBox`]: ./struct.EvolveBox.html

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

/// A trait used to calculate the size and alignment of an [`EvolveBox`].
/// This trait is unsafe to implement, as returning the wrong alignment or size
/// for any type in the list can easily result in memory unsafety.
///
/// As this trait is already implemented for [`()`] and [`L`] there should be no need to
/// implement this as a user of this crate.
///
/// [`EvolveBox`]: ./struct.EvolveBox.html
/// [`()`]: https://doc.rust-lang.org/std/primitive.unit.html
/// [`L`]: ./struct.L.html
pub unsafe trait ListLayout {
    fn size() -> usize;
    fn align() -> usize;
}

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

/// A trait used to calculate the current type contained in the [`EvolveBox`] at compile time,
/// meaning that there should not be a runtime cost when using an [`EvolveBox`].
///
/// This trait is an implementation detail of this crate and can be mostly ignored.
///
/// # Examples
///
/// ```
/// use evobox::{L, List};
///
/// fn element_types(value: &L<u8, L<u16, L<u32>>>) {
///     fn first(_: &impl List<(), Value = u8>) {}
///     first(value);
///
///     fn second(_: &impl List<L<()>, Value = u16>) {}
///     second(value);
///
///     fn third(_: &impl List<L<L<()>>, Value = u32>) {}
///     third(value);
/// }
/// ```
///
/// [`EvolveBox`]: ./struct.EvolveBox.html
pub trait List<V>: ListLayout {
    type Value;
}

impl<E, C: ListLayout> List<()> for L<E, C> {
    type Value = E;
}

impl<E, B, C: List<B>> List<L<B>> for L<E, C> {
    type Value = C::Value;
}

/// A singly linked list containing types, indexed by itself using the [`List`] trait and
/// used by [`EvolveBox`] to store all possible types.
///
/// For examples of its actual usage please look at the documentation for the [`EvolveBox`].
///
/// # Examples
///
/// ```
/// use evobox::{L, List};
///
/// fn element_types(value: &L<u8, L<u16, L<u32>>>) {
///     fn first(_: &impl List<(), Value = u8>) {}
///     first(value);
///
///     fn second(_: &impl List<L<()>, Value = u16>) {}
///     second(value);
///
///     fn third(_: &impl List<L<L<()>>, Value = u32>) {}
///     third(value);
/// }
/// ```
/// [`EvolveBox`]: ./struct.EvolveBox.html
/// [`List`]: ./trait.List.html
pub struct L<E, C = ()> {
    _marker: PhantomData<fn(E, C)>,
}

/// A pointer type which allows for safe transformations of its content without reallocation.
///
/// An `EvolveBox` has the same size as a [`Box`] and has the smallest size and alignment on the heap needed
/// to store its largest possible variant.
///
/// Therefore `EvolveBox` should be a zero cost abstraction,
/// meaning that there should be no runtime difference between a [`Box`] pointing at an [untagged union] and an `EvolveBox`,
/// while using an `EvolveBox` is also safe.
///
/// The size and alignment of the allocated memory is stored in the type `S`, which is a list of all used types,  
/// as it is required for deallocation.
///
/// # Examples
///
/// Using `EvolveBox` inside of a function.
///
/// ```rust
/// use evobox::{EvolveBox, L};
///
/// let s: EvolveBox<L<&str, L<String, L<u32>>>> = EvolveBox::new("7");
/// let owned = s.evolve(|v| v.to_string());
/// assert_eq!(owned.as_str(), "7");
///
/// let seven = owned.try_evolve(|s| s.parse()).expect("invalid integer");
/// assert_eq!(*seven, 7);
/// ```
///
/// Storing it in a generic struct.
///
/// ```rust
/// use evobox::{EvolveBox, List, L};
///
/// enum Ty {
///     Integer,
///     String,
///     Boolean,
/// }
///
/// #[derive(Debug)]
/// struct TypeError;
///
/// struct Variable<'a, N, T>
/// where
///     L<&'a str, L<usize>>: List<N>,
///     L<&'a str, L<Ty>>: List<T>,
/// {
///     name: EvolveBox<L<&'a str, L<usize>>, N>,
///     ty: EvolveBox<L<&'a str, L<Ty>>, T>,
/// }
///
/// impl<'a> Variable<'a, (), ()> {
///     fn new(name: &'a str, ty: &'a str) -> Self {
///         Self {
///             name: EvolveBox::new(name),
///             ty: EvolveBox::new(ty),
///         }
///     }
/// }
///
/// impl<'a, T> Variable<'a, (), T>
/// where
///     L<&'a str, L<Ty>>: List<T>,
/// {
///     fn resolve_names(self, names: &mut Vec<&'a str>) -> Variable<'a, L<()>, T> {
///         let id = names.len();
///         let name = self.name.evolve(|name| {
///             names.push(name);
///             id
///         });
///
///         Variable { name, ty: self.ty }
///     }
/// }
///
/// impl<'a, N> Variable<'a, N, ()>
/// where
///     L<&'a str, L<usize>>: List<N>,
/// {
///     fn resolve_types(self) -> Result<Variable<'a, N, L<()>>, TypeError> {
///         let ty = self.ty.try_evolve(|ty|
///             match ty {
///                 "int" => Ok(Ty::Integer),
///                 "string" => Ok(Ty::String),
///                 "bool" => Ok(Ty::Boolean),
///                 _ => Err(TypeError)
///             }
///         )?;
///
///         Ok(Variable { name: self.name, ty })
///     }
/// }
///
/// let a = Variable::new("a", "int");
/// let b = Variable::new("b", "string");
///
/// let mut names = Vec::new();
/// let a = a.resolve_names(&mut names);
/// let _ = a.resolve_types().expect("unknown type");
/// let b = b.resolve_types().expect("unknown type");
/// let _ = b.resolve_names(&mut names);
/// ```
/// [`Box`]: https://doc.rust-lang.org/std/boxed/struct.Box.html
/// [untagged union]: https://doc.rust-lang.org/std/keyword.union.html
pub struct EvolveBox<S: List<P>, P = ()> {
    _marker: PhantomData<fn(S, P)>,
    current: NonNull<S::Value>,
}

unsafe impl<S: List<P>, P> Send for EvolveBox<S, P> where S::Value: Send {}
unsafe impl<S: List<P>, P> Sync for EvolveBox<S, P> where S::Value: Sync {}

impl<S: List<()>> EvolveBox<S, ()> {
    /// Allocates memory on the heap and then places `x` into it.
    /// This does not actually allocate if all types used in `S` are zero-sized.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use evobox::{EvolveBox, L};
    /// let value = EvolveBox::<L<_>>::new(7);
    ///
    /// assert_eq!(*value, 7);
    /// ```
    pub fn new(x: S::Value) -> Self {
        if let Some(layout) = Self::calculate_layout() {
            unsafe {
                let current = a::alloc(layout).cast::<S::Value>();
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

impl<S: List<P>, P> EvolveBox<S, P> {
    fn calculate_layout() -> Option<Layout> {
        let size = S::size();
        let align = S::align();
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
    /// # use evobox::{EvolveBox, L};
    /// let evolve_box = EvolveBox::<L<_>>::new("hi");
    /// assert_eq!("hi", evolve_box.into_inner());
    /// ```
    pub fn into_inner(self) -> S::Value {
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

impl<S: List<P>, P> EvolveBox<S, P> {
    /// Converts the current value to the next one
    /// without requiring a new allocation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use evobox::{EvolveBox, L};
    ///
    /// let int_box: EvolveBox<L<u32, L<String>>> = EvolveBox::new(7);
    /// let str_box = int_box.evolve(|i| format!("{}", i));
    /// assert_eq!(str_box.as_str(), "7");
    /// ```
    pub fn evolve<F>(self, f: F) -> EvolveBox<S, L<P>>
    where
        F: FnOnce(<S as List<P>>::Value) -> <S as List<L<P>>>::Value,
        S: List<L<P>>,
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
            let mut pointer = pointer.cast();
            ptr::write(pointer.as_mut(), next);
            EvolveBox {
                _marker: PhantomData,
                current: pointer,
            }
        }
    }

    /// Tries to convert the current value to the next one without
    /// requiring a new allocation. The error is propagated outwards in case
    /// the conversion fails.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use evobox::{EvolveBox, L};
    /// use std::convert::TryFrom;
    ///
    /// let origin: EvolveBox<L<u32, L<u16, L<u8>>>> = EvolveBox::new(256);
    ///
    /// let success = origin.try_evolve(u16::try_from).unwrap();
    /// assert_eq!(*success, 256);
    ///
    /// let error = success.try_evolve(u8::try_from);
    /// assert!(error.is_err());
    /// ```
    pub fn try_evolve<F, E>(self, f: F) -> Result<EvolveBox<S, L<P>>, E>
    where
        F: FnOnce(<S as List<P>>::Value) -> Result<<S as List<L<P>>>::Value, E>,
        S: List<L<P>>,
    {
        let pointer = self.current;
        // SAFETY: prevent `self` from being dropped
        mem::forget(self);
        unsafe {
            let value = ptr::read(pointer.as_ptr());
            match f(value) {
                Ok(next) => {
                    // SAFETY: thanks to `calculate_layout` the pointer must
                    // support the type `V` as well. So this cast is safe
                    let mut pointer = pointer.cast();
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

impl<S: List<P>, P> AsRef<S::Value> for EvolveBox<S, P> {
    fn as_ref(&self) -> &S::Value {
        self.deref()
    }
}

impl<S: List<P>, P> AsMut<S::Value> for EvolveBox<S, P> {
    fn as_mut(&mut self) -> &mut S::Value {
        self.deref_mut()
    }
}

impl<S: List<P>, P> Deref for EvolveBox<S, P> {
    type Target = S::Value;

    fn deref(&self) -> &S::Value {
        unsafe { self.current.as_ref() }
    }
}

impl<S: List<P>, P> DerefMut for EvolveBox<S, P> {
    fn deref_mut(&mut self) -> &mut S::Value {
        unsafe { self.current.as_mut() }
    }
}

impl<S1: List<P1>, P1, S2: List<P2>, P2> PartialEq<EvolveBox<S2, P2>> for EvolveBox<S1, P1>
where
    S1::Value: PartialEq<S2::Value>,
{
    fn eq(&self, other: &EvolveBox<S2, P2>) -> bool {
        self.deref() == other.deref()
    }
}

impl<S: List<P>, P> Eq for EvolveBox<S, P> where S::Value: Eq {}

impl<S: List<P>, P> fmt::Debug for EvolveBox<S, P>
where
    S::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<S: List<P>, P> Drop for EvolveBox<S, P> {
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
        let mut t = EvolveBox::<L<u32>>::new(7);
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

        let mut t = EvolveBox::<L<Empty, L<Foo, L<Bar>>>>::new(Empty);
        *t = Empty;

        assert_eq!(
            Bar,
            t.evolve(|t| {
                assert_eq!(Empty, t);
                Foo
            })
            .evolve(|_| Bar)
            .into_inner()
        );
    }

    #[test]
    fn evolve() {
        let int_box = EvolveBox::<L<u32, L<String>>>::new(7);
        let str_box = int_box.evolve(|i| format!("{}", i));
        assert_eq!(str_box.as_str(), "7");
    }

    #[test]
    fn double_free() {
        let ddt = EvolveBox::<L<DDT>>::new(DDT::default());
        ddt.into_inner();
    }

    #[test]
    fn sizes() {
        let evo = EvolveBox::<L<u8, L<u16, L<u32, L<u64, L<u8, L<u16>>>>>>>::new(7);
        assert_eq!(
            7,
            evo.evolve(From::from)
                .evolve(From::from)
                .evolve(From::from)
                .try_evolve(TryFrom::try_from)
                .unwrap()
                .evolve(From::from)
                .into_inner()
        );
    }
}
