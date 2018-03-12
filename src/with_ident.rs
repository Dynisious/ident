//! Declares the `WithIdent` type.
//!
//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2018/03/12

use std::ops::{Deref, DerefMut};
use std::convert::{AsRef, AsMut, From, Into};

/// `WithIdent` wraps any value of type `T` and a unique identifier of type `I`.
///
/// The fields of a `WithIdent` instance cannot be accessed but the `T` value can be
/// accessed via a `Box` _like_ interface.
///
/// It can be useful to think of `WithIdent` as a tuple of (I, T), so `From` and `Into`
/// have been implemented for just that conversion.
#[derive(Clone, Copy)]
pub struct WithIdent<T, I: Eq = usize> {
    /// The unique `identifier` of a `WithIdent` instance.
    identifier: I,
    /// The inner `value` of a `WithIdent` instance.
    value: T,
}

impl<T, I: Eq> WithIdent<T, I> {
    /// Constructs a new `WithIdent` value from parts.
    ///
    /// # Params
    ///
    /// identifier --- The unique `identifier` of a `WithIdent` instance.  
    /// value --- The inner `value` of a `WithIdent` instance.
    pub fn new(identifier: I, value: T) -> Self {
        Self { identifier, value }
    }
    /// Returns an immutable reference to the `identifier` of this `WithIdent`.
    pub fn get_identifier(&self) -> &I {
        &self.identifier
    }
    /// Compares the `identifiers` of two `WithIdent` instances for equality.
    pub fn same_id(a: &Self, b: &Self) -> bool {
        a.identifier == b.identifier
    }
    /// Consumes the `WithIdent` returning the wrapped `T` value.
    ///
    /// Note: this is an associated function, which means that you have to call it as
    /// `WithIdent::into_value(wi)` instead of `wi.into_value()`. This is so that there is no
    /// conflict with a method on the inner type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate ident;
    /// # use ident::*;
    /// # fn main() {
    /// let wi = WithIdent::new(0, 5);
    /// let value = WithIdent::into_value(wi);
    /// # }
    /// ```
    pub fn into_value(wi: Self) -> T {
        wi.value
    }
    /// Consumes the `WithIdent` returning a new instance wrapping the result of the mapping.
    ///
    /// Note: this is an associated function, which means that you have to call it as
    /// `WithIdent::map(wi, f)` instead of `wi.map(f)`. This is so that there is no conflict
    /// with a method on the inner type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate ident;
    /// # use ident::*;
    /// # fn main() {
    /// let wi = WithIdent::new(0, 5);
    /// assert_eq!(10, *WithIdent::map(wi, |x| 2 * x));
    /// # }
    /// ```
    pub fn map<F, U>(wi: Self, f: F) -> WithIdent<U, I>
        where F: FnOnce(T) -> U {
        WithIdent::new(wi.identifier, f(wi.value))
    }
}

impl<T, I: Eq + Clone> WithIdent<T, I> {
    /// Returns a new `WithIdent` instance wrapping a reference to the original value.
    ///
    /// Note: this is an associated function, which means that you have to call it as
    /// `WithIdent::as_ref(&wi)` instead of `wi.as_ref()`. This is so that there is no conflict
    /// with a method on the inner type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate ident;
    /// # use ident::*;
    /// # fn main() {
    /// let wi = WithIdent::new(0, 5);
    /// assert_eq!(&5, *WithIdent::as_ref(&wi));
    /// # }
    /// ```
    pub fn as_ref(wi: &Self) -> WithIdent<&T, I> {
        WithIdent::new(wi.identifier.clone(), &wi.value)
    }
    /// Returns a new `WithIdent` instance wrapping a mutable reference to the original value.
    ///
    /// Note: this is an associated function, which means that you have to call it as
    /// `WithIdent::as_mut(&wi)` instead of `wi.as_mut()`. This is so that there is no conflict
    /// with a method on the inner type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate ident;
    /// # use ident::*;
    /// # fn main() {
    /// let mut wi = WithIdent::new(0, 5);
    /// assert_eq!(&5, *WithIdent::as_mut(&mut wi));
    /// # }
    /// ```
    pub fn as_mut(wi: &mut Self) -> WithIdent<&mut T, I> {
        WithIdent::new(wi.identifier.clone(), &mut wi.value)
    }
}

impl<T, I: Eq> From<(I, T)> for WithIdent<T, I> {
    fn from((id, value): (I, T)) -> Self {
        Self::new(id, value)
    }
}

impl<T, I: Eq> Into<(I, T)> for WithIdent<T, I> {
    fn into(self) -> (I, T) {
        (self.identifier, self.value)
    }
}

impl<T, I: Eq> Deref for WithIdent<T, I> {
    type Target = T;
    
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T, I: Eq> DerefMut for WithIdent<T, I> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T, I: Eq> AsRef<T> for WithIdent<T, I> {
    fn as_ref(&self) -> &T {
        &self.value
    }
}

impl<T, I: Eq> AsMut<T> for WithIdent<T, I> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.value
    }
}
