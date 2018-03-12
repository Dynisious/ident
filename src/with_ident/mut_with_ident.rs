
use std::ops::{Deref, DerefMut};
use std::borrow::{Borrow, BorrowMut};
use std::convert::{From, Into};
use super::*;

#[derive(Clone, Copy)]
pub struct WithIdentMut<T, I: Eq = usize>(WithIdent<T, I>);

impl<T, I: Eq> WithIdentMut<T, I> {
    /// Constructs a new `WithIdentMut` value from parts.
    ///
    /// # Params
    ///
    /// identifier --- The unique `identifier` of a `WithIdentMut` instance.  
    /// value --- The inner `value` of a `WithIdentMut` instance.
    pub fn new(identifier: I, value: T) -> Self {
        WithIdentMut(WithIdent::new(identifier, value))
    }
}

impl<T, I: Eq + Clone> WithIdentMut<T, I> {
    /// Returns a new `WithIdentMut` instance wrapping a mutable reference to the original value.
    ///
    /// Note: this is an associated function, which means that you have to call it as
    /// `WithIdentMut::as_mut(&wi)` instead of `wi.as_mut()`. This is so that there is no conflict
    /// with a method on the inner type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate ident;
    /// # use ident::*;
    /// # fn main() {
    /// let mut wi = WithIdentMut::new(0, 5);
    /// assert_eq!(&5, **WithIdentMut::as_mut(&mut wi));
    /// # }
    /// ```
    pub fn as_mut(wi: &mut Self) -> WithIdentMut<&mut T, I> {
        WithIdentMut::new(wi.identifier.clone(), &mut wi.0.value)
    }
}

impl<T, I: Eq> From<(I, T)> for WithIdentMut<T, I> {
    fn from((id, value): (I, T)) -> Self {
        Self::new(id, value)
    }
}

impl<T, I: Eq> Into<(I, T)> for WithIdentMut<T, I> {
    fn into(self) -> (I, T) {
        WithIdent::into(self.into())
    }
}

impl<T, I: Eq> From<WithIdent<T, I>> for WithIdentMut<T, I> {
    fn from(from: WithIdent<T, I>) -> Self {
        WithIdentMut(from)
    }
}

impl<T, I: Eq> Into<WithIdent<T, I>> for WithIdentMut<T, I> {
    fn into(self) -> WithIdent<T, I> {
        self.0
    }
}

impl<T, I: Eq> Deref for WithIdentMut<T, I> {
    type Target = WithIdent<T, I>;
    
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, I: Eq> DerefMut for WithIdentMut<T, I> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, I: Eq> Borrow<WithIdent<T, I>> for WithIdentMut<T, I> {
    fn borrow(&self) -> &WithIdent<T, I> {
        &self.0
    }
}

impl<T, I: Eq> BorrowMut<WithIdent<T, I>> for WithIdentMut<T, I> {
    fn borrow_mut(&mut self) -> &mut WithIdent<T, I> {
        &mut self.0
    }
}

impl<T, I: Eq> Borrow<T> for WithIdentMut<T, I> {
    fn borrow(&self) -> &T {
        &self.0.value
    }
}

impl<T, I: Eq> BorrowMut<T> for WithIdentMut<T, I> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut self.0.value
    }
}
