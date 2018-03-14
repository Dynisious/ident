//! Declares the `IdentCollection` trait and several implementations for standard collections.
//!
//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2018/03/13

use std::mem::swap;
use std::collections::*;
use std::borrow::BorrowMut;
use super::*;

/// The `IdentCollection` trait provides functionality for collections working with
/// `WithIdent` values.
pub trait IdentCollection<T, I = usize, E = WithIdent<T, I>>
    where E: BorrowMut<WithIdent<T, I>>, I: Eq {
    /// Inserts the passed value or updates the first value found with an equal `identifier`.
    ///
    /// If a value is updated the old value is returned in a `Some(value)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate ident;
    /// # use ident::*;
    /// # fn main() {
    /// let mut vec = Vec::with_capacity(1);
    /// let a = WithIdent::new(1, 5);
    /// let b = WithIdent::new(1, 10);
    ///
    /// assert!(vec.insert_by_id(a.clone()).is_none()); //Inserting.
    /// assert_eq!(*a, *vec.insert_by_id(b.clone()).unwrap()); //Updating.
    /// assert_eq!(*b, *vec[0]); //Updated value.
    /// # }
    /// ```
    fn insert_by_id(&mut self, value: E) -> Option<E>;
    /// Searches for the passed `identifier` in the collection.
    ///
    /// # Params
    ///
    /// identifier --- The `identifier` to seach for.
    fn contains_id(&self, identifier: &I) -> bool;
    /// Attempts to retrieve a reference to the value with the passed `identifier`.
    ///
    /// # Params
    ///
    /// identifier --- The `identifier` to seach for.
    fn get_with_id(&self, identifier: &I) -> Option<&E>;
    /// Attempts to retrieve a mutable reference to the value with the passed `identifier`.
    ///
    /// # Params
    ///
    /// identifier --- The `identifier` to seach for.
    fn get_mut_with_id(&mut self, identifier: &I) -> Option<&mut E>;
}

impl<T, I, E> IdentCollection<T, I, E> for Vec<E>
    where E: BorrowMut<WithIdent<T, I>>, I: Eq {
    fn insert_by_id(&mut self, mut value: E) -> Option<E> {
        if let Some(e) = self.iter_mut().find(|e| WithIdent::<T, I>::same_ident(value.borrow(), E::borrow(e))) {
            swap::<T>(E::borrow_mut(e), value.borrow_mut());
            return Some(value)
        }
        self.push(value); None
    }
    fn contains_id(&self, identifier: &I) -> bool {
        self.iter().any(|e| E::borrow(e).get_identifier() == identifier)
    }
    fn get_with_id(&self, identifier: &I) -> Option<&E> {
        self.iter().find(|e| E::borrow(e).get_identifier() == identifier)
    }
    fn get_mut_with_id(&mut self, identifier: &I) -> Option<&mut E> {
        self.iter_mut().find(|e| E::borrow(e).get_identifier() == identifier)
    }
}

impl<T, I, E> IdentCollection<T, I, E> for VecDeque<E>
    where E: BorrowMut<WithIdent<T, I>>, I: Eq {
    fn insert_by_id(&mut self, mut value: E) -> Option<E> {
        if let Some(e) = self.iter_mut().find(|e| WithIdent::same_ident(value.borrow(), E::borrow(e))) {
            swap::<T>(E::borrow_mut(e), value.borrow_mut());
            return Some(value)
        }
        self.push_back(value); None
    }
    fn contains_id(&self, identifier: &I) -> bool {
        self.iter().any(|e| E::borrow(e).get_identifier() == identifier)
    }
    fn get_with_id(&self, identifier: &I) -> Option<&E> {
        self.iter().find(|e| E::borrow(e).get_identifier() == identifier)
    }
    fn get_mut_with_id(&mut self, identifier: &I) -> Option<&mut E> {
        self.iter_mut().find(|e| E::borrow(e).get_identifier() == identifier)
    }
}

impl<T, I, E> IdentCollection<T, I, E> for LinkedList<E>
    where E: BorrowMut<WithIdent<T, I>>, I: Eq {
    fn insert_by_id(&mut self, mut value: E) -> Option<E> {
        if let Some(e) = self.iter_mut().find(|e| WithIdent::same_ident(value.borrow(), E::borrow(e))) {
            swap::<T>(E::borrow_mut(e), value.borrow_mut());
            return Some(value)
        }
        self.push_back(value); None
    }
    fn contains_id(&self, identifier: &I) -> bool {
        self.iter().any(|e| E::borrow(e).get_identifier() == identifier)
    }
    fn get_with_id(&self, identifier: &I) -> Option<&E> {
        self.iter().find(|e| E::borrow(e).get_identifier() == identifier)
    }
    fn get_mut_with_id(&mut self, identifier: &I) -> Option<&mut E> {
        self.iter_mut().find(|e| E::borrow(e).get_identifier() == identifier)
    }
}

#[cfg(test)]
mod tests {
    macro_rules! test_collection {
        ($type:tt, $($init:tt)*) => {{
            use ident_collections::*;
            
            let mut collection = $($init)*;
            let a = WithIdent::<usize>::new(1, 5);
            let b = WithIdent::<usize>::new(1, 10);
            
            assert!(collection.insert_by_id(a).is_none(),
                concat!("`", stringify!($type), "::insert_by_id` returned a value while inserting.")
            );
            assert_eq!(*a, *collection.insert_by_id(b)
                .expect(concat!("`", stringify!($type), "::insert_by_id` failed while updating a value.")),
                concat!("`", stringify!($type), "::insert_by_id` returned an incorrect value from update.")
            );
            assert!(collection.contains_id(&1),
                concat!("`", stringify!($type), "::contains_id` failed to find identifier.")
            );
            assert!(!collection.contains_id(&0),
                concat!("`", stringify!($type), "::contains_id` found an identifier when it shouldn't.")
            );
            assert_eq!(*b, **collection.get_with_id(&1)
                .expect(concat!("`", stringify!($type), "::get_with_id` failed to find a value.")),
                concat!("`", stringify!($type), "::get_with_id` returned incorrect value.")
            );
            assert_eq!(*b, **collection.get_with_id(&1)
                .expect(concat!("`", stringify!($type), "::get_mut_with_id` failed to find a value.")),
                concat!("`", stringify!($type), "::get_mut_with_id` returned incorrect value.")
            );
        }}
    }
    
    #[test]
    fn test_vec() {
        test_collection!(Vec, Vec::with_capacity(1))
    }
    #[test]
    fn test_vecdeque() {
        test_collection!(VecDeque, VecDeque::with_capacity(1))
    }
    #[test]
    fn test_linkedlist() {
        test_collection!(LinkedList, LinkedList::new())
    }
}
