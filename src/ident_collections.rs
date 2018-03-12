//! Declares the `IdentCollection` trait and several implementations for standard collections.
//!
//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2018/03/12

use std::collections::*;
use std::hash::Hash;
use std::mem::swap;
use std::borrow::{Borrow, BorrowMut};
use with_ident::*;

/// The `IdentCollection` trait provides functionality for collections working with
/// `WithIdent` values.
pub trait IdentCollection<'a, E, T, I = usize>
    where E: Borrow<WithIdent<T, I>>, I: Eq + Clone {
    /// Inserts the passed value if there are no other elements with the passed `identifier`.
    ///
    /// Returns `true` if the insertion succeeds.
    fn insert_by_id(&mut self, value: E) -> bool;
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
    fn get_with_id(&'a self, identifier: &I) -> Option<WithIdent<&'a T, I>>;
    /*
    /// Attempts to retrieve a mutable reference to the value with the passed `identifier`.
    ///
    /// # Params
    ///
    /// identifier --- The `identifier` to seach for.
    fn get_mut_with_id(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>>;
    */
}

/// The `IdentCollectionMut` trait provides functionality for collections working with
/// `WithIdentMut` values.
pub trait IdentCollectionMut<'a, E, T, I = usize>
    where E: BorrowMut<WithIdentMut<T, I>>, I: Eq + Clone {
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
    /// let a = WithIdentMut::new(1, 5);
    /// let b = WithIdentMut::new(1, 10);
    ///
    /// assert!(vec.update_by_id(a.clone()).is_none()); //Inserting.
    /// assert_eq!(**vec.update_by_id(b.clone()).unwrap(), **a); //Updating.
    /// assert_eq!(**vec[0], **b); //Updated value.
    /// # }
    /// ```
    fn update_by_id(&mut self, value: E) -> Option<E>;
    /// Attempts to retrieve a mutable reference to the value with the passed `identifier`.
    ///
    /// # Params
    ///
    /// identifier --- The `identifier` to seach for.
    fn get_mut_with_id(&'a mut self, identifier: &I) -> Option<WithIdentMut<&'a mut T, I>>;
}

impl<'a, E, T, I> IdentCollection<'a, E, T, I> for Vec<E>
    where E: Borrow<WithIdent<T, I>>, I: 'a + Eq + Clone {
    fn insert_by_id(&mut self, value: E) -> bool {
        if self.iter_mut().any(|e| WithIdent::same_id(value.borrow(), E::borrow(e))) {
            return false
        }
        self.push(value); true
    }
    fn contains_id(&self, identifier: &I) -> bool {
        self.iter().any(|e| WithIdent::get_identifier(e.borrow()) == identifier)
    }
    fn get_with_id(&'a self, identifier: &I) -> Option<WithIdent<&'a T, I>> {
        self.iter()
        .find(|e| WithIdent::get_identifier(E::borrow(e)) == identifier)
        .map(|e| WithIdent::as_ref(e.borrow()))
    }
}

impl<'a, E, T, I> IdentCollectionMut<'a, E, T, I> for Vec<E>
    where E: BorrowMut<WithIdentMut<T, I>>, I: 'a + Eq + Clone {
    fn update_by_id(&mut self, mut value: E) -> Option<E> {
        if let Some(e) = self.iter_mut().find(|e| WithIdent::same_id(value.borrow(), E::borrow(e))) {
            swap::<T>(
                WithIdentMut::borrow_mut(E::borrow_mut(e)),
                WithIdentMut::borrow_mut(E::borrow_mut(&mut value))
            );
            return Some(value)
        }
        self.push(value); None
    }
    fn get_mut_with_id(&'a mut self, identifier: &I) -> Option<WithIdentMut<&'a mut T, I>> {
        self.iter_mut()
        .find(|e| WithIdent::get_identifier(E::borrow(e)) == identifier)
        .map(|e| WithIdentMut::as_mut(e.borrow_mut()))
    }
}
/*
impl<T, I: Eq + Clone> IdentCollection<T, I> for VecDeque<WithIdent<T, I>> {
    fn insert_by_id(&mut self, mut value: WithIdent<T, I>) -> Option<WithIdent<T, I>> {
        if let Some(ref mut e) = self.iter_mut().find(|e| WithIdent::same_id(&value, e)) {
            swap::<T>(e, &mut value);
            return Some(value)
        }
        self.push_back(value); None
    }
    fn contains_id(&self, identifier: &I) -> bool {
        self.iter().any(|e| e.get_identifier() == identifier)
    }
    fn get_with_id(&self, identifier: I) -> Option<WithIdent<&T, I>> {
        self.iter().find(|e| *e.get_identifier() == identifier).map(WithIdent::borrow)
    }
    fn get_mut_with_id(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>> {
        self.iter_mut().find(|e| *e.get_identifier() == identifier).map(WithIdent::as_mut)
    }
}

impl<T, I: Eq + Clone> IdentCollection<T, I> for LinkedList<WithIdent<T, I>> {
    fn insert_by_id(&mut self, mut value: WithIdent<T, I>) -> Option<WithIdent<T, I>> {
        if let Some(ref mut e) = self.iter_mut().find(|e| WithIdent::same_id(&value, e)) {
            swap::<T>(e, &mut value);
            return Some(value)
        }
        self.push_back(value); None
    }
    fn contains_id(&self, identifier: &I) -> bool {
        self.iter().any(|e| e.get_identifier() == identifier)
    }
    fn get_with_id(&self, identifier: I) -> Option<WithIdent<&T, I>> {
        self.iter().find(|e| *e.get_identifier() == identifier).map(WithIdent::borrow)
    }
    fn get_mut_with_id(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>> {
        self.iter_mut().find(|e| *e.get_identifier() == identifier).map(WithIdent::as_mut)
    }
}

impl<T, I: Eq + Hash + Clone> IdentCollection<T, I> for HashMap<I, T> {
    fn insert_by_id(&mut self, value: WithIdent<T, I>) -> Option<WithIdent<T, I>> {
        let (key, value) = value.into();
        
        self.insert(key.clone(), value)
        .map(|old| WithIdent::new(key, old))
    }
    fn contains_id(&self, identifier: &I) -> bool {
        self.contains_key(identifier)
    }
    fn get_with_id(&self, identifier: I) -> Option<WithIdent<&T, I>> {
        self.get(&identifier).map(|value| WithIdent::new(identifier, value))
    }
    fn get_mut_with_id(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>> {
        self.get_mut(&identifier).map(|value| WithIdent::new(identifier, value))
    }
}

impl<T, I: Eq + Hash + Clone + Ord> IdentCollection<T, I> for BTreeMap<I, T> {
    fn insert_by_id(&mut self, value: WithIdent<T, I>) -> Option<WithIdent<T, I>> {
        let (key, value) = value.into();
        
        self.insert(key.clone(), value)
        .map(|old| WithIdent::new(key, old))
    }
    fn contains_id(&self, identifier: &I) -> bool {
        self.contains_key(identifier)
    }
    fn get_with_id(&self, identifier: I) -> Option<WithIdent<&T, I>> {
        self.get(&identifier).map(|value| WithIdent::new(identifier, value))
    }
    fn get_mut_with_id(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>> {
        self.get_mut(&identifier).map(|value| WithIdent::new(identifier, value))
    }
}
*/
#[cfg(test)]
mod tests {
    use super::*;
    
    macro_rules! test_collection {
        ($type:tt, $($init:tt)*) => {{
            let mut collection = $($init)*;
            let a = WithIdentMut::<usize>::new(1, 5);
            let b = WithIdentMut::<usize>::new(1, 10);
            
            assert!(collection.insert_by_id(a),
                concat!("`", stringify!($type), "::insert_by_id` failed to insert.")
            );
            assert!(!collection.insert_by_id(a),
                concat!("`", stringify!($type), "::insert_by_id` did not fail while there was an matching identifier.")
            );
            assert_eq!(**a, **collection.update_by_id(b)
                .expect(concat!("`", stringify!($type), "::insert_by_id` failed while updating a value.")),
                concat!("`", stringify!($type), "::insert_by_id` returned an incorrect value from update.")
            );
            assert!(collection.contains_id(&1),
                concat!("`", stringify!($type), "::contains_id` failed to find identifier.")
            );
            assert!(!collection.contains_id(&0),
                concat!("`", stringify!($type), "::contains_id` found an identifier when it shouldn't.")
            );
            assert_eq!(&**b, *collection.get_with_id(&1)
                .expect(concat!("`", stringify!($type), "::get_with_id` failed to find a value.")),
                concat!("`", stringify!($type), "::get_with_id` returned incorrect value.")
            );
            assert_eq!(&**b, **collection.get_mut_with_id(&1)
                .expect(concat!("`", stringify!($type), "::get_mut_with_id` failed to find a value.")),
                concat!("`", stringify!($type), "::get_mut_with_id` returned incorrect value.")
            );
        }}
    }
    
    #[test]
    fn test_vec() {
        test_collection!(Vec, Vec::with_capacity(1))
    }
    /*
    #[test]
    fn test_vecdeque() {
        test_collection!(VecDeque, VecDeque::with_capacity(1))
    }
    #[test]
    fn test_linkedlist() {
        test_collection!(LinkedList, LinkedList::new())
    }
    #[test]
    fn test_hash_map() {
        test_collection!(HashMap, HashMap::with_capacity(1))
    }
    #[test]
    fn test_btreemap() {
        test_collection!(BTreeMap, BTreeMap::new())
    }
    */
}
