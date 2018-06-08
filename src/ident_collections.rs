//! Declares the `IdentCollection` trait and several implementations for standard collections.
//!
//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2018/03/13

use std::mem::swap;
use std::collections::*;
use super::*;

/// The `IdentCollection` trait provides functionality for collections working with
/// `WithIdent` values.
pub trait IdentCollection<T, I: Eq = usize> {
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
    /// assert!(vec.insert_by_ident(a.clone()).is_none()); //Inserting.
    /// assert_eq!(a, vec.insert_by_ident(b.clone()).unwrap()); //Updating.
    /// assert_eq!(b, vec[0]); //Updated value.
    /// # }
    /// ```
    fn insert_by_ident(&mut self, value: WithIdent<T, I>) -> Option<WithIdent<T, I>>;
    /// Searches for the passed `identifier` in the collection.
    ///
    /// # Params
    ///
    /// identifier --- The `identifier` to seach for.
    fn contains_ident(&self, identifier: &I) -> bool;
    /// Attempts to retrieve a reference to the value with the passed `identifier`.
    ///
    /// If a reference is found it is returned with the identifier attached.
    ///
    /// # Params
    ///
    /// identifier --- The `identifier` to seach for.
    fn get_with_ident(&self, identifier: I) -> Option<WithIdent<&T, I>>;
    /// Attempts to retrieve a mutable reference to the value with the passed `identifier`.
    ///
    /// If a reference is found it is returned with the identifier attached.
    ///
    /// # Params
    ///
    /// identifier --- The `identifier` to seach for.
    fn get_mut_with_ident(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>>;
}

impl<T> IdentCollection<T, usize> for Vec<T> {
    fn insert_by_ident(&mut self, mut value: WithIdent<T, usize>) -> Option<WithIdent<T, usize>> {
        use std::mem::swap;

        //Check if the index exists.
        //The index exists.
        if *value.ident() < self.len() {
            //Swap the values.
            swap(&mut self[*value.ident()], &mut value);
            //Return the old value.
            Some(value)
        //The index doesn't exist.
        } else {
            let (index, value) = value.into();

            //Will panic if `index` is not the end of the `Vec`.
            self.insert(index, value); None
        }
    }
    fn contains_ident(&self, identifier: &usize) -> bool { *identifier < self.len() }
    fn get_with_ident(&self, identifier: usize) -> Option<WithIdent<&T, usize>> {
        self.get(identifier).map(|value| WithIdent::new(identifier, value))
    }
    fn get_mut_with_ident(&mut self, identifier: usize) -> Option<WithIdent<&mut T, usize>> {
        self.get_mut(identifier).map(|value| WithIdent::new(identifier, value))
    }
}

impl<T, I: Eq> IdentCollection<T, I> for Vec<WithIdent<T, I>> {
    fn insert_by_ident(&mut self, mut value: WithIdent<T, I>) -> Option<WithIdent<T, I>> {
        if let Some(e) = self.iter_mut().find(|e| WithIdent::same_ident(&value, e)) {
            swap::<T>(e, &mut value);
            return Some(value);
        }
        self.push(value); None
    }
    fn contains_ident(&self, identifier: &I) -> bool {
        self.iter().any(|e| e.ident() == identifier)
    }
    fn get_with_ident(&self, identifier: I) -> Option<WithIdent<&T, I>> {
        self.iter().find(|e| e.ident() == &identifier)
        .map(|e| WithIdent::new(identifier, e.as_ref()))
    }
    fn get_mut_with_ident(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>> {
        self.iter_mut().find(|e| e.ident() == &identifier)
        .map(|e| WithIdent::new(identifier, e.as_mut()))
    }
}

impl<T, I: Eq> IdentCollection<T, I> for VecDeque<WithIdent<T, I>> {
    fn insert_by_ident(&mut self, mut value: WithIdent<T, I>) -> Option<WithIdent<T, I>> {
        if let Some(e) = self.iter_mut().find(|e| WithIdent::same_ident(&value, e)) {
            swap::<T>(e, &mut value);
            return Some(value);
        }
        self.push_back(value); None
    }
    fn contains_ident(&self, identifier: &I) -> bool {
        self.iter().any(|e| e.ident() == identifier)
    }
    fn get_with_ident(&self, identifier: I) -> Option<WithIdent<&T, I>> {
        self.iter().find(|e| e.ident() == &identifier)
        .map(|e| WithIdent::new(identifier, e.as_ref()))
    }
    fn get_mut_with_ident(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>> {
        self.iter_mut().find(|e| e.ident() == &identifier)
        .map(|e| WithIdent::new(identifier, e.as_mut()))
    }
}

impl<T, I: Eq> IdentCollection<T, I> for LinkedList<WithIdent<T, I>> {
    fn insert_by_ident(&mut self, mut value: WithIdent<T, I>) -> Option<WithIdent<T, I>> {
        if let Some(e) = self.iter_mut().find(|e| WithIdent::same_ident(&value, e)) {
            swap::<T>(e, &mut value);
            return Some(value);
        }
        self.push_back(value); None
    }
    fn contains_ident(&self, identifier: &I) -> bool {
        self.iter().any(|e| e.ident() == identifier)
    }
    fn get_with_ident(&self, identifier: I) -> Option<WithIdent<&T, I>> {
        self.iter().find(|e| e.ident() == &identifier)
        .map(|e| WithIdent::new(identifier, e.as_ref()))
    }
    fn get_mut_with_ident(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>> {
        self.iter_mut().find(|e| e.ident() == &identifier)
        .map(|e| WithIdent::new(identifier, e.as_mut()))
    }
}

impl<T, I, S> IdentCollection<T, I> for HashMap<I, T, S> where I: Eq + ::std::hash::Hash + Clone, S: std::hash::BuildHasher {
    fn insert_by_ident(&mut self, value: WithIdent<T, I>) -> Option<WithIdent<T, I>> {
        let (ident, value) = value.into();
        self.insert(ident.clone(), value)
        .map(|e| WithIdent::new(ident, e))
    }
    fn contains_ident(&self, identifier: &I) -> bool {
        self.contains_key(identifier)
    }
    fn get_with_ident(&self, identifier: I) -> Option<WithIdent<&T, I>> {
        self.get(&identifier)
        .map(|e| WithIdent::new(identifier, e))
    }
    fn get_mut_with_ident(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>> {
        self.get_mut(&identifier)
        .map(|e| WithIdent::new(identifier, e))
    }
}

impl<T, I> IdentCollection<T, I> for BTreeMap<I, T> where I: Eq + Ord + Clone {
    fn insert_by_ident(&mut self, value: WithIdent<T, I>) -> Option<WithIdent<T, I>> {
        let (ident, value) = value.into();
        self.insert(ident.clone(), value)
        .map(|e| WithIdent::new(ident, e))
    }
    fn contains_ident(&self, identifier: &I) -> bool {
        self.contains_key(identifier)
    }
    fn get_with_ident(&self, identifier: I) -> Option<WithIdent<&T, I>> {
        self.get(&identifier)
        .map(|e| WithIdent::new(identifier, e))
    }
    fn get_mut_with_ident(&mut self, identifier: I) -> Option<WithIdent<&mut T, I>> {
        self.get_mut(&identifier)
        .map(|e| WithIdent::new(identifier, e))
    }
}

#[cfg(test)]
mod tests {
    macro_rules! test_collection {
        ($type:tt, $init:expr) => {{
            use ident_collections::*;
            
            let mut collection = $init;
            let a = WithIdent::<usize>::new(0usize, 5usize);
            let mut b = WithIdent::<usize>::new(0usize, 10usize);
            
            assert!(collection.insert_by_ident(a).is_none(),
                concat!("`", stringify!($type), "::insert_by_ident` returned a value while inserting.")
            );
            assert_eq!(a, collection.insert_by_ident(b)
                .expect(concat!("`", stringify!($type), "::insert_by_ident` failed while updating a value.")),
                concat!("`", stringify!($type), "::insert_by_ident` returned an incorrect value from update.")
            );
            assert!(collection.contains_ident(&0usize),
                concat!("`", stringify!($type), "::contains_ident` failed to find identifier.")
            );
            assert!(!collection.contains_ident(&1usize),
                concat!("`", stringify!($type), "::contains_ident` found an identifier when it shouldn't.")
            );
            assert_eq!(WithIdent::as_ref(&b), collection.get_with_ident(0usize)
                .expect(concat!("`", stringify!($type), "::get_with_ident` failed to find a value.")),
                concat!("`", stringify!($type), "::get_with_ident` returned incorrect value.")
            );
            assert_eq!(WithIdent::as_mut(&mut b), collection.get_mut_with_ident(0usize)
                .expect(concat!("`", stringify!($type), "::get_mut_with_ident` failed to find a value.")),
                concat!("`", stringify!($type), "::get_mut_with_ident` returned incorrect value.")
            );
        }}
    }
    
    #[test]
    fn test_vec() {
        test_collection!(Vec, Vec::<usize>::with_capacity(1))
    }
    // #[test]
    // fn test_vec_ident() {
    //     test_collection!(Vec, Vec::<WithIdent<usize, usize>>::with_capacity(1))
    // }
    #[test]
    fn test_vecdeque() {
        test_collection!(VecDeque, VecDeque::<WithIdent<usize, usize>>::with_capacity(1))
    }
    #[test]
    fn test_linkedlist() {
        test_collection!(LinkedList, LinkedList::<WithIdent<usize, usize>>::new())
    }
    #[test]
    fn test_hashmap() {
        test_collection!(HashMap, HashMap::<usize, usize>::with_capacity(1))
    }
    #[test]
    fn test_btreemap() {
        test_collection!(BTreeMap, BTreeMap::new())
    }
}
