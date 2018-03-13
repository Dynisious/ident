
use std::convert::From;
use super::*;

/// Derives an `identifier` from a value.
///
/// `DeriveIdent` is a "quality of life" trait when using [`WithIdent`](./struct.WithIdent.html).
///
/// Any type `T` which implements this trait can easily be converted into a
/// `WithIdent<T, I>` instance using `From` and `Into`.
pub trait DeriveIdent<I: Eq> {
    
    /// Returns an `Identifier` value derived from the passed `value`.
    ///
    /// Note: this is an associated function, which means that you have to call it as
    /// `DeriveIdent::derive_ident(value)` instead of `value.derive_ident()`. This is so
    /// that there is no conflict with a method on the inner type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate ident;
    /// # use ident::*;
    /// # fn main() {
    /// assert_eq!(5, DeriveIdent::derive_ident(&5)); //Integer types return themselves by default.
    ///
    /// let wi = WithIdent::from(5);
    /// assert_eq!(wi.get_identifier(), &5);
    /// assert_eq!(*wi, 5);
    /// # }
    /// ```
    fn derive_ident(value: &Self) -> I;
}

impl<T: DeriveIdent<I>, I: Eq> From<T> for WithIdent<T, I> {
    fn from(from: T) -> Self {
        Self::new(DeriveIdent::derive_ident(&from), from)
    }
}

/// In some cases, such as `integer` types, a value is its own unique `identifier`.
///
/// This macro implements [`DeriveIdent`](./trait.DeriveIdent.html) for the passed type to
/// simply return itself. (NOTE: the type must derive `Clone`)
#[macro_export]
macro_rules! impl_identity {
    ($type:ty) => {
        impl DeriveIdent<$type> for $type {
            fn derive_ident(value: &Self) -> $type {
                value.clone()
            }
        }
    };
    ($type:tt $($t:tt)*) => {
        impl_identity!($type);
        impl_identity!($($t)*);
    };
}

impl_identity! { usize isize u8 i8 u16 i16 u32 i32 u64 i64 }

/// A hash is often a useful and convenient `identifier` value.
///
/// This macro implements [`DeriveIdent<u64>`](./trait.DeriveIdent.html) for the passed
/// type using the passed [`Hasher`](https://doc.rust-lang.org/std/hash/trait.Hasher.html).
/// (NOTE: the type must derive [`Hash`](https://doc.rust-lang.org/std/hash/trait.Hash.html))
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// extern crate ident;
///
/// use std::collections::hash_map::DefaultHasher;
/// use ident::*;
///
/// #[derive(Hash)]
/// struct MyType(pub usize);
///
/// //Implements DeriveIdent<u64> for MyType using DefaultHasher to calculate the hash.
/// impl_hash_identity!(MyType, DefaultHasher);
///
/// fn main() {
///     let x = MyType(5);
///     println!("{}", DeriveIdent::<u64>::derive_ident(&x));
/// }
/// ```
#[macro_export]
macro_rules! impl_hash_identity {
    (($type:tt, $hasher:tt)) => {
        impl DeriveIdent<u64> for $type {
            fn derive_ident(value: &Self) -> u64 {
                use std::hash::{Hash, Hasher};
                
                let mut hasher = $hasher::default();
                value.hash(&mut hasher);
                hasher.finish()
            }
        }
    };
    (($type:tt, $hasher:tt) $($t:tt)*) => {
        impl_hash_identity!(($type, $hasher));
        impl_hash_identity!($($t)*);
    };
    ($type:tt, $hasher:tt) => (impl_hash_identity!(($type, $hasher)););
}
