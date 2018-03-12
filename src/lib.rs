//! A crate for creating and using types with an __immutable__ identifier field.
//!
//! Author --- daniel.bechaz@gmail.com  
//! Last Moddified --- 2018/02/12
//!
//! The main type provided by this crate is [`WithIdent`](./with_ident/struct.WithIdent.html).

pub mod with_ident;
pub mod ident_collections;

pub use with_ident::*;
pub use ident_collections::*;
