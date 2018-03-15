# [ident](https://crates.io/crates/ident)
A Rust utility crate for wrapping types with an __immutable__ identifier and storing/accessing such types in collections by that identifier.

## How Do I Use This Crate?
First add the crate to your `Cargo.toml`:
```toml
[dependencies]
ident = "*" # or the specific version you want to use.
```
And import the crate to your own `main.rs`/`lib.rs`:
```rust
extern crate ident;

use ident::*;
```

## Ok, But What Does This Crate _Do_?
Lets say you have some type:
```rust
#[derive(Clone)]
struct Foo {
    x: usize
}

impl Foo {
    pub fn new(x: usize) -> Self {
        Self { x }
    }
    pub fn do_stuff(&mut self) {
        //Your code.
    }
}
```
And you have a collection of `Foo`s
```rust
use std::collections::HashMap;

fn main() {
    let mut my_foos = HashMap::with_capacity(2);
    my_foos.insert(5, Foo::new(10));
    my_foos.insert(10, Foo::new(5));

    let mut foo = my_foos.get(&5).unwrap().clone();
    foo.do_stuff();
}
```
Its often useful to remember where you got you value from (`my_foos[5]` in this case). That would normally mean creating a new variable which you have to remember to pass everywhere but with `ident`:
```rust
use ident::*;
use std::collections::HashMap;

fn main() {
    let mut my_foos = HashMap::with_capacity(2);
    my_foos.insert(5, Foo::new(10));
    my_foos.insert(10, Foo::new(5));

    let mut foo = WithIdent::new(5, my_foos.get(5).unwrap().clone());
    foo.do_stuff();
}
```
We are able to get the _key_ bundled with the _value_ while still accessing the _value_ as if the _key_ wasn't there.

This is a simple use case however:
* Getting and Inserting with an "identifier" is implemented on standard collections.
* Rust is able to infer the type of your value without your intervention.
* There are several utility functions for `WithIdent` which allow you to manipulate the inner value or the identifier as needed.
