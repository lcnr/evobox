# Evobox

A pointer type which allows for safe transformations of its content without reallocation.
This crate does not depend on the standard library, and can be used in `#![no_std]` contexts.
It does however require the `alloc` crate.

## Examples

```rust
use evobox::{EvolveBox, L};

let s: EvolveBox<L<&str, L<String, L<u32>>>> = EvolveBox::new("7");
let owned = s.evolve(|v| v.to_string());
assert_eq!(owned.as_str(), "7");

let seven = owned.try_evolve(|s| s.parse()).expect("invalid integer");
assert_eq!(*seven, 7);
```
