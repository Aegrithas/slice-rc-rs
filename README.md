# Slice `Rc`

This crate provides a variation of reference-counted pointer that allows sub-slices to also contribute to the reference counter. A basic example of that different:

```rust
use slice_rc::Src;

fn main() {
  let hello_world: Src<str> = Src::new("Hello World!");
  let world: Src<str> = hello_world.slice(6..11);
  
  assert_eq!(hello_world, "Hello World!");
  assert_eq!(world, "World");
}
```

See the documentation at [https://docs.rs/slice-rc/] for more elaborate examples.
