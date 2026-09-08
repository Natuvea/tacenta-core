/// A Rust struct with a field named `mk`.
///
/// Lean names a structure's auto-generated constructor `mk`, so the field and
/// the constructor collide in the translated file and it no longer elaborates.
/// Renaming the field (see `control.rs`) makes the same code translate and
/// build cleanly.
pub struct S {
    pub mk: u32,
}

pub fn get(s: &S) -> u32 {
    s.mk
}
