// The control: identical, with the field renamed. This one builds.
pub struct S {
    pub key: u32,
}

pub fn get(s: &S) -> u32 {
    s.key
}
