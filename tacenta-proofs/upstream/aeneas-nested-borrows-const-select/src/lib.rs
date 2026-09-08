//! Selecting between two `&'static [u8]` constants with a `match` is rejected
//! with "Nested borrows are not supported yet", and the enclosing function's
//! body becomes `sorry`.
//!
//! `control` and `repro` are the same code. They differ only in how many
//! variants the enum has. With one variant the match is vacuous, Aeneas folds
//! it away, and the constant is used directly; with two it must actually
//! select, and that is what fails. So a crate can translate cleanly while the
//! construct it depends on does not work, and only grow the error later, when
//! a second variant is added for the reason the parameter was introduced.
//!
//! This is what makes the failure worth reporting: the one-variant case gives
//! a false green, so the cost lands on whoever adds the second variant, which
//! may be much later and in unrelated work.

const LEFT: &[u8] = b"left";
const RIGHT: &[u8] = b"right";

pub enum One {
    Left,
}

pub enum Two {
    Left,
    Right,
}

/// Control: one variant, so the match folds. Translates.
pub fn control(p: One) -> usize {
    let s: &[u8] = match p {
        One::Left => LEFT,
    };
    s.len()
}

/// Repro: two variants, so the match must select. Body becomes `sorry`.
pub fn repro(p: Two) -> usize {
    let s: &[u8] = match p {
        Two::Left => LEFT,
        Two::Right => RIGHT,
    };
    s.len()
}
