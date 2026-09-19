//! Session establishment and lifecycle orchestration.
//!
//! The implementation lives in the translation-leaf `tacenta-lifecycle`
//! crate. Re-exporting it here preserves the public `tacenta_core::sessions`
//! API while keeping the code translated as one public call graph.

pub use tacenta_lifecycle::*;
