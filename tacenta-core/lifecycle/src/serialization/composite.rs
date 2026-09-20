//! The Triple Ratchet's composite header on the wire.
//!
//! The encoding, its decoder and their types live in `tacenta-wire`
//! (`tacenta-core/wire`), a leaf crate, so that the Charon/Aeneas translation
//! covers the decoder every ratchet message a peer sends goes through. This
//! module re-exports them under the path the engine, its tests, the fuzz targets
//! and the conformance runner use.

pub use tacenta_wire::{
    AgreementType, CHUNK_BYTES, COMPOSITE_LEN, Codeword, Composite, decode_composite,
    encode_composite,
};
