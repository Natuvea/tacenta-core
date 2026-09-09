//! Message-layer byte compatibility with any other implementation is not
//! attempted, and this module is how that is enforced by the type checker
//! rather than by a comment.
//!
//! The published specifications leave several HKDF inputs to the application:
//! the X3DH/PQXDH `info` string and its operand spellings, `KDF_RK`'s `info`
//! string, `KDF_CK`'s constant bytes, the message-key `info` string, the
//! SHA-256/SHA-512 hash choice, and the `SPQR_PROTOCOL_INFO` and
//! `TR_PROTOCOL_INFO` identifiers of Double Ratchet revision 4. Another
//! implementation's values for these are not derivable from any published
//! specification or from anything visible on the wire, and this engine does
//! not attempt to obtain them (`tacenta-spec/CONSTANTS.md`). Every constant
//! this engine emits or accepts is tier "fact" or "ours" there.
//!
//! [`ExternalKdfProfile`](crate::interop::ExternalKdfProfile) has one field per
//! such input and **no constructor**: not a private one guarded by a runtime check, none at all,
//! anywhere in this crate. A function that produced an external
//! implementation's message-layer bytes would take an `ExternalKdfProfile` by
//! value, so no such function can be written, let alone called: code that
//! tries does not compile. Nothing in this crate constructs or consumes the
//! type.
//!
//! The interoperability scope is the bundle layer (README, "What is and is
//! not claimed"), where every constant needed travels on the wire.

/// The application-chosen HKDF inputs of the message layer, with no
/// constructor. See the module documentation.
///
/// `allow(dead_code)` is deliberate: every field is meant to go unread, and
/// the lint exists to flag exactly that state in code that did not intend it.
/// This code intends it.
#[allow(dead_code)]
pub struct ExternalKdfProfile {
    /// The X3DH/PQXDH `info` string, including its exact curve, hash, and KEM
    /// operand spellings.
    x3dh_info: &'static [u8],
    /// The `KDF_RK` `info` string.
    kdf_rk_info: &'static [u8],
    /// The `KDF_CK` constant bytes. The Double Ratchet specification gives
    /// `0x01`/`0x02` as an example, not a mandate.
    kdf_ck_bytes: (&'static [u8], &'static [u8]),
    /// The message-key HKDF `info` string.
    message_key_info: &'static [u8],
    /// SHA-256 or SHA-512.
    hash: ExternalHash,
    /// `SPQR_PROTOCOL_INFO`, named in Double Ratchet revision 4 sections 5-7.
    /// Distinct from this engine's own `PROTOCOL_INFO` in `tacenta-braid`,
    /// which is tier "ours" in `CONSTANTS.md` and needs no entry here.
    spqr_protocol_info: &'static [u8],
    /// `TR_PROTOCOL_INFO`, same revision, same sections.
    tr_protocol_info: &'static [u8],
}

/// SHA-256 or SHA-512. Kept separate from `ExternalKdfProfile` having a
/// `Default` impl, since the choice itself is one of the application-chosen
/// inputs, not a fallback for it.
#[allow(dead_code)]
enum ExternalHash {
    Sha256,
    Sha512,
}
