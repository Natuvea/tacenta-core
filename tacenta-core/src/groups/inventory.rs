//! Bounded canonical preimages for hosted device-inventory statements.

use crate::primitives::{dh::PublicKeyBytes, xeddsa};
use rand_core::{CryptoRng, RngCore};
use sha2::{Digest, Sha256};
use tacenta_session::is_canonical_x25519;

pub const INVENTORY_DOMAIN: &[u8] = b"Tacenta Inventory Statement v1";
const INVENTORY_SIGNING_LABEL: &[u8] = b"Tacenta:inventory-statement:v1\xff";
/// Domain separation for the commitment a replacement stores for its exact
/// retired binding.
pub const BINDING_COMMITMENT_LABEL: &[u8] = b"Tacenta:inventory-binding-commitment:v1\xff";
pub const GROUP_EPOCH_V1: u64 = 1;
pub const MAX_ACCOUNT_BYTES: usize = 256;
pub const MAX_ACTIVE_BINDINGS: usize = 8;
pub const MAX_RECENT_REVOCATIONS: usize = 8;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DeviceBinding {
    pub device_id: u32,
    pub identity_public_key: [u8; 32],
    pub capabilities: u64,
    pub replacement_predecessor: Option<[u8; 32]>,
}

/// Computes the version-one commitment of one canonical device binding.
///
/// This binds every encoded binding field, including a prior replacement
/// predecessor. A replacement names this value for the exact active binding it
/// retires; it is neither an identity-key fingerprint nor a device-id alias.
pub fn binding_commitment(binding: &DeviceBinding) -> Result<[u8; 32], Error> {
    binding_ok(binding)?;
    let mut encoded = Vec::with_capacity(4 + 32 + 8 + 1 + 32);
    put_binding(&mut encoded, binding);
    let mut digest = Sha256::new();
    digest.update(BINDING_COMMITMENT_LABEL);
    digest.update(encoded);
    Ok(digest.finalize().into())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Revocation {
    pub binding: DeviceBinding,
    pub terminal_generation: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InventoryStatement {
    pub issuer_key_id: u64,
    pub account_handle: String,
    pub inventory_generation: u64,
    pub active: Vec<DeviceBinding>,
    pub revocation_floor_generation: u64,
    pub revoked: Vec<Revocation>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Malformed,
    NonCanonical,
    Unsupported,
    NonContributory,
    Policy,
}

/// Product-owned policy hooks for accepting a signed inventory statement.
///
/// The codec can establish syntax, canonical ordering, and the cryptographic
/// signature. It cannot establish that an issuer is bound to an account or
/// that a statement is fresh in a product's database. Callers that rely on an
/// inventory statement must provide those decisions here and call
/// [`InventoryStatement::validate_for`].
pub trait InventoryPolicy {
    /// Resolve the issuer id in the statement for this account. Returning
    /// `None` refuses an unbound issuer instead of treating the id as a key.
    fn issuer_public_key(&self, issuer_key_id: u64, account_handle: &str) -> Option<[u8; 32]>;

    /// Decide whether this statement generation is acceptable for the account.
    /// A product can require equality with its current generation or apply a
    /// deliberately documented freshness window.
    fn generation_is_current(&self, account_handle: &str, generation: u64) -> bool;

    /// Enforce product identity, revocation, and device policy for each
    /// binding, including historical bindings in the revocation list.
    fn binding_is_allowed(&self, account_handle: &str, binding: &DeviceBinding) -> bool;
}

impl InventoryStatement {
    /// Decodes only a fully canonical unsigned v1 statement preimage.
    pub fn decode_unsigned(bytes: &[u8]) -> Result<Self, Error> {
        let mut input = bytes;
        take_exact(&mut input, INVENTORY_DOMAIN)?;
        let issuer_key_id = take_u64(&mut input)?;
        let account_handle =
            String::from_utf8(take_lp(&mut input)?.to_vec()).map_err(|_| Error::Malformed)?;
        let inventory_generation = take_u64(&mut input)?;
        let active = take_many(&mut input, take_binding)?;
        let revocation_floor_generation = take_u64(&mut input)?;
        let revoked = take_many(&mut input, |rest| {
            Ok(Revocation {
                binding: take_binding(rest)?,
                terminal_generation: take_u64(rest)?,
            })
        })?;
        if !input.is_empty() {
            return Err(Error::Malformed);
        }
        let statement = Self {
            issuer_key_id,
            account_handle,
            inventory_generation,
            active,
            revocation_floor_generation,
            revoked,
        };
        if statement.encode_unsigned()? != bytes {
            return Err(Error::NonCanonical);
        }
        Ok(statement)
    }

    /// Validates and encodes the exact unsigned v1 statement preimage.
    pub fn encode_unsigned(&self) -> Result<Vec<u8>, Error> {
        let account = self.account_handle.as_bytes();
        if account.is_empty() || account.len() > MAX_ACCOUNT_BYTES {
            return Err(Error::Malformed);
        }
        if self.active.len() > MAX_ACTIVE_BINDINGS || self.revoked.len() > MAX_RECENT_REVOCATIONS {
            return Err(Error::Malformed);
        }
        if self.revocation_floor_generation > self.inventory_generation {
            return Err(Error::Malformed);
        }
        canonical_bindings(&self.active)?;
        let mut previous = None;
        for revoked in &self.revoked {
            if revoked.terminal_generation <= self.revocation_floor_generation
                || revoked.terminal_generation > self.inventory_generation
            {
                return Err(Error::Malformed);
            }
            binding_ok(&revoked.binding)?;
            if previous.is_some_and(|prior| prior >= revoked) {
                return Err(Error::NonCanonical);
            }
            if self.active.binary_search(&revoked.binding).is_ok() {
                return Err(Error::NonCanonical);
            }
            previous = Some(revoked);
        }
        let mut out = INVENTORY_DOMAIN.to_vec();
        out.extend_from_slice(&self.issuer_key_id.to_be_bytes());
        out.extend_from_slice(&(account.len() as u32).to_be_bytes());
        out.extend_from_slice(account);
        out.extend_from_slice(&self.inventory_generation.to_be_bytes());
        out.extend_from_slice(&(self.active.len() as u32).to_be_bytes());
        for binding in &self.active {
            put_binding(&mut out, binding);
        }
        out.extend_from_slice(&self.revocation_floor_generation.to_be_bytes());
        out.extend_from_slice(&(self.revoked.len() as u32).to_be_bytes());
        for revoked in &self.revoked {
            put_binding(&mut out, &revoked.binding);
            out.extend_from_slice(&revoked.terminal_generation.to_be_bytes());
        }
        Ok(out)
    }

    /// Signs this exact canonical statement under the dedicated hosted-issuer
    /// key. The caller keeps the issuer secret outside this public statement.
    pub fn sign<R: RngCore + CryptoRng>(
        &self,
        issuer_secret: &[u8; 32],
        rng: &mut R,
    ) -> Result<[u8; 64], Error> {
        Ok(xeddsa::sign(
            issuer_secret,
            &signing_input(&self.encode_unsigned()?),
            rng,
        ))
    }

    /// Verifies an issuer signature over this exact canonical statement.
    pub fn verify(&self, issuer_public: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
        let unsigned = self.encode_unsigned()?;
        xeddsa::verify(
            &PublicKeyBytes::from_bytes(*issuer_public),
            &signing_input(&unsigned),
            signature,
        )
        .map_err(|_| Error::Malformed)
    }

    /// Validates a signed statement at the explicit product boundary.
    ///
    /// `decode_signed` is intentionally only a syntax and signature check. It
    /// does not know which issuer belongs to an account, whether the
    /// generation is fresh, or what device/revocation policy a product uses.
    /// This method performs the core identity-key checks and delegates those
    /// product decisions to `policy` before returning an accepted statement.
    pub fn validate_for<P: InventoryPolicy>(
        &self,
        signature: &[u8; 64],
        policy: &P,
    ) -> Result<(), Error> {
        let issuer_public = policy
            .issuer_public_key(self.issuer_key_id, &self.account_handle)
            .ok_or(Error::Policy)?;
        self.verify(&issuer_public, signature)?;
        if !policy.generation_is_current(&self.account_handle, self.inventory_generation) {
            return Err(Error::Policy);
        }

        let mut seen_device_ids = Vec::with_capacity(self.active.len());
        for binding in self
            .active
            .iter()
            .chain(self.revoked.iter().map(|r| &r.binding))
        {
            validate_identity_key(&binding.identity_public_key)?;
            if !policy.binding_is_allowed(&self.account_handle, binding) {
                return Err(Error::Policy);
            }
        }
        for binding in &self.active {
            if seen_device_ids.contains(&binding.device_id) {
                return Err(Error::Policy);
            }
            seen_device_ids.push(binding.device_id);

            if let Some(predecessor) = binding.replacement_predecessor {
                let found = self.revoked.iter().any(|revoked| {
                    revoked.binding.device_id == binding.device_id
                        && binding_commitment(&revoked.binding)
                            .is_ok_and(|commitment| commitment == predecessor)
                });
                if !found {
                    return Err(Error::Policy);
                }
            }
        }
        Ok(())
    }

    pub fn encode_signed<R: RngCore + CryptoRng>(
        &self,
        issuer_secret: &[u8; 32],
        rng: &mut R,
    ) -> Result<Vec<u8>, Error> {
        let mut bytes = self.encode_unsigned()?;
        bytes.extend_from_slice(&self.sign(issuer_secret, rng)?);
        Ok(bytes)
    }

    pub fn decode_signed(bytes: &[u8], issuer_public: &[u8; 32]) -> Result<Self, Error> {
        let unsigned_len = bytes.len().checked_sub(64).ok_or(Error::Malformed)?;
        let statement = Self::decode_unsigned(&bytes[..unsigned_len])?;
        let signature = bytes[unsigned_len..]
            .try_into()
            .map_err(|_| Error::Malformed)?;
        statement.verify(issuer_public, &signature)?;
        Ok(statement)
    }
}

fn take_exact(input: &mut &[u8], expected: &[u8]) -> Result<(), Error> {
    let value = take(input, expected.len())?;
    if value == expected {
        Ok(())
    } else {
        Err(Error::Malformed)
    }
}
fn take<'a>(input: &mut &'a [u8], n: usize) -> Result<&'a [u8], Error> {
    let (head, tail) = input.split_at_checked(n).ok_or(Error::Malformed)?;
    *input = tail;
    Ok(head)
}
fn take_u32(input: &mut &[u8]) -> Result<u32, Error> {
    Ok(u32::from_be_bytes(
        take(input, 4)?.try_into().map_err(|_| Error::Malformed)?,
    ))
}
fn take_u64(input: &mut &[u8]) -> Result<u64, Error> {
    Ok(u64::from_be_bytes(
        take(input, 8)?.try_into().map_err(|_| Error::Malformed)?,
    ))
}
fn take_lp<'a>(input: &mut &'a [u8]) -> Result<&'a [u8], Error> {
    let length = take_u32(input)? as usize;
    take(input, length)
}
fn take_many<T>(
    input: &mut &[u8],
    mut parse: impl FnMut(&mut &[u8]) -> Result<T, Error>,
) -> Result<Vec<T>, Error> {
    let count = take_u32(input)? as usize;
    if count > MAX_ACTIVE_BINDINGS {
        return Err(Error::Malformed);
    }
    (0..count).map(|_| parse(input)).collect()
}
fn take_binding(input: &mut &[u8]) -> Result<DeviceBinding, Error> {
    let device_id = take_u32(input)?;
    let identity_public_key = take(input, 32)?.try_into().map_err(|_| Error::Malformed)?;
    let capabilities = take_u64(input)?;
    let replacement_predecessor = match take(input, 1)?[0] {
        0 => None,
        1 => Some(take(input, 32)?.try_into().map_err(|_| Error::Malformed)?),
        _ => return Err(Error::Malformed),
    };
    Ok(DeviceBinding {
        device_id,
        identity_public_key,
        capabilities,
        replacement_predecessor,
    })
}

fn signing_input(unsigned: &[u8]) -> Vec<u8> {
    let mut input = Vec::with_capacity(INVENTORY_SIGNING_LABEL.len() + unsigned.len());
    input.extend_from_slice(INVENTORY_SIGNING_LABEL);
    input.extend_from_slice(unsigned);
    input
}

fn canonical_bindings(bindings: &[DeviceBinding]) -> Result<(), Error> {
    let mut previous = None;
    for binding in bindings {
        binding_ok(binding)?;
        if previous.is_some_and(|prior| prior >= binding) {
            return Err(Error::NonCanonical);
        }
        previous = Some(binding);
    }
    Ok(())
}
fn binding_ok(binding: &DeviceBinding) -> Result<(), Error> {
    if binding.capabilities & !GROUP_EPOCH_V1 != 0 || binding.capabilities == 0 {
        Err(Error::Unsupported)
    } else {
        Ok(())
    }
}

fn validate_identity_key(key: &[u8; 32]) -> Result<(), Error> {
    if !is_canonical_x25519(key) {
        return Err(Error::NonCanonical);
    }
    // Every low-order X25519 point produces a non-contributory agreement for
    // every private key. One fixed, clamped scalar is sufficient to detect
    // that class; canonicality was checked above, so this is not an encoding
    // test in disguise.
    let probe = crate::primitives::dh::PrivateKey::from_bytes([7; 32]);
    if probe.agree(&PublicKeyBytes::from_bytes(*key)).is_none() {
        return Err(Error::NonContributory);
    }
    Ok(())
}
fn put_binding(out: &mut Vec<u8>, binding: &DeviceBinding) {
    out.extend_from_slice(&binding.device_id.to_be_bytes());
    out.extend_from_slice(&binding.identity_public_key);
    out.extend_from_slice(&binding.capabilities.to_be_bytes());
    match binding.replacement_predecessor {
        Some(previous) => {
            out.push(1);
            out.extend_from_slice(&previous);
        }
        None => out.push(0),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestPolicy {
        secret: [u8; 32],
        issuer_bound: bool,
        generation_current: bool,
    }

    impl InventoryPolicy for TestPolicy {
        fn issuer_public_key(&self, issuer_key_id: u64, account_handle: &str) -> Option<[u8; 32]> {
            if self.issuer_bound && issuer_key_id == 7 && account_handle == "acme/alice" {
                Some(
                    crate::primitives::dh::PrivateKey::from_bytes(self.secret)
                        .public_key()
                        .as_bytes()
                        .to_owned(),
                )
            } else {
                None
            }
        }

        fn generation_is_current(&self, _account_handle: &str, _generation: u64) -> bool {
            self.generation_current
        }

        fn binding_is_allowed(&self, _account_handle: &str, _binding: &DeviceBinding) -> bool {
            true
        }
    }

    fn policy() -> TestPolicy {
        TestPolicy {
            secret: [9; 32],
            issuer_bound: true,
            generation_current: true,
        }
    }

    fn make_statement(active: Vec<DeviceBinding>) -> InventoryStatement {
        InventoryStatement {
            issuer_key_id: 7,
            account_handle: "acme/alice".into(),
            inventory_generation: 2,
            active,
            revocation_floor_generation: 0,
            revoked: vec![],
        }
    }
    fn binding(id: u32) -> DeviceBinding {
        DeviceBinding {
            device_id: id,
            identity_public_key: [id as u8; 32],
            capabilities: GROUP_EPOCH_V1,
            replacement_predecessor: None,
        }
    }
    #[test]
    fn canonical_inventory_preimage_is_bounded_and_refuses_reordered_bindings() {
        let statement = InventoryStatement {
            issuer_key_id: 7,
            account_handle: "acme/alice".into(),
            inventory_generation: 2,
            active: vec![binding(1), binding(2)],
            revocation_floor_generation: 0,
            revoked: vec![],
        };
        assert!(
            statement
                .encode_unsigned()
                .unwrap()
                .starts_with(INVENTORY_DOMAIN)
        );
        let mut reordered = statement;
        reordered.active.swap(0, 1);
        assert_eq!(reordered.encode_unsigned(), Err(Error::NonCanonical));
    }

    #[test]
    fn issuer_signature_binds_the_exact_canonical_statement() {
        let statement = InventoryStatement {
            issuer_key_id: 7,
            account_handle: "acme/alice".into(),
            inventory_generation: 2,
            active: vec![binding(1)],
            revocation_floor_generation: 0,
            revoked: vec![],
        };
        let secret = [9; 32];
        let public = crate::primitives::dh::PrivateKey::from_bytes(secret)
            .public_key()
            .as_bytes()
            .to_owned();
        let signature = statement.sign(&secret, &mut rand_core::OsRng).unwrap();
        assert_eq!(statement.verify(&public, &signature), Ok(()));
        let mut changed = statement;
        changed.inventory_generation = 3;
        assert_eq!(changed.verify(&public, &signature), Err(Error::Malformed));
    }

    #[test]
    fn replacement_commitment_binds_every_canonical_binding_field() {
        let binding = DeviceBinding {
            device_id: 7,
            identity_public_key: [3; 32],
            capabilities: GROUP_EPOCH_V1,
            replacement_predecessor: Some([4; 32]),
        };
        assert_eq!(
            binding_commitment(&binding).unwrap(),
            [
                0x00, 0xdc, 0x59, 0x26, 0x0f, 0xb9, 0x8d, 0xea, 0xe1, 0x9a, 0x0f, 0x07, 0xfb, 0x6c,
                0xe9, 0xa9, 0xb6, 0xe0, 0x43, 0x1f, 0xf9, 0x63, 0xc8, 0xe4, 0xbe, 0xcd, 0x12, 0xf2,
                0x05, 0x2d, 0xe9, 0x81,
            ]
        );
        let mut changed = binding;
        changed.device_id = 8;
        assert_ne!(
            binding_commitment(&changed).unwrap(),
            binding_commitment(&DeviceBinding {
                device_id: 7,
                identity_public_key: [3; 32],
                capabilities: GROUP_EPOCH_V1,
                replacement_predecessor: Some([4; 32]),
            })
            .unwrap()
        );
    }

    #[test]
    fn unsigned_decoder_refuses_trailing_and_noncanonical_data() {
        let statement = InventoryStatement {
            issuer_key_id: 7,
            account_handle: "acme/alice".into(),
            inventory_generation: 2,
            active: vec![binding(1)],
            revocation_floor_generation: 0,
            revoked: vec![],
        };
        let encoded = statement.encode_unsigned().unwrap();
        assert_eq!(InventoryStatement::decode_unsigned(&encoded), Ok(statement));
        let mut trailing = encoded;
        trailing.push(0);
        assert_eq!(
            InventoryStatement::decode_unsigned(&trailing),
            Err(Error::Malformed)
        );
    }

    #[test]
    fn signed_decoder_requires_the_issuer_signature() {
        let statement = InventoryStatement {
            issuer_key_id: 7,
            account_handle: "acme/alice".into(),
            inventory_generation: 2,
            active: vec![binding(1)],
            revocation_floor_generation: 0,
            revoked: vec![],
        };
        let secret = [9; 32];
        let public = crate::primitives::dh::PrivateKey::from_bytes(secret)
            .public_key()
            .as_bytes()
            .to_owned();
        let encoded = statement
            .encode_signed(&secret, &mut rand_core::OsRng)
            .unwrap();
        assert_eq!(
            InventoryStatement::decode_signed(&encoded, &public),
            Ok(statement)
        );
        let mut altered = encoded;
        altered[0] ^= 1;
        assert_eq!(
            InventoryStatement::decode_signed(&altered, &public),
            Err(Error::Malformed)
        );
    }

    #[test]
    fn policy_validation_accepts_a_bound_fresh_contributory_statement() {
        let statement = make_statement(vec![binding(1)]);
        let policy = policy();
        let signature = statement
            .sign(&policy.secret, &mut rand_core::OsRng)
            .unwrap();
        assert_eq!(statement.validate_for(&signature, &policy), Ok(()));
    }

    #[test]
    fn policy_validation_refuses_unbound_stale_and_noncontributory_inputs() {
        let mut policy = policy();
        let statement = make_statement(vec![binding(1)]);
        let signature = statement
            .sign(&policy.secret, &mut rand_core::OsRng)
            .unwrap();

        policy.issuer_bound = false;
        assert_eq!(
            statement.validate_for(&signature, &policy),
            Err(Error::Policy)
        );

        policy.issuer_bound = true;
        policy.generation_current = false;
        assert_eq!(
            statement.validate_for(&signature, &policy),
            Err(Error::Policy)
        );

        let mut low_order = binding(1);
        low_order.identity_public_key = [0; 32];
        let statement = make_statement(vec![low_order]);
        let signature = statement
            .sign(&policy.secret, &mut rand_core::OsRng)
            .unwrap();
        policy.generation_current = true;
        assert_eq!(
            statement.validate_for(&signature, &policy),
            Err(Error::NonContributory)
        );
    }

    #[test]
    fn policy_validation_refuses_duplicate_devices_and_orphan_replacements() {
        let first = DeviceBinding {
            device_id: 1,
            identity_public_key: [3; 32],
            capabilities: GROUP_EPOCH_V1,
            replacement_predecessor: None,
        };
        let second = DeviceBinding {
            device_id: 1,
            identity_public_key: [4; 32],
            capabilities: GROUP_EPOCH_V1,
            replacement_predecessor: None,
        };
        let policy = policy();
        let statement = make_statement(vec![first, second]);
        let signature = statement
            .sign(&policy.secret, &mut rand_core::OsRng)
            .unwrap();
        assert_eq!(
            statement.validate_for(&signature, &policy),
            Err(Error::Policy)
        );

        let replacement = DeviceBinding {
            device_id: 2,
            identity_public_key: [5; 32],
            capabilities: GROUP_EPOCH_V1,
            replacement_predecessor: Some([0x55; 32]),
        };
        let statement = make_statement(vec![replacement]);
        let signature = statement
            .sign(&policy.secret, &mut rand_core::OsRng)
            .unwrap();
        assert_eq!(
            statement.validate_for(&signature, &policy),
            Err(Error::Policy)
        );
    }
}
