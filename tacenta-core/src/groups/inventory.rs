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
#[non_exhaustive]
pub enum Error {
    /// Bytes that do not parse, or a signature that does not verify.
    Malformed,
    NonCanonical,
    Unsupported,
    /// An identity key is a low-order point.
    NonContributory,
    /// The statement names a different account from the one requested.
    WrongAccount,
    /// The policy has no verification key for this issuer and account.
    IssuerUnbound,
    /// The policy does not accept this generation for the account.
    Stale,
    /// Two active bindings carry the same `device_id`.
    DuplicateDevice,
    /// The policy refused a binding or the statement as a whole.
    Refused,
}

/// Whether a binding appears in a statement's `active` or `revoked` list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingStatus {
    Active,
    Revoked,
}

/// Product-owned policy hooks for accepting a signed inventory statement.
///
/// Decoding establishes syntax and canonical form, and verification
/// establishes the issuer signature. Neither establishes that an issuer is bound
/// to an account, that a statement is fresh in a product's database, or that a
/// device set is one the product allows. Those decisions are made here, and
/// [`InventoryStatement::accept`] is the only way to obtain an
/// [`AcceptedInventory`].
pub trait InventoryPolicy {
    /// Resolve the issuer id in the statement for this account. Returning
    /// `None` refuses an unbound issuer instead of treating the id as a key.
    fn issuer_public_key(&self, issuer_key_id: u64, account_handle: &str) -> Option<[u8; 32]>;

    /// Decide whether this generation is acceptable for the account. The
    /// statement carries a generation but no freshness rule: equality with a
    /// stored current value, a window, or anything else is the product's.
    /// Two different validly signed statements at one generation are not
    /// distinguished by the format, so a product that needs to detect that
    /// must record what it has seen.
    fn generation_is_current(&self, account_handle: &str, generation: u64) -> bool;

    /// Enforce product identity and device policy for one binding. Called for
    /// every active binding and every revoked binding, each with its status.
    fn binding_is_allowed(
        &self,
        account_handle: &str,
        binding: &DeviceBinding,
        status: BindingStatus,
    ) -> bool;

    /// Enforce policy that needs the whole statement, which the per-binding
    /// hook cannot see. The format does not require an identity key to be
    /// unique across bindings, a revoked key to stay revoked, or a
    /// replacement to differ from what it replaces; a product that requires
    /// any of these checks them here.
    fn statement_is_allowed(&self, statement: &InventoryStatement) -> bool;
}

/// A statement that [`InventoryStatement::accept`] approved for one account
/// under one policy. It can only be constructed there and cannot be changed
/// afterwards, so group code that takes this type cannot be handed a merely
/// decoded statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AcceptedInventory {
    statement: InventoryStatement,
}

impl AcceptedInventory {
    pub fn statement(&self) -> &InventoryStatement {
        &self.statement
    }
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

    /// Approves this statement for `expected_account`, or refuses it.
    ///
    /// The checks run in this order and the first failure is returned:
    ///
    /// 1. the statement's account equals `expected_account` byte for byte, before
    ///    any hook runs, so a valid statement for another account under a shared
    ///    issuer key is refused;
    /// 2. the policy resolves the issuer key for the statement's account;
    /// 3. the issuer signature verifies;
    /// 4. the policy accepts the generation;
    /// 5. no two active bindings share a `device_id`;
    /// 6. every identity key, active and revoked, is canonical and is not a
    ///    low-order point;
    /// 7. the policy accepts each binding, then the statement as a whole.
    ///
    /// Not checked here, by design: that a `replacement_predecessor` names a
    /// binding in `revoked` (revoked entries at or below the floor are dropped
    /// from the statement, and a replacement may carry a new `device_id`);
    /// identity keys that are off the curve or of mixed torsion; and key
    /// uniqueness or non-reactivation across bindings. See the specification,
    /// "Accepting a signed statement".
    pub fn accept<P: InventoryPolicy>(
        &self,
        expected_account: &str,
        signature: &[u8; 64],
        policy: &P,
    ) -> Result<AcceptedInventory, Error> {
        if self.account_handle != expected_account {
            return Err(Error::WrongAccount);
        }
        let issuer_public = policy
            .issuer_public_key(self.issuer_key_id, &self.account_handle)
            .ok_or(Error::IssuerUnbound)?;
        self.verify(&issuer_public, signature)?;
        if !policy.generation_is_current(&self.account_handle, self.inventory_generation) {
            return Err(Error::Stale);
        }

        let mut seen_device_ids = Vec::with_capacity(self.active.len());
        for binding in &self.active {
            if seen_device_ids.contains(&binding.device_id) {
                return Err(Error::DuplicateDevice);
            }
            seen_device_ids.push(binding.device_id);
        }
        let bindings = self
            .active
            .iter()
            .map(|binding| (binding, BindingStatus::Active))
            .chain(
                self.revoked
                    .iter()
                    .map(|revoked| (&revoked.binding, BindingStatus::Revoked)),
            );
        for (binding, status) in bindings {
            validate_identity_key(&binding.identity_public_key)?;
            if !policy.binding_is_allowed(&self.account_handle, binding, status) {
                return Err(Error::Refused);
            }
        }
        if !policy.statement_is_allowed(self) {
            return Err(Error::Refused);
        }
        Ok(AcceptedInventory {
            statement: self.clone(),
        })
    }

    /// Decodes signed wire bytes and approves them for `expected_account`.
    /// This is the one-call path: the signature is taken from the trailing 64
    /// bytes, and the issuer key comes from the policy rather than from the
    /// caller, who cannot know it before reading the statement.
    pub fn accept_signed<P: InventoryPolicy>(
        bytes: &[u8],
        expected_account: &str,
        policy: &P,
    ) -> Result<AcceptedInventory, Error> {
        let (statement, signature) = Self::split_signed(bytes)?;
        statement.accept(expected_account, &signature, policy)
    }

    fn split_signed(bytes: &[u8]) -> Result<(Self, [u8; 64]), Error> {
        let unsigned_len = bytes.len().checked_sub(64).ok_or(Error::Malformed)?;
        let statement = Self::decode_unsigned(&bytes[..unsigned_len])?;
        let signature = bytes[unsigned_len..]
            .try_into()
            .map_err(|_| Error::Malformed)?;
        Ok((statement, signature))
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

    /// Decodes signed bytes and checks the signature under a key the caller
    /// already holds. The result is **not accepted**: nothing here checks the
    /// account, freshness, or any policy, and the type is the same as a decoded
    /// but unsigned statement. Use [`InventoryStatement::accept_signed`] to
    /// obtain an [`AcceptedInventory`].
    pub fn decode_signed(bytes: &[u8], issuer_public: &[u8; 32]) -> Result<Self, Error> {
        let (statement, signature) = Self::split_signed(bytes)?;
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

    const ALICE: &str = "acme/alice";
    const BOB: &str = "acme/bob";
    const ALICE_SECRET: [u8; 32] = [9; 32];
    const BOB_SECRET: [u8; 32] = [10; 32];

    fn public_of(secret: [u8; 32]) -> [u8; 32] {
        crate::primitives::dh::PrivateKey::from_bytes(secret)
            .public_key()
            .as_bytes()
            .to_owned()
    }

    /// A policy whose hooks compare their arguments with expected values, so a
    /// caller that passes the wrong account, generation, or status is caught.
    struct TestPolicy {
        /// (issuer id, account, issuer public key). An account of `""` matches
        /// every account: one hosted issuer key for a whole tenant.
        issuers: Vec<(u64, &'static str, [u8; 32])>,
        /// (account, the one generation this policy accepts for it).
        current: Vec<(&'static str, u64)>,
        /// Refuse this key when it appears with this status.
        denied: Option<([u8; 32], BindingStatus)>,
        /// Refuse any statement whose bindings repeat an identity key.
        require_unique_keys: bool,
        refuse_statement: bool,
        hook_calls: std::cell::Cell<u32>,
    }

    impl TestPolicy {
        fn known(&self, account_handle: &str) -> bool {
            self.current
                .iter()
                .any(|(account, _)| *account == account_handle)
        }
    }

    impl InventoryPolicy for TestPolicy {
        fn issuer_public_key(&self, issuer_key_id: u64, account_handle: &str) -> Option<[u8; 32]> {
            self.hook_calls.set(self.hook_calls.get() + 1);
            self.issuers
                .iter()
                .find(|(id, account, _)| {
                    *id == issuer_key_id && (account.is_empty() || *account == account_handle)
                })
                .map(|(_, _, key)| *key)
        }

        fn generation_is_current(&self, account_handle: &str, generation: u64) -> bool {
            self.hook_calls.set(self.hook_calls.get() + 1);
            self.current
                .iter()
                .any(|(account, current)| *account == account_handle && *current == generation)
        }

        fn binding_is_allowed(
            &self,
            account_handle: &str,
            binding: &DeviceBinding,
            status: BindingStatus,
        ) -> bool {
            self.hook_calls.set(self.hook_calls.get() + 1);
            if !self.known(account_handle) {
                return false;
            }
            !self
                .denied
                .is_some_and(|(key, denied)| key == binding.identity_public_key && denied == status)
        }

        fn statement_is_allowed(&self, statement: &InventoryStatement) -> bool {
            self.hook_calls.set(self.hook_calls.get() + 1);
            if self.refuse_statement || !self.known(&statement.account_handle) {
                return false;
            }
            if self.require_unique_keys {
                let keys: Vec<_> = statement
                    .active
                    .iter()
                    .chain(statement.revoked.iter().map(|r| &r.binding))
                    .map(|b| b.identity_public_key)
                    .collect();
                return keys
                    .iter()
                    .enumerate()
                    .all(|(i, key)| !keys[..i].contains(key));
            }
            true
        }
    }

    fn policy() -> TestPolicy {
        TestPolicy {
            issuers: vec![
                (7, ALICE, public_of(ALICE_SECRET)),
                (8, BOB, public_of(BOB_SECRET)),
            ],
            current: vec![(ALICE, 2), (BOB, 5)],
            denied: None,
            require_unique_keys: false,
            refuse_statement: false,
            hook_calls: std::cell::Cell::new(0),
        }
    }

    fn statement_for(
        issuer_key_id: u64,
        account: &str,
        generation: u64,
        active: Vec<DeviceBinding>,
    ) -> InventoryStatement {
        InventoryStatement {
            issuer_key_id,
            account_handle: account.into(),
            inventory_generation: generation,
            active,
            revocation_floor_generation: 0,
            revoked: vec![],
        }
    }
    fn make_statement(active: Vec<DeviceBinding>) -> InventoryStatement {
        statement_for(7, ALICE, 2, active)
    }
    fn with_revoked(
        mut statement: InventoryStatement,
        revoked: Vec<DeviceBinding>,
    ) -> InventoryStatement {
        statement.revoked = revoked
            .into_iter()
            .map(|binding| Revocation {
                binding,
                terminal_generation: 1,
            })
            .collect();
        statement
    }
    fn sign(statement: &InventoryStatement, secret: [u8; 32]) -> [u8; 64] {
        statement.sign(&secret, &mut rand_core::OsRng).unwrap()
    }
    /// Signs under the account's own issuer key and accepts for that account.
    fn accept_alice(
        statement: &InventoryStatement,
        policy: &TestPolicy,
    ) -> Result<AcceptedInventory, Error> {
        statement.accept(ALICE, &sign(statement, ALICE_SECRET), policy)
    }
    fn keyed(id: u32, key: [u8; 32]) -> DeviceBinding {
        DeviceBinding {
            identity_public_key: key,
            ..binding(id)
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

    const LOW_ORDER: [[u8; 32]; 5] = [
        [0; 32],
        {
            let mut k = [0u8; 32];
            k[0] = 1;
            k
        },
        // p - 1
        {
            let mut k = [0xffu8; 32];
            k[0] = 0xec;
            k[31] = 0x7f;
            k
        },
        [
            0xe0, 0xeb, 0x7a, 0x7c, 0x3b, 0x41, 0xb8, 0xae, 0x16, 0x56, 0xe3, 0xfa, 0xf1, 0x9f,
            0xc4, 0x6a, 0xda, 0x09, 0x8d, 0xeb, 0x9c, 0x32, 0xb1, 0xfd, 0x86, 0x62, 0x05, 0x16,
            0x5f, 0x49, 0xb8, 0x00,
        ],
        [
            0x5f, 0x9c, 0x95, 0xbc, 0xa3, 0x50, 0x8c, 0x24, 0xb1, 0xd0, 0xb1, 0x55, 0x9c, 0x83,
            0xef, 0x5b, 0x04, 0x44, 0x5c, 0xc4, 0x58, 0x1c, 0x8e, 0x86, 0xd8, 0x22, 0x4e, 0xdd,
            0xd0, 0x9f, 0x11, 0x57,
        ],
    ];

    fn non_canonical() -> Vec<[u8; 32]> {
        // p, p + 1, p + 9 (all below 2^255 but not below p), the all-ones string,
        // and the two spellings of small values that only differ in bit 255.
        let p_plus = |n: u8| {
            let mut k = [0xffu8; 32];
            k[0] = 0xed + n;
            k[31] = 0x7f;
            k
        };
        let mut nine_high = [0u8; 32];
        nine_high[0] = 9;
        nine_high[31] = 0x80;
        let mut zero_high = [0u8; 32];
        zero_high[31] = 0x80;
        vec![
            p_plus(0),
            p_plus(1),
            p_plus(9),
            [0xff; 32],
            nine_high,
            zero_high,
        ]
    }

    #[test]
    fn accepts_a_bound_fresh_statement_for_each_account() {
        let policy = policy();
        let alice = make_statement(vec![binding(1), binding(2)]);
        let accepted = accept_alice(&alice, &policy).unwrap();
        assert_eq!(accepted.statement(), &alice);

        // A second account, issuer id and generation: the hooks must be given
        // this statement's own values, not another statement's.
        let bob = statement_for(8, BOB, 5, vec![binding(3)]);
        let accepted = bob.accept(BOB, &sign(&bob, BOB_SECRET), &policy).unwrap();
        assert_eq!(accepted.statement(), &bob);
    }

    #[test]
    fn refuses_another_accounts_statement_before_any_hook_runs() {
        // One issuer key for the whole tenant: the shape the hosted profile has.
        let mut policy = policy();
        policy.issuers = vec![(9, "", public_of(ALICE_SECRET))];
        let bob = statement_for(9, BOB, 5, vec![binding(3)]);
        let signature = sign(&bob, ALICE_SECRET);
        assert!(bob.accept(BOB, &signature, &policy).is_ok());
        policy.hook_calls.set(0);
        assert_eq!(
            bob.accept(ALICE, &signature, &policy),
            Err(Error::WrongAccount)
        );
        assert_eq!(policy.hook_calls.get(), 0);
        // Byte for byte, not case-folded.
        assert_eq!(
            bob.accept("ACME/BOB", &signature, &policy),
            Err(Error::WrongAccount)
        );
    }

    #[test]
    fn refuses_an_issuer_the_policy_does_not_bind_to_the_account() {
        let policy = policy();
        let unknown_id = statement_for(99, ALICE, 2, vec![binding(1)]);
        assert_eq!(
            accept_alice(&unknown_id, &policy),
            Err(Error::IssuerUnbound)
        );
        // Issuer 8 exists, but for another account.
        let wrong_pair = statement_for(8, ALICE, 2, vec![binding(1)]);
        assert_eq!(
            accept_alice(&wrong_pair, &policy),
            Err(Error::IssuerUnbound)
        );
    }

    #[test]
    fn refuses_a_bad_or_misattributed_signature() {
        let policy = policy();
        let statement = make_statement(vec![binding(1)]);
        let good = sign(&statement, ALICE_SECRET);
        assert!(statement.accept(ALICE, &good, &policy).is_ok());

        let mut tampered = good;
        tampered[10] ^= 1;
        assert_eq!(
            statement.accept(ALICE, &tampered, &policy),
            Err(Error::Malformed)
        );
        // Signed by a key the policy does not hold for this issuer.
        assert_eq!(
            statement.accept(ALICE, &sign(&statement, BOB_SECRET), &policy),
            Err(Error::Malformed)
        );
        // Statement changed after it was signed.
        let mut changed = statement;
        changed.inventory_generation = 3;
        assert_eq!(changed.accept(ALICE, &good, &policy), Err(Error::Malformed));
    }

    #[test]
    fn refuses_a_generation_the_policy_does_not_accept() {
        let policy = policy();
        assert_eq!(
            accept_alice(&statement_for(7, ALICE, 3, vec![binding(1)]), &policy),
            Err(Error::Stale)
        );
        assert_eq!(
            accept_alice(&statement_for(7, ALICE, 1, vec![binding(1)]), &policy),
            Err(Error::Stale)
        );
    }

    #[test]
    fn refuses_low_order_identity_keys_wherever_they_appear() {
        let policy = policy();
        for key in LOW_ORDER {
            let active = make_statement(vec![keyed(1, key)]);
            assert_eq!(
                accept_alice(&active, &policy),
                Err(Error::NonContributory),
                "active {key:02x?}"
            );
            let revoked = with_revoked(make_statement(vec![binding(2)]), vec![keyed(1, key)]);
            assert_eq!(
                accept_alice(&revoked, &policy),
                Err(Error::NonContributory),
                "revoked {key:02x?}"
            );
        }
    }

    #[test]
    fn refuses_non_canonical_identity_keys_wherever_they_appear() {
        let policy = policy();
        for key in non_canonical() {
            let active = make_statement(vec![keyed(1, key)]);
            assert_eq!(
                accept_alice(&active, &policy),
                Err(Error::NonCanonical),
                "active {key:02x?}"
            );
            let revoked = with_revoked(make_statement(vec![binding(2)]), vec![keyed(1, key)]);
            assert_eq!(
                accept_alice(&revoked, &policy),
                Err(Error::NonCanonical),
                "revoked {key:02x?}"
            );
        }
    }

    #[test]
    fn ordinary_keys_are_accepted_and_off_curve_keys_are_a_stated_limit() {
        let policy = policy();
        let mut base = [0u8; 32];
        base[0] = 9;
        assert!(accept_alice(&make_statement(vec![keyed(1, base)]), &policy).is_ok());
        // u = 2 has no point on the curve (it is on the quadratic twist), so no
        // honest device holds a private key for it. The format does not refuse
        // it; the specification lists this as not checked.
        let mut twist = [0u8; 32];
        twist[0] = 2;
        assert!(accept_alice(&make_statement(vec![keyed(1, twist)]), &policy).is_ok());
    }

    #[test]
    fn refuses_two_active_bindings_with_one_device_id() {
        let policy = policy();
        let statement = make_statement(vec![keyed(1, [3; 32]), keyed(1, [4; 32])]);
        assert_eq!(
            accept_alice(&statement, &policy),
            Err(Error::DuplicateDevice)
        );
        // The same device id may appear once active and once revoked: that is
        // what replacing a device's key under its old id looks like.
        let replaced = with_revoked(
            make_statement(vec![keyed(1, [4; 32])]),
            vec![keyed(1, [3; 32])],
        );
        assert!(accept_alice(&replaced, &policy).is_ok());
    }

    #[test]
    fn binding_hook_is_told_the_account_and_each_bindings_status() {
        let mut policy = policy();
        let key = [3; 32];
        policy.denied = Some((key, BindingStatus::Revoked));
        let revoked = with_revoked(make_statement(vec![binding(2)]), vec![keyed(1, key)]);
        assert_eq!(accept_alice(&revoked, &policy), Err(Error::Refused));
        // The same key, active, is not what this policy denies.
        assert!(accept_alice(&make_statement(vec![keyed(1, key)]), &policy).is_ok());

        policy.denied = Some((key, BindingStatus::Active));
        assert_eq!(
            accept_alice(&make_statement(vec![keyed(1, key)]), &policy),
            Err(Error::Refused)
        );
        assert!(accept_alice(&revoked, &policy).is_ok());
    }

    #[test]
    fn statement_hook_expresses_the_rules_the_format_leaves_to_the_product() {
        let mut policy = policy();
        let statement = make_statement(vec![binding(1)]);
        policy.refuse_statement = true;
        assert_eq!(accept_alice(&statement, &policy), Err(Error::Refused));
        policy.refuse_statement = false;
        assert!(accept_alice(&statement, &policy).is_ok());

        // Shapes the format accepts and a product may not want. With
        // `require_unique_keys` each is refused; without it each is accepted.
        let one_key_two_devices = make_statement(vec![keyed(1, [3; 32]), keyed(2, [3; 32])]);
        let relinked_revoked_key = with_revoked(
            make_statement(vec![keyed(2, [3; 32])]),
            vec![keyed(1, [3; 32])],
        );
        let no_op_replacement = with_revoked(
            make_statement(vec![keyed(1, [3; 32])]),
            vec![DeviceBinding {
                replacement_predecessor: Some([0x55; 32]),
                ..keyed(1, [3; 32])
            }],
        );
        for shape in [one_key_two_devices, relinked_revoked_key, no_op_replacement] {
            policy.require_unique_keys = false;
            assert!(accept_alice(&shape, &policy).is_ok(), "{shape:?}");
            policy.require_unique_keys = true;
            assert_eq!(
                accept_alice(&shape, &policy),
                Err(Error::Refused),
                "{shape:?}"
            );
        }
    }

    #[test]
    fn replacement_predecessor_is_not_checked_against_the_revoked_list() {
        let policy = policy();
        let old = keyed(1, [3; 32]);
        let commitment = binding_commitment(&old).unwrap();
        let replacement = |id| DeviceBinding {
            replacement_predecessor: Some(commitment),
            ..keyed(id, [4; 32])
        };

        // The retired binding is still listed, under the same device id.
        let listed = with_revoked(make_statement(vec![replacement(1)]), vec![old.clone()]);
        assert!(accept_alice(&listed, &policy).is_ok());

        // Under a new device id, which the lifecycle allows.
        let new_id = with_revoked(make_statement(vec![replacement(2)]), vec![old.clone()]);
        assert!(accept_alice(&new_id, &policy).is_ok());

        // Its tombstone has been compacted away: revoked at generation 1, floor
        // 2, statement at generation 5. The marker outlives the tombstone.
        let mut policy = policy;
        policy.current = vec![(ALICE, 5)];
        let mut compacted = statement_for(7, ALICE, 5, vec![replacement(1)]);
        compacted.revocation_floor_generation = 2;
        assert!(accept_alice(&compacted, &policy).is_ok());
    }

    #[test]
    fn accept_signed_takes_wire_bytes_end_to_end() {
        let policy = policy();
        let statement = make_statement(vec![binding(1)]);
        let wire = statement
            .encode_signed(&ALICE_SECRET, &mut rand_core::OsRng)
            .unwrap();
        let accepted = InventoryStatement::accept_signed(&wire, ALICE, &policy).unwrap();
        assert_eq!(accepted.statement(), &statement);

        assert_eq!(
            InventoryStatement::accept_signed(&wire, BOB, &policy),
            Err(Error::WrongAccount)
        );
        assert_eq!(
            InventoryStatement::accept_signed(&wire[..40], ALICE, &policy),
            Err(Error::Malformed)
        );
        let mut bad_signature = wire.clone();
        *bad_signature.last_mut().unwrap() ^= 1;
        assert_eq!(
            InventoryStatement::accept_signed(&bad_signature, ALICE, &policy),
            Err(Error::Malformed)
        );
        let mut bad_body = wire;
        bad_body[0] ^= 1;
        assert_eq!(
            InventoryStatement::accept_signed(&bad_body, ALICE, &policy),
            Err(Error::Malformed)
        );
    }
}
