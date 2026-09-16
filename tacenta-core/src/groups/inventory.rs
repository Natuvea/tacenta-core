//! Bounded canonical preimages for hosted device-inventory statements.

use crate::primitives::{dh::PublicKeyBytes, xeddsa};
use rand_core::{CryptoRng, RngCore};

pub const INVENTORY_DOMAIN: &[u8] = b"Tacenta Inventory Statement v1";
const INVENTORY_SIGNING_LABEL: &[u8] = b"Tacenta:inventory-statement:v1\xff";
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
        let active = take_many(&mut input, |rest| take_binding(rest))?;
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
}

fn take_exact<'a>(input: &mut &'a [u8], expected: &[u8]) -> Result<(), Error> {
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
}
