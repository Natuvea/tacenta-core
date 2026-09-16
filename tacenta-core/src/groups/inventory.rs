//! Bounded canonical preimages for hosted device-inventory statements.

pub const INVENTORY_DOMAIN: &[u8] = b"Tacenta Inventory Statement v1";
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
}
