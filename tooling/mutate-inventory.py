#!/usr/bin/env python3
"""Mutation harness for the hosted-inventory acceptance boundary.

    python3 tooling/mutate-inventory.py                 # every mutant
    python3 tooling/mutate-inventory.py --list          # ids and descriptions
    python3 tooling/mutate-inventory.py --applies       # only check the list still matches the source
    python3 tooling/mutate-inventory.py --only O07 K05  # some mutants

`tacenta-core/src/groups/inventory.rs` is the mutated file. Each mutant is one
edit to its production code (never to its tests), built into a scratch copy of
the tree and run against the module's unit tests, the library's other unit
tests and the vector runner, `tacenta-core/tests/group_commitments.rs`. A mutant
that leaves every one of those green has survived, and a survivor is either a
gap in the tests or an edit that changes nothing. The list below says which.

Every mutant carries an expectation. `killed` is the default and the point.
`equivalent` is a claim that the edit changes no verdict, kept with the reason,
and the harness fails if such a mutant is killed, so a reason that stops being
true does not linger. The harness also fails when an edit no longer applies to
exactly one place in the source, when the unmutated tree does not pass, and
when a mutant does not compile, so the list cannot rot quietly.

The working tree is never modified: the mutants are built in a temporary copy
of `tacenta-core` and of the vectors. Nothing here runs in CI; it is a
reproducible count, not a gate. It needs `cargo`. Set `CARGO_TARGET_DIR` (or
pass `--target-dir`) to reuse a build between runs; each mutant then rebuilds
only `tacenta-core`.

Exit status is 0 only if every expectation held.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE = os.path.join("tacenta-core", "src", "groups", "inventory.rs")
TEST_MARK = "#[cfg(test)]\nmod tests {"
TEST_COMMAND = ["cargo", "test", "-j", "4", "--lib", "--test", "group_commitments", "--no-fail-fast"]

# --- the blocks of `accept`, so an order mutant is built from the real text ----
B_ENCODING = "        let unsigned = self.encode_unsigned()?;\n"
B_ACCOUNT = (
    "        if self.account_handle != expected_account {\n"
    "            return Err(Error::WrongAccount);\n"
    "        }\n"
)
B_ISSUER = (
    "        let issuer_public = policy\n"
    "            .issuer_public_key(self.issuer_key_id, &self.account_handle)\n"
    "            .ok_or(Error::IssuerUnbound)?;\n"
)
B_SIGNATURE = "        verify_signature(&unsigned, &issuer_public, signature)?;\n"
B_FRESHNESS = (
    "        if !policy.generation_is_current(&self.account_handle, self.inventory_generation) {\n"
    "            return Err(Error::Stale);\n"
    "        }\n"
)
B_DEVICES = "        self.check_unique_devices()?;\n"
B_KEYS = (
    "        // Every key is examined before any binding or statement hook runs, so\n"
    "        // neither runs on a statement that carries an unsound key anywhere. The\n"
    "        // issuer and generation hooks have already run, as the order requires.\n"
    "        self.check_identity_keys()?;\n"
)
B_BINDINGS = (
    "        for (binding, status) in self.bindings() {\n"
    "            if !policy.binding_is_allowed(&self.account_handle, binding, status) {\n"
    "                return Err(Error::Refused);\n"
    "            }\n"
    "        }\n"
)
B_STATEMENT = (
    "        if !policy.statement_is_allowed(self) {\n"
    "            return Err(Error::Refused);\n"
    "        }\n"
)
BLOCKS = {
    "encoding": B_ENCODING, "account": B_ACCOUNT, "issuer": B_ISSUER, "signature": B_SIGNATURE,
    "freshness": B_FRESHNESS, "devices": B_DEVICES, "keys": B_KEYS, "bindings": B_BINDINGS,
    "statement": B_STATEMENT,
}
BASE_ORDER = ["encoding", "account", "issuer", "signature", "freshness", "devices", "keys",
              "bindings", "statement"]
CHAIN = "".join(BLOCKS[name] for name in BASE_ORDER)

MUTANTS = []  # (id, area, description, old, new, equivalent reason or None)


def m(mid, area, description, old, new):
    MUTANTS.append((mid, area, description, old, new, None))


def eq(mid, area, description, old, new, reason):
    MUTANTS.append((mid, area, description, old, new, reason))


def order(mid, description, names):
    MUTANTS.append((mid, "order", description, CHAIN, "".join(BLOCKS[n] for n in names), None))


# ------------------------------------------------------------------ accept: checks
m("A01", "accept", "account check inverted", "if self.account_handle != expected_account {",
  "if self.account_handle == expected_account {")
m("A02", "accept", "account check removed", "if self.account_handle != expected_account {", "if false {")
m("A03", "accept", "account compared without case",
  "if self.account_handle != expected_account {",
  "if !self.account_handle.eq_ignore_ascii_case(expected_account) {")
m("A04", "accept", "account compared by prefix only",
  "if self.account_handle != expected_account {",
  "if !self.account_handle.starts_with(expected_account) {")
m("A05", "accept", "an unbound issuer becomes an all-zero key",
  "            .ok_or(Error::IssuerUnbound)?;", "            .unwrap_or([0u8; 32]);")
m("A06", "accept", "the signature result is ignored",
  "        verify_signature(&unsigned, &issuer_public, signature)?;",
  "        let _ = verify_signature(&unsigned, &issuer_public, signature);")
m("A07", "accept", "the freshness hook is not consulted",
  "        if !policy.generation_is_current(&self.account_handle, self.inventory_generation) {",
  "        if false && !policy.generation_is_current(&self.account_handle, self.inventory_generation) {")
m("A08", "accept", "the freshness answer is inverted",
  "        if !policy.generation_is_current(&self.account_handle, self.inventory_generation) {",
  "        if policy.generation_is_current(&self.account_handle, self.inventory_generation) {")
m("A09", "accept", "the freshness hook is given the floor, not the generation",
  "policy.generation_is_current(&self.account_handle, self.inventory_generation)",
  "policy.generation_is_current(&self.account_handle, self.revocation_floor_generation)")
m("A10", "accept", "the duplicate device check is skipped in accept",
  B_DEVICES + B_KEYS, B_KEYS)
m("A11", "accept", "the identity key pass is skipped in accept",
  B_KEYS + B_BINDINGS, B_BINDINGS)
m("A12", "accept", "duplicate device ids are never recorded",
  "            seen_device_ids.push(binding.device_id);", "            let _ = &seen_device_ids;")
m("A13", "accept", "the duplicate comparison is removed",
  "            if seen_device_ids.contains(&binding.device_id) {",
  "            if false && seen_device_ids.contains(&binding.device_id) {")
m("A14", "accept", "the key pass skips revoked entries",
  "        for (binding, _) in self.bindings() {\n            validate_identity_key",
  "        for (binding, _) in self.bindings().take(self.active.len()) {\n            validate_identity_key")
m("A15", "accept", "the key pass skips active entries",
  "        for (binding, _) in self.bindings() {\n            validate_identity_key",
  "        for (binding, _) in self.bindings().skip(self.active.len()) {\n            validate_identity_key")
m("A16", "accept", "the key pass examines only the first entry",
  "        for (binding, _) in self.bindings() {\n            validate_identity_key",
  "        for (binding, _) in self.bindings().take(1) {\n            validate_identity_key")
m("A17", "accept", "the key pass skips the first entry",
  "        for (binding, _) in self.bindings() {\n            validate_identity_key",
  "        for (binding, _) in self.bindings().skip(1) {\n            validate_identity_key")
m("A18", "accept", "the key pass skips the last entry",
  "        for (binding, _) in self.bindings() {\n            validate_identity_key",
  "        for (binding, _) in self\n            .bindings()\n            .take((self.active.len() + self.revoked.len()).saturating_sub(1))\n        {\n            validate_identity_key")
m("A19", "accept", "the key pass ignores its result",
  "            validate_identity_key(&binding.identity_public_key)?;",
  "            let _ = validate_identity_key(&binding.identity_public_key);")
m("A20", "accept", "the binding hook is skipped for revoked entries",
  "        for (binding, status) in self.bindings() {\n            if !policy",
  "        for (binding, status) in self.bindings().filter(|(_, s)| *s == BindingStatus::Active) {\n            if !policy")
m("A21", "accept", "the binding hook is skipped for active entries",
  "        for (binding, status) in self.bindings() {\n            if !policy",
  "        for (binding, status) in self.bindings().filter(|(_, s)| *s == BindingStatus::Revoked) {\n            if !policy")
m("A22", "accept", "active entries are reported as revoked",
  ".map(|binding| (binding, BindingStatus::Active))",
  ".map(|binding| (binding, BindingStatus::Revoked))")
m("A23", "accept", "revoked entries are reported as active",
  ".map(|revoked| (&revoked.binding, BindingStatus::Revoked))",
  ".map(|revoked| (&revoked.binding, BindingStatus::Active))")
m("A24", "accept", "the binding answer is inverted",
  "            if !policy.binding_is_allowed(&self.account_handle, binding, status) {",
  "            if policy.binding_is_allowed(&self.account_handle, binding, status) {")
m("A25", "accept", "the binding hook stops after the first entry",
  "                return Err(Error::Refused);\n            }\n        }\n        if !policy.statement_is_allowed",
  "                return Err(Error::Refused);\n            }\n            break;\n        }\n        if !policy.statement_is_allowed")
m("A26", "accept", "the statement hook is not consulted",
  "        if !policy.statement_is_allowed(self) {", "        if false && !policy.statement_is_allowed(self) {")
m("A27", "accept", "the statement answer is inverted",
  "        if !policy.statement_is_allowed(self) {", "        if policy.statement_is_allowed(self) {")
m("A28", "accept", "the statement hook is given a statement without its active list",
  "policy.statement_is_allowed(self)",
  "policy.statement_is_allowed(&InventoryStatement { active: vec![], ..self.clone() })")
m("A29", "accept", "the accepted value loses its last active binding",
  "            statement: self.clone(),",
  "            statement: {\n                let mut s = self.clone();\n                s.active.pop();\n                s\n            },")
m("A30", "accept", "the accepted value has another generation",
  "            statement: self.clone(),",
  "            statement: {\n                let mut s = self.clone();\n                s.inventory_generation ^= 1;\n                s\n            },")
m("A31", "accept", "the issuer hook is given issuer id 0",
  "            .issuer_public_key(self.issuer_key_id, &self.account_handle)",
  "            .issuer_public_key(0, &self.account_handle)")
eq("A32", "accept", "the issuer hook is given the asked-for account, not the statement's",
   "            .issuer_public_key(self.issuer_key_id, &self.account_handle)",
   "            .issuer_public_key(self.issuer_key_id, expected_account)",
   "the two accounts are equal here, by check 1")
eq("A33", "accept", "the binding hook is given the asked-for account, not the statement's",
   "policy.binding_is_allowed(&self.account_handle, binding, status)",
   "policy.binding_is_allowed(expected_account, binding, status)",
   "the two accounts are equal here, by check 1")
m("A34", "accept", "accept_signed asks about the statement's own account",
  "        statement.accept(expected_account, &signature, policy)",
  "        statement.accept(&statement.account_handle.clone(), &signature, policy)")
m("A35", "accept", "accept_signed returns the decoded statement without accepting it",
  "        statement.accept(expected_account, &signature, policy)\n    }\n\n    fn split_signed",
  "        let _ = (expected_account, signature, policy);\n        Ok(AcceptedInventory { statement })\n    }\n\n    fn split_signed")
m("A36", "accept", "the encoding rules are not applied to a hand-built statement",
  B_ENCODING, "        let unsigned = self.encode_unsigned().unwrap_or_default();\n")

# ------------------------------------------------------------------ the order of the checks
order("O01", "freshness before the signature",
      ["encoding", "account", "issuer", "freshness", "signature", "devices", "keys", "bindings", "statement"])
order("O02", "freshness before the issuer lookup",
      ["encoding", "account", "freshness", "issuer", "signature", "devices", "keys", "bindings", "statement"])
order("O03", "the duplicate check before freshness",
      ["encoding", "account", "issuer", "signature", "devices", "freshness", "keys", "bindings", "statement"])
order("O04", "the key pass before the duplicate check",
      ["encoding", "account", "issuer", "signature", "freshness", "keys", "devices", "bindings", "statement"])
order("O05", "the key pass before freshness",
      ["encoding", "account", "issuer", "signature", "keys", "freshness", "devices", "bindings", "statement"])
order("O06", "the issuer lookup before the account check",
      ["encoding", "issuer", "account", "signature", "freshness", "devices", "keys", "bindings", "statement"])
order("O07", "the statement hook before the binding hooks",
      ["encoding", "account", "issuer", "signature", "freshness", "devices", "keys", "statement", "bindings"])
order("O08", "the statement hook before the key pass",
      ["encoding", "account", "issuer", "signature", "freshness", "devices", "statement", "keys", "bindings"])
order("O09", "the binding hooks before the key pass",
      ["encoding", "account", "issuer", "signature", "freshness", "devices", "bindings", "keys", "statement"])
order("O10", "the signature after freshness and the duplicate check",
      ["encoding", "account", "issuer", "freshness", "devices", "signature", "keys", "bindings", "statement"])
order("O11", "the account check after the issuer lookup",
      ["encoding", "issuer", "signature", "account", "freshness", "devices", "keys", "bindings", "statement"])
order("O12", "the encoding rules after the account check",
      ["account", "encoding", "issuer", "signature", "freshness", "devices", "keys", "bindings", "statement"])
order("O13", "the encoding rules after the issuer lookup",
      ["account", "issuer", "encoding", "signature", "freshness", "devices", "keys", "bindings", "statement"])
MUTANTS.append((
    "O14", "order", "one pass: each key is checked just before its binding hook", CHAIN,
    B_ENCODING + B_ACCOUNT + B_ISSUER + B_SIGNATURE + B_FRESHNESS + B_DEVICES
    + "        for (binding, status) in self.bindings() {\n"
      "            validate_identity_key(&binding.identity_public_key)?;\n"
      "            if !policy.binding_is_allowed(&self.account_handle, binding, status) {\n"
      "                return Err(Error::Refused);\n"
      "            }\n"
      "        }\n" + B_STATEMENT, None))
MUTANTS.append((
    "O15", "order", "active keys first, revoked keys inside the binding pass", CHAIN,
    B_ENCODING + B_ACCOUNT + B_ISSUER + B_SIGNATURE + B_FRESHNESS + B_DEVICES
    + "        for (binding, _) in self.bindings().take(self.active.len()) {\n"
      "            validate_identity_key(&binding.identity_public_key)?;\n"
      "        }\n"
      "        for (binding, status) in self.bindings() {\n"
      "            if status == BindingStatus::Revoked {\n"
      "                validate_identity_key(&binding.identity_public_key)?;\n"
      "            }\n"
      "            if !policy.binding_is_allowed(&self.account_handle, binding, status) {\n"
      "                return Err(Error::Refused);\n"
      "            }\n"
      "        }\n" + B_STATEMENT, None))
m("O16", "order", "revoked entries before active entries",
  "        self.active\n            .iter()\n            .map(|binding| (binding, BindingStatus::Active))\n"
  "            .chain(\n                self.revoked\n                    .iter()\n"
  "                    .map(|revoked| (&revoked.binding, BindingStatus::Revoked)),\n            )",
  "        self.revoked\n            .iter()\n            .map(|revoked| (&revoked.binding, BindingStatus::Revoked))\n"
  "            .chain(\n                self.active\n                    .iter()\n"
  "                    .map(|binding| (binding, BindingStatus::Active)),\n            )")
m("O17", "order", "binding hooks run in reverse order",
  "        for (binding, status) in self.bindings() {\n            if !policy",
  "        for (binding, status) in self.bindings().collect::<Vec<_>>().into_iter().rev() {\n            if !policy")

# ------------------------------------------------------------------ check 6
m("K01", "key", "the canonical test is removed", "    if !is_canonical_x25519(key) {", "    if false {")
m("K02", "key", "the canonical test is inverted", "    if !is_canonical_x25519(key) {",
  "    if is_canonical_x25519(key) {")
m("K03", "key", "the low-order probe is inverted",
  "probe.agree(&PublicKeyBytes::from_bytes(*key)).is_none()",
  "probe.agree(&PublicKeyBytes::from_bytes(*key)).is_some()")
m("K04", "key", "the low-order probe is removed (the class loses its own error)",
  "    if probe.agree(&PublicKeyBytes::from_bytes(*key)).is_none() {",
  "    if false && probe.agree(&PublicKeyBytes::from_bytes(*key)).is_none() {")
m("K05", "key", "the prime-order test is removed (mixed torsion accepted)",
  "        Some(point) if point.is_torsion_free() => Ok(()),",
  "        Some(_) => Ok(()),")
m("K06", "key", "a key with no point on the curve is accepted",
  "        Some(point) if point.is_torsion_free() => Ok(()),\n        _ => Err(Error::NotPrimeOrder),",
  "        Some(point) if point.is_torsion_free() => Ok(()),\n        None => Ok(()),\n        _ => Err(Error::NotPrimeOrder),")
m("K07", "key", "the prime-order refusal is reported as non-contributory",
  "        _ => Err(Error::NotPrimeOrder),", "        _ => Err(Error::NonContributory),")
m("K08", "key", "a non-canonical key is reported as non-contributory",
  "    if !is_canonical_x25519(key) {\n        return Err(Error::NonCanonical);",
  "    if !is_canonical_x25519(key) {\n        return Err(Error::NonContributory);")
m("K09", "key", "the low-order probe is applied to the wrong argument (a fixed key)",
  "probe.agree(&PublicKeyBytes::from_bytes(*key))",
  "probe.agree(&PublicKeyBytes::from_bytes([9; 32]))")
eq("K10", "key", "the lift takes the other sign of x", "MontgomeryPoint(*key).to_edwards(0)",
   "MontgomeryPoint(*key).to_edwards(1)",
   "the two points with one y-coordinate are negatives, and a point and its negative have one order")
eq("K11", "key", "the probe scalar is [255; 32]", "PrivateKey::from_bytes([7; 32])",
   "PrivateKey::from_bytes([255; 32])",
   "any clamped scalar takes exactly the points of order dividing 8 to the identity")
eq("K12", "key", "the probe scalar is [0; 32]", "PrivateKey::from_bytes([7; 32])",
   "PrivateKey::from_bytes([0; 32])",
   "clamping sets bit 254, so the scalar is 2^254, a multiple of 8 in range, and detects the same class")

# ------------------------------------------------------------------ the issuer's pre-sign check
m("S01", "sign", "sign does not run the pre-sign check",
  "        self.check_for_signing()?;\n        self.sign_unchecked(issuer_secret, rng)",
  "        self.sign_unchecked(issuer_secret, rng)")
m("S02", "sign", "the pre-sign check skips the duplicate device check",
  "        self.encode_unsigned()?;\n        self.check_unique_devices()?;\n        self.check_identity_keys()\n",
  "        self.encode_unsigned()?;\n        self.check_identity_keys()\n")
m("S03", "sign", "the pre-sign check skips the key check",
  "        self.encode_unsigned()?;\n        self.check_unique_devices()?;\n        self.check_identity_keys()\n",
  "        self.encode_unsigned()?;\n        self.check_unique_devices()\n")
m("S04", "sign", "the pre-sign check skips the encoding rules",
  "        self.encode_unsigned()?;\n        self.check_unique_devices()?;\n        self.check_identity_keys()\n",
  "        self.check_unique_devices()?;\n        self.check_identity_keys()\n")
m("S05", "sign", "encode_signed signs without the pre-sign check",
  "        bytes.extend_from_slice(&self.sign(issuer_secret, rng)?);",
  "        bytes.extend_from_slice(&self.sign_unchecked(issuer_secret, rng)?);")

# ------------------------------------------------------------------ the encoding rules
m("C01", "codec", "an empty account handle is allowed",
  "        if account.is_empty() || account.len() > MAX_ACCOUNT_BYTES {",
  "        if account.len() > MAX_ACCOUNT_BYTES {")
m("C02", "codec", "the account bound refuses 256 bytes",
  "account.len() > MAX_ACCOUNT_BYTES {", "account.len() >= MAX_ACCOUNT_BYTES {")
m("C03", "codec", "the account bound allows 257 bytes",
  "account.len() > MAX_ACCOUNT_BYTES {", "account.len() > MAX_ACCOUNT_BYTES + 1 {")
m("C04", "codec", "the account bound counts characters, not bytes",
  "        if account.is_empty() || account.len() > MAX_ACCOUNT_BYTES {",
  "        if account.is_empty() || self.account_handle.chars().count() > MAX_ACCOUNT_BYTES {")
m("C05", "codec", "nine active bindings are allowed",
  "self.active.len() > MAX_ACTIVE_BINDINGS ||", "self.active.len() > MAX_ACTIVE_BINDINGS + 1 ||")
m("C06", "codec", "nine revoked entries are allowed",
  "|| self.revoked.len() > MAX_RECENT_REVOCATIONS {",
  "|| self.revoked.len() > MAX_RECENT_REVOCATIONS + 1 {")
m("C07", "codec", "eight active bindings are refused",
  "self.active.len() > MAX_ACTIVE_BINDINGS ||", "self.active.len() >= MAX_ACTIVE_BINDINGS ||")
m("C08", "codec", "a floor above the generation is allowed by one",
  "if self.revocation_floor_generation > self.inventory_generation {",
  "if self.revocation_floor_generation > self.inventory_generation.saturating_add(1) {")
m("C09", "codec", "a floor equal to the generation is refused",
  "if self.revocation_floor_generation > self.inventory_generation {",
  "if self.revocation_floor_generation >= self.inventory_generation {")
m("C10", "codec", "the floor rule is removed",
  "if self.revocation_floor_generation > self.inventory_generation {", "if false {")
m("C11", "codec", "a terminal generation at the floor is kept",
  "if revoked.terminal_generation <= self.revocation_floor_generation",
  "if revoked.terminal_generation < self.revocation_floor_generation")
m("C12", "codec", "a terminal generation at the statement's generation is refused",
  "|| revoked.terminal_generation > self.inventory_generation",
  "|| revoked.terminal_generation >= self.inventory_generation")
m("C13", "codec", "a terminal generation must break both bounds to be refused",
  "if revoked.terminal_generation <= self.revocation_floor_generation\n                || revoked.terminal_generation > self.inventory_generation",
  "if revoked.terminal_generation <= self.revocation_floor_generation\n                && revoked.terminal_generation > self.inventory_generation")
m("C14", "codec", "a repeated revoked entry is allowed",
  "if previous.is_some_and(|prior| prior >= revoked) {",
  "if previous.is_some_and(|prior| prior > revoked) {")
m("C15", "codec", "the revoked list must be descending",
  "if previous.is_some_and(|prior| prior >= revoked) {",
  "if previous.is_some_and(|prior| prior <= revoked) {")
m("C16", "codec", "a binding in both lists is allowed",
  "            if self.active.binary_search(&revoked.binding).is_ok() {",
  "            if false && self.active.binary_search(&revoked.binding).is_ok() {")
m("C17", "codec", "a repeated active binding is allowed",
  "if previous.is_some_and(|prior| prior >= binding) {",
  "if previous.is_some_and(|prior| prior > binding) {")
m("C18", "codec", "the active list must be descending",
  "if previous.is_some_and(|prior| prior >= binding) {",
  "if previous.is_some_and(|prior| prior <= binding) {")
m("C19", "codec", "a capability word of zero is allowed",
  "    if binding.capabilities & !GROUP_EPOCH_V1 != 0 || binding.capabilities == 0 {",
  "    if binding.capabilities & !GROUP_EPOCH_V1 != 0 {")
m("C20", "codec", "unknown capability bits are allowed",
  "    if binding.capabilities & !GROUP_EPOCH_V1 != 0 || binding.capabilities == 0 {",
  "    if binding.capabilities == 0 {")
m("C21", "codec", "the capability rule is not applied to active bindings",
  "    for binding in bindings {\n        binding_ok(binding)?;",
  "    for binding in bindings {")
m("C22", "codec", "the capability rule is not applied to revoked bindings",
  "            binding_ok(&revoked.binding)?;\n", "")
m("C23", "codec", "a predecessor tag other than 0 or 1 is read as no predecessor",
  "        _ => return Err(Error::Malformed),\n    };\n    Ok(DeviceBinding",
  "        _ => None,\n    };\n    Ok(DeviceBinding")
m("C24", "codec", "a predecessor tag of 2 is read as present",
  "        1 => Some(take(input, 32)?.try_into().map_err(|_| Error::Malformed)?),",
  "        1 | 2 => Some(take(input, 32)?.try_into().map_err(|_| Error::Malformed)?),")
m("C25", "codec", "trailing bytes are tolerated",
  "        if !input.is_empty() {\n            return Err(Error::Malformed);\n        }",
  "        if false {\n            return Err(Error::Malformed);\n        }")
eq("C26", "codec", "the decoder's re-encoding comparison is a comparison with itself",
   "        if statement.encode_unsigned()? != bytes {",
   "        if statement.encode_unsigned()? != statement.encode_unsigned()? {",
   "the parse is strict and injective, so a value that parses re-encodes to its input; the comparison "
   "is defence in depth and the encoder's own validation, kept in this edit, does the refusing")
m("C27", "codec", "the decoder skips the encoder's validation and the comparison",
  "        if statement.encode_unsigned()? != bytes {",
  "        if false && statement.encode_unsigned()? != bytes {")
eq("C28", "codec", "the decoder's count bound allows one more",
   "    if count > max {", "    if count > max + 1 {",
   "the encoder refuses the same statement, with the same error, once it is built; the bound only "
   "refuses a hostile count before the entries are parsed")
eq("C29", "codec", "the decoder's count bound is removed",
   "    if count > max {", "    if false {",
   "the encoder refuses the same statement, with the same error; each entry parsed consumes input, so "
   "the loop ends when the input does")
m("C30", "codec", "the signature is split off 63 bytes from the end",
  "checked_sub(64)", "checked_sub(63)")
m("C31", "codec", "a bad signature is reported as a non-canonical encoding",
  "    .map_err(|_| Error::BadSignature)", "    .map_err(|_| Error::NonCanonical)")
m("C32", "codec", "decode_signed does not check the signature",
  "        statement.verify(issuer_public, &signature)?;\n        Ok(statement)",
  "        let _ = (issuer_public, signature);\n        Ok(statement)")
m("C33", "codec", "the signing label is left off the signing input",
  "    input.extend_from_slice(INVENTORY_SIGNING_LABEL);\n", "")
m("C34", "codec", "an account that is not UTF-8 is repaired, not refused",
  "String::from_utf8(take_lp(&mut input)?.to_vec()).map_err(|_| Error::Malformed)?",
  "String::from_utf8_lossy(take_lp(&mut input)?).into_owned()")
m("C35", "codec", "the domain prefix is not compared",
  "    if value == expected {\n        Ok(())", "    if value == expected || true {\n        Ok(())")
m("C36", "codec", "a predecessor is written with the wrong tag",
  "        Some(previous) => {\n            out.push(1);", "        Some(previous) => {\n            out.push(0);")
m("C37", "codec", "the predecessor is not written",
  "            out.extend_from_slice(&previous);\n", "            let _ = previous;\n")
m("C38", "codec", "the capability word is written little-endian",
  "    out.extend_from_slice(&binding.capabilities.to_be_bytes());",
  "    out.extend_from_slice(&binding.capabilities.to_le_bytes());")
m("C39", "codec", "the commitment ignores the capability rule",
  "pub fn binding_commitment(binding: &DeviceBinding) -> Result<[u8; 32], Error> {\n    binding_ok(binding)?;\n",
  "pub fn binding_commitment(binding: &DeviceBinding) -> Result<[u8; 32], Error> {\n")
m("C40", "codec", "the commitment label is left off",
  "    digest.update(BINDING_COMMITMENT_LABEL);\n", "")
m("C41", "codec", "the commitment leaves out the predecessor",
  "    put_binding(&mut encoded, binding);\n    let mut digest",
  "    put_binding(&mut encoded, &DeviceBinding {\n        replacement_predecessor: None,\n        ..binding.clone()\n    });\n    let mut digest")
m("C42", "codec", "the account length prefix counts characters",
  "        out.extend_from_slice(&(account.len() as u32).to_be_bytes());",
  "        out.extend_from_slice(&(self.account_handle.chars().count() as u32).to_be_bytes());")


# ----------------------------------------------------------------------- driver
def split_source(text):
    at = text.index(TEST_MARK)
    return text[:at], text[at:]


def apply(prod, mutant):
    mid, _area, _desc, old, new, _reason = mutant
    count = prod.count(old)
    if count != 1:
        raise ValueError("%s: the text to replace occurs %d times, not once" % (mid, count))
    return prod.replace(old, new)


def copy_tree(dst):
    """A scratch copy of the crate and the vectors it reads; never the tree itself."""
    skip = shutil.ignore_patterns("target", "fuzz", ".git", "__pycache__")
    shutil.copytree(os.path.join(ROOT, "tacenta-core"), os.path.join(dst, "tacenta-core"), ignore=skip)
    vectors = os.path.join("tacenta-test-vectors", "vectors")
    shutil.copytree(os.path.join(ROOT, vectors), os.path.join(dst, vectors))


def run_tests(crate, target_dir, args, timeout):
    env = dict(os.environ, CARGO_TARGET_DIR=target_dir)
    started = time.time()
    try:
        done = subprocess.run(args, cwd=crate, env=env, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", [], time.time() - started
    out = done.stdout + done.stderr
    if "could not compile" in out or re.search(r"^error\[E\d+\]", out, re.M):
        return "compile-error", [out[-1500:]], time.time() - started
    failed = re.findall(r"^test (\S+) \.\.\. FAILED", out, re.M)
    if done.returncode == 0:
        return "passed", [], time.time() - started
    return "failed", failed or ["(the test run failed)"], time.time() - started


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--list", action="store_true", help="print the mutants and stop")
    ap.add_argument("--applies", action="store_true", help="check every edit applies once, without building")
    ap.add_argument("--only", nargs="+", metavar="ID", help="run only these mutants")
    ap.add_argument("--target-dir", help="cargo target directory (default: $CARGO_TARGET_DIR, else a temporary one)")
    ap.add_argument("--timeout", type=int, default=900, help="seconds allowed for one mutant's test run")
    ap.add_argument("--json", metavar="FILE", help="write the results here")
    ap.add_argument("--test-args", nargs=argparse.REMAINDER,
                    help="cargo arguments replacing the default test command, for example to see "
                         "which mutants a smaller set of tests would miss")
    ns = ap.parse_args()

    ids = [mutant[0] for mutant in MUTANTS]
    if len(set(ids)) != len(ids):
        sys.exit("mutate-inventory: duplicate mutant ids")
    chosen = [x for x in MUTANTS if not ns.only or x[0] in ns.only]
    unknown = set(ns.only or []) - set(ids)
    if unknown:
        sys.exit("mutate-inventory: no such mutant: " + ", ".join(sorted(unknown)))
    if ns.list:
        for mid, area, description, _old, _new, reason in chosen:
            print("%-4s %-7s %s%s" % (mid, area, description, "  [equivalent]" if reason else ""))
        print("%d mutants (%d claimed equivalent)" % (len(chosen), sum(1 for x in chosen if x[5])))
        return 0

    with open(os.path.join(ROOT, SOURCE)) as f:
        prod, tests = split_source(f.read())
    if prod.count(CHAIN) != 1:
        sys.exit("mutate-inventory: the block list for `accept` no longer matches the source")
    misses = []
    for mutant in chosen:
        try:
            apply(prod, mutant)
        except ValueError as e:
            misses.append(str(e))
    if misses:
        print("\n".join("does not apply: " + x for x in misses), file=sys.stderr)
        return 1
    if ns.applies:
        print("mutate-inventory: all %d edits apply exactly once" % len(chosen))
        return 0

    args = ["cargo"] + ns.test_args if ns.test_args else TEST_COMMAND
    target = ns.target_dir or os.environ.get("CARGO_TARGET_DIR")
    scratch = tempfile.mkdtemp(prefix="mutate-inventory-")
    try:
        target = target or os.path.join(scratch, "target")
        copy_tree(scratch)
        crate = os.path.join(scratch, "tacenta-core")
        path = os.path.join(scratch, SOURCE)

        with open(path, "w") as f:
            f.write(prod + tests)
        status, detail, took = run_tests(crate, target, args, ns.timeout)
        print("unmutated: %s (%.0fs)" % (status, took), flush=True)
        if status != "passed":
            print("mutate-inventory: the unmutated tree does not pass its tests\n" + "\n".join(detail), file=sys.stderr)
            return 1

        results, problems = [], 0
        for mutant in chosen:
            mid, area, description, _old, _new, reason = mutant
            with open(path, "w") as f:
                f.write(apply(prod, mutant) + tests)
            status, detail, took = run_tests(crate, target, args, ns.timeout)
            if status == "compile-error":
                verdict = "INVALID (does not compile)"
                problems += 1
            elif status == "passed":
                verdict = "survived (equivalent)" if reason else "SURVIVED"
                problems += 0 if reason else 1
            else:
                verdict = "KILLED" if not reason else "KILLED (claimed equivalent)"
                problems += 1 if reason else 0
            killers = [d.split("::")[-1] for d in detail][:3] if status in ("failed", "timeout") else []
            print("%-4s %-28s [%s] %s%s (%.0fs)" % (
                mid, verdict, area, description, "  by " + ", ".join(killers) if killers else "", took), flush=True)
            results.append({"id": mid, "area": area, "description": description, "status": status,
                            "equivalent": reason, "killed_by": detail if status == "failed" else []})
        with open(path, "w") as f:
            f.write(prod + tests)

        killed = sum(1 for r in results if r["status"] in ("failed", "timeout"))
        equiv = sum(1 for r in results if r["status"] == "passed" and r["equivalent"])
        survived = sum(1 for r in results if r["status"] == "passed" and not r["equivalent"])
        print("\n%d mutants: %d killed, %d survived as claimed equivalent, %d unexpected"
              % (len(results), killed, equiv, problems))
        if survived:
            print("survivors: " + ", ".join(r["id"] for r in results if r["status"] == "passed" and not r["equivalent"]))
        if ns.json:
            with open(ns.json, "w") as f:
                json.dump(results, f, indent=1)
        return 0 if problems == 0 else 1
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
