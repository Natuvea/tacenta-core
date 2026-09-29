use serde_json::Value;
use std::cell::RefCell;
use std::collections::BTreeSet;
use tacenta_core::groups::inventory::{
    BindingStatus, DeviceBinding, Error, InventoryPolicy, InventoryStatement, Revocation,
    binding_commitment,
};
use tacenta_core::groups::{payload_commitment, roster_commitment};

#[test]
fn group_commitment_vectors_pin_domain_separation() {
    let text = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../tacenta-test-vectors/vectors/groups/group-commitments-v1.json"
    ));
    let document: serde_json::Value = serde_json::from_str(text).expect("vectors are valid JSON");
    assert_eq!(
        document["schema"], "tacenta-group-commitments-v1",
        "the vector schema names its fixed commitment contract"
    );

    let cases = document["cases"].as_array().expect("cases are an array");
    assert_eq!(cases.len(), 2, "one vector pins each commitment domain");
    for case in cases {
        let input = hex::decode(case["input_hex"].as_str().expect("input is hex"))
            .expect("input hex decodes");
        let expected = hex::decode(case["output_hex"].as_str().expect("output is hex"))
            .expect("output hex decodes");
        let actual = match case["operation"].as_str() {
            Some("roster_commitment") => roster_commitment(&input),
            Some("payload_commitment") => payload_commitment(&input),
            other => panic!("unknown vector operation: {other:?}"),
        };
        assert_eq!(
            actual.as_slice(),
            expected.as_slice(),
            "case {:?}",
            case["id"]
        );
    }
}

#[test]
fn group_commitment_domains_do_not_cross() {
    let value = b"same canonical bytes";
    assert_ne!(roster_commitment(value), payload_commitment(value));
}

/// An object whose keys are exactly `required` plus any of `optional`. A vector
/// file that grows a field this runner does not read fails here, rather than
/// being silently ignored.
fn closed<'a>(value: &'a Value, required: &[&str], optional: &[&str], what: &str) -> &'a Value {
    let object = value
        .as_object()
        .unwrap_or_else(|| panic!("{what}: not an object"));
    for key in required {
        assert!(object.contains_key(*key), "{what}: missing `{key}`");
    }
    for key in object.keys() {
        assert!(
            required.contains(&key.as_str()) || optional.contains(&key.as_str()),
            "{what}: unread field `{key}`"
        );
    }
    value
}

fn bytes32(value: &Value, what: &str) -> [u8; 32] {
    hex::decode(
        value
            .as_str()
            .unwrap_or_else(|| panic!("{what}: not a string")),
    )
    .unwrap_or_else(|_| panic!("{what}: not hex"))
    .try_into()
    .unwrap_or_else(|_| panic!("{what}: not 32 bytes"))
}

fn binding_from(value: &Value, what: &str) -> DeviceBinding {
    closed(
        value,
        &["device_id", "identity_hex", "capabilities"],
        &["replacement_predecessor_hex"],
        what,
    );
    DeviceBinding {
        device_id: u32::try_from(value["device_id"].as_u64().expect("device_id is a u64"))
            .expect("device_id is a u32"),
        identity_public_key: bytes32(&value["identity_hex"], what),
        capabilities: value["capabilities"]
            .as_u64()
            .expect("capabilities is a u64"),
        replacement_predecessor: value
            .get("replacement_predecessor_hex")
            .map(|hex| bytes32(hex, what)),
    }
}

fn statement_from(case: &Value, what: &str) -> InventoryStatement {
    closed(
        case,
        &[
            "id",
            "issuer_key_id",
            "account_handle",
            "inventory_generation",
            "active",
            "revocation_floor_generation",
            "revoked",
            "unsigned_hex",
        ],
        &[],
        what,
    );
    InventoryStatement {
        issuer_key_id: case["issuer_key_id"]
            .as_u64()
            .expect("issuer_key_id is a u64"),
        account_handle: case["account_handle"]
            .as_str()
            .expect("account is a string")
            .into(),
        inventory_generation: case["inventory_generation"]
            .as_u64()
            .expect("inventory_generation is a u64"),
        active: case["active"]
            .as_array()
            .expect("active is an array")
            .iter()
            .enumerate()
            .map(|(i, binding)| binding_from(binding, &format!("{what}.active[{i}]")))
            .collect(),
        revocation_floor_generation: case["revocation_floor_generation"]
            .as_u64()
            .expect("revocation_floor_generation is a u64"),
        revoked: case["revoked"]
            .as_array()
            .expect("revoked is an array")
            .iter()
            .enumerate()
            .map(|(i, entry)| {
                let what = format!("{what}.revoked[{i}]");
                closed(entry, &["binding", "terminal_generation"], &[], &what);
                Revocation {
                    binding: binding_from(&entry["binding"], &what),
                    terminal_generation: entry["terminal_generation"]
                        .as_u64()
                        .expect("terminal_generation is a u64"),
                }
            })
            .collect(),
    }
}

fn cases_of(text: &str, schema: &str) -> Vec<Value> {
    let document: Value = serde_json::from_str(text).expect("vectors are valid JSON");
    closed(&document, &["schema", "comment", "cases"], &[], schema);
    assert_eq!(document["schema"], schema);
    let cases = document["cases"]
        .as_array()
        .expect("cases are an array")
        .clone();
    let mut ids: Vec<_> = cases
        .iter()
        .map(|case| case["id"].as_str().expect("id"))
        .collect();
    let total = ids.len();
    ids.sort_unstable();
    ids.dedup();
    assert_eq!(ids.len(), total, "{schema}: case ids are unique");
    cases
}

macro_rules! inventory_cases {
    ($file:literal, $schema:literal) => {
        cases_of(
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../tacenta-test-vectors/vectors/groups/",
                $file
            )),
            $schema,
        )
    };
}

/// Each case's fields encode to its bytes and its bytes decode to its fields,
/// so a field the encoder ignored, or a decoder that dropped one, fails here.
#[test]
fn inventory_statement_vectors_pin_canonical_preimages() {
    let cases = inventory_cases!(
        "inventory-statements-v1.json",
        "tacenta-inventory-statements-v1"
    );
    assert_eq!(cases.len(), 27, "every statement case is present");
    assert!(cases.iter().any(|case| case["id"] == "one-active-binding"));
    for case in &cases {
        let what = format!("case {}", case["id"]);
        let statement = statement_from(case, &what);
        let expected = hex::decode(case["unsigned_hex"].as_str().unwrap()).unwrap();
        assert_eq!(
            statement.encode_unsigned().unwrap(),
            expected,
            "{what}: encode"
        );
        assert_eq!(
            InventoryStatement::decode_unsigned(&expected),
            Ok(statement),
            "{what}: decode"
        );
    }
}

/// Every case has one defect against a valid encoding, so a decoder that skips
/// the rule the case breaks accepts it.
#[test]
fn inventory_decode_refusal_vectors_are_refused() {
    let cases = inventory_cases!(
        "inventory-decode-refusals-v1.json",
        "tacenta-inventory-decode-refusals-v1"
    );
    assert_eq!(cases.len(), 54, "every refusal case is present");
    for case in &cases {
        let what = format!("case {}", case["id"]);
        closed(case, &["id", "rule", "unsigned_hex"], &[], &what);
        assert!(
            !case["rule"].as_str().expect("rule is a string").is_empty(),
            "{what}"
        );
        let bytes = hex::decode(case["unsigned_hex"].as_str().unwrap()).unwrap();
        assert!(
            InventoryStatement::decode_unsigned(&bytes).is_err(),
            "{what}: the decoder accepted a statement that breaks `{}`",
            case["rule"]
        );
    }
}

#[test]
fn inventory_binding_commitment_vectors() {
    let cases = inventory_cases!(
        "inventory-binding-commitments-v1.json",
        "tacenta-inventory-binding-commitments-v1"
    );
    assert_eq!(cases.len(), 10, "every commitment case is present");
    let mut refused = 0;
    for case in &cases {
        let what = format!("case {}", case["id"]);
        closed(case, &["id", "binding", "commitment_hex"], &[], &what);
        let binding = binding_from(&case["binding"], &what);
        match case["commitment_hex"].as_str() {
            Some(hex) => assert_eq!(
                binding_commitment(&binding).unwrap().as_slice(),
                hex::decode(hex).unwrap().as_slice(),
                "{what}"
            ),
            None => {
                refused += 1;
                assert_eq!(
                    binding_commitment(&binding),
                    Err(Error::Unsupported),
                    "{what}"
                );
            }
        }
    }
    assert!(refused >= 4, "the commitment refusals are present");
}

/// The scripted policy of the acceptance vectors (README, Vector layouts),
/// recording every call it receives in the vectors' notation.
struct ScriptedPolicy {
    issuers: Vec<(u64, Option<Vec<u8>>, [u8; 32])>,
    fresh: Vec<(Vec<u8>, u64)>,
    refuse_binding: Option<([u8; 32], BindingStatus)>,
    refuse_every_binding: bool,
    refuse_statement: bool,
    calls: RefCell<Vec<String>>,
}

impl ScriptedPolicy {
    fn from_case(policy: &Value, what: &str) -> Self {
        closed(
            policy,
            &[
                "issuers",
                "fresh",
                "refuse_binding",
                "refuse_every_binding",
                "refuse_statement",
            ],
            &[],
            what,
        );
        let issuers = policy["issuers"]
            .as_array()
            .expect("issuers is an array")
            .iter()
            .map(|issuer| {
                closed(
                    issuer,
                    &["issuer_key_id", "account_hex", "verification_key_hex"],
                    &[],
                    what,
                );
                (
                    issuer["issuer_key_id"]
                        .as_u64()
                        .expect("issuer id is a u64"),
                    issuer["account_hex"]
                        .as_str()
                        .map(|account| hex::decode(account).expect("account is hex")),
                    bytes32(&issuer["verification_key_hex"], what),
                )
            })
            .collect();
        let fresh = policy["fresh"]
            .as_array()
            .expect("fresh is an array")
            .iter()
            .map(|entry| {
                closed(entry, &["account_hex", "generation"], &[], what);
                (
                    hex::decode(entry["account_hex"].as_str().expect("account is a string"))
                        .expect("account is hex"),
                    entry["generation"].as_u64().expect("generation is a u64"),
                )
            })
            .collect();
        let refuse_binding = match &policy["refuse_binding"] {
            Value::Null => None,
            refused => {
                closed(refused, &["identity_hex", "status"], &[], what);
                let status = match refused["status"].as_str() {
                    Some("active") => BindingStatus::Active,
                    Some("revoked") => BindingStatus::Revoked,
                    other => panic!("{what}: unknown status {other:?}"),
                };
                Some((bytes32(&refused["identity_hex"], what), status))
            }
        };
        ScriptedPolicy {
            issuers,
            fresh,
            refuse_binding,
            refuse_every_binding: policy["refuse_every_binding"].as_bool().expect("a boolean"),
            refuse_statement: policy["refuse_statement"].as_bool().expect("a boolean"),
            calls: RefCell::new(Vec::new()),
        }
    }
}

impl InventoryPolicy for ScriptedPolicy {
    fn issuer_public_key(&self, issuer_key_id: u64, account_handle: &str) -> Option<[u8; 32]> {
        self.calls.borrow_mut().push(format!(
            "issuer:{issuer_key_id}:{}",
            hex::encode(account_handle)
        ));
        self.issuers
            .iter()
            .find(|(id, account, _)| {
                *id == issuer_key_id
                    && account
                        .as_ref()
                        .is_none_or(|account| account == account_handle.as_bytes())
            })
            .map(|(_, _, key)| *key)
    }

    fn generation_is_current(&self, account_handle: &str, generation: u64) -> bool {
        self.calls.borrow_mut().push(format!(
            "freshness:{}:{generation}",
            hex::encode(account_handle)
        ));
        self.fresh.iter().any(|(account, current)| {
            account == account_handle.as_bytes() && *current == generation
        })
    }

    fn binding_is_allowed(
        &self,
        _account_handle: &str,
        binding: &DeviceBinding,
        status: BindingStatus,
    ) -> bool {
        self.calls.borrow_mut().push(format!(
            "binding:{}:{}:{}:{}:{}",
            if status == BindingStatus::Active {
                "A"
            } else {
                "R"
            },
            binding.device_id,
            hex::encode(binding.identity_public_key),
            binding.capabilities,
            binding
                .replacement_predecessor
                .map_or("-".into(), hex::encode)
        ));
        !(self.refuse_every_binding
            || self.refuse_binding == Some((binding.identity_public_key, status)))
    }

    fn statement_is_allowed(&self, _statement: &InventoryStatement) -> bool {
        self.calls.borrow_mut().push("statement".into());
        !self.refuse_statement
    }
}

/// The check that refused, in the vectors' vocabulary. Implementations report
/// refusals in their own words (error-handling.md); this maps `tacenta-core`'s.
/// A variant that reports both a decode failure and a non-canonical identity
/// key is told apart by whether any hook had run.
fn refusal_class(error: Error, calls: &[String]) -> &'static str {
    match error {
        Error::Malformed | Error::Unsupported => {
            assert!(calls.is_empty(), "a decode failure precedes every hook");
            "decode"
        }
        Error::NonCanonical if calls.is_empty() => "decode",
        Error::NonCanonical | Error::NonContributory | Error::NotPrimeOrder => "identity-key",
        Error::WrongAccount => "account",
        Error::IssuerUnbound => "issuer",
        Error::BadSignature => "signature",
        Error::Stale => "freshness",
        Error::DuplicateDevice => "duplicate-device",
        Error::Refused => {
            if calls.last().is_some_and(|call| call == "statement") {
                "statement-policy"
            } else {
                "binding-policy"
            }
        }
        other => panic!("an error the vectors do not map: {other:?}"),
    }
}

/// Each signed statement is run through `accept_signed` against its scripted
/// policy. The refusal, and every call the policy received in order, must
/// equal the vector's, so the order of the checks and of the hooks is pinned.
#[test]
fn inventory_acceptance_vectors() {
    let cases = inventory_cases!(
        "inventory-acceptance-v1.json",
        "tacenta-inventory-acceptance-v1"
    );
    assert_eq!(cases.len(), 148, "every acceptance case is present");
    let mut refused_by = BTreeSet::new();
    let mut accepted = 0;
    for case in &cases {
        let what = format!("case {}", case["id"]);
        closed(
            case,
            &[
                "id",
                "signed_hex",
                "expected_account_hex",
                "policy",
                "refusal",
                "hook_calls",
            ],
            &[],
            &what,
        );
        let signed = hex::decode(case["signed_hex"].as_str().unwrap()).unwrap();
        let account =
            String::from_utf8(hex::decode(case["expected_account_hex"].as_str().unwrap()).unwrap())
                .expect("the account asked about is UTF-8");
        let policy = ScriptedPolicy::from_case(&case["policy"], &what);
        let result = InventoryStatement::accept_signed(&signed, &account, &policy);
        let calls = policy.calls.take();
        match (&case["refusal"], result) {
            (Value::Null, Ok(inventory)) => {
                accepted += 1;
                assert_eq!(
                    inventory.statement().encode_unsigned().unwrap(),
                    signed[..signed.len() - 64],
                    "{what}: the accepted statement is the one that was signed"
                );
            }
            (Value::String(expected), Err(error)) => {
                assert_eq!(refusal_class(error, &calls), expected, "{what}: {error:?}");
                refused_by.insert(expected.clone());
            }
            (expected, result) => panic!("{what}: expected {expected}, got {result:?}"),
        }
        let expected_calls: Vec<String> = case["hook_calls"]
            .as_array()
            .expect("hook_calls is an array")
            .iter()
            .map(|call| call.as_str().expect("a call is a string").to_owned())
            .collect();
        assert_eq!(calls, expected_calls, "{what}: the policy's calls");
    }
    assert!(accepted >= 15, "accepted cases are present");
    assert_eq!(
        refused_by.into_iter().collect::<Vec<_>>(),
        [
            "account",
            "binding-policy",
            "decode",
            "duplicate-device",
            "freshness",
            "identity-key",
            "issuer",
            "signature",
            "statement-policy",
        ],
        "every check refuses at least one case"
    );
}
