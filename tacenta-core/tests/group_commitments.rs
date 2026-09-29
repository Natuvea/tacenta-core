use serde_json::Value;
use tacenta_core::groups::inventory::{
    DeviceBinding, Error, InventoryStatement, Revocation, binding_commitment,
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
