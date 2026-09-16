use tacenta_core::groups::inventory::{DeviceBinding, GROUP_EPOCH_V1, InventoryStatement};
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

#[test]
fn inventory_statement_vectors_pin_canonical_preimages() {
    let text = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../tacenta-test-vectors/vectors/groups/inventory-statements-v1.json"
    ));
    let document: serde_json::Value = serde_json::from_str(text).expect("vectors are valid JSON");
    assert_eq!(document["schema"], "tacenta-inventory-statements-v1");
    for case in document["cases"].as_array().expect("cases are an array") {
        let identity: [u8; 32] = hex::decode(case["active"][0]["identity_hex"].as_str().unwrap())
            .unwrap()
            .try_into()
            .unwrap();
        let statement = InventoryStatement {
            issuer_key_id: case["issuer_key_id"].as_u64().unwrap(),
            account_handle: case["account_handle"].as_str().unwrap().into(),
            inventory_generation: case["inventory_generation"].as_u64().unwrap(),
            active: vec![DeviceBinding {
                device_id: case["active"][0]["device_id"].as_u64().unwrap() as u32,
                identity_public_key: identity,
                capabilities: GROUP_EPOCH_V1,
                replacement_predecessor: None,
            }],
            revocation_floor_generation: 0,
            revoked: vec![],
        };
        let expected = hex::decode(case["unsigned_hex"].as_str().unwrap()).unwrap();
        assert_eq!(statement.encode_unsigned().unwrap(), expected);
        assert_eq!(
            InventoryStatement::decode_unsigned(&expected),
            Ok(statement)
        );
    }
}
