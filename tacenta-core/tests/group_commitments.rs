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
