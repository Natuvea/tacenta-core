//! Property tests for tacenta-core's bounded protobuf profile (`tacenta-protobuf`)
//! against `tacenta-spec/protocol/protobuf-profile.md`: the varint reader and
//! encoder, the outer length bound, and the two message types' readers
//! (`parse_ratchet_body`, `parse_prekey_body`) and encoders (`encode_ratchet_body`,
//! `encode_prekey_body`).
//!
//! They live in this runner because it is the one test target outside the
//! translated crate that already links `tacenta-protobuf`. The vectors in
//! `tests/protobuf.rs` pin chosen regions the model generated; these generate the
//! regions. The oracle is a reference encoder written here from the page (base-128
//! little-endian varints, a tag of `field * 8 + wire`, a length-delimited value as its
//! varint length and its bytes), so it shares no code with the crate.
//!
//! Generator: a splitmix64 stream (`Gen`) seeded from `SEED`. Replay: the seed is fixed
//! in this file, so every run is the same run, and each assertion message names the
//! case. Case count: `CASES` (2,000) per property.

use tacenta_protobuf::{
    MAX_MESSAGE_LEN, PrekeyBody, RatchetBody, Reader, encode_prekey_body, encode_ratchet_body,
    encode_varint, parse_prekey_body, parse_ratchet_body,
};

const SEED: u64 = 0x9b0f_0b0f;
const CASES: usize = 2000;

/// splitmix64.
struct Gen(u64);

impl Gen {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    /// A 32-bit value, often at a varint width boundary.
    fn u32(&mut self) -> u32 {
        match self.below(4) {
            0 => self.next() as u32,
            1 => [
                0,
                1,
                127,
                128,
                16383,
                16384,
                2097151,
                2097152,
                268435455,
                268435456,
                u32::MAX,
            ][self.below(11) as usize],
            _ => (self.next() as u32) >> self.below(32),
        }
    }
    fn bytes(&mut self, max: u64) -> Vec<u8> {
        let n = if self.below(5) == 0 {
            0
        } else {
            self.below(max + 1)
        };
        (0..n).map(|_| self.next() as u8).collect()
    }
}

/// The page's varint: base-128, little-endian, least significant group first, the
/// top bit saying whether another byte follows; the minimal spelling.
fn varint(mut v: u32) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let low = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(low);
            return out;
        }
        out.push(low | 0x80);
    }
}

fn v_field(field: u32, value: u32) -> Vec<u8> {
    let mut out = varint(field * 8);
    out.extend(varint(value));
    out
}

fn ld_field(field: u32, value: &[u8]) -> Vec<u8> {
    let mut out = varint(field * 8 + 2);
    out.extend(varint(value.len() as u32));
    out.extend_from_slice(value);
    out
}

/// The same field number carried with the other wire type: a varint field re-tagged
/// length-delimited (its varint as the bytes), a length-delimited field re-tagged varint.
fn other_wire_type(g: &mut Gen, field: &[u8]) -> Vec<u8> {
    let tag = field[0];
    let number = (tag >> 3) as u32;
    if tag & 7 == 0 {
        ld_field(number, &field[1..])
    } else {
        v_field(number, g.u32())
    }
}

fn shuffle(g: &mut Gen, fields: &mut [Vec<u8>]) {
    for i in (1..fields.len()).rev() {
        let j = g.below(i as u64 + 1) as usize;
        fields.swap(i, j);
    }
}

/// A varint the page refuses, made from a value: a non-minimal spelling (a final
/// `0x00` after a continuation), a sixth byte, a value past 32 bits, or input that
/// ends before a final byte.
fn bad_varint(g: &mut Gen, v: u32) -> Vec<u8> {
    let mut b = varint(v);
    match g.below(4) {
        0 => {
            let last = b.len() - 1;
            b[last] |= 0x80;
            if b.len() < 5 {
                b.push(0x00);
            } else {
                b.push(0x01);
            }
        }
        1 => b = vec![0x80, 0x80, 0x80, 0x80, 0x80, 0x01],
        2 => b = vec![0xff, 0xff, 0xff, 0xff, 0x10 + g.below(0x70) as u8],
        _ => {
            b = varint(v.max(128));
            b.pop();
        }
    }
    b
}

/// Every 32-bit value's minimal spelling reads back as that value and is exactly what
/// the encoder emits, consuming exactly its own bytes and leaving what follows; and
/// a non-minimal spelling, a sixth byte, a value past 32 bits, and input that ends
/// before a final byte are refused.
///
/// Specification: protobuf-profile.md, Varints: "A varint is base-128 and
/// little-endian: each byte carries seven bits of the value, least significant group
/// first, and its top bit says whether another byte follows"; the refusals "It is
/// longer than five bytes", "It is not minimal. A final byte of `0x00` in any position
/// but the first is refused", "Its value does not fit 32 bits" and "The input ends
/// first"; and "Bytes after the final byte are not part of the varint".
#[test]
fn varints_are_the_pages_and_only_the_minimal_spelling_reads() {
    let mut g = Gen(SEED);
    for case in 0..CASES {
        let v = g.u32();
        let enc = varint(v);
        assert_eq!(
            encode_varint(Vec::new(), v),
            Ok(enc.clone()),
            "case {case}: encoder for {v}"
        );
        let mut with_tail = enc.clone();
        with_tail.extend(g.bytes(4));
        let mut r = Reader::new(with_tail).unwrap();
        assert_eq!(r.varint(), Ok(v), "case {case}: read {v}");
        assert_eq!(r.at, enc.len(), "case {case}: consumed only the varint");
        let bad = bad_varint(&mut g, v);
        assert!(
            Reader::new(bad.clone()).unwrap().varint().is_err(),
            "case {case}: {bad:02x?} read"
        );
    }
}

/// A region one byte over the bound is refused before any byte is read, and a region
/// of exactly the bound is not refused for its length.
///
/// Specification: protobuf-profile.md, Bounds: "A region longer than `maxMessageLen`
/// bytes is refused before any byte of it is read. A region of exactly
/// `maxMessageLen` bytes is within the bound."
#[test]
fn the_outer_bound_is_the_pages() {
    assert_eq!(MAX_MESSAGE_LEN, 16384);
    assert!(Reader::new(vec![0u8; 16384]).is_ok());
    assert!(Reader::new(vec![0u8; 16385]).is_err());
}

fn ratchet_fields(b: &RatchetBody) -> Vec<Vec<u8>> {
    vec![
        ld_field(1, &b.ratchet_key),
        v_field(2, b.counter),
        v_field(3, b.previous_counter),
        ld_field(4, &b.ciphertext),
        ld_field(5, &b.pq),
    ]
}

fn assert_ratchet_eq(a: &RatchetBody, b: &RatchetBody, case: usize) {
    assert_eq!(a.ratchet_key, b.ratchet_key, "case {case}: ratchetKey");
    assert_eq!(a.counter, b.counter, "case {case}: counter");
    assert_eq!(
        a.previous_counter, b.previous_counter,
        "case {case}: previousCounter"
    );
    assert_eq!(a.ciphertext, b.ciphertext, "case {case}: ciphertext");
    assert_eq!(a.pq, b.pq, "case {case}: pq");
}

/// A ratchet message body's five fields, in any of their orders, with any values
/// (empty byte fields and zero counters included), parse to those values; the
/// encoder emits them in ascending field-number order; and a body with a field
/// missing, a field repeated, a field number from 6 to 15, a defined number with the
/// other wire type, or a byte left over, is refused.
///
/// Specification: protobuf-profile.md, Ratchet message body (the table of fields 1 to
/// 5 and their wire types; "**Every field is required.** A body missing any of the
/// five is refused", "A field number of 6 to 15 passes the tag check and is then
/// refused at step 3. A repeated field number is refused at step 2. The body is refused
/// if any byte of the region is left over"); Field order and canonicality ("**Field
/// order is free.**", "The implementation's encoders emit fields in ascending
/// field-number order"; "Nothing inside a field is validated"); Fields in a message,
/// step 3 ("a defined number carrying the other wire type" is refused), for every
/// defined field.
#[test]
fn ratchet_bodies_parse_in_any_order_and_refuse_what_the_page_refuses() {
    let mut g = Gen(SEED ^ 1);
    for case in 0..CASES {
        let body = RatchetBody {
            ratchet_key: g.bytes(40),
            counter: g.u32(),
            previous_counter: g.u32(),
            ciphertext: g.bytes(600),
            pq: g.bytes(80),
        };
        let mut fields = ratchet_fields(&body);
        assert_eq!(
            encode_ratchet_body(&body),
            Ok(fields.concat()),
            "case {case}: encoder"
        );
        shuffle(&mut g, &mut fields);
        let parsed = parse_ratchet_body(fields.concat())
            .unwrap_or_else(|e| panic!("case {case}: refused {e:?}"));
        assert_ratchet_eq(&parsed, &body, case);

        let mut bad = fields.clone();
        match g.below(5) {
            0 => {
                bad.remove(g.below(5) as usize);
            }
            1 => {
                let i = g.below(5) as usize;
                let again = bad[i].clone();
                bad.insert(g.below(6) as usize, again);
            }
            2 => {
                let n = 6 + g.below(10) as u32;
                let extra = if g.below(2) == 0 {
                    v_field(n, g.u32())
                } else {
                    ld_field(n, &g.bytes(8))
                };
                bad.insert(g.below(6) as usize, extra);
            }
            3 => {
                // A defined field carried with the other wire type, in place of the real one.
                let i = g.below(5) as usize;
                bad[i] = other_wire_type(&mut g, &bad[i]);
            }
            _ => bad.push(vec![g.next() as u8]),
        }
        assert!(
            parse_ratchet_body(bad.concat()).is_err(),
            "case {case}: accepted a refused body"
        );
    }
}

/// A prekey envelope's fields, in any order, with field 1 present (zero included) or
/// absent, parse to those values, an absent field 1 differing from a present zero;
/// the encoder emits ascending order and omits an absent field 1; and an envelope
/// with a required field missing, a field repeated (field 1 included), a field number
/// from 9 to 15, a defined field carried with the other wire type, or a byte left over
/// is refused.
///
/// Specification: protobuf-profile.md, Prekey envelope ("**Field 1, `prekeyId`, is
/// optional ...** When absent, the parsed envelope has no identifier. That is not the
/// same as an identifier of zero", "Fields 2 to 8 are required", "A field number of 9
/// to 15 passes the tag check and is then refused at step 3. A repeated field number,
/// including a repeated field 1, is refused at step 2", "it is refused if any byte is
/// left over"); Field order and canonicality ("emit fields in ascending field-number
/// order and omit an absent `prekeyId` entirely"); Fields in a message, step 3 ("a
/// defined number carrying the other wire type" is refused), for every defined field.
#[test]
fn prekey_envelopes_parse_in_any_order_and_refuse_what_the_page_refuses() {
    let mut g = Gen(SEED ^ 2);
    for case in 0..CASES {
        let prekey_id = match g.below(3) {
            0 => None,
            1 => Some(0),
            _ => Some(g.u32()),
        };
        let body = PrekeyBody {
            prekey_id,
            base_key: g.bytes(40),
            identity_key: g.bytes(40),
            message: g.bytes(400),
            registration_id: g.u32(),
            signed_prekey_id: g.u32(),
            pq_prekey_id: g.u32(),
            kem: g.bytes(200),
        };
        let mut fields = Vec::new();
        if let Some(id) = prekey_id {
            fields.push(v_field(1, id));
        }
        fields.extend([
            ld_field(2, &body.base_key),
            ld_field(3, &body.identity_key),
            ld_field(4, &body.message),
            v_field(5, body.registration_id),
            v_field(6, body.signed_prekey_id),
            v_field(7, body.pq_prekey_id),
            ld_field(8, &body.kem),
        ]);
        assert_eq!(
            encode_prekey_body(&body),
            Ok(fields.concat()),
            "case {case}: encoder"
        );
        shuffle(&mut g, &mut fields);
        let p = parse_prekey_body(fields.concat())
            .unwrap_or_else(|e| panic!("case {case}: refused {e:?}"));
        assert_eq!(p.prekey_id, body.prekey_id, "case {case}: prekeyId");
        assert_eq!(
            (&p.base_key, &p.identity_key, &p.message, &p.kem),
            (&body.base_key, &body.identity_key, &body.message, &body.kem),
            "case {case}: byte fields"
        );
        assert_eq!(
            (p.registration_id, p.signed_prekey_id, p.pq_prekey_id),
            (
                body.registration_id,
                body.signed_prekey_id,
                body.pq_prekey_id
            ),
            "case {case}: identifiers"
        );

        let mut bad = fields.clone();
        let len = bad.len() as u64;
        match g.below(5) {
            4 => {
                // A defined field carried with the other wire type, in place of the real one.
                let i = g.below(len) as usize;
                bad[i] = other_wire_type(&mut g, &bad[i]);
            }
            0 => {
                // A required field (2 to 8) removed.
                let required: Vec<usize> = (0..bad.len()).filter(|i| bad[*i][0] != 0x08).collect();
                bad.remove(required[g.below(required.len() as u64) as usize]);
            }
            1 => {
                let i = g.below(len) as usize;
                let again = bad[i].clone();
                bad.insert(g.below(len + 1) as usize, again);
            }
            2 => {
                let n = 9 + g.below(7) as u32;
                let extra = if g.below(2) == 0 {
                    v_field(n, g.u32())
                } else {
                    ld_field(n, &g.bytes(8))
                };
                bad.insert(g.below(len + 1) as usize, extra);
            }
            _ => bad.push(vec![g.next() as u8]),
        }
        assert!(
            parse_prekey_body(bad.concat()).is_err(),
            "case {case}: accepted a refused envelope"
        );
    }
}
