"""PROJECT-CONTROLLED DRY RUN. NOT INDEPENDENT EVIDENCE. It does not close or reclassify the open item.

The real-primitive session vectors (`session-establishment/session-e2e.json`),
derived from the specification's rules and this reader's own primitives.

Each vector names its inputs (the secrets, the random draws and the plaintexts)
and the bytes every step of a handshake produces from them. This module
computes those steps from the inputs, in the order session-establishment.md,
triple-ratchet.md, ratchet.md, sparse-pq-ratchet.md, mlkem-braid.md and
session-persistence.md give them, and compares each result with the vector. A
vector that echoes a value it should have derived does not pass.

Dry run: the ML-KEM-1024 and Braid key-generation steps below were added by the
project's own agent standing in for a person, in a directory built for that
purpose (RECORD.md). They compute: the responder's KEM key pairs from
`bob_last_resort_kem_d_z` and `bob_one_time_kem_d_z` (K1); the encapsulation of
`alice_kem_encapsulation_m` to the bundle's key (K2); the decapsulation by the
responder (K3); `SK` and everything after it from the computed secret (K4); the
Braid's header from the `d` half of `alice_braid_keygen_d_z` and the 96-byte value
under the authenticator (B1, B2).

What it does not derive is listed here and in `reader/README.md` and
`../GAPS-11.md`, and `test_session_e2e_sweep.py` holds the list to what the code
does (it corrupts every input and field and requires the reader to notice
exactly the ones this module claims to check):

- The Braid's stored `key_pair` inside `alice_session_after_first_send`: 11,872
  bytes whose layout the specification delegates to the KEM library
  (session-persistence.md, Braid). The header and `ek_vector` it holds are
  computed (B1), but nothing locates them in the field.
- The `z` half of `alice_braid_keygen_d_z`: it is stored only inside that
  `key_pair`, so no output shows it.
- The `z` half of `bob_one_time_kem_d_z`: it matters only to implicit
  rejection, and the one-time key's decapsulation key is not stored after the
  message is received. The `z` half of `bob_last_resort_kem_d_z` is read: it is
  the last 32 bytes of the stored key pair.
- `bob_repeat_random`: consumed by the implementation and never observable in
  an output.

This module was written in the repository with the implementation's runner in
view. It follows the pages it cites, but it is not a clean-room pass and makes
no claim to be one (`reader/README.md`, Provenance).
"""

import functools
from dataclasses import replace

from tacenta_reader import aead, braid, curve25519, persistence, pqxdh, ratchet, spqr, triple, wire
from tacenta_reader import constants as K
from tacenta_reader import erasure, mlkem

bx = bytes.fromhex


class Mismatch(Exception):
    """The vector says something this derivation does not."""


# The names each vector must carry, exactly. A field or input the vector adds
# that nothing here reads fails, and so does one it drops.
COMMON_FIELDS = {
    "aead_output", "alice_session_after_first_send", "associated_data",
    "bob_prekey_store_after_receipt", "bob_session_after_receipt",
    "bob_session_after_repeat", "bundle", "composite_header", "dh1", "dh2", "dh3",
    "initial_message", "kem_ciphertext", "kem_shared_secret", "low_order_repeat",
    "mk", "mk_ec", "mk_pq", "ratchet_message", "repeat_initial", "repeat_plaintext",
    "responder_plaintext", "sk", "split_ec", "split_pq", "torsion_initial",
}
FIELDS = {
    "one-time-prekeys-first-message": COMMON_FIELDS | {"dh4"},
    "last-resort-first-message": COMMON_FIELDS | {
        "bob_session_low_order_established", "low_order_initial", "replay_identity",
        "changed_identity_repeat", "torsion_repeat", "unrelated_repeat"},
}
COMMON_INPUTS = {
    "alice_braid_keygen_d_z", "alice_ephemeral_secret", "alice_identity_secret",
    "alice_kem_encapsulation_m", "alice_ratchet_secret", "bob_identity_secret",
    "bob_last_resort_kem_d_z", "bob_last_resort_kem_signature_nonce",
    "bob_ratchet_secret", "bob_repeat_random", "bob_signed_prekey_secret",
    "bob_signed_prekey_signature_nonce", "plaintext", "repeat_plaintext",
}
INPUTS = {
    "one-time-prekeys-first-message": COMMON_INPUTS | {
        "bob_one_time_curve_secret", "bob_one_time_kem_d_z",
        "bob_one_time_kem_signature_nonce"},
    "last-resort-first-message": COMMON_INPUTS | {"other_identity_secret", "unrelated_ephemeral_secret"},
}

# Inputs this module never reads, so that changing one cannot change its
# verdict: consumed by the implementation and never observable (see above).
UNREAD_INPUTS = {"bob_repeat_random"}

# Byte ranges (start, end) of inputs this module reads only in part. Each is the
# `z` half of a `d || z` draw that no output shows (see above), so changing a
# byte in one cannot change the verdict, and a byte outside it must.
UNREAD_INPUT_RANGES = {
    "alice_braid_keygen_d_z": [(32, 64)],
    "bob_one_time_kem_d_z": [(32, 64)],
}


@functools.lru_cache(maxsize=256)
def _decapsulate(dk, ciphertext):
    """FIPS 203 Decaps_internal, kept for the run: a pure function of its two
    arguments, called for several spellings of one message."""
    return mlkem.decaps_internal(dk, ciphertext)


def _eq(what, want, got):
    if bytes(want) != bytes(got):
        raise Mismatch(f"{what}: expected {bytes(want).hex()[:64]}, derived {bytes(got).hex()[:64]}")


def _field(f, name, got):
    _eq(name, bx(f[name]), got)


def _torsion_spelling(what, original, other):
    """`other` is the spelling the vectors use: the byte-wise smallest of the
    seven other canonical u-coordinates that differ from `original` by a
    multiple of a point of order 8 (tacenta-test-vectors/README.md, Vector
    layouts). Derived here from the group's order alone."""
    translates = curve25519.torsion_translates(original)
    if len(translates) != 7:
        raise Mismatch(f"{what}: the original has {len(translates)} other spellings, not 7")
    if bytes(other) != translates[0]:
        raise Mismatch(f"{what}: not the smallest of the seven other spellings of the "
                       "original's agreement class")
    return translates


def _refuse_low_order(what, key):
    """A low-order u-coordinate gives an all-zero X25519 output under every
    clamped key (session-establishment.md, Notation)."""
    for secret in (bytes([0x77]) * 32, bytes([0x5d]) * 32):
        try:
            curve25519.x25519_contributory(secret, key)
        except curve25519.NonContributory:
            continue
        raise Mismatch(f"{what}: not a low-order key")


def _sign(secret, message, nonce):
    return curve25519.xeddsa_sign(secret, message, nonce)


def check(v):
    """Derive the vector `v` from its inputs, and compare."""
    vid = v["id"]
    if vid not in FIELDS:
        raise Mismatch(f"no derivation for the session vector {vid}")
    i, f = v["inputs"], v["fields"]
    if set(f) != FIELDS[vid]:
        raise Mismatch(f"fields differ: only in the vector {sorted(set(f) - FIELDS[vid])}, "
                       f"only derived {sorted(FIELDS[vid] - set(f))}")
    if set(i) != INPUTS[vid]:
        raise Mismatch(f"inputs differ: only in the vector {sorted(set(i) - INPUTS[vid])}, "
                       f"only read {sorted(INPUTS[vid] - set(i))}")
    one_time = vid == "one-time-prekeys-first-message"

    # ------------------------------------------------------------- the keys
    alice_secret, bob_secret = bx(i["alice_identity_secret"]), bx(i["bob_identity_secret"])
    alice_ik = curve25519.x25519_public(alice_secret)
    bob_ik = curve25519.x25519_public(bob_secret)
    spk_secret = bx(i["bob_signed_prekey_secret"])
    spk = curve25519.x25519_public(spk_secret)
    otpk_secret = bx(i["bob_one_time_curve_secret"]) if one_time else None
    otpk = curve25519.x25519_public(otpk_secret) if one_time else None
    eph_secret = bx(i["alice_ephemeral_secret"])
    alice_eph = curve25519.x25519_public(eph_secret)
    ratchet_secret = bx(i["alice_ratchet_secret"])
    alice_ratchet_pub = curve25519.x25519_public(ratchet_secret)
    plaintext, repeat_plaintext = bx(i["plaintext"]), bx(i["repeat_plaintext"])

    # ------------------------------------------------------------ the bundle
    # key-deletion.md numbers a store's keys from one counter, in the order the
    # signed prekey, the one-time curve prekeys, the last-resort KEM prekey and
    # the one-time KEM prekeys; session-persistence.md, Prekey store, says what
    # `publish` names: the last one-time entry of each kind, or the last-resort
    # KEM prekey and no one-time curve prekey. One one-time prekey of each kind
    # makes the ids (1, 2, 4) and the last-resort key 3; none makes (1, none, 2).
    ids = (1, 2, 4) if one_time else (1, K.ABSENT_ID, 2)
    last_resort_id = 3 if one_time else 2
    next_id = 5 if one_time else 3
    kem_nonce = bx(i["bob_one_time_kem_signature_nonce" if one_time
                     else "bob_last_resort_kem_signature_nonce"])

    # K1: each KEM prekey pair is FIPS 203 KeyGen_internal(d, z) of a 64-byte
    # draw, d first (session-establishment.md, Primitives, ML-KEM-1024, Key
    # generation). The bundle names the one-time key when there is one and the
    # last-resort key otherwise (session-persistence.md, Prekey store).
    def kem_pair_from(name):
        d_z = bx(i[name])
        if len(d_z) != 64:
            raise Mismatch(f"{name} is not 64 bytes")
        return mlkem.keygen_internal(d_z[:32], d_z[32:])

    last_resort_ek, last_resort_dk = kem_pair_from("bob_last_resort_kem_d_z")
    kem_ek, kem_dk = (kem_pair_from("bob_one_time_kem_d_z") if one_time
                      else (last_resort_ek, last_resort_dk))
    pqxdh.check_kem_prekey(kem_ek)                       # the page's section 7.2 check, on the computed key
    bundle = wire.PrekeyBundle(
        identity_key=bob_ik, signed_prekey=spk,
        signed_prekey_signature=_sign(bob_secret, wire.encode_ec(spk),
                                      bx(i["bob_signed_prekey_signature_nonce"])),
        kem_prekey=kem_ek,
        kem_prekey_signature=_sign(bob_secret, wire.encode_kem(kem_ek), kem_nonce),
        one_time_prekey=otpk, signed_prekey_id=ids[0], one_time_prekey_id=ids[1],
        kem_prekey_id=ids[2])
    _field(f, "bundle", wire.encode_bundle(bundle))
    for what, sig, message in (
            ("signed prekey", bundle.signed_prekey_signature, wire.encode_ec(spk)),
            ("KEM prekey", bundle.kem_prekey_signature, wire.encode_kem(bundle.kem_prekey))):
        if curve25519.xeddsa_verify(bob_ik, message, sig) is None:
            raise Mismatch(f"the bundle's {what} signature does not verify under the identity key")

    # ------------------------------------------- Alice: agreements and SK
    dh1, dh2, dh3, dh4 = pqxdh.initiator_agreements(alice_secret, eph_secret, bob_ik, spk, otpk)
    for name, got in (("dh1", dh1), ("dh2", dh2), ("dh3", dh3)) + ((("dh4", dh4),) if one_time else ()):
        _field(f, name, got)
    # K2: Encaps_internal(ek, m) with the 32-byte draw as m (Encapsulation).
    kem_m = bx(i["alice_kem_encapsulation_m"])
    kem_secret, kem_ciphertext = mlkem.encaps_internal(kem_ek, kem_m)
    pqxdh.check_kem_ciphertext(kem_ciphertext)
    _field(f, "kem_ciphertext", kem_ciphertext)
    _field(f, "kem_shared_secret", kem_secret)
    # K3: the responder's decapsulation with the decapsulation key the message
    # names gives the same secret.
    _eq("decapsulation", kem_secret, _decapsulate(kem_dk, kem_ciphertext))
    # K4: SK and everything after it come from the computed secret.
    sk = pqxdh.shared_secret(dh1, dh2, dh3, dh4, kem_secret)
    _field(f, "sk", sk)
    split_ec, split_pq = triple.split_secret(sk)
    _field(f, "split_ec", split_ec)
    _field(f, "split_pq", split_pq)
    identity_ad = pqxdh.associated_data(alice_ik, bob_ik)
    _field(f, "associated_data", wire.concat_ad(identity_ad, bx(f["composite_header"])))

    # ------------------- Alice: the Braid's boundary, then the first message
    # The stored Braid is what a send from KeysUnsampled leaves: the state
    # KeysSampled holding a key pair (delegated layout) and an encoder over the
    # header and its MAC. Only the key pair is a boundary now. The
    # authenticator is Init(1, SK).
    alice_v = persistence.session_from_bytes(bx(f["alice_session_after_first_send"]))
    stored = alice_v.braid
    if stored.tag != braid.KEYS_SAMPLED or stored.epoch != 1:
        raise Mismatch("Alice's Braid is not KeysSampled at epoch 1 after her first send")
    auth = braid.Auth.init(1, sk)
    _eq("Braid authenticator", auth.root_key + auth.mac_key, stored.auth_root + stored.auth_mac)
    # B1: key generation from the draw gives the header, rho || H(ek), and
    # ek_vector, which validates against the header (mlkem-braid.md, The KEM split).
    braid_d_z = bx(i["alice_braid_keygen_d_z"])
    if len(braid_d_z) != 64:
        raise Mismatch("alice_braid_keygen_d_z is not 64 bytes")
    braid_ek, _braid_dk = mlkem.keygen_internal(braid_d_z[:32], braid_d_z[32:])
    braid_header, braid_ek_vector = mlkem.braid_split(braid_ek)
    if not braid.validate_ek_vector(braid_header, braid_ek_vector):
        raise Mismatch("the Braid's ek_vector does not validate against its own header")
    # B2: the 96-byte value is the header and its MAC under Init(1, SK); it is
    # what the stored header encoder holds, three chunks with one codeword issued.
    value = braid_header + auth.mac_hdr(1, braid_header)
    header_encoder = stored.fields["hdr_enc"]
    _eq("the Braid's header value against the stored header encoder", value,
        b"".join(header_encoder.chunks))
    if header_encoder.next != 1 or header_encoder.exhausted:
        raise Mismatch("Alice's header encoder has not issued exactly one codeword")
    before_send = braid.from_persisted(stored)
    before_send.hdr_enc = erasure.Encoder.for_value(value)
    first = braid.send(before_send, None)
    if (first.message.epoch, first.message.type, first.message.codeword[0], first.epoch) != (
            1, K.AG_HDR, 0, 0):
        raise Mismatch("the Braid's first send is not header codeword 0 at epoch 1")
    _eq("Braid after the first send", braid.export(first.state),
        persistence.braid_to_bytes(stored))

    c0 = ratchet.init_initiator(split_ec, alice_ratchet_pub, spk,
                                curve25519.x25519_contributory(ratchet_secret, spk))
    s0 = spqr.init(split_pq, spqr.A2B)

    def send(classical, sparse, braid_state, text):
        """One message: the Braid first, then both ratchets, the two message
        keys combined, the composite header as associated data."""
        sent = braid.send(braid_state, None)
        classical, header, mk_ec = ratchet.send(classical)
        sparse, pq_epoch, pq_n, mk_pq = spqr.send(sparse, sent.epoch, None, None)
        composite = wire.CompositeHeader(
            dh=header.dh, pn=header.pn, n=header.n, pq_epoch=pq_epoch, pq_n=pq_n,
            **braid.header_fields(sent.message))
        composite_bytes = wire.encode_composite(composite)
        mk = triple.combine(mk_ec, mk_pq)
        sealed = aead.seal(mk, wire.concat_ad(identity_ad, composite_bytes), text)
        return (classical, sparse, sent.state, mk_ec, mk_pq, mk, composite_bytes,
                sealed, wire.encode_ratchet_message(composite, sealed))

    (c1, s1, braid1, mk_ec, mk_pq, mk, composite_bytes, sealed, ratchet_message) = send(
        c0, s0, before_send, plaintext)
    for name, got in (("mk_ec", mk_ec), ("mk_pq", mk_pq), ("mk", mk),
                      ("composite_header", composite_bytes), ("aead_output", sealed),
                      ("ratchet_message", ratchet_message)):
        _field(f, name, got)
    wrapper = wire.InitialMessage(
        identity=wire.encode_ec(alice_ik), ephemeral=wire.encode_ec(alice_eph),
        kem_ciphertext=kem_ciphertext, signed_prekey_id=bundle.signed_prekey_id,
        one_time_prekey_id=bundle.one_time_prekey_id, kem_prekey_id=bundle.kem_prekey_id,
        ratchet_message=ratchet_message)
    _field(f, "initial_message", wire.encode_initial(wrapper))
    pending = persistence.PendingInitial(
        alice_eph, kem_ciphertext, bundle.signed_prekey_id, bundle.one_time_prekey_id,
        bundle.kem_prekey_id)
    _field(f, "alice_session_after_first_send", persistence.session_to_bytes(
        persistence.SessionState(persistence.TripleState(c1, s1), braid.to_persisted(braid1),
                                 ratchet_secret, identity_ad, alice_ik, bob_ik, pending, None)))

    # The initiator repeats the wrapper around a second message until it hears
    # a reply (session-persistence.md, `pending_initial`).
    (_c2, _s2, _braid2, _, _, _, _, _, repeat_ratchet_message) = send(
        c1, s1, braid1, repeat_plaintext)
    repeat = replace(wrapper, ratchet_message=repeat_ratchet_message)
    _field(f, "repeat_initial", wire.encode_initial(repeat))

    # ------------------------------------------- Bob: agreements, same SK
    def responder_sk(message):
        """SK as the responder derives it from a decoded initial message: the
        decapsulation of the message's own ciphertext with the decapsulation key
        it names (K3), the four agreements, then the KDF."""
        ika, eka = pqxdh.handshake_keys(message)
        r1, r2, r3, r4 = pqxdh.responder_agreements(bob_secret, spk_secret, otpk_secret, ika, eka)
        pqxdh.check_kem_ciphertext(message.kem_ciphertext)
        decapsulated = _decapsulate(kem_dk, message.kem_ciphertext)
        return (r1, r2, r3, r4), pqxdh.shared_secret(r1, r2, r3, r4, decapsulated)

    spellings = {}
    for name in ("initial_message", "torsion_initial"):
        message = wire.decode_initial(bx(f[name]))
        agreed, agreed_sk = responder_sk(message)
        _eq(f"{name}: the responder's agreements", b"".join(x for x in agreed if x),
            b"".join(x for x in (dh1, dh2, dh3, dh4) if x))
        _eq(f"{name}: SK", sk, agreed_sk)
        spellings[name] = message

    canonical = spellings["initial_message"]
    torsion = spellings["torsion_initial"]
    _torsion_spelling("torsion_initial's ephemeral", canonical.ephemeral[1:], torsion.ephemeral[1:])
    _eq("torsion_initial differs from initial_message in the ephemeral only",
        wire.encode_initial(replace(canonical, ephemeral=torsion.ephemeral)), bx(f["torsion_initial"]))

    # ---------------------- Bob: the session, from the message that opens it
    opening = torsion if one_time else canonical
    agreement = braid.BraidAgreement(None)
    party = triple.init_responder(sk, identity_ad, spk_secret, braid.init_responder(sk))
    party, first_plaintext = triple.decrypt(party, agreement, opening.ratchet_message,
                                            bx(i["bob_ratchet_secret"]))
    _field(f, "responder_plaintext", first_plaintext)
    _eq("responder_plaintext against the input plaintext", plaintext, first_plaintext)

    def session_of(party, established):
        return persistence.SessionState(
            persistence.TripleState(party.classical, party.sparse),
            braid.to_persisted(party.agreement_state), party.ratchet_private, identity_ad,
            bob_ik, alice_ik, None, established)

    responder = session_of(party, opening.ephemeral)
    _field(f, "bob_session_after_receipt", persistence.session_to_bytes(responder))

    # -------------------- Bob: the wrapper of a session that already exists
    def receive(session, raw):
        """Session.decrypt for an initial message (session-establishment.md,
        Receiving the initial message): decode, the class and identity tests on
        the session, then the ratchet message inside. Returns the session that
        results and the plaintext; the argument is what it was."""
        inside = {}

        def decrypt_inner(ratchet_message):
            party = triple.Party(
                session.triple.classical, session.triple.sparse, session.ratchet_private,
                braid.from_persisted(session.braid), identity_ad)
            party, text = triple.decrypt(party, agreement, ratchet_message,
                                         bx(i["bob_repeat_random"]))
            inside["session"] = session_of(party, session.established_ephemeral)
            return text

        text = pqxdh.receive_repeated_initial(session, raw, decrypt_inner)
        return inside["session"], text

    def refused(what, session, raw):
        """Refused as not a repeat, without reaching the inner message, and
        the session object is what it was afterwards."""
        before = persistence.session_to_bytes(session)
        try:
            pqxdh.receive_repeated_initial(
                session, raw, lambda _r: (_ for _ in ()).throw(
                    Mismatch(f"{what}: the ratchet message inside was decrypted")))
        except pqxdh.NotARepeatedInitial:
            pass
        else:
            raise Mismatch(f"{what}: accepted as a repeated initial message")
        if persistence.session_to_bytes(session) != before:
            raise Mismatch(f"{what}: the refusal changed the session")

    def no_plaintext(what, session, raw):
        """A wrapper the session recognises as a repeat around a ratchet message
        it has already read yields no plaintext and changes nothing
        (session-establishment.md, Receiving the initial message)."""
        before = persistence.session_to_bytes(session)
        try:
            receive(session, raw)
        except pqxdh.NotARepeatedInitial:
            raise Mismatch(f"{what}: refused as not a repeat, not as already read")
        except ratchet.RatchetError:
            pass
        else:
            raise Mismatch(f"{what}: yielded a plaintext a second time")
        if persistence.session_to_bytes(session) != before:
            raise Mismatch(f"{what}: the refusal changed the session")

    repeat_message = wire.decode_initial(bx(f["repeat_initial"]))
    low_order_repeat = replace(repeat_message, ephemeral=wire.encode_ec(bytes(32)))
    _field(f, "low_order_repeat", wire.encode_initial(low_order_repeat))
    _refuse_low_order("low_order_repeat's ephemeral", bytes(32))
    refused("a low-order repeated initial", responder, bx(f["low_order_repeat"]))

    no_plaintext("the message that established the session, sent again", responder,
                 bx(f["initial_message"]))

    if one_time:
        # The canonical repeat is the same agreement as the torsion spelling
        # that opened the session.
        after_repeat, second_plaintext = receive(responder, bx(f["repeat_initial"]))
    else:
        # The other direction: the canonical spelling opened the session, and
        # a byte-different spelling of the same agreement is its repeat.
        torsion_repeat = wire.decode_initial(bx(f["torsion_repeat"]))
        _torsion_spelling("torsion_repeat's ephemeral", repeat_message.ephemeral[1:],
                          torsion_repeat.ephemeral[1:])
        _eq("torsion_repeat differs from repeat_initial in the ephemeral only",
            wire.encode_initial(replace(repeat_message, ephemeral=torsion_repeat.ephemeral)),
            bx(f["torsion_repeat"]))
        after_repeat, second_plaintext = receive(responder, bx(f["torsion_repeat"]))
    _field(f, "repeat_plaintext", second_plaintext)
    _eq("repeat_plaintext against the input", repeat_plaintext, second_plaintext)
    _field(f, "bob_session_after_repeat", persistence.session_to_bytes(after_repeat))

    # ----------------------- the last-resort path, and what refuses there
    store = persistence.prekey_store_from_bytes(bx(f["bob_prekey_store_after_receipt"]))
    # K1, the stored pair: `dk || ek` (session-persistence.md, Prekey store) of
    # the last-resort draw. In the one-time vector the pair after receipt is
    # that key, the one-time key having been consumed.
    kem_pair = last_resort_dk + last_resort_ek
    seen = [] if one_time else [(last_resort_id, pqxdh.last_resort_fingerprint(sk))]
    expected_store = persistence.PrekeyStore(
        identity_public=bob_ik, signed_prekey_secret=spk_secret, signed_prekey_id=ids[0],
        signed_prekey_sig=bundle.signed_prekey_signature, one_time=[], kem_pair=kem_pair,
        kem_id=last_resort_id,
        kem_sig=(_sign(bob_secret, wire.encode_kem(kem_pair[K.KEM_DK_LEN:]),
                       bx(i["bob_last_resort_kem_signature_nonce"]))),
        kem_one_time=[], next_id=next_id, seen=seen, legacy_blocked=[],
        previous_signed=None, previous_kem=None)
    _field(f, "bob_prekey_store_after_receipt", persistence.prekey_store_to_bytes(expected_store))

    if not one_time:
        _field(f, "replay_identity", pqxdh.last_resort_fingerprint(sk))
        # A spent handshake is refused in every spelling of its agreement, and
        # the same message is accepted when the record does not hold it: the
        # refusal is the record's and not the message's.
        empty = replace(store, seen=[])
        for name in ("initial_message", "torsion_initial"):
            message = spellings[name]
            _, message_sk = responder_sk(message)
            try:
                pqxdh.check_last_resort(store, message, message_sk)
            except pqxdh.ReplayedLastResort:
                pass
            else:
                raise Mismatch(f"{name}: a spent last-resort handshake was not refused as a replay")
            _eq(f"{name}: accepted by a store without the record",
                pqxdh.last_resort_fingerprint(sk),
                pqxdh.check_last_resort(empty, message, message_sk))
        low_order_initial = replace(canonical, ephemeral=wire.encode_ec(bytes(32)))
        _field(f, "low_order_initial", wire.encode_initial(low_order_initial))
        try:
            responder_sk(low_order_initial)
        except curve25519.NonContributory:
            pass
        else:
            raise Mismatch("low_order_initial: the responder's agreement was contributory")

        # The wrapper of an established session refuses what is not the same
        # agreement class.
        unrelated = curve25519.x25519_public(bx(i["unrelated_ephemeral_secret"]))
        if curve25519.torsion_related(unrelated, canonical.ephemeral[1:]) or (
                unrelated == canonical.ephemeral[1:]):
            raise Mismatch("unrelated_repeat: the ephemeral is in the established class")
        # It is contributory under the session's key, so the refusal is the
        # class comparison's and not the non-contributory check's.
        curve25519.x25519_contributory(responder.ratchet_private, unrelated)
        unrelated_repeat = replace(repeat_message, ephemeral=wire.encode_ec(unrelated))
        _field(f, "unrelated_repeat", wire.encode_initial(unrelated_repeat))
        refused("an unrelated contributory ephemeral", responder, bx(f["unrelated_repeat"]))

        # The identity must be the peer's, byte for byte: another valid key is
        # not a repeat of the message that established the session.
        other = curve25519.x25519_public(bx(i["other_identity_secret"]))
        if other == alice_ik:
            raise Mismatch("changed_identity_repeat: the other identity is the initiator's")
        changed = replace(repeat_message, identity=wire.encode_ec(other))
        _field(f, "changed_identity_repeat", wire.encode_initial(changed))
        refused("an identity that is another key", responder, bx(f["changed_identity_repeat"]))

        # Not only the spelling the vector records. Every canonical spelling of
        # the initiator's ephemeral is the same agreement, so each replays the
        # spent handshake and each is a repeat.
        for spelling in curve25519.torsion_translates(canonical.ephemeral[1:]):
            other = replace(canonical, ephemeral=wire.encode_ec(spelling))
            _, other_sk = responder_sk(other)
            _eq("another spelling's SK", sk, other_sk)
            try:
                pqxdh.check_last_resort(store, other, other_sk)
            except pqxdh.ReplayedLastResort:
                pass
            else:
                raise Mismatch("a spent handshake in another spelling was not refused as a replay")
        for spelling in curve25519.torsion_translates(repeat_message.ephemeral[1:]):
            other = replace(repeat_message, ephemeral=wire.encode_ec(spelling))
            _, text = receive(responder, wire.encode_initial(other))
            _eq("a repeat in another spelling", repeat_plaintext, text)

        # Both agreements non-contributory: the session stores a low-order
        # established ephemeral, imports, and the byte-equal wrapper is still
        # not a repeat.
        low_session = replace(responder, established_ephemeral=wire.encode_ec(bytes(32)))
        _field(f, "bob_session_low_order_established", persistence.session_to_bytes(low_session))
        persistence.session_from_bytes(bx(f["bob_session_low_order_established"]))
        refused("a low-order repeated initial against a low-order established ephemeral",
                low_session, bx(f["low_order_repeat"]))
