#!/usr/bin/env python3
"""
Specification-only semantic operation reader for the P6 session/prekey
operation-trace corpus (tacenta-test-vectors/traces/session-operation-trace.json).

This reader is deliberately independent of tacenta-core, tacenta-model and any
other implementation: every rule function below cites the specification
section it comes from, and nothing here reads or imports implementation code
(none is present in this clean-room packet).

What it does NOT do, by design (JIE-SUN-V3-START-HERE.md, "must not infer
implementation internals, private storage layout, random-source calls, error
variants, or check order"):
  - it does not compute cryptography. Whether a ciphertext authenticates, a
    signature verifies, or two byte fields match is a declared fact per step,
    taken from the trace's own fixture prose -- the abstraction boundary the
    included sources themselves draw (session-establishment.md composes DH,
    KEM and AEAD primitives; it does not ask a caller to recompute them).
  - it does not choose an internal error-variant name. Where the specification
    names a required refusal (error-handling.md, "Conditions a caller must act
    on are named"), the reader checks that name; where it does not
    (error-handling.md, "The error types... are left to an implementation"),
    the reader checks only the required outcome ("refused"), not any variant.

Each FACTS entry below records, in a comment, the exact fixture sentence in
session-operation-trace.json that licenses the declared fact.
"""

import json
import sys
from pathlib import Path

TRACE_PATH = Path("tacenta-test-vectors/traces/session-operation-trace.json")

# ---------------------------------------------------------------------------
# Declared cryptographic/comparison facts per (trace id, step index).
# These are the trace's own stated abstractions (fixture prose), not values
# this reader computes. Every entry cites the fixture sentence it comes from.
# ---------------------------------------------------------------------------
INITIAL_STATE = {
    "prekey-store-identifier-ceiling": {"next_id_at_ceiling": True},
    # fixture: "a prekey store whose next_id already stands at u32::MAX"
    # (key-deletion.md, One-time prekeys are replenished, identifier space end).
}

FACTS = {
    "establish-initiator-with-one-time-curve-prekey": {
        0: dict(bundle_well_formed=True, signatures_valid=True, dh_contributory=True),
        # fixture: "Bob's published bundle, carrying a one-time curve prekey
        # and a one-time KEM prekey" -- an honestly published bundle.
    },
    "establish-initiator-without-one-time-curve-prekey": {
        0: dict(bundle_well_formed=True, signatures_valid=True, dh_contributory=True),
    },
    "establish-initiator-bad-prekey-signature-refused": {
        0: dict(bundle_well_formed=True, signatures_valid=False, dh_contributory=True),
        # fixture: "a well-formed, decodable bundle whose signed-prekey
        # signature does not verify under the bundle's own identity key".
    },
    "establish-initiator-non-contributory-dh-refused": {
        0: dict(bundle_well_formed=True, signatures_valid=True, dh_contributory=False),
        # fixture: "a well-formed, canonically-encoded bundle whose signed
        # prekey is a low-order curve point, so DH(EKA, SPKB) is all-zero".
    },
    "establish-initiator-malformed-bundle-refused": {
        0: dict(bundle_well_formed=False),
        # fixture: "a bundle whose identity_key is re-spelled with bit 255
        # set, failing DecodeEC's canonical check" -- fails to decode, so
        # signatures and DH are never reached.
    },
    "control-family9-malformed-bundle-wrongly-pending": {
        0: dict(bundle_well_formed=False),
    },
    "establish-responder-with-one-time-curve-prekey": {
        0: dict(ciphertext_authenticates=True, names_one_time_curve=True,
                kem_path="one-time", already_consumed=False, is_last_resort=False),
        # fixture: "...whose ciphertext authenticates"; "naming ... one
        # one-time curve prekey and one one-time KEM prekey".
    },
    "establish-responder-last-resort": {
        0: dict(ciphertext_authenticates=True, names_one_time_curve=False,
                kem_path="last-resort", already_consumed=False, is_last_resort=True,
                is_last_resort_replay=False, last_resort_record_full=False),
        # fixture: "naming no one-time curve prekey and Bob's last-resort KEM
        # prekey, never seen before, whose ciphertext authenticates".
    },
    "establish-responder-forged-initial-ciphertext": {
        0: dict(ciphertext_authenticates=False, names_one_time_curve=True,
                kem_path="one-time", already_consumed=False, is_last_resort=False),
        # fixture: "naming the same prekeys as alice-initial-with-otpk, whose
        # AEAD tag does not verify under the derived SK".
    },
    "one-time-kem-prekey-replay-refused": {
        0: dict(names_one_time_curve=True, kem_path="one-time",
                already_consumed=True, is_last_resort=False),
        # fixture: "the identical bytes of alice-initial-with-otpk, offered
        # again with no existing responder session to recognise it as a
        # repeat" -- the one-time prekeys it names were already deleted on
        # first use (key-deletion.md, "the responder... deletes the private
        # half of every one-time prekey the message named").
    },
    "last-resort-handshake-replay-refused": {
        0: dict(kem_path="last-resort", is_last_resort=True,
                is_last_resort_replay=True, last_resort_record_full=False),
        # fixture: "the identical bytes of that earlier accepted last-resort
        # initial message" against a store "whose last-resort replay record
        # already holds the fingerprint of an earlier accepted handshake".
    },
    "last-resort-record-full-refused": {
        0: dict(kem_path="last-resort", is_last_resort=True,
                is_last_resort_replay=False, last_resort_record_full=True),
        # fixture: "a fresh, never-seen last-resort initial message" against
        # a store "whose current last-resort KEM key's replay record already
        # holds MAX_LAST_RESORT_SEEN entries".
    },
    "repeated-initial-accepted-on-responder-session": {
        0: dict(actor_role="responder", ephemeral_matches=True, identity_matches=True,
                inner_message_already_read=False),
        # fixture: "the identical bytes of alice-initial-with-otpk, sent again
        # before Bob's first reply reaches Alice" -- same ephemeral, same
        # identity, not yet read a second time.
    },
    "not-a-repeated-initial-on-initiator-session": {
        0: dict(actor_role="initiator"),
        # fixture: "Alice's own initiator session" -- session-establishment.md:
        # "always on an initiator's session, it refuses the message".
    },
    "not-a-repeated-initial-changed-ephemeral": {
        0: dict(actor_role="responder", ephemeral_matches=False, identity_matches=True),
        # fixture: "an initial message from Alice with a new ephemeral key,
        # the same identity key".
    },
    "not-a-repeated-initial-changed-identity": {
        0: dict(actor_role="responder", ephemeral_matches=False, identity_matches=False),
        # fixture: "an initial message with a new identity key and a new
        # ephemeral key".
    },
    "restore-prekey-store-then-replenish": {
        0: dict(bytes_valid=True),
        # fixture: "Bob's prekey store, exported to bytes before a restart"
        # -- an honestly exported store, not corrupted.
        1: dict(),
    },
    "restore-session-then-send": {
        0: dict(bytes_valid=True),
        1: dict(sending_chain_exists=True, counter_not_exhausted=True),
    },
    "control-wrong-durable-effect": {
        0: dict(ciphertext_authenticates=True, names_one_time_curve=True,
                kem_path="one-time", already_consumed=False, is_last_resort=False),
        # Same declared facts as establish-responder-with-one-time-curve-prekey
        # -- the control's comment says its step "is exactly
        # establish-responder-with-one-time-curve-prekey's".
    },
    "control-missing-required-input": {
        0: dict(),  # No facts possible: the step is missing its message input.
    },
    "receive-ordinary-authenticated": {
        0: dict(ciphertext_authenticates=True, is_duplicate=False, braid_mac_fails=False, braid_already_failed=False),
        # fixture: "the next message on that chain, whose ciphertext authenticates".
    },
    "receive-out-of-order-then-recovery-then-duplicate-refused": {
        0: dict(ciphertext_authenticates=True, is_duplicate=False, braid_mac_fails=False, braid_already_failed=False),
        # fixture: "delivered before its first ... the receiver stores message
        # 1's key and decrypts message 2" -- the skip itself is internal state
        # this grammar does not model; only the accept/refuse and durable
        # effect are checked.
        1: dict(ciphertext_authenticates=True, is_duplicate=False, braid_mac_fails=False, braid_already_failed=False),
        # fixture: "its key was stored by the previous step and is used and
        # removed" -- recovery via the skipped-key store (ratchet.md, Skipped
        # keys), still an ordinary accept from this grammar's point of view.
        2: dict(is_duplicate=True, braid_already_failed=False),
        # fixture: "delivered again after message 2 has already been read" --
        # ratchet.md: "whose key is not stored is not accepted: its key has
        # already been used, expired, or evicted."
    },
    "control-family7-duplicate-wrongly-accepted": {
        0: dict(is_duplicate=True, braid_already_failed=False),
        # Same fact as the last step above: an already-read message replayed.
    },
    "braid-terminal-failure-persists-and-refuses": {
        0: dict(ciphertext_authenticates=True, is_duplicate=False, braid_mac_fails=True, braid_already_failed=False),
        # fixture: "whose outer ratchet AEAD tag authenticates but whose Braid
        # header or ciphertext MAC does not verify, moving the Braid to Failed".
        1: dict(bytes_valid=True),
        2: dict(braid_already_failed=True),
        # fixture: "attempts to send after restoring" a session "with its now-
        # Failed Braid" -- mlkem-braid.md, "it refuses encrypt and decrypt
        # with AgreementFailed once the Braid has failed... it keeps the
        # failed state and refuses that send too."
    },
    "control-family8-missing-message-input": {
        0: dict(),  # No facts possible: the step is missing its message input.
    },
}

REQUIRED_INPUTS = {
    # Per-operation required fixture references. Derived from what the cited
    # specification section says the operation needs to be carried out at
    # all, not from any implementation's function signature.
    "create-prekey-store": ["identity"],                      # session-establishment.md, Keys
    "publish-bundle": ["store"],                               # session-establishment.md, Publishing keys
    "replenish": ["store"],                                    # key-deletion.md, One-time prekeys are replenished
    "rotate-signed-prekey": ["store"],                          # key-deletion.md, Signed prekeys rotate
    "rotate-kem": ["store"],                                    # key-deletion.md, Signed prekeys rotate (rotate_kem)
    "establish-initiator": ["bundle"],                          # session-establishment.md, Sending the initial message
    "establish-responder": ["store", "message"],                # session-establishment.md, Receiving the initial message
    "send": ["session"],                                        # ratchet.md, Sending and receiving
    "receive": ["session", "message"],                          # ratchet.md, Sending and receiving
    "receive-repeated-initial": ["session", "message"],         # session-establishment.md, Receiving the initial message
    "restore-prekey-store": ["bytes"],                          # session-persistence.md, Prekey store
    "restore-session": ["bytes"],                               # session-persistence.md, Session
}

CITES = {
    "create-prekey-store": "key-deletion.md, 'create_prekeys with n one-time prekeys of each kind numbers the store in one pass'",
    "publish-bundle": "key-deletion.md, 'every call returns the same bundle until a message consumes what it names'",
    "replenish": "key-deletion.md, 'One-time prekeys are replenished, and identifiers never repeat' / identifier-ceiling paragraph",
    "rotate-signed-prekey": "key-deletion.md, 'Signed prekeys rotate, and the retired one is kept for exactly one rotation'",
    "rotate-kem": "key-deletion.md, 'rotate_kem does the same for the signed last-resort KEM prekey'",
    "establish-initiator": "session-establishment.md, Sending the initial message",
    "establish-responder": "session-establishment.md, Receiving the initial message; Replay, and why the ratchet must follow",
    "send": "ratchet.md, Sending and receiving; triple-ratchet.md, Sending and receiving",
    "receive": "ratchet.md, Sending and receiving; Skipped keys; mlkem-braid.md, Failure",
    "receive-repeated-initial": "session-establishment.md, Receiving the initial message",
    "restore-prekey-store": "session-persistence.md, Prekey store",
    "restore-session": "session-persistence.md, Session",
}


class Verdict:
    def __init__(self, outcome, refusal=None, effect=None, cite=""):
        self.outcome = outcome
        self.refusal = refusal
        self.effect = effect or {}
        self.cite = cite


class StoreState:
    """Tracks only what the trace grammar's effect vocabulary can observe."""
    def __init__(self):
        self.next_id_at_ceiling = False
        self.retired_signed_occupied = False
        self.retired_kem_occupied = False

    def clone(self):
        s = StoreState()
        s.__dict__.update(self.__dict__)
        return s


def rule_create_prekey_store(step, state, facts):
    return Verdict("ok", effect={"prekey_store": "created", "session": "unchanged", "next_id": "advanced"},
                    cite=CITES["create-prekey-store"])


def rule_publish_bundle(step, state, facts):
    return Verdict("ok", effect={"prekey_store": "unchanged", "session": "unchanged"},
                    cite=CITES["publish-bundle"])


def rule_replenish(step, state, facts):
    if state.next_id_at_ceiling:
        # key-deletion.md: "Once next_id stands at u32::MAX it adds nothing
        # further and keeps what it has added."
        return Verdict("ok", effect={"prekey_store": "unchanged", "session": "unchanged", "next_id": "at-ceiling"},
                        cite=CITES["replenish"] + " (identifier-ceiling quiet no-op)")
    return Verdict("ok", effect={"prekey_store": "replenished", "session": "unchanged", "next_id": "advanced"},
                    cite=CITES["replenish"])


def rule_rotate_signed(step, state, facts):
    if state.next_id_at_ceiling:
        # key-deletion.md: "once that counter stands at u32::MAX each of
        # rotate_signed_prekey and rotate_kem returns without rotating,
        # silently."
        return Verdict("ok", effect={"prekey_store": "unchanged", "session": "unchanged", "next_id": "at-ceiling"},
                        cite=CITES["rotate-signed-prekey"] + " (identifier-ceiling quiet no-op)")
    was_occupied = state.retired_signed_occupied
    state.retired_signed_occupied = True
    field = "dropped" if was_occupied else "retained"
    # key-deletion.md: "the key it replaces becomes the store's previous
    # signed prekey... when a second rotation moves another key into the
    # previous slot, the one already there is zeroed and dropped."
    return Verdict("ok", effect={"prekey_store": "signed-prekey-rotated", "session": "unchanged",
                                  "next_id": "advanced", "retired_signed_prekey": field},
                    cite=CITES["rotate-signed-prekey"])


def rule_rotate_kem(step, state, facts):
    if state.next_id_at_ceiling:
        return Verdict("ok", effect={"prekey_store": "unchanged", "session": "unchanged", "next_id": "at-ceiling"},
                        cite=CITES["rotate-kem"] + " (identifier-ceiling quiet no-op)")
    was_occupied = state.retired_kem_occupied
    state.retired_kem_occupied = True
    field = "dropped" if was_occupied else "retained"
    return Verdict("ok", effect={"prekey_store": "kem-prekey-rotated", "session": "unchanged",
                                  "next_id": "advanced", "retired_kem_prekey": field},
                    cite=CITES["rotate-kem"])


def rule_establish_initiator(step, state, facts):
    unchanged = {"prekey_store": "unchanged", "session": "unchanged"}

    if not facts.get("bundle_well_formed", True):
        # message-format.md, Curve public keys / Rejection: a bundle carrying
        # a re-spelled (non-canonical) key does not decode. session-
        # establishment.md: Alice "has then computed no agreement and sent
        # nothing" when a bundle check like this fails before any agreement.
        return Verdict("refused", refusal="decode-failure", effect=unchanged,
                        cite="message-format.md, Curve public keys; Rejection; "
                             "session-establishment.md, 'She has then computed no agreement and sent nothing'")

    if not facts.get("signatures_valid", True):
        # session-establishment.md, Sending the initial message: "Alice
        # verifies every signature in the bundle and aborts if any fails.
        # This is not optional." error-handling.md names no refusal for this
        # condition, so only the outcome is checked.
        return Verdict("refused", refusal=None, effect=unchanged,
                        cite="session-establishment.md, Sending the initial message, "
                             "'Alice verifies every signature in the bundle and aborts if any fails'")

    if not facts.get("dh_contributory", True):
        # session-establishment.md, Notation: "Both sides refuse a
        # Diffie-Hellman output that is not contributory, which a low-order
        # public key produces." Again no named refusal.
        return Verdict("refused", refusal=None, effect=unchanged,
                        cite="session-establishment.md, Notation, "
                             "'Both sides refuse a Diffie-Hellman output that is not contributory'")

    # session-establishment.md: the initiator derives SK, sends the initial
    # message, and holds a pending session; it does not touch the peer's
    # prekey store (that store belongs to the responder, not to this actor).
    return Verdict("ok", effect={"prekey_store": "unchanged", "session": "initiator-pending"},
                    cite=CITES["establish-initiator"])


def rule_establish_responder(step, state, facts):
    cite_replay = "session-establishment.md, Replay, and why the ratchet must follow; The fingerprint"
    cite_recv = "session-establishment.md, Receiving the initial message"
    cite_kd = "key-deletion.md, 'a message that fails to authenticate leaves the store as it found it'"

    if facts.get("is_last_resort"):
        # session-establishment.md: "Bob computes the fingerprint before he
        # decapsulates. He refuses the message (ReplayedLastResort) if any
        # entry in the record holds that fingerprint."
        if facts.get("is_last_resort_replay"):
            return Verdict("refused", refusal="ReplayedLastResort",
                            effect={"prekey_store": "unchanged", "session": "unchanged",
                                    "one_time_curve": "unchanged", "one_time_kem": "unchanged",
                                    "last_resort_record": "unchanged"},
                            cite=cite_replay)
        # key-deletion.md: "a last-resort handshake it has not seen, arriving
        # while the key it names has spent that key's budget, is refused
        # (LastResortRecordFull) before anything is decrypted or changed."
        if facts.get("last_resort_record_full"):
            return Verdict("refused", refusal="LastResortRecordFull",
                            effect={"prekey_store": "unchanged", "session": "unchanged",
                                    "one_time_curve": "unchanged", "one_time_kem": "unchanged",
                                    "last_resort_record": "unchanged"},
                            cite=cite_replay)

    if facts.get("already_consumed"):
        # The named one-time prekey's private half is already deleted
        # (key-deletion.md, "Establishing a session" / "That last deletion is
        # what makes a one-time prekey one-time"). error-handling.md names no
        # refusal for this condition, so only the outcome is checked.
        return Verdict("refused", refusal=None,
                        effect={"prekey_store": "unchanged", "session": "unchanged",
                                "one_time_curve": "unchanged", "one_time_kem": "unchanged",
                                "last_resort_record": "unchanged"},
                        cite=cite_kd)

    if not facts.get("ciphertext_authenticates", False):
        return Verdict("refused", refusal="authentication-failure",
                        effect={"prekey_store": "unchanged", "session": "unchanged",
                                "one_time_curve": "unchanged", "one_time_kem": "unchanged",
                                "last_resort_record": "unchanged"},
                        cite=cite_kd)

    # Success. key-deletion.md: "if it decrypts, it deletes the private half
    # of every one-time prekey the message named, curve and KEM alike."
    if facts.get("is_last_resort"):
        return Verdict("ok", effect={
            "prekey_store": "last-resort-fingerprint-added",
            "session": "responder-established",
            "one_time_curve": "deleted" if facts.get("names_one_time_curve") else "absent",
            "one_time_kem": "last-resort",
            "last_resort_record": "added",
        }, cite=cite_recv)

    return Verdict("ok", effect={
        "prekey_store": "one-time-keys-deleted",
        "session": "responder-established",
        "one_time_curve": "deleted" if facts.get("names_one_time_curve") else "absent",
        "one_time_kem": "deleted",
    }, cite=cite_recv)


def rule_receive_repeated_initial(step, state, facts):
    cite = CITES["receive-repeated-initial"]
    if facts.get("actor_role") == "initiator":
        # "Otherwise, and always on an initiator's session, it refuses the
        # message."
        return Verdict("refused", refusal="NotARepeatedInitial",
                        effect={"prekey_store": "unchanged", "session": "unchanged"}, cite=cite)
    if not (facts.get("ephemeral_matches") and facts.get("identity_matches")):
        return Verdict("refused", refusal="NotARepeatedInitial",
                        effect={"prekey_store": "unchanged", "session": "unchanged"}, cite=cite)
    if not facts.get("inner_message_already_read", False):
        return Verdict("ok", effect={"prekey_store": "unchanged", "session": "message-accepted"}, cite=cite)
    # Not exercised by this corpus: an already-read repeat. No trace covers it.
    return Verdict("ok", effect={"prekey_store": "unchanged", "session": "unchanged"},
                    cite=cite + " (message already read; ratchet refuses the inner message)")


def rule_send(step, state, facts):
    if facts.get("braid_already_failed"):
        # mlkem-braid.md, Failure: "Session puts nothing from a failed Braid
        # on the wire: it refuses encrypt and decrypt with AgreementFailed
        # once the Braid has failed... it keeps the failed state and refuses
        # that send too." error-handling.md names this condition ("An
        # agreement that has failed is reported as failed") but the schema's
        # refusal enum has no matching value, so only the outcome is checked
        # -- see the finding recorded in the return record.
        return Verdict("refused", refusal=None,
                        effect={"prekey_store": "unchanged", "session": "unchanged"},
                        cite="mlkem-braid.md, Failure, 'Session puts nothing from a failed Braid on the wire'")
    return Verdict("ok", effect={"prekey_store": "unchanged", "session": "message-accepted"},
                    cite=CITES["send"])


def rule_receive(step, state, facts):
    if facts.get("braid_already_failed"):
        return Verdict("refused", refusal=None,
                        effect={"prekey_store": "unchanged", "session": "unchanged"},
                        cite="mlkem-braid.md, Failure, 'Session puts nothing from a failed Braid on the wire'")

    if facts.get("is_duplicate"):
        # ratchet.md, Sending and receiving: "A message whose ratchet key
        # equals DHr, whose number N is below Nr, and whose key is not
        # stored is not accepted: its key has already been used, expired, or
        # evicted." error-handling.md names no refusal for this condition.
        return Verdict("refused", refusal=None,
                        effect={"prekey_store": "unchanged", "session": "unchanged"},
                        cite="ratchet.md, Sending and receiving, 'is not accepted: its key has already "
                             "been used, expired, or evicted'")

    if not facts.get("ciphertext_authenticates", False):
        return Verdict("refused", refusal="authentication-failure",
                        effect={"prekey_store": "unchanged", "session": "unchanged"},
                        cite="message-format.md, Authenticated encryption")

    if facts.get("braid_mac_fails"):
        # mlkem-braid.md, Failure: a MAC that does not verify moves the Braid
        # to Failed. "A receive's move to Failed, like any other transition,
        # is adopted only once the message carrying it has authenticated.
        # That message is accepted and its plaintext returned; the refusals
        # begin with the next one." The outer message is accepted (outcome
        # ok); the notable durable effect this step produces is the session's
        # Braid entering the terminal Failed state.
        return Verdict("ok", effect={"prekey_store": "unchanged", "session": "terminal-failed"},
                        cite="mlkem-braid.md, Failure")

    # Ordinary accepted receive, in order or recovered from the skipped-key
    # store (ratchet.md, Skipped keys: "the receiver derives and stores the
    # intervening message keys ... so a later arrival still decrypts").
    return Verdict("ok", effect={"prekey_store": "unchanged", "session": "message-accepted"},
                    cite=CITES["receive"])


def rule_restore_prekey_store(step, state, facts):
    return Verdict("ok", effect={"prekey_store": "restored", "session": "unchanged"},
                    cite=CITES["restore-prekey-store"])


def rule_restore_session(step, state, facts):
    return Verdict("ok", effect={"prekey_store": "unchanged", "session": "restored"},
                    cite=CITES["restore-session"])


RULES = {
    "create-prekey-store": rule_create_prekey_store,
    "publish-bundle": rule_publish_bundle,
    "replenish": rule_replenish,
    "rotate-signed-prekey": rule_rotate_signed,
    "rotate-kem": rule_rotate_kem,
    "establish-initiator": rule_establish_initiator,
    "establish-responder": rule_establish_responder,
    "send": rule_send,
    "receive": rule_receive,
    "receive-repeated-initial": rule_receive_repeated_initial,
    "restore-prekey-store": rule_restore_prekey_store,
    "restore-session": rule_restore_session,
}


def check_required_inputs(op, inputs):
    required = REQUIRED_INPUTS.get(op, [])
    present = set((inputs or {}).keys())
    missing = [r for r in required if r not in present]
    return missing


def evaluate_step(trace_id, idx, step, state):
    op = step["op"]
    inputs = step.get("inputs", {})
    missing = check_required_inputs(op, inputs)
    if missing:
        return None, ("CANNOT-EVALUATE",
                       f"missing required input(s) {missing} for op '{op}'; "
                       f"cannot determine outcome or effect without them "
                       f"({CITES.get(op, 'operation requires this input to be carried out at all')})")

    facts = FACTS.get(trace_id, {}).get(idx, {})
    rule = RULES.get(op)
    if rule is None:
        return None, ("CANNOT-EVALUATE", f"no specification rule implemented for op '{op}'")
    verdict = rule(step, state, facts)
    return verdict, None


def compare(declared_expect, declared_effect, verdict):
    problems = []
    if declared_expect.get("outcome") != verdict.outcome:
        problems.append(
            f"outcome: declared '{declared_expect.get('outcome')}' but specification requires '{verdict.outcome}'")
    if verdict.outcome == "refused":
        declared_refusal = declared_expect.get("refusal")
        if verdict.refusal is not None and declared_refusal != verdict.refusal:
            problems.append(
                f"refusal: declared '{declared_refusal}' but specification names '{verdict.refusal}'")
        if verdict.refusal is None and declared_refusal is not None:
            problems.append(
                f"refusal: declared '{declared_refusal}' but the specification names no refusal for this "
                f"condition (error-handling.md leaves the error type to the implementation)")
    for field, expected_value in verdict.effect.items():
        declared_value = declared_effect.get(field)
        if declared_value != expected_value:
            problems.append(
                f"effect.{field}: declared '{declared_value}' but specification requires '{expected_value}'")
    return problems


def main():
    data = json.loads(TRACE_PATH.read_text())
    assert data["schema_version"] == 1
    assert data["algorithm"] == "session-operation-trace"

    total_steps = 0
    total_failed_steps = 0
    trace_results = []

    for trace in data["traces"]:
        trace_id = trace["id"]
        state = StoreState()
        for field, value in INITIAL_STATE.get(trace_id, {}).items():
            setattr(state, field, value)
        step_lines = []
        trace_ok = True
        for idx, step in enumerate(trace["steps"]):
            total_steps += 1
            verdict, error = evaluate_step(trace_id, idx, step, state)
            if error is not None:
                status, msg = error
                step_lines.append(f"  step {idx} [{step['actor']} {step['op']}]: {status} -- {msg}")
                trace_ok = False
                total_failed_steps += 1
                continue
            problems = compare(step["expect"], step["effect"], verdict)
            if problems:
                trace_ok = False
                total_failed_steps += 1
                step_lines.append(f"  step {idx} [{step['actor']} {step['op']}]: FAIL")
                for p in problems:
                    step_lines.append(f"      - {p}")
                step_lines.append(f"      source: {verdict.cite}")
            else:
                step_lines.append(f"  step {idx} [{step['actor']} {step['op']}]: PASS "
                                   f"(outcome={verdict.outcome}"
                                   + (f", refusal={verdict.refusal}" if verdict.refusal else "")
                                   + f") -- {verdict.cite}")
        trace_results.append((trace_id, trace_ok, step_lines))

    print(f"session-operation-trace.json: {len(data['traces'])} traces, {total_steps} steps\n")
    for trace_id, trace_ok, step_lines in trace_results:
        print(f"TRACE {trace_id}: {'PASS' if trace_ok else 'FAIL'}")
        for line in step_lines:
            print(line)
        print()

    print(f"SUMMARY: {total_steps - total_failed_steps}/{total_steps} steps passed, "
          f"{total_failed_steps} failed, across {len(trace_results)} traces")

    failed_ordinary = [t for t, ok, _ in trace_results if not ok and not t.startswith("control-")]
    failed_controls = [t for t, ok, _ in trace_results if not ok and t.startswith("control-")]
    passed_controls = [t for t, ok, _ in trace_results if ok and t.startswith("control-")]

    print(f"Ordinary traces that FAILED (should be empty): {failed_ordinary}")
    print(f"Control traces that FAILED as required: {failed_controls}")
    if passed_controls:
        print(f"WARNING -- control traces that incorrectly PASSED: {passed_controls}")

    expected_controls = [t for t, _, _ in trace_results if t.startswith("control-")]
    return 0 if (not failed_ordinary and not passed_controls
                 and len(failed_controls) == len(expected_controls)) else 1


if __name__ == "__main__":
    sys.exit(main())
