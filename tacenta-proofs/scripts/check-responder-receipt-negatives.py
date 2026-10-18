#!/usr/bin/env python3
"""Hold the responder's first-receipt theorems against a planted fault.

`Translation/UnitLifecycleResponderFirstReceipt.lean` shows that, on the bytes the initiator's first `encrypt`
emits, `establish_responder` past the store's refusals returns exactly one of a non-contributory candidate
agreement, an AEAD refusal or what the open of the initiator's seal returns, and under two boundary laws returns
the initiator's plaintext with the committed store and one draw; the laws hold in one interpretation and one run
reaches the success.  A proof that Lean accepts after the fact it rests on is removed would hold nothing, so this
script makes one change to a copy of the module and requires Lean to refuse it, at a named place, with an error
that names what the change removed:

  * the auxiliary specification: the receiver's sparse chains not swapped against the sender's (refused in
    `first_receive_key`: the receiver steps the sender's receiving chain), the root relation dropped from the
    first receive (same place), the first header's sparse number 2 (same place: the receiver would have to
    skip and store a key), the decoder
    round trip without the codeword-length condition (refused in `decode_encodeMessage`), the model's success
    claimed to keep the oracle and the ratchet key claimed always replaced by the draw (refused in
    `first_frame_model_outcomes`);
  * the two laws: the AEAD law weakened to "opening returns" (refused in `aead_open_sealed`) and the contributory
    law weakened to "the agreement does not return `none`" (refused in `responder_candidate_agreement`);
  * the bridges: the responder's associated data claimed with the two identity keys in the other order (refused
    in `first_identityAd_eq`), the responder's classical root claimed to be the initiator's root after its
    derivation (refused in `first_init_pair`), the attributed source claimed to be the header without its MAC
    (refused in `first_receipt_run_inputs`, where `HonestChunk` asks for 96 bytes);
  * the outcomes: the non-contributory refusal claimed when the candidate agreement returns (refused in
    `responder_first_frame_inner_outcomes`);
  * the model step the composition rests on: a frame sealed under a caller-chosen message key instead of the first
    key of the sender's chains (refused in `first_frame_model_outcomes`, which decodes and opens the frame sealed
    under the key the receiver derives);
  * the composition chain: the responder's success claimed to return a caller-chosen plaintext (refused in
    `initiator_first_send_responder_receives`), the responder fed the plaintext instead of the bytes the first
    send returned (refused in `initiator_first_send_responder_receives`), the store claimed unchanged on the
    one-time path (refused in `responder_first_frame_succeeds`), the responder's draws claimed untouched on
    success (refused in `initiator_first_send_responder_receives`), the header source without its MAC (refused
    there too);
  * the joint model keeping the first-frame model's AEAD, whose seal returns the empty vector (refused in
    `modelFirstReceipt_aeadRoundTrip`);
  * the contributory law with its premise dropped, the module's pins kept (refused at the pin of
    `DhAgreeContributoryShape`).

Every change is to a statement or a definition; none replaces a proof step.  Each refusal is a proof-breakage
check at a named place: it shows that the proof there depends on what the change removed (or, for the last, that
the pin holds the definition), not that the changed statement is false.  In particular the two controls on the
composition chain (a different plaintext claimed, the plaintext fed instead of the bytes) show that the composed
proof uses the plaintext and the bytes it names; the other-key control sits on the model step the composition rests
on and shows that step's proof uses the first key, not that the composition does.  No control covers the chain's own
key step (the initiator's message key rewritten to the first key and carried into the responder's frame premise):
planted there, a key change makes Lean exhaust its heartbeats unifying the two frames, which is not counted as a
refusal.  None of these is a proof that the responder refuses such inputs, which nothing here shows (no AEAD
authenticity law is assumed).

The changes are checked on a copy without the module's pins, so that the refusal comes from a proof and not
from a pin, except the one kept with its pins.  The unmodified copies must be accepted first.  A timeout, a
compiler that does not start, a syntax error, an unrelated failure and a refusal elsewhere than the named
place never count; an error whose first line names a kind of failure that is not a refusal (an unresolved
name, a syntax error) voids the run anywhere in the copy, compared without regard to case, and the script
checks at start that this guard fires on the toolchain's own `Unknown identifier`.  These are controls on
copies of the Lean; no source, olean or git state changes.

Dependencies must be built (`lake build Translation.UnitLifecycleResponderFirstFrame`).
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / 'translation/Translation/UnitLifecycleResponderFirstReceipt.lean'

CONTRIB_DEF = ('    ∃ x, I.dhPrivAgree a pb = ok (some x)\n',
               '    I.dhPrivAgree a pb ≠ ok none\n')
CONTRIB_IS = ('      ∃ x, tacenta_boundary.dh.PrivateKey.agree a pb = ok (some x) := Iff.rfl\n',
              '      tacenta_boundary.dh.PrivateKey.agree a pb ≠ ok none := Iff.rfl\n')
CONTRIB_NOPREMISE_DEF = ('  ∀ (a b : I.PrivateKey) (pb : I.PublicKeyBytes), I.dhPrivPublicKey b = ok pb →\n'
                         '    ∃ x, I.dhPrivAgree a pb = ok (some x)\n',
                         '  ∀ (a b : I.PrivateKey) (pb : I.PublicKeyBytes),\n'
                         '    ∃ x, I.dhPrivAgree a pb = ok (some x)\n')
CONTRIB_NOPREMISE_IS = ('      tacenta_boundary.dh.PrivateKey.public_key b = ok pb →\n'
                        '      ∃ x, tacenta_boundary.dh.PrivateKey.agree a pb = ok (some x) := Iff.rfl\n',
                        '      ∃ x, tacenta_boundary.dh.PrivateKey.agree a pb = ok (some x) := Iff.rfl\n')

OUTCOMES_STATEMENT = (
    'theorem first_frame_model_outcomes (viewA viewB : Model.Lifecycle.CodewordView)\n'
    '    (oracleA oracleB : Model.Lifecycle.Oracle) (mA mB : Model.Lifecycle.Session)\n'
    '    (a4 peer b rkA cksA prk k1 k2 ec : Model.State.Key) (secret pt : Model.Lifecycle.Bytes)\n'
    '    (chunk : Model.Braid.Chunk) (d : Model.State.Key)\n'
    '    (hA : mA.triple = firstSenderTriple a4 peer rkA cksA prk k1 k2)\n'
    '    (hB : mB.triple = firstReceiverTriple b ec prk k1 k2)\n'
    '    (hkdf : Model.State.kdfRk ec d .tacenta = (rkA, cksA))\n'
    '    (hbraid : mB.braid = Model.Braid.initBob secret)\n'
    '    (had : mB.identityAd = mA.identityAd)\n'
    '    (hlen : a4.length = 32) (hkey : Model.Messages.checkKey a4 = some ())\n'
    '    (hchunk : (viewA.send mA.braid chunk).data.length = 32)\n'
    '    (hagree : oracleB.dhAgree mB.ratchetPrivate a4 = some d) :\n'
    '    (oracleB.draws = [] ∧\n'
    '      Model.Lifecycle.decryptRatchet viewB oracleB mB (firstFrame viewA oracleA mA pt (firstKey cksA k1) chunk) =\n'
    '        { session := mB, result := .error .ceiling, oracle := oracleB }) ∨\n'
    '    (∃ c rest, oracleB.draws = c :: rest ∧ oracleB.dhAgree c a4 = none ∧\n'
    '      Model.Lifecycle.decryptRatchet viewB oracleB mB (firstFrame viewA oracleA mA pt (firstKey cksA k1) chunk) =\n'
    '        { session := mB, result := .error (.handshake .nonContributoryAgreement),\n'
    '          oracle := { oracleB with draws := rest } }) ∨\n'
    '    (∃ c rest dSend, oracleB.draws = c :: rest ∧ oracleB.dhAgree c a4 = some dSend ∧\n'
    '      firstOpen oracleA oracleB (firstKey cksA k1) pt (firstAd viewA mA chunk) = none ∧\n'
    '      Model.Lifecycle.decryptRatchet viewB oracleB mB (firstFrame viewA oracleA mA pt (firstKey cksA k1) chunk) =\n'
    '        { session := mB, result := .error .aead, oracle := { oracleB with draws := rest } }) ∨\n'
    '    (∃ c rest dSend x, oracleB.draws = c :: rest ∧ oracleB.dhAgree c a4 = some dSend ∧\n'
    '      firstOpen oracleA oracleB (firstKey cksA k1) pt (firstAd viewA mA chunk) = some x ∧\n'
    '      Model.Lifecycle.decryptRatchet viewB oracleB mB (firstFrame viewA oracleA mA pt (firstKey cksA k1) chunk) =\n'
    '        { session := firstReceiptSession mB secret\n'
    '            (viewB.receive mB.braid (viewA.send mA.braid chunk).index (viewA.send mA.braid chunk).data)\n'
    '            ec prk k1 k2 a4 d dSend (oracleB.dhPublic c) c\n'
    '          result := .ok x\n'
    '          oracle := { oracleB with draws := rest } }) := by\n'
)

HEADLINE_SUCCESS = ('        lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =\n'
                    '          ok (core.result.Result.Ok (sB\', ptB), storeB\', rngB\') ∧\n'
                    '        ptB.val = plaintext.val ∧ traceB rngB\' = restB ∧\n'
                    '        ResponderCommit storeB bundleA.kem_prekey_id')

# (copy, name, [(old text, new text), ...] each occurring exactly once, a regular expression the refused
#  output must contain, where the refusal must be: declarations one of whose lines holds an error, or
#  ('pin', name) for the `#guard_msgs` line of the `#print` pin of `name`)
MUTANTS = [
    ('module', 'receiver-sparse-chains-not-swapped',
     [('      { rk := prk, epoch := 0, chains := [(0, { send := some ⟨k2, 0⟩, receive := some ⟨k1, 0⟩ })],\n',
       '      { rk := prk, epoch := 0, chains := [(0, { send := some ⟨k1, 0⟩, receive := some ⟨k2, 0⟩ })],\n')],
     r'⊢ k1 = k2 ∧\n\s+\(Model\.SparseRatchet\.kdfCk k2 1\)\.1 = \(Model\.SparseRatchet\.kdfCk k1 1\)\.1', ['first_receive_key']),
    ('module', 'first-receive-without-the-root-relation',
     [('theorem first_receive_key (b ec prk k1 k2 a4 d dSend newPub rkA cksA : Key)\n'
       '    (hkdf : Model.State.kdfRk ec d .tacenta = (rkA, cksA)) :\n',
       'theorem first_receive_key (b ec prk k1 k2 a4 d dSend newPub rkA cksA : Key)\n'
       '    (hkdf : True) :\n')],
     r'Model\.TripleRatchet\.combine \(Model\.State\.kdfCk \(Model\.State\.kdfRk ec d Model\.State\.LabelSet\.tacenta\)\.2\)\.2[\s\S]*=\s+Model\.TripleRatchet\.combine \(Model\.State\.kdfCk cksA\)\.2', ['first_receive_key']),
    ('module', 'first-header-sparse-number-two',
     [('def firstHeader (a4 : Key) : Model.Triple.Header := ⟨⟨a4, 0, 0⟩, 0, 1⟩\n',
       'def firstHeader (a4 : Key) : Model.Triple.Header := ⟨⟨a4, 0, 0⟩, 0, 2⟩\n')],
     r'Model\.SparseRatchet\.maxSkippedStore ≤\s+\(Model\.SparseRatchet\.skipSurvivors', ['first_receive_key']),
    ('module', 'decode-without-the-codeword-length',
     [('    (hc : ∀ c, h.agChunk = some c → c.data.length = 32) :\n',
       '    (hc : True) :\n')],
     r'Function expected at\n  hc\nbut this term has type\n  True', ['decode_encodeMessage']),
    ('module', 'model-success-keeps-the-oracle',
     [('          result := .ok x\n          oracle := { oracleB with draws := rest } }) := by\n',
       '          result := .ok x\n          oracle := oracleB }) := by\n')],
     r'sigVerify := oracleB\.sigVerify, sigSign := oracleB\.sigSign \} =\n    oracleB', ['first_frame_model_outcomes']),
    ('module', 'ratchet-key-always-the-draw',
     [('    ratchetPrivate := if newPub == mB.triple.classical.dhsPub then mB.ratchetPrivate else c }\n',
       '    ratchetPrivate := c }\n')],
     r'⊢ oracleB\.dhPublic c = b → mB\.ratchetPrivate = c', ['first_frame_model_outcomes']),
    ('module', 'aead-law-only-opening-returns',
     [('    ∃ v, I.aeadDecrypt k1 k2 iv (alloc.vec.Vec.deref ct) ad = ok (core.result.Result.Ok v) ∧ v.val = pt.val\n',
       '    ∃ v, I.aeadDecrypt k1 k2 iv (alloc.vec.Vec.deref ct) ad = ok v\n'),
      ('        ok (core.result.Result.Ok v) ∧ v.val = pt.val := Iff.rfl\n',
       '        ok v := Iff.rfl\n')],
     r'Dependent elimination failed: Failed to solve equation\n  ok v = tacenta_boundary\.aead\.decrypt K1 K2 IV ct\.deref A', ['aead_open_sealed']),
    ('module', 'contributory-law-only-agreement-returns', [CONTRIB_DEF, CONTRIB_IS],
     r'`x✝ : k\.agree q\.ratchetPublic = ok none → False` is not an inductive datatype', ['responder_candidate_agreement']),
    ('module', 'associated-data-in-the-other-order',
     [('    (hpi : p.peerIdentity = q.ourPublic) (hop : p.ourPublic = bundle.bundle.identity_key) :\n',
       '    (hpi : p.peerIdentity = bundle.bundle.identity_key) (hop : p.ourPublic = q.ourPublic) :\n')],
     r'Did not find an occurrence of the pattern\n  lifecycle\.identity_ad q\.ourPublic bundle\.bundle\.identity_key\nin the target expression\n  lifecycle\.identity_ad bundle\.bundle\.identity_key q\.ourPublic', ['first_identityAd_eq']),
    ('module', 'responder-root-claimed-the-derived-root',
     [('      t = responderTriple b ec prk c1 c2 := by\n',
       '      t = responderTriple b rk prk c1 c2 := by\n')],
     r"⊢ ec = rk'", ['first_init_pair']),
    ('module', 'attributed-source-without-the-mac',
     [('    (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize) (c : tacenta_erasure.Chunk)\n'
       '    (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)\n'
       '    (hsend : view.send mA.braid (modelChunkOf src c) = modelCodewordOf c)\n',
       '    (hsrc : src.length = Model.Braid.headerSize) (c : tacenta_erasure.Chunk)\n'
       '    (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)\n'
       '    (hsend : view.send mA.braid (modelChunkOf src c) = modelCodewordOf c)\n')],
     r'hsrc\n has type\n  List\.length src = Model\.Braid\.headerSize\nbut is expected to have type\n  List\.length src = Model\.Braid\.headerSize \+ Model\.Braid\.macSize', ['first_receipt_run_inputs']),
    ('module', 'non-contributory-claimed-when-the-agreement-returns',
     [('      ((inner.1 = core.result.Result.Err (lifecycle.Error.Handshake SessionError.NonContributoryAgreement) ∧\n'
       '          oracleB.dhAgree dB (arrayOf q.ratchetBytes) = none) ∨\n',
       '      ((inner.1 = core.result.Result.Err (lifecycle.Error.Handshake SessionError.NonContributoryAgreement) ∧\n'
       '          oracleB.dhAgree dB (arrayOf q.ratchetBytes) ≠ none) ∨\n')],
     r'hnone\nhas type\n  oracleB\.dhAgree dB \(arrayOf q\.ratchetBytes\) = none\nbut is expected to have type\n  oracleB\.dhAgree dB \(arrayOf q\.ratchetBytes\) ≠ none', ['responder_first_frame_inner_outcomes']),
    ('module', 'responder-claimed-another-plaintext',
     [('    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)\n'
       '    (rng : R) (htrace : trace rng = oracle.draws) (d1 d2 : Model.Lifecycle.Key)\n'
       '    (rest : List Model.Lifecycle.Key) (hdraws : trace rng = d1 :: d2 :: rest)\n'
       '    (bytes : alloc.vec.Vec Std.U8) (s\' : lifecycle.Session) (rng\' : R)\n'
       '    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok bytes, s\', rng\'))\n'
       '    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)\n'
       '    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)\n'
       '    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)\n',
       '    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)\n'
       '    (rng : R) (htrace : trace rng = oracle.draws) (d1 d2 : Model.Lifecycle.Key)\n'
       '    (rest : List Model.Lifecycle.Key) (hdraws : trace rng = d1 :: d2 :: rest)\n'
       '    (bytes : alloc.vec.Vec Std.U8) (s\' : lifecycle.Session) (rng\' : R)\n'
       '    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok bytes, s\', rng\'))\n'
       '    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)\n'
       '    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)\n'
       '    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)\n'
       '    (plaintext2 : Slice Std.U8)\n'),
      (HEADLINE_SUCCESS, HEADLINE_SUCCESS.replace('ptB.val = plaintext.val', 'ptB.val = plaintext2.val'))],
     r'but is expected to have type[\s\S]*↑ptB = ↑plaintext2 ∧', ['initiator_first_send_responder_receives']),
    ('module', 'frame-sealed-under-another-key',
     [(OUTCOMES_STATEMENT, OUTCOMES_STATEMENT.replace('(chunk : Model.Braid.Chunk) (d : Model.State.Key)', '(chunk : Model.Braid.Chunk) (d : Model.State.Key) (mk\' : Model.State.Key)').replace('(firstFrame viewA oracleA mA pt (firstKey cksA k1) chunk)', '(firstFrame viewA oracleA mA pt mk\' chunk)'))],
     r'Did not find an occurrence of the pattern\n  Model\.CompositeHeader\.decodeDetailed \(firstFrame viewA oracleA mA pt \(firstKey cksA k1\) chunk\)\nin the target expression\n  \(match Model\.CompositeHeader\.decodeDetailed \(firstFrame viewA oracleA mA pt mk\' chunk\)', ['first_frame_model_outcomes']),
    ('module', 'responder-fed-the-plaintext-not-the-sent-bytes',
     [(HEADLINE_SUCCESS, HEADLINE_SUCCESS.replace('(alloc.vec.Vec.deref bytes)', 'plaintext')),
      ('      ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)\n'
       '        (dSend : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes) (ptB : alloc.vec.Vec U8)\n',
       '      ∃ (p : ResponderPreparedParts ourB storeB plaintext) (ec : Array U8 32#usize)\n'
       '        (dSend : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes) (ptB : alloc.vec.Vec U8)\n')],
     r'ResponderPreparedParts ourB storeB bytes\.deref\nbut is expected to have type\n  ResponderPreparedParts ourB storeB plaintext', ['initiator_first_send_responder_receives']),
    ('module', 'store-claimed-unchanged-on-the-one-time-path',
     [('        ResponderCommit storeB bundle.kem_prekey_id bundle.one_time_prekey_id p.lastResort p.replay storeB\' ∧\n'
       '        (p.lastResort = false → p.replay = none) ∧\n',
       '        ResponderCommit storeB bundle.kem_prekey_id bundle.one_time_prekey_id p.lastResort p.replay storeB\' ∧\n'
       '        (p.lastResort = false → storeB\' = storeB) ∧\n')],
     r'hrep\.left\nhas type\n  p\.lastResort = false → p\.replay = none\nbut is expected to have type\n  p\.lastResort = false → storeB\' = storeB', ['responder_first_frame_succeeds']),
    ('module', 'responder-draws-claimed-untouched',
     [(HEADLINE_SUCCESS, HEADLINE_SUCCESS.replace("traceB rngB' = restB", "traceB rngB' = traceB rngB"))],
     r'but is expected to have type[\s\S]*traceB rngB\' = traceB rngB ∧', ['initiator_first_send_responder_receives']),
    ('module', 'header-source-without-the-mac',
     [('  (ekSeed ++ K.hashEk ekSeed ekVector) ++ a.macHdr 1 (ekSeed ++ K.hashEk ekSeed ekVector)\n',
       '  (ekSeed ++ K.hashEk ekSeed ekVector)\n')],
     r'Tactic `rfl` failed: The left-hand side[\s\S]*\(SessionUnitBraidT3\.AuthOf q\.auth\)\.macHdr 1[\s\S]*is not definitionally equal to the right-hand side\n  \{ source := headerSource', ['initiator_first_send_responder_receives']),
    ('module', 'joint-model-keeps-the-empty-seal',
     [('  { Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame with\n'
       '    aeadEncrypt := fun _ _ _ p _ => ok (Tacenta.UnitOracleModel.sealModel p)\n'
       '    aeadDecrypt := fun _ _ _ c _ => ok (Tacenta.UnitOracleModel.openModel c) }\n',
       '  { Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame with\n'
       '    aeadDecrypt := fun _ _ _ c _ => ok (Tacenta.UnitOracleModel.openModel c) }\n')],
     r'Tactic `subst` failed[\s\S]*UnitLifecycleResponderFirstFrame\.Interp\.modelFirstFrame\.aeadEncrypt k1 k2 iv pt ad = ok ct', ['modelFirstReceipt_aeadRoundTrip']),
    ('pinned', 'contributory-law-without-its-premise-pinned', [CONTRIB_NOPREMISE_DEF, CONTRIB_NOPREMISE_IS],
     r'Docstring on `#guard_msgs` does not match generated message',
     ('pin', 'Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape')),
]

NOT_A_REFUSAL = ('unknown identifier', 'unknown constant', 'unexpected token', "expected '",
                 'unknown namespace', 'does not contain')


# Lean capitalises its error messages (`Unknown identifier`, `Unknown constant`, `Function expected`), so the
# guard is matched case-insensitively, on the first line of each error, where Lean names the kind of failure.
ERROR_HEAD = re.compile(r'^\S+\.lean:\d+:\d+: error(?:\([^)]*\))?: (.*)$', re.M)


def not_a_refusal(output, guards):
    """Whether an error of `output` is of a kind that is not a refusal (a name that does not resolve, a syntax
    error, ...), compared without regard to case."""
    heads = [head.lower() for head in ERROR_HEAD.findall(output)]
    return any(bad in head for head in heads for bad in guards)


def guard_self_test(guards):
    """The guard must fire on the toolchain's own spelling of an unresolved name."""
    sample = ("/tmp/x.lean:3:8: error(lean.unknownIdentifier): Unknown identifier `fooBar`\n"
              "/tmp/x.lean:4:2: error: unsolved goals\n")
    if not not_a_refusal(sample, guards):
        raise SystemExit('GUARD BROKEN: the not-a-refusal guard does not fire on `Unknown identifier`')


def run_lean(path, log, timeout):
    with log.open('w') as output:
        try:
            process = subprocess.Popen(
                ['lake', 'env', 'lean', str(path)], cwd=ROOT / 'translation',
                stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
            )
        except OSError as error:
            raise SystemExit(f'COMPILER LAUNCH FAILED (not a passing control): {error}')
        try:
            status = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait()
            raise SystemExit(f'TIMEOUT (not a passing control): {path.name}; see {log}')
    return status, log.read_text()


def without_pins(text, path):
    cut = text.find('\n/-! ## Pins')
    if cut < 0:
        raise SystemExit(f'no pin section found in {path.name}')
    return text[:cut] + '\n'


DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*'
                  r'(theorem|lemma|def|abbrev|structure|instance|inductive)\s+(\S+)')
COMMAND = re.compile(r'^(?:@\[|/--|/-!|#|theorem |lemma |def |abbrev |structure |instance |'
                     r'inductive |private |protected |noncomputable |set_option |attribute |open |'
                     r'namespace |section |end |variable )')


def declaration_lines(text, name):
    """The 1-based line range of the declaration `name` in `text` (its leading `set_option ... in`
    and doc comment excluded), or None."""
    lines = text.split('\n')
    for k, line in enumerate(lines):
        m = DECL.match(line)
        if m and (m.group(2) == name or m.group(2).endswith('.' + name)):
            end = k + 1
            while end < len(lines) and not COMMAND.match(lines[end]):
                end += 1
            return k + 1, end
    return None


def pin_line(text, name):
    """The 1-based line of the `#guard_msgs in` that precedes `#print name`, or None."""
    lines = text.split('\n')
    for k in range(1, len(lines)):
        if lines[k] == f'#print {name}' and lines[k - 1].startswith('#guard_msgs'):
            return k
    return None


ERROR_AT = re.compile(r'^\S+\.lean:(\d+):\d+: error', re.M)


def check_refused(name, status, output, marker, log, mutated, where):
    refused = (status != 0 and 'error' in output and re.search(marker, output)
               and not not_a_refusal(output, NOT_A_REFUSAL))
    if not refused:
        raise SystemExit(f'FAILED control {name}: expected Lean to refuse it with `{marker}`, '
                         f'exit={status}; {log}')
    errors = {int(n) for n in ERROR_AT.findall(output)}
    if isinstance(where, tuple):
        line = pin_line(mutated, where[1])
        if line is None:
            raise SystemExit(f'FAILED control {name}: the copy has no `#print {where[1]}` pin, so '
                             f'its refusal cannot be the pin\'s; {log}')
        if line not in errors:
            raise SystemExit(f'FAILED control {name}: refused, but not at the pin of {where[1]} '
                             f'(line {line}); {log}')
        return f'the pin of {where[1]}'
    for decl in where:
        span = declaration_lines(mutated, decl)
        if span is None:
            raise SystemExit(f'Target changed for {name}: no declaration {decl} in the copy')
        if any(span[0] <= e <= span[1] for e in errors):
            return decl
    raise SystemExit(f'FAILED control {name}: refused, but in none of {", ".join(where)}; {log}')


def main():
    guard_self_test(NOT_A_REFUSAL)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-dir', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    logs = args.log_dir or Path(tempfile.mkdtemp(prefix='responder-receipt-logs-'))
    logs.mkdir(parents=True, exist_ok=True)
    module = MODULE.read_text()
    sources = {
        'module': without_pins(module, MODULE),
        'pinned': module,
    }
    results = {
        'module_sha256': hashlib.sha256(module.encode()).hexdigest(),
        'accepted': [], 'rejected': {},
    }
    with tempfile.TemporaryDirectory(prefix='responder-receipt-controls-') as tmp:
        tmp = Path(tmp)
        for label, text in sources.items():
            path = tmp / f'baseline_{label}.lean'
            path.write_text(text)
            status, output = run_lean(path, logs / f'baseline_{label}.log', args.timeout)
            if status or 'sorry' in output or 'error' in output:
                raise SystemExit(f'BASELINE FAILED for the {label} copy; no mutation evidence: '
                                 f'{logs / f"baseline_{label}.log"}')
            results['accepted'].append(label)
            print(f'PASS: the unmodified {label} copy is accepted', flush=True)
        for label, name, edits, marker, where in MUTANTS:
            source = sources[label]
            mutated = source
            for old, new in edits:
                found = mutated.count(old)
                if found != 1:
                    raise SystemExit(f'Target changed for {name}: expected 1 occurrence of the '
                                     f'text in the {label} copy, found {found}')
                mutated = mutated.replace(old, new, 1)
            assert mutated != source
            path = tmp / f'{label}_{name}.lean'
            path.write_text(mutated)
            log = logs / f'{label}_{name}.log'
            status, output = run_lean(path, log, args.timeout)
            place = check_refused(name, status, output, marker, log, mutated, where)
            results['rejected'][f'{label}/{name}'] = {'exit': status, 'marker': marker, 'at': place}
            print(f'PASS: {label}/{name} refused by Lean in {place}', flush=True)
    (logs / 'result.json').write_text(json.dumps(results, indent=2) + '\n')
    print(f'{len(results["accepted"])} unmodified copies accepted, {len(results["rejected"])} changes '
          f'refused at their named places; logs: {logs}', flush=True)


if __name__ == '__main__':
    sys.exit(main())
