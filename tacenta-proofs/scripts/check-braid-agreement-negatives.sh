#!/usr/bin/env bash
# Hold the evidence about the Braid refinement agreements of the Session unit to mutations.
#
# Four modules carry that evidence:
#
#   UnitSatisfiabilityBraidAgreements.lean  the six KEM and KDF agreements and the law `TruncatePrefix` as
#                                           shapes over an interpretation, each bound to the real predicate
#                                           by `Iff.rfl`, and one interpretation that satisfies all of them
#                                           with the axiom-level shapes of the session records.
#   UnitSatisfiabilityErasureAgrees.lean    `ErasureCloneAgrees` and the encoder clause of `ErasureAgrees`.
#   UnitSatisfiabilityBraidStates.lean      witnesses for the state-level hypotheses of the four refinement
#                                           theorems, at all twelve state constructors and at the states the
#                                           real constructors build.
#   UnitBraidEntryPoints.lean               the two entry points with the defined-function hypotheses
#                                           discharged.
#   UnitErasureRs*.lean                     the Reed-Solomon proof that the translated erasure coder
#                                           refines the model (`ErasureAgrees`).
#
# Each case below applies ONE change to a copy of a module and requires `lake env lean` to fail. Where a
# theorem is named, the failure must be an error inside that theorem (a bridge that is no longer
# `Iff.rfl`, a witness that no longer builds); where a pin is named, the failure must be the pin's own
# mismatch. The unmodified copy must pass first: a refusal is only evidence if acceptance is possible. A copy
# that fails because the build is missing (no olean, unknown module) is not a refusal and is reported as a
# failure of this script. The modules the copies import must be built (`lake build`).
#
# The groups:
#   bridges     a shape changed by one constant, premise or conjunct, so that its `Iff.rfl` bridge to the real
#               predicate is rejected. The aggregate theorem must name every `_is` bridge of the module.
#   model       the interpretation changed so that one agreement breaks, and the width fact it rests on
#               changed so that it is false at 32 bits.
#   witnesses   a state witness changed so that one state-level hypothesis breaks, and the definitions the
#               state theorems are stated through weakened.
#   statements  a pinned statement weakened, so that the `#guard_msgs` pin refuses it.
#   entry       an entry point restated with a premise dropped.
#   rs          the Reed-Solomon proof of the unit's `ErasureAgrees`: a specification function changed,
#               so that the module proving a kernel statement about it must refuse; a statement of
#               the proof plan changed, so that the module that proves it must refuse; the decoder
#               invariant changed, so that the glue must refuse.
set -euo pipefail

cd "$(dirname "$0")/.."
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT INT TERM

TMP="$tmp" python3 - <<'PY'
import os, re, subprocess, sys

tmp = os.environ["TMP"]
translation = "translation"
base = os.path.join(translation, "Translation")


def read(name):
    return open(os.path.join(base, name + ".lean")).read()


agree = read("UnitSatisfiabilityBraidAgreements")
erasure = read("UnitSatisfiabilityErasureAgrees")
states = read("UnitSatisfiabilityBraidStates")
entry = read("UnitBraidEntryPoints")
rs_defs = read("UnitErasureRsDefs")
rs_kernel = read("UnitErasureRsKernel")
rs_stmts = read("UnitErasureRsStatements")
rs_glue = read("UnitErasureRsGlue")

FIRST_ONLY = {"erasure-clause-encoder-of-the-empty-message", "statement-entry-adds-a-premise"}
INFRA = ("object file", "unknown module prefix", "no such file", "could not find",
         "unknown package", "failed to read file")
PIN_MISMATCH = "does not match generated message"
ANY = "any error"
FILTER = os.environ.get("BRAIDNEG_FILTER", "")
cases = 0
accepted = 0
wrong = []


def run(text):
    path = os.path.join(tmp, "case.lean")
    with open(path, "w") as f:
        f.write(text)
    p = subprocess.run(["lake", "env", "lean", path], cwd=translation,
                       capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def infra(out):
    low = out.lower()
    return any(s in low for s in INFRA)


RESOURCE = ("heartbeats", "maximum recursion depth", "timeout", "out of memory")


def errors(out):
    """(line, first line of the message) of every error, in the order Lean printed them."""
    return [(int(m.group(1)), m.group(2)) for m in
            re.finditer(r"case\.lean:(\d+):\d+: error[^:]*: ([^\n]*)", out)]


def region(text, name):
    """First and last line (1-based) of the declaration `name` in the module text."""
    lines = text.split("\n")
    starts = [i for i, l in enumerate(lines)
              if re.match(r"(?:private |noncomputable )?(?:theorem|def|structure) " + re.escape(name) + r"\b", l)]
    if len(starts) != 1:
        return None
    start = starts[0]
    end = len(lines)
    for j in range(start + 1, len(lines)):
        if re.match(r"(?:/--|/-!|theorem |def |noncomputable def |private |structure |end |namespace |open )", lines[j]):
            end = j
            break
    return start + 1, end


def passes(name, text):
    global cases, accepted
    if FILTER and FILTER not in name:
        return
    cases += 1
    accepted += 1
    rc, out = run(text)
    if rc != 0 or infra(out):
        wrong.append(f"{name}: expected acceptance, was refused:\n{out[:1500]}")


def refused(name, text, where):
    if FILTER and FILTER not in name:
        return
    """`where` is a theorem or definition of the unmutated module whose body must contain an error, or
    the string PIN_MISMATCH."""
    global cases
    cases += 1
    rc, out = run(text)
    if rc == 0:
        wrong.append(f"{name}: expected a refusal in {where}, was accepted")
        return
    if infra(out):
        wrong.append(f"{name}: failed because the build is missing, not as a refusal:\n{out[:600]}")
        return
    if where == PIN_MISMATCH:
        if PIN_MISMATCH not in out:
            wrong.append(f"{name}: refused, but not by a pin:\n{out[:1200]}")
        return
    if where == ANY:
        errs = [m for _, m in errors(out)]
        if not errs or all(any(k in m.lower() for k in RESOURCE) for m in errs):
            wrong.append(f"{name}: refused only by a resource limit or without an error:\n{out[:600]}")
        elif os.environ.get("BRAIDNEG_VERBOSE"):
            print(f"  {name}: {errs[0][:140]}")
        return
    r = region(text, where)
    if r is None:
        wrong.append(f"{name}: cannot locate {where} in the mutated text")
        return
    inside = [(e, m) for e, m in errors(out) if r[0] <= e <= r[1]]
    if not inside:
        wrong.append(f"{name}: refused, but not inside {where} (lines {r[0]}-{r[1]}, errors at {[e for e, _ in errors(out)]}):\n{out[:1200]}")
    elif all(any(k in m.lower() for k in RESOURCE) for _, m in inside):
        wrong.append(f"{name}: refused only by a resource limit inside {where}, which is not a refusal: {inside[0][1]}")
    elif os.environ.get("BRAIDNEG_VERBOSE"):
        print(f"  {name}: {inside[0][1][:140]}")


_LEAN_PATH = []


def lean_path():
    if not _LEAN_PATH:
        p = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=translation,
                           capture_output=True, text=True)
        _LEAN_PATH.append(p.stdout.strip())
    return _LEAN_PATH[0]


def refused_through(name, dep_name, dep_text, text, why):
    """Mutate the module `dep_name`, build its olean in a scratch directory that shadows the built one,
    and require `text` (an unmodified dependent) to be refused."""
    global cases
    if FILTER and FILTER not in name:
        return
    cases += 1
    odir = os.path.join(tmp, "o_" + name)
    os.makedirs(os.path.join(odir, "Translation"), exist_ok=True)
    # The scratch directory holds a `Translation` directory, and Lean resolves every `Translation.*`
    # module from the first search-path entry that has one, so the built oleans are linked into it.
    built = os.path.abspath(os.path.join(translation, ".lake", "build", "lib", "lean", "Translation"))
    for fn in os.listdir(built):
        if fn.endswith(".olean") and fn != dep_name + ".olean":
            os.symlink(os.path.join(built, fn), os.path.join(odir, "Translation", fn))
    dep = os.path.join(tmp, dep_name + ".lean")
    with open(dep, "w") as f:
        f.write(dep_text)
    lp = odir + ":" + lean_path()
    env = dict(os.environ, LEAN_PATH=lp)
    r = subprocess.run(["lean", "--root=" + tmp, "-o", os.path.join(odir, "Translation", dep_name + ".olean"), dep],
                       cwd=translation, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        wrong.append(f"{name}: the mutated {dep_name} does not compile, so the case tests nothing:\n{(r.stdout + r.stderr)[:600]}")
        return
    path = os.path.join(tmp, "case_dependent.lean")
    with open(path, "w") as f:
        f.write(text)
    r = subprocess.run(["lean", path], cwd=translation, capture_output=True, text=True, env=env)
    out = r.stdout + r.stderr
    if r.returncode == 0:
        wrong.append(f"{name}: the dependent module was accepted ({why})")
    elif infra(out):
        wrong.append(f"{name}: failed because the build is missing, not as a refusal:\n{out[:600]}")
    else:
        errs = [m for m in re.findall(r"case_dependent\.lean:\d+:\d+: error[^:]*: ([^\n]*)", out)]
        if not errs or all(any(k in m.lower() for k in RESOURCE) for m in errs):
            wrong.append(f"{name}: refused only by a resource limit or without an error ({why}):\n{out[:600]}")
        elif os.environ.get("BRAIDNEG_VERBOSE"):
            print(f"  {name}: {errs[0][:140]}")


def once(text, old, new, what):
    # a pin's docstring repeats a statement, so a statement is changed at its first occurrence only
    if what in FIRST_ONLY and text.count(old) >= 1:
        return text.replace(old, new, 1)
    if text.count(old) != 1:
        wrong.append(f"{what}: the text to change occurs {text.count(old)} times, expected once")
        return None
    return text.replace(old, new)


# ------------------------------------------------------------- the first module
passes("agreements-unmodified", agree)

# the aggregate names every `_is` bridge
bridges = set(re.findall(r"^theorem (\w+_is)\b", agree, re.M))
agg = re.search(r"theorem braid_agreement_shapes_are_predicates :.*?:=\s*⟨(.*?)⟩\s*\n", agree, re.S)
named = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", agg.group(1))) if agg else set()
for b in sorted(bridges - named):
    wrong.append(f"bridge {b} is declared but braid_agreement_shapes_are_predicates does not name it")
if len(bridges) != 7:
    wrong.append(f"the module declares {len(bridges)} `_is` bridges, expected 7: {sorted(bridges)}")

controls = [
    # bridges: one constant, premise or conjunct changed, so the shape is not the predicate
    ("bridge-kemlen-swaps-ct1-and-ct2",
     "(∃ v, I.CT1_LEN = ok v ∧ v.val = K.ct1Size)", "(∃ v, I.CT1_LEN = ok v ∧ v.val = K.ct2Size)",
     "KemLenAgrees_is"),
    ("bridge-kemagrees-drops-the-rngtotal-premise",
     "      Tacenta.SessionUnitBraidT1.RngTotal rc →\n      ∃ kp rng' rand,", "      ∃ kp rng' rand,",
     "KemAgreesFor_is"),
    ("bridge-kemagrees-header-loses-the-hash",
     "vecOf h = (K.keyGen rand).2.1 ++ K.hashEk (K.keyGen rand).2.1 (K.keyGen rand).2.2)",
     "vecOf h = (K.keyGen rand).2.1)", "KemAgreesFor_is"),
    ("bridge-validateek-flips-the-verdict",
     "(r = true ↔ K.hashEk ekSeed (sliceOf ekVector) = hek)", "(r = false ↔ K.hashEk ekSeed (sliceOf ekVector) = hek)",
     "ValidateEkAgrees_is"),
    ("bridge-validateek-drops-the-seed-length-premise",
     "    ekSeed.length = 32 → hek.length = 32 → ekVector.length = K.ekSize →\n    sliceOf header = ekSeed ++ hek →\n    ∃ r, I.validateEk",
     "    hek.length = 32 → ekVector.length = K.ekSize →\n    sliceOf header = ekSeed ++ hek →\n    ∃ r, I.validateEk",
     "ValidateEkAgrees_is"),
    ("bridge-kemclone-drops-the-ek-vector-clause",
     "    (∀ v, I.ikpEkVector kp = ok v → I.ikpEkVector kp' = ok v) ∧\n", "", "KemCloneAgrees_is"),
    ("bridge-hkdf-drops-the-8160-premise",
     "  ∀ (N : Usize) (salt ikm info : Slice Std.U8), N.val ≤ 8160 →\n    ∃ r, I.hkdfSha256",
     "  ∀ (N : Usize) (salt ikm info : Slice Std.U8),\n    ∃ r, I.hkdfSha256", "BraidHkdfAgrees_is"),
    ("bridge-hmac-swaps-key-and-data",
     "    ∃ r, I.hmacSha256 key data = ok r ∧\n      keyOf r = Model.Kdf.hmac (sliceOf key) (sliceOf data)",
     "    ∃ r, I.hmacSha256 data key = ok r ∧\n      keyOf r = Model.Kdf.hmac (sliceOf key) (sliceOf data)", "BraidHmacAgrees_is"),
    ("bridge-truncate-prefix-takes-the-suffix",
     "    I.vecTruncate Global v n = ok v' ∧ v'.val = v.val.take n.val",
     "    I.vecTruncate Global v n = ok v' ∧ v'.val = v.val.drop n.val", "TruncatePrefix_is"),
    # the model: one field broken
    ("model-header-len-is-63", "    HEADER_LEN := ok 64#usize", "    HEADER_LEN := ok 63#usize", "modelT3_kemLen"),
    ("model-kdf-returns-zeros",
     "def hkdfImpl (N : Usize) (salt ikm info : Slice Std.U8) : Array Std.U8 N :=\n  ⟨(Model.Kdf.hkdf (sliceOf salt) (sliceOf ikm) (sliceOf info) N.val).map toU8,\n    by simp [Model.Kdf.hkdf_length]⟩",
     "def hkdfImpl (N : Usize) (salt ikm info : Slice Std.U8) : Array Std.U8 N :=\n  ⟨(List.replicate N.val (0 : UInt8)).map toU8, by simp⟩",
     "modelT3_hkdfAgrees"),
    ("model-validate-ek-always-true",
     "    validateEk := fun header ekVector =>\n      ok (decide (Model.Braid.toyKem.hashEk ((sliceOf header).take 32) (sliceOf ekVector)\n        = (sliceOf header).drop 32)) }",
     "    validateEk := fun header ekVector => ok true }", "modelT3_validateEk"),
    ("model-decapsulates-to-the-wrong-secret",
     "    ikpDecapsulate := fun r _ _ => ok (core.result.Result.Ok (arr32 (seedOf r)))",
     "    ikpDecapsulate := fun r _ _ => ok (core.result.Result.Ok (arr32 (seedOf (r + 1))))", "modelT3_kemAgrees"),
    ("model-encapsulate2-returns-40-bytes",
     "ok (core.result.Result.Ok (vecOfBytes (List.replicate 32 9) (by simp; exact le32)))",
     "ok (core.result.Result.Ok (vecOfBytes (List.replicate 40 9) (by simp; exact usize_max_ge 40 (by norm_num))))",
     "modelT3_kemAgrees"),
    # the width fact every witness rests on, made false at 32 bits
    ("width-fact-claims-2-to-the-33", "theorem usize_max_ge (n : ℕ) (h : n ≤ 2 ^ 32 - 1) : n ≤ Usize.max := by",
     "theorem usize_max_ge (n : ℕ) (h : n ≤ 2 ^ 33 - 1) : n ≤ Usize.max := by", "usize_max_ge"),
    # the model must satisfy the law, not only the agreements
    ("model-truncate-keeps-everything",
     "    HEADER_LEN := ok 64#usize\n", "    HEADER_LEN := ok 64#usize\n    vecTruncate := fun _ v _ => ok v\n", "modelT3_truncatePrefix"),
]
for name, old, new, where in controls:
    t = once(agree, old, new, name)
    if t is not None:
        refused(name, t, where)

# the statement pins refuse a weaker statement that keeps its proof
stmt = [
    ("statement-headline-drops-the-truncate-law",
     "      T3Agreements I K ∧ AllT1Shapes I ∧ StdLaws I ∧ TruncatePrefixShape I :=\n  ⟨Interp.modelT3, Model.Braid.toyKem, modelT3_t3, modelT3_allT1, modelT3_stdLaws,\n    modelT3_truncatePrefix⟩",
     "      T3Agreements I K ∧ AllT1Shapes I ∧ StdLaws I :=\n  ⟨Interp.modelT3, Model.Braid.toyKem, modelT3_t3, modelT3_allT1, modelT3_stdLaws⟩"),
    ("statement-headline-drops-the-agreements",
     "      T3Agreements I K ∧ AllT1Shapes I ∧ StdLaws I ∧ TruncatePrefixShape I :=\n  ⟨Interp.modelT3, Model.Braid.toyKem, modelT3_t3, modelT3_allT1, modelT3_stdLaws,\n    modelT3_truncatePrefix⟩",
     "      AllT1Shapes I ∧ StdLaws I ∧ TruncatePrefixShape I :=\n  ⟨Interp.modelT3, Model.Braid.toyKem, modelT3_allT1, modelT3_stdLaws,\n    modelT3_truncatePrefix⟩"),
    ("statement-aggregate-drops-the-hmac-bridge",
     "    (Tacenta.SessionUnitBraidT3.BraidHmacAgrees ↔ HmacAgreesShape Interp.real) ∧\n    (TruncatePrefix ↔ TruncatePrefixShape Interp.real) :=\n  ⟨KemLenAgrees_is, KemAgreesFor_is, ValidateEkAgrees_is, KemCloneAgrees_is, BraidHkdfAgrees_is,\n    BraidHmacAgrees_is, TruncatePrefix_is⟩",
     "    (TruncatePrefix ↔ TruncatePrefixShape Interp.real) :=\n  ⟨KemLenAgrees_is, KemAgreesFor_is, ValidateEkAgrees_is, KemCloneAgrees_is, BraidHkdfAgrees_is,\n    TruncatePrefix_is⟩"),
]
for name, old, new in stmt:
    t = once(agree, old, new, name)
    if t is not None:
        refused(name, t, PIN_MISMATCH)

# ------------------------------------------------------------- the erasure module
passes("erasure-unmodified", erasure)
for name, old, new, where in [
    ("erasure-clause-decoder-sized-for-zero",
     "Tacenta.SessionUnitBraidT3.DecoderRefines real (Model.Braid.Decoder.new n.val)) :=\n  Iff.rfl",
     "Tacenta.SessionUnitBraidT3.DecoderRefines real (Model.Braid.Decoder.new 0)) :=\n  Iff.rfl",
     "erasureAgrees_iff_clauses"),
    ("erasure-clause-encoder-of-the-empty-message",
     "        Tacenta.SessionUnitBraidT3.EncoderRefines real\n          (Model.Braid.encode (Tacenta.SessionUnitBraidT3.sliceOf s))) ∧",
     "        Tacenta.SessionUnitBraidT3.EncoderRefines real\n          (Model.Braid.encode [])) ∧", "erasureAgrees_iff_clauses"),
    # the encoder simulation at the exhaustion edge: one more step than a u16 index allows
    ("erasure-simulation-past-the-last-index",
     "theorem encoderSim_live : ∀ (n : ℕ) (e : Encoder) (m : Model.Braid.Encoder),\n    e.exhausted = false → e.next.val = m.next → m.next + n ≤ 65536 → EncoderSim n e m := by",
     "theorem encoderSim_live : ∀ (n : ℕ) (e : Encoder) (m : Model.Braid.Encoder),\n    e.exhausted = false → e.next.val = m.next → m.next + n ≤ 65537 → EncoderSim n e m := by",
     "encoderSim_live"),
    ("erasure-encoder-without-the-div-ceil-hypothesis",
     "theorem erasureAgrees_encoder (hdc : Tacenta.UnitSatisfiabilityErasure.DivCeil32) :",
     "theorem erasureAgrees_encoder :", "erasureAgrees_encoder"),
]:
    t = once(erasure, old, new, name)
    if t is not None:
        refused(name, t, where)
t = once(erasure, "theorem erasureAgrees_encoder (hdc : Tacenta.UnitSatisfiabilityErasure.DivCeil32) :",
         "theorem erasureAgrees_encoder (hdc : Tacenta.UnitSatisfiabilityErasure.DivCeil32) (hx : True) :",
         "statement-encoder-adds-a-premise")
if t is not None:
    # the proof still builds with an extra unused premise; the pin must refuse the changed statement
    refused("statement-encoder-adds-a-premise", t, PIN_MISMATCH)

# -------------------------------------------------------------- the states module
passes("states-unmodified", states)
for name, old, new, where in [
    ("witness-epoch-headroom-at-the-ceiling",
     "theorem epoch_one_headroom : (1#u64 : Std.U64).val + 1 < Std.U64.max := by\n  scalar_tac",
     "theorem epoch_one_headroom : (1#u64 : Std.U64).val + 1 < Std.U64.max - 1000000000000000000000 := by\n  scalar_tac",
     "epoch_one_headroom"),
    ("witness-decoder-sized-for-ct2-where-the-state-needs-ct1",
     "obtain ⟨d, hd, hneed⟩ := I.dec K.ct1Size (by omega)\n  refine ⟨State.HeaderSent",
     "obtain ⟨d, hd, hneed⟩ := I.dec K.ct2Size (by omega)\n  refine ⟨State.HeaderSent", "good_headerSent"),
    ("witness-encoder-past-the-live-bound",
     "theorem live_encode (m : Bytes) : (Model.Braid.encode m).next < 65536 := by\n  simp [Model.Braid.encode]",
     "theorem live_encode (m : Bytes) : (Model.Braid.encode m).next < 0 := by\n  simp [Model.Braid.encode]",
     "live_encode"),
    ("witness-honest-chunk-with-a-source-of-the-wrong-size",
     "theorem honest_noHeaderReceived {mm : Model.Braid.Msg}\n    (n : ℕ) (src : Bytes) (hn : src.length = n)",
     "theorem honest_noHeaderReceived {mm : Model.Braid.Msg}\n    (n : ℕ) (src : Bytes) (hn : src.length = n + 1)",
     "honest_noHeaderReceived"),
    ("witness-message-type-that-does-not-feed-the-decoder",
     "msg_exists hea .Hdr .hdr trivial 1#u64 _ hl\n  refine ⟨State.NoHeaderReceived",
     "msg_exists hea .Ek .ek trivial 1#u64 _ hl\n  refine ⟨State.NoHeaderReceived", "recv_noHeaderReceived"),
    ("witness-initiator-against-the-responder-initial-state",
     "StateRefines K b.state (Model.Braid.initAlice (sliceOf secret)) ∧\n      Tacenta.SessionUnitBraidT1.State.ct1_bounded b.state ∧\n      Tacenta.SessionUnitBraidT1.State.decoders_bounded b.state ∧\n      (Tacenta.SessionUnitBraidT1.State.epoch_val b.state).val + 1 < Std.U64.max ∧\n      EncodersLive (Model.Braid.initAlice (sliceOf secret)) ⦄ := by\n  unfold Braid.initiator",
     "StateRefines K b.state (Model.Braid.initBob (sliceOf secret)) ∧\n      Tacenta.SessionUnitBraidT1.State.ct1_bounded b.state ∧\n      Tacenta.SessionUnitBraidT1.State.decoders_bounded b.state ∧\n      (Tacenta.SessionUnitBraidT1.State.epoch_val b.state).val + 1 < Std.U64.max ∧\n      EncodersLive (Model.Braid.initAlice (sliceOf secret)) ⦄ := by\n  unfold Braid.initiator",
     "initiator_refines"),
    ("witness-responder-without-the-div-ceil-law",
     "    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (secret : Slice Std.U8) :\n    Braid.responder",
     "    (secret : Slice Std.U8) :\n    Braid.responder", "responder_refines"),
    # the definitions the state theorems are stated through
    ("definition-good-drops-the-epoch-headroom",
     "  (Tacenta.SessionUnitBraidT1.State.epoch_val s).val + 1 < Std.U64.max ∧ EncodersLive m\n\n/-- `Good` unfolds",
     "  True ∧ EncodersLive m\n\n/-- `Good` unfolds", "Good_iff"),
    ("definition-recvwitness-drops-honest-chunk",
     "    Good K s m ∧ MsgRefines msg mm ∧ HonestChunk m mm ∧ mm.epoch = m.epoch ∧\n    (∃ mc, mm.data = some mc) ∧ FeedsDecoder m mm.type ∧ modelTag m = c ∧ mm.type = ty\n\n",
     "    Good K s m ∧ MsgRefines msg mm ∧ True ∧ mm.epoch = m.epoch ∧\n    (∃ mc, mm.data = some mc) ∧ FeedsDecoder m mm.type ∧ modelTag m = c ∧ mm.type = ty\n\n",
     "RecvWitness_iff"),
]:
    t = once(states, old, new, name)
    if t is not None:
        refused(name, t, where)
for name, old, new in [
    ("statement-twelve-states-covers-eleven",
     "    ∀ t : ℕ, t < 12 → ∃ (s : State)", "    ∀ t : ℕ, t < 11 → ∃ (s : State)"),
    ("definition-state-tag-repeats-a-number",
     "  | .Ct2Sampled .. => 10\n  | .Failed => 11", "  | .Ct2Sampled .. => 10\n  | .Failed => 10"),
    ("definition-feeds-decoder-admits-a-pair",
     "  | .ct1Acknowledged .., .ekCt1Ack => True\n", "  | .ct1Acknowledged .., .ekCt1Ack => True\n  | .keysUnsampled .., .hdr => True\n"),
]:
    t = once(states, old, new, name)
    if t is not None:
        refused(name, t, PIN_MISMATCH)

# -------------------------------------------------------------- the entry points
passes("entry-unmodified", entry)
for name, old, new, where in [
    ("entry-receive-without-the-truncate-law",
     "theorem Braid.receive_refines_given_erasure\n    (htr : Tacenta.SessionUnitErasureT1.TruncateTotal)\n    {K : Model.Braid.Kem}",
     "theorem Braid.receive_refines_given_erasure\n    {K : Model.Braid.Kem}", "Braid.receive_refines_given_erasure"),
    ("entry-defined-hypotheses-cite-the-wrong-clone-theorem",
     "  ⟨Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees,\n    Tacenta.UnitSatisfiabilityErasure.decoderAddChunk_total,",
     "  ⟨Tacenta.UnitSatisfiabilityErasure.encoderClone_total,\n    Tacenta.UnitSatisfiabilityErasure.decoderAddChunk_total,", "defined_hypotheses_given_erasure"),
]:
    t = once(entry, old, new, name)
    if t is not None:
        refused(name, t, where)
t = once(entry, "    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)\n    (hzz : Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal)\n    (hrf : Tacenta.SessionUnitBraidT1.RangeFullIndexTotal)\n    (self : tacenta_session_unit.tacenta_braid.Braid)\n    (msg",
         "    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)\n    (hzz : Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal)\n    (hrf : Tacenta.SessionUnitBraidT1.RangeFullIndexTotal)\n    (self : tacenta_session_unit.tacenta_braid.Braid)\n    (hdup : True)\n    (msg", "statement-entry-adds-a-premise")
if t is not None:
    # the proof still builds with an extra unused premise; the pin must refuse the changed statement
    refused("statement-entry-adds-a-premise", t, PIN_MISMATCH)


# ---------------------------------------------------- the Reed-Solomon proof
passes("rs-statements-unmodified", rs_stmts)
passes("rs-glue-unmodified", rs_glue)

# a specification function changed: the module that proves the kernel statement against it refuses
for name, old, new, why in [
    ("rs-spec-product-starts-from-zero",
     "    Model.Gf65536.one\n\n/-- `weights`", "    Model.Gf65536.zero\n\n/-- `weights`",
     "K_weights holds of the product, not of a product that starts from zero"),
    ("rs-spec-evaluation-multiplies-instead-of-adds",
     "(List.zipWith Model.Gf65536.mul cs vs).foldl Model.Gf65536.add Model.Gf65536.zero",
     "(List.zipWith Model.Gf65536.mul cs vs).foldl Model.Gf65536.mul Model.Gf65536.zero",
     "K_evaluate computes a sum"),
    ("rs-spec-coefficients-use-the-node-not-x",
     "(prodNe (fun j => Model.Gf65536.add x (xs.getD j 0#16)) xs.length i)",
     "(prodNe (fun j => Model.Gf65536.add 0#16 (xs.getD j 0#16)) xs.length i)",
     "K_coefficients depends on x"),
]:
    t = once(rs_defs, old, new, name)
    if t is not None:
        refused_through(name, "UnitErasureRsDefs", t, rs_kernel, why)

# a statement of the plan changed: the theorem that proves it refuses
for name, old, new, where in [
    ("rs-statement-next-chunk-claims-the-next-index",
     "cbytes ch = Model.Erasure.codeword (storeBytes e.chunks) e.next.val ⦄ :=",
     "cbytes ch = Model.Erasure.codeword (storeBytes e.chunks) (e.next.val + 1) ⦄ :=", "E_next"),
    ("rs-statement-add-chunk-verdict-inverted",
     "(r.1 = true ↔ r.2.«have».val.length ≠ d.«have».val.length) ⦄ :=",
     "(r.1 = true ↔ r.2.«have».val.length = d.«have».val.length) ⦄ :=", "D_add"),
    ("rs-statement-recovery-with-fewer-indices-than-chunks",
     "(hlen : idxs.length = Model.Erasure.chunkCount m.length) :\n    Model.Erasure.Decoder.message",
     "(hlen : idxs.length + 1 = Model.Erasure.chunkCount m.length) :\n    Model.Erasure.Decoder.message", "M_recover"),
]:
    t = once(rs_stmts, old, new, name)
    if t is not None:
        refused(name, t, where)

# the decoder invariant changed: the glue refuses
t = once(rs_glue, "  rel : (haveHeld d).map Prod.fst = ((md.chunks.map (·.index)).reverse).take d.needed.val",
         "  rel : (haveHeld d).map Prod.fst = ((md.chunks.map (·.index))).take d.needed.val",
         "rs-invariant-the-decoder-holds-the-newest-indices")
if t is not None:
    refused("rs-invariant-the-decoder-holds-the-newest-indices", t, ANY)

# the pins hold the statements
for name, old, new in [
    ("rs-pin-glue-drops-a-law",
     "theorem erasureAgrees (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)\n    (htr : TruncatePrefix) : ErasureAgrees :=",
     "theorem erasureAgrees (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)\n    (htr : TruncatePrefix) (hx : True) : ErasureAgrees :="),
]:
    t = once(rs_glue, old, new, name)
    if t is not None:
        refused(name, t, PIN_MISMATCH)

if wrong:
    sys.stderr.write("braid-agreement negatives: %d of %d cases gave the wrong result\n" % (len(wrong), cases))
    for w in wrong:
        sys.stderr.write("  WRONG  " + w + "\n")
    sys.exit(1)
print("braid-agreement negatives: %d cases gave the expected result "
      "(%d unmodified inputs accepted, %d mutations refused)" % (cases, accepted, cases - accepted))
PY
