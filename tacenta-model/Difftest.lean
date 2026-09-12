/-
Difftest: the model's half of the differential harness (ADR-0008, practice 9).

`lake exe difftest` reads requests on stdin and prints, for each one, what
`Model.Ratchet` or `Model.SparseRatchet` does with it: after the start and
after every operation, whether the operation was taken or refused and the
bytes `Model.PersistedState` writes the state as. The other half is
`tacenta-test-vectors/runners/rust/tests/differential.rs`, which generates the
requests from a printed seed, sends them here, replays the same operations on
`tacenta-ratchet` and `tacenta-spqr`, and compares the two transcripts step by
step.

**This file decides nothing.** It reads the operations it is given, runs the
model's own `send`, `receive` and `advance` on them, and prints the result. It
does not choose which operations to run -- the Rust side does that, blind to
what either side will answer -- and it holds no expectation to check against.
Where the two transcripts differ, the difference is between `tacenta-model` and
`tacenta-core`, which under ADR-0006 is a finding.

The operation encodings are the ones `tacenta-test-vectors/README.md` gives for
the `steps` input of `vectors/persistence/ratchet-state.json` and
`sparse-ratchet-state.json`, so a sequence here and a sequence there mean the
same thing, and `Vectors.lean`'s `RatchetStep.bytes` and `SparseStep.bytes`
write what this reads.

## The requests

    run ratchet fresh  <role(1) || sk(32) || our_pub(32) || peer_pub(32) || dh_out(32)>  <steps>
    run ratchet stored <stored bytes>                                                    <steps>
    run sparse  fresh  <direction(1) || sk(32)>                                          <steps>
    run sparse  stored <stored bytes>                                                    <steps>
    read ratchet <bytes>
    read sparse  <bytes>

Every byte string is lowercase hex, and `<steps>` may be empty. A `fresh` start
runs the model's own initialisation, so that initialisation is compared too; a
`stored` start is bytes both sides read, so that a state neither side could
build by sending and receiving -- a counter at its ceiling, say -- can still be
the starting point.

## The answers

    start ok <bytes> <readback>
    step <i> ok <bytes> <readback>
    step <i> refused <ceiling|other> <bytes> <readback>
    end

`<bytes>` is `toBytes` of the state the step left, which for a refused step is
the state it started from: the model's operations are functions returning
`Option`, so a refusal leaves the state alone. `<readback>` is `same`,
`differs` or `refused:<kind>`, the model's reader run on those same bytes,
which is the export-and-import check at every step rather than at chosen ones.

`<ceiling|other>` says whether the counter the refused operation would have
stepped is at its ceiling in the state the step ran from, by the model's own
reservations (`Model.State.u32Max`, `Model.SparseRatchet.u64Max`) and the
predicates `Vectors.lean` uses for the ceiling vectors. The Rust side uses it
in one direction only: a step `tacenta-core` refuses as `ChainExhausted` must
be a step the model refuses at a counter's ceiling. The other direction does
not hold and is not asserted -- a receive at `nr = u32::MAX` numbered below it
is refused as out of order by both sides, not as exhaustion.

A `stored` start the model's reader refuses answers `start refused <kind>` and
then `end`, and runs no operations. A `read` answers `read ok <bytes>`, the
accepted state written back, or `read refused <kind>`, with `<kind>` the
refusal named as `session-persistence.md`, Rejection, names it. Every answer
ends with `end`, whichever request it answers, so the caller reads one answer
without knowing what it asked.

A malformed request is an error and stops the run, rather than an answer that
could be mistaken for the model's.
-/
import Model.PersistedState
import Model.Ratchet
import Model.SparseRatchet

namespace Difftest

abbrev Bytes := List UInt8

open Model.State (u32Max)
open Model.SparseRatchet (u64Max)

/-! ## Hex -/

def hexDigit (n : UInt8) : Char :=
  let m := n.toNat
  if m < 10 then Char.ofNat (48 + m) else Char.ofNat (97 + m - 10)

def byteHex (b : UInt8) : String :=
  String.ofList [hexDigit (b >>> 4), hexDigit (b &&& 0x0f)]

def toHex (bs : Bytes) : String := String.join (bs.map byteHex)

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def bytesOfChars : List Char → Option Bytes
  | [] => some []
  | a :: b :: rest =>
    match hexVal a, hexVal b, bytesOfChars rest with
    | some x, some y, some t => some (UInt8.ofNat (x * 16 + y) :: t)
    | _, _, _ => none
  | _ => none

def ofHex (s : String) : Option Bytes := bytesOfChars s.toList

/-- A fixed-width big-endian field, as both formats write them. -/
def beValue (bs : Bytes) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `bs`, from `at`, `len` bytes. -/
def slice (bs : Bytes) (at_ len : Nat) : Bytes := (bs.drop at_).take len

/-! ## Refusals -/

/-- The name a refusal is given, as `Vectors.lean` names it: the two
    `session-persistence.md`, Rejection, states. -/
def refusalName : Model.PersistedState.Refusal → String
  | .wrongVersion => "wrong-version"
  | .shortOrMalformed => "short-or-malformed"

/-! ## The operations, as the vectors encode them -/

/-- One operation on a classical ratchet state: `00` a send, `01` a receive
    with the header's `dh(32) || pn(4) || n(4)` and the step's
    `dh_recv(32) || dh_send(32) || new_pub(32)` after it. -/
inductive RatchetStep where
  | send
  | receive (h : Model.State.Header) (dhRecv dhSend newPub : Model.State.Key)

/-- The operations a buffer holds, or `none` if it is not a whole number of
    them. `fuel` is the buffer's length, which bounds the number of steps. -/
def decodeRatchetSteps : Nat → Bytes → Option (List RatchetStep)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, b :: rest =>
    if b == 0x00 then
      (decodeRatchetSteps fuel rest).map (RatchetStep.send :: ·)
    else if b == 0x01 then
      if rest.length < 136 then none
      else
        let h : Model.State.Header :=
          { dh := slice rest 0 32, pn := beValue (slice rest 32 4), n := beValue (slice rest 36 4) }
        (decodeRatchetSteps fuel (rest.drop 136)).map
          (RatchetStep.receive h (slice rest 40 32) (slice rest 72 32) (slice rest 104 32) :: ·)
    else none

/-- One operation on a sparse ratchet state: `op(1) || epoch(8) ||
    output_present(1) || output_epoch(8) || output_key(32)`, and a receive's
    message number `n(8)` after that. The bytes of an absent output are not
    read, as the Rust runner's replay does not read them either. -/
inductive SparseStep where
  | send (epoch : Nat) (out : Option Model.SparseRatchet.Output)
  | receive (epoch : Nat) (out : Option Model.SparseRatchet.Output) (n : Nat)

/-- The agreement's output at `output_present`, or `none` for a tag that names
    neither presence. -/
def decodeOutput (bs : Bytes) : Option (Option Model.SparseRatchet.Output) :=
  match bs.head? with
  | some 0x00 => some none
  | some 0x01 => some (some { keyEpoch := beValue (slice bs 1 8), key := slice bs 9 32 })
  | _ => none

def decodeSparseSteps : Nat → Bytes → Option (List SparseStep)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, b :: rest =>
    if rest.length < 49 then none
    else
      match decodeOutput (rest.drop 8) with
      | none => none
      | some out =>
        let e := beValue (slice rest 0 8)
        if b == 0x00 then
          (decodeSparseSteps fuel (rest.drop 49)).map (SparseStep.send e out :: ·)
        else if b == 0x01 then
          if rest.length < 57 then none
          else
            (decodeSparseSteps fuel (rest.drop 57)).map
              (SparseStep.receive e out (beValue (slice rest 49 8)) :: ·)
        else none

/-! ## Running one operation

Each is the model's own operation, with the state it leaves. Nothing here
decides whether a refusal is right. -/

def stepRatchet (st : Model.State.State) : RatchetStep → Option Model.State.State
  | .send => (Model.Ratchet.send st).map (·.1)
  | .receive h r d np => (Model.Ratchet.receive st h r d np).map (·.1)

def stepSparse (st : Model.SparseRatchet.State) : SparseStep → Option Model.SparseRatchet.State
  | .send e out => (Model.SparseRatchet.send st e out).map (·.1)
  | .receive e out n => (Model.SparseRatchet.receive st e out n).map (·.1)

/-! ### Whether a refused operation's counter is at its ceiling

The predicates `Vectors.lean` gives the ceiling vectors as `atCeiling`, on the
state the operation ran from. Used in one direction: what `tacenta-core`
refuses as `ChainExhausted` must be at a ceiling here. -/

def ratchetAtCeiling (st : Model.State.State) : RatchetStep → Bool
  | .send => st.cks.isSome && st.ns == u32Max
  | .receive _ _ _ _ => st.ckr.isSome && st.nr == u32Max

/-- The state a sparse operation's own advance leaves, when it has one. The
    epoch's ceiling is reached inside `advance`, so the chain counters are read
    from after it. -/
def sparseAdvanced (st : Model.SparseRatchet.State)
    (out : Option Model.SparseRatchet.Output) : Option Model.SparseRatchet.State :=
  match out with
  | none => some st
  | some o => Model.SparseRatchet.advance st o

/-- The counter of the chain an operation would step, if the state holds it. -/
def sparseCounter (st : Model.SparseRatchet.State) (e : Nat) (sendSide : Bool) : Option Nat :=
  (Model.SparseRatchet.findChains st e).bind fun cs =>
    (if sendSide then cs.send else cs.receive).map (·.n)

def sparseAtCeilingOf (st : Model.SparseRatchet.State) (e : Nat)
    (out : Option Model.SparseRatchet.Output) (sendSide : Bool) : Bool :=
  match sparseAdvanced st out with
  -- The advance itself was refused. It is the epoch's ceiling when the step
  -- would have reached the reserved epoch, and the epoch out of order
  -- otherwise.
  | none => decide (st.epoch + 1 ≥ u64Max)
  | some st1 => sparseCounter st1 e sendSide == some u64Max

def sparseAtCeiling (st : Model.SparseRatchet.State) : SparseStep → Bool
  | .send e out => sparseAtCeilingOf st e out true
  | .receive e out _ => sparseAtCeilingOf st e out false

/-! ## The transcript -/

/-- A state's bytes, and what the model's reader makes of them. -/
structure Written where
  bytes : Bytes
  readback : String

def writtenRatchet (st : Model.State.State) : Written :=
  let bs := Model.PersistedState.RatchetState.toBytes st
  { bytes := bs,
    readback :=
      match Model.PersistedState.RatchetState.ofBytes bs with
      | .ok st' => if st' = st then "same" else "differs"
      | .error r => "refused:" ++ refusalName r }

def writtenSparse (st : Model.SparseRatchet.State) : Written :=
  let bs := Model.PersistedState.SparseState.toBytes st
  { bytes := bs,
    readback :=
      match Model.PersistedState.SparseState.ofBytes bs with
      | .ok st' => if st' = st then "same" else "differs"
      | .error r => "refused:" ++ refusalName r }

def Written.line (w : Written) : String := toHex w.bytes ++ " " ++ w.readback

/-- One run's answer, as a list of lines. `write` is the state's bytes, `step`
    one operation with its ceiling flag, and both are given by the caller so
    that the two ratchets share this loop rather than repeating it. -/
def transcript {σ α : Type} (start : σ) (steps : List α) (write : σ → Written)
    (run : σ → α → Option σ) (atCeiling : σ → α → Bool) : List String :=
  let rec go (st : σ) (i : Nat) : List α → List String
    | [] => ["end"]
    | s :: rest =>
      match run st s with
      | some st' =>
        ("step " ++ toString i ++ " ok " ++ (write st').line) :: go st' (i + 1) rest
      | none =>
        ("step " ++ toString i ++ " refused " ++
          (if atCeiling st s then "ceiling" else "other") ++ " " ++ (write st).line)
          :: go st (i + 1) rest
  ("start ok " ++ (write start).line) :: go start 1 steps

/-! ## Requests -/

/-- A `fresh` classical start: `role(1) || sk(32) || our_pub(32) ||
    peer_pub(32) || dh_out(32)`. Role `00` is the party that sends first and
    `01` the party that receives first, whose `peer_pub` and `dh_out` are
    present in the layout and unused. -/
def freshRatchet (bs : Bytes) : Option Model.State.State :=
  if bs.length ≠ 129 then none
  else
    let sk := slice bs 1 32
    let ourPub := slice bs 33 32
    match bs.head? with
    | some 0x00 => some (Model.Ratchet.initSender sk ourPub (slice bs 65 32) (slice bs 97 32) .tacenta)
    | some 0x01 => some (Model.Ratchet.initReceiver sk ourPub .tacenta)
    | _ => none

/-- A `fresh` sparse start: `direction(1) || sk(32)`. -/
def freshSparse (bs : Bytes) : Option Model.SparseRatchet.State :=
  if bs.length ≠ 33 then none
  else
    let sk := slice bs 1 32
    match bs.head? with
    | some 0x00 => some (Model.SparseRatchet.initAlice sk)
    | some 0x01 => some (Model.SparseRatchet.initBob sk)
    | _ => none

def runRatchet (start : Model.State.State) (steps : Bytes) : Except String (List String) :=
  match decodeRatchetSteps steps.length steps with
  | none => .error "difftest: the classical ratchet's steps are not a whole number of operations"
  | some ss => .ok (transcript start ss writtenRatchet stepRatchet ratchetAtCeiling)

def runSparse (start : Model.SparseRatchet.State) (steps : Bytes) : Except String (List String) :=
  match decodeSparseSteps steps.length steps with
  | none => .error "difftest: the sparse ratchet's steps are not a whole number of operations"
  | some ss => .ok (transcript start ss writtenSparse stepSparse sparseAtCeiling)

/-- A `stored` start, read by the model's reader before anything runs. -/
def storedRun {σ : Type} (reader : Bytes → Except Model.PersistedState.Refusal σ)
    (go : σ → Bytes → Except String (List String)) (start steps : Bytes) :
    Except String (List String) :=
  match reader start with
  | .error r => .ok ["start refused " ++ refusalName r, "end"]
  | .ok st => go st steps

def hexArg (what s : String) : Except String Bytes :=
  match ofHex s with
  | some bs => .ok bs
  | none => .error ("difftest: " ++ what ++ " is not lowercase hex")

/-- One request's answer. -/
def handle (line : String) : Except String (List String) :=
  match line.splitOn " " with
  | ["run", algorithm, "fresh", startHex, stepsHex] => do
    let start ← hexArg "a fresh start" startHex
    let steps ← hexArg "the steps" stepsHex
    match algorithm with
    | "ratchet" =>
      match freshRatchet start with
      | some st => runRatchet st steps
      | none => .error "difftest: a fresh classical start is role(1), sk, our_pub, peer_pub, dh_out"
    | "sparse" =>
      match freshSparse start with
      | some st => runSparse st steps
      | none => .error "difftest: a fresh sparse start is direction(1) and sk(32)"
    | other => .error ("difftest: no algorithm " ++ other)
  | ["run", algorithm, "stored", startHex, stepsHex] => do
    let start ← hexArg "a stored start" startHex
    let steps ← hexArg "the steps" stepsHex
    match algorithm with
    | "ratchet" =>
      storedRun Model.PersistedState.RatchetState.ofBytes runRatchet start steps
    | "sparse" =>
      storedRun Model.PersistedState.SparseState.ofBytes runSparse start steps
    | other => .error ("difftest: no algorithm " ++ other)
  | ["read", algorithm, bytesHex] => do
    let bs ← hexArg "the stored bytes" bytesHex
    match algorithm with
    | "ratchet" =>
      match Model.PersistedState.RatchetState.ofBytes bs with
      | .ok st => .ok ["read ok " ++ toHex (Model.PersistedState.RatchetState.toBytes st), "end"]
      | .error r => .ok ["read refused " ++ refusalName r, "end"]
    | "sparse" =>
      match Model.PersistedState.SparseState.ofBytes bs with
      | .ok st => .ok ["read ok " ++ toHex (Model.PersistedState.SparseState.toBytes st), "end"]
      | .error r => .ok ["read refused " ++ refusalName r, "end"]
    | other => .error ("difftest: no algorithm " ++ other)
  | _ => .error ("difftest: not a request: " ++ line)

end Difftest

/-- Every request on stdin, answered in order. A malformed request stops the
    run: an answer the caller could mistake for the model's is worse than no
    answer at all. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let out ← IO.getStdout
  for line in input.splitOn "\n" do
    -- The lines are written by the Rust side, so nothing is trimmed but the
    -- carriage return a Windows runner's pipe may add.
    let request := line.replace "\r" ""
    if !request.isEmpty then
      match Difftest.handle request with
      | .ok lines => for l in lines do out.putStrLn l
      | .error e => throw (IO.userError e)
