#!/usr/bin/env bash
# Fail if a claimed T1 or T3 theorem of the leaf crates or the three-leaf unit takes a boundary
# hypothesis that nothing connects to a statement some function satisfies, takes a hypothesis that is
# not a named predicate, or quantifies over a variable that only hypotheses mention.
#
# Why. A hypothesis nothing satisfies makes the theorem that takes it true and empty, and neither
# the kernel nor `#print axioms` notices. Compilation, the pins and `attest.py` do not look at the
# hypotheses of a claimed theorem: a dead hypothesis added to one, and a witness deleted from
# `Satisfiability.lean`, were both accepted by every other gate until this one. This gate reads the
# hypotheses from the built environment and joins them with the bridges, existence theorems and
# derivations that are there.
#
# Which theorems. The entries of `manifests/verification-manifest.json` whose section heading contains
# `tier T1`, `tier T3` or `decoded state` and not `session lifecycle`, in two environments that cannot
# be loaded together (the leaf crates, and the three-leaf unit, which re-declares the leaves' generated
# names). A reworded heading would silently remove its theorems, so the gate also requires at least
# 109 leaf and 31 three-leaf-unit theorems (`MIN_CLAIMED` below, raised when the ledger grows). The
# theorems of the section that proves the hypotheses from laws are not gated by it, and neither are the
# Session unit's ported copies (held by the pins and by `check-session-satisfiability-negatives.sh`).
#
# What it reads. For each claimed theorem, every binder that is a proposition or an instance and has no
# free variable. Those are the boundary hypotheses: a closed predicate (`T1.HmacTotal`,
# `SpqrT3.VecRetainAgrees`, an instance such as `T1.DerivedKeysModel`), or a closed statement that names
# no predicate, which fails.
#
# What it requires. A closed predicate P is connected when one of these holds:
#   - a bridge: a theorem `P <-> S` whose right side, read through the hand-written data definitions it
#     names, reaches no function the translation defines, and an existence theorem whose conclusion is an
#     `Exists`, a `Nonempty` or a conjunction with one, and which mentions a constant of the shape `S` is
#     built from. The bridge is checked by the kernel, so P cannot drift from S.
#   - a bridge to other closed predicates (`P <-> Q`): P is connected when every such Q is. A predicate
#     bridged to itself, or to a cycle of predicates, is not connected.
#   - a derivation: a theorem whose conclusion is P (or a conjunction that has P as a conjunct), named
#     in the claim ledger, all of whose hypotheses that are propositions or instances are closed
#     predicates that are themselves connected. A derivation that takes a hypothesis with a free
#     variable is refused.
#   - P is `True`.
# A bridge whose right side reaches a defined function is void: the shape is satisfiable by choosing any
# function, and a defined function is not a choice, so it says nothing about the body. A void bridge is
# reported, and it fails the gate when it is the only thing connecting P.
# A claimed theorem that quantifies over a variable that no non-proposition binder or conclusion
# mentions, with a hypothesis about it that mentions nothing the theorem uses (`(n : Nat) (hn : n < 0)`),
# fails. A claimed theorem that is not in its environment fails.
#
# What it cannot see. It does not show that a connected hypothesis is satisfiable: an existence theorem
# is recognised by its shape (its conclusion is an existence and it names the shape), so a weakened one
# (`... or True`) passes, and the pins and `CLAIMS.md` are what name the real ones. It does not decide
# that the shape a bridge names is the right statement (the `Iff.rfl` compares P with S, a reader
# compares S with the crate). It does not see that two hypotheses of one theorem hold together (the
# groups that mention a shared opaque constant are argued in `CLAIMS.md` and `LIMITATIONS.md`, not
# computed here). It does not see a dead hypothesis that has a free variable and mentions real state
# (`hroom : s.chains.length < 0`): the state relations and the numeric bounds are held by the state
# witnesses and by `tooling/check-precondition-shapes.py`. A dead hypothesis added to a theorem outside
# the claimed set, such as the derivations in the section that proves the hypotheses from laws, is held
# by the statement pins of those theorems and by nothing here, except that a derivation the gate relies
# on is refused if it takes a hypothesis with a free variable.
#
# The Lean text below is not part of the Lean package: `check-lean-constructs.sh` refuses
# elaboration-time code and any reference to the `Lean` namespace in the translation package,
# and `tooling/check-precondition-shapes.py` expects every Lean file of a package directory to be
# one it scans. `check-hypothesis-witnesses-negatives.sh` holds this gate to mutations; no workflow
# runs it yet.
#
# Needs the translation package built (`no-sorry.sh` runs it after the build). About a minute of CPU:
# each environment loads Mathlib and the whole translation once.
#
# HYPWIT_ROOT names another `tacenta-proofs` directory to read (the negatives script points it at
# a disposable copy). Run from any directory.
set -euo pipefail

root="${HYPWIT_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT INT TERM

ROOT="$root" TMP="$tmp" python3 - <<'PYEOF'
import collections, json, os, subprocess, sys

root = os.environ["ROOT"]
tmp = os.environ["TMP"]
translation = os.path.join(root, "translation")

LEAN = r'''
import Lean
import @@MODULE@@

open Lean Meta Elab Command

namespace HypWitness

def modOf (env : Environment) (c : Name) : String :=
  match env.getModuleIdxFor? c with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => "<local>"

def isGenMod (m : String) : Bool := m.startsWith "Translation.Tacenta"

def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def consts (e : Expr) : Array Name := e.getUsedConstants

def jstr (s : String) : String := toString (Json.str s)
def jarr (xs : Array String) : String := "[" ++ ", ".intercalate (xs.map jstr).toList ++ "]"
def trunc (s : String) (n : Nat) : String :=
  if s.length > n then (String.ofList (s.toList.take n)) ++ "..." else s

def headName (t : Expr) : String :=
  (t.getAppFn.constName?.map (·.toString)).getD
    (if t.isForall then "forall" else if t.getAppFn.isFVar then "fvar" else "other")

def dumpTheorem (env : Environment) (n : Name) : MetaM (Array String) := do
  let some ci := env.find? n | return #[s!"\{\"thm\": {jstr n.toString}, \"missing\": true}"]
  let lines ← forallTelescope ci.type fun xs body => do
    -- A data binder that nothing but propositions mention, where each such proposition mentions no
    -- other data binder that the theorem uses (the conclusion or another non-proposition binder
    -- depends on it): a hypothesis such as `(n : Nat) (hn : n < 0)` constrains nothing the theorem is
    -- about. `(bytes) (s) (hdec : decode bytes = ok s)` is not one, because `s` is used.
    let mut isData : Array Bool := #[]
    let mut outside : Array Bool := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      let dataBinder := !(← isProp d.type) && d.binderInfo != .instImplicit
      let mut used := body.containsFVar x.fvarId!
      for y in xs do
        if y == x then continue
        let dy ← y.fvarId!.getDecl
        if dy.type.containsFVar x.fvarId! && !(← isProp dy.type) then used := true
      isData := isData.push dataBinder
      outside := outside.push used
    let mut orphans : Array String := #[]
    for i in [0:xs.size] do
      if !isData[i]! || outside[i]! then continue
      let x := xs[i]!
      let mut dead := false
      for j in [0:xs.size] do
        if j == i then continue
        let dy ← xs[j]!.fvarId!.getDecl
        if !(← isProp dy.type) || !dy.type.containsFVar x.fvarId! then continue
        let mut mentionsUsed := false
        for k in [0:xs.size] do
          if k != i && isData[k]! && outside[k]! && dy.type.containsFVar xs[k]!.fvarId! then mentionsUsed := true
        if !mentionsUsed then dead := true
      if dead then orphans := orphans.push (← xs[i]!.fvarId!.getDecl).userName.toString
    let mut lines : Array String := #[s!"\{\"thm\": {jstr n.toString}, \"module\": {jstr (modOf env n)}, \"orphans\": {jarr orphans}}"]
    let mut idx := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      let t := d.type
      let isP ← isProp t
      let bi := match d.binderInfo with
        | .default => "default" | .implicit => "implicit"
        | .strictImplicit => "strictImplicit" | .instImplicit => "inst"
      let closed := (t.find? (fun e => e.isFVar)).isNone
      let ppt ← ppExpr t
      lines := lines.push s!"\{\"thm\": {jstr n.toString}, \"idx\": {idx}, \"name\": {jstr d.userName.toString}, \"bi\": {jstr bi}, \"isProp\": {isP}, \"closed\": {closed}, \"head\": {jstr (headName t)}, \"pp\": {jstr (trunc (toString ppt) 300)}}"
      idx := idx + 1
    return lines
  return lines

/-- Closed predicates concluded by `e`, reading a conjunction as its conjuncts. -/
partial def conclPreds (e : Expr) : Array String :=
  if e.isAppOfArity ``And 2 then conclPreds (e.getArg! 0) ++ conclPreds (e.getArg! 1)
  else match e.getAppFn.constName? with
    | some h => if h.getRoot == `Tacenta && e.getAppNumArgs == 0 then #[h.toString] else #[]
    | none => #[]

def genKinds (env : Environment) (e : Expr) : Array String :=
  ((consts e).filter (fun x => isGenMod (modOf env x))).filterMap (fun x =>
    match env.find? x with
    | some xi => some (x.toString ++ ":" ++ kindOf xi)
    | none => none)

/-- The generated definitions an expression reaches, descending through the hand-written `Tacenta.*`
data definitions it names (so an alias for a defined function is seen) and stopping at the first
generated one. -/
partial def deepGenDefs (env : Environment) (e : Expr) (visited : IO.Ref (Std.HashSet Name))
    (depth : Nat) : IO (Array String) := do
  let mut out : Array String := #[]
  for c in consts e do
    if (← visited.get).contains c then continue
    visited.modify (·.insert c)
    match env.find? c with
    | none => pure ()
    | some ci =>
      if isGenMod (modOf env c) then
        -- a function the translation defines; not a structure projection or a type
        if kindOf ci == "def" && !(env.isProjectionFn c) && !ci.type.isSort then
          out := out.push (c.toString ++ ":def")
      else if c.getRoot == `Tacenta && depth < 8 then
        match ci with
        | .defnInfo d =>
          -- a shape or a predicate (its result is a proposition) is compared as a whole by the bridge;
          -- a data definition may be an alias for a defined function, so it is read through
          unless d.type.getForallBody.isProp do
            out := out ++ (← deepGenDefs env d.value visited (depth + 1))
        | _ => pure ()
  return out

/-- The closed hand-written predicates (definitions of type `Prop`) an expression names. -/
def closedPreds (env : Environment) (e : Expr) : Array String :=
  ((consts e).filter (fun x => x.getRoot == `Tacenta)).filterMap (fun x =>
    match env.find? x with
    | some (.defnInfo d) => if d.type.isProp then some x.toString else none
    | _ => none)

/-- Whether a conclusion asserts an existence: `Exists` or `Nonempty`, or a conjunction with one. -/
partial def existsHead (e : Expr) : Bool :=
  if e.isAppOfArity ``And 2 then existsHead (e.getArg! 0) || existsHead (e.getArg! 1)
  else match e.getAppFn.constName? with
    | some h => h == ``Exists || h == ``Nonempty
    | none => false

def dumpDecl (env : Environment) (c : Name) (ci : ConstantInfo) : MetaM (Array String) := do
  let ty := ci.type
  let m := modOf env c
  let mut out : Array String := #[]
  if ty.isAppOfArity ``Iff 2 then
    let l := ty.getArg! 0
    let r := ty.getArg! 1
    let tac (e : Expr) := ((consts e).filter (fun x => x.getRoot == `Tacenta)).map (·.toString)
    let visited ← IO.mkRef (∅ : Std.HashSet Name)
    let deep ← deepGenDefs env r visited 0
    out := out.push s!"\{\"iff\": {jstr c.toString}, \"module\": {jstr m}, \"lhs\": {jarr (tac l)}, \"rhsTac\": {jarr (tac r)}, \"rhsClosed\": {jarr (closedPreds env r)}, \"rhsGen\": {jarr deep}}"
  let ex ← (try
    forallTelescope ty fun _ body =>
      if existsHead body then
        let tac := ((consts body).filter (fun x => x.getRoot == `Tacenta)).map (·.toString)
        pure (some s!"\{\"exist\": {jstr c.toString}, \"module\": {jstr m}, \"tac\": {jarr tac}}")
      else pure none
  catch _ => pure none)
  if let some s := ex then out := out.push s
  let r ← (try
    forallTelescope ty fun xs body => do
      let cs := conclPreds body
      if cs.isEmpty then pure none
      else
        let mut hs : Array String := #[]
        for x in xs do
          let d ← x.fvarId!.getDecl
          if (← isProp d.type) || d.binderInfo == .instImplicit then
            let closed := (d.type.find? (fun e => e.isFVar)).isNone
            hs := hs.push ((if closed then "" else "~") ++ headName d.type)
        pure (some s!"\{\"deriv\": {jstr c.toString}, \"module\": {jstr m}, \"concl\": {jarr cs}, \"hyps\": {jarr hs}}")
  catch _ => pure none)
  if let some s := r then out := out.push s
  return out

end HypWitness

open HypWitness in
#eval show MetaM Unit from do
  let env ← getEnv
  let namesPath := (← IO.getEnv "HW_NAMES").getD "names.txt"
  let outp := (← IO.getEnv "HW_OUT").getD "out.jsonl"
  let txt ← IO.FS.readFile namesPath
  let mut out : Array String := #[]
  for l in txt.splitOn "\n" do
    if l != "" then out := out ++ (← dumpTheorem env l.toName)
  for (c, ci) in env.constants.toList do
    let m := modOf env c
    unless m.startsWith "Translation." && !isGenMod m do continue
    unless (match ci with | .thmInfo _ => true | _ => false) do continue
    if c.isInternal then continue
    if c.toString.endsWith ".eq_1" || c.toString.endsWith "match_1" then continue
    try out := out ++ (← dumpDecl env c ci) catch _ => pure ()
  for (c, ci) in env.constants.toList do
    if c.getRoot == `Tacenta then
      match ci with
      | .defnInfo d =>
        if d.value.isConstOf ``True then
          out := out.push s!"\{\"trivial\": {jstr c.toString}}"
      | _ => pure ()
  IO.FS.writeFile outp ("\n".intercalate out.toList ++ "\n")
  IO.println s!"hypothesis-witness dump: {out.size} lines"
'''

ENVS = [("LEAF", "Translation.AxiomAudit"), ("TRIPLE", "Translation.AxiomAuditTripleUnit")]

# The claimed theorems are chosen by the words of a section heading. A heading that is reworded drops
# its theorems without any other gate noticing, so the gate also requires at least this many in each
# environment. The numbers are those of the ledger the gate was written against; raise them when the
# ledger gains claimed T1 or T3 theorems of these environments, never lower them to make a run pass.
MIN_CLAIMED = {"LEAF": 109, "TRIPLE": 31}


def env_of(name):
    ns = name.split(".")[1]
    if ns.startswith("SessionUnit"):
        return None
    return "TRIPLE" if ns.startswith("Unit") else "LEAF"


manifest = json.load(open(os.path.join(root, "manifests", "verification-manifest.json")))
ledger = {(c.get("resolved") or c["theorem"]) for c in manifest["claims"]}
claimed = {"LEAF": [], "TRIPLE": []}
headings = collections.OrderedDict()
seen = set()
for c in manifest["claims"]:
    s = c["section"]
    if not (("tier T1" in s or "tier T3" in s or "decoded state" in s) and "session lifecycle" not in s):
        continue
    n = c.get("resolved") or c["theorem"]
    if n in seen:
        continue
    seen.add(n)
    e = env_of(n)
    if e:
        claimed[e].append(n)
        headings[(e, s)] = headings.get((e, s), 0) + 1


def dump(tag, module):
    names = os.path.join(tmp, f"names_{tag}.txt")
    out = os.path.join(tmp, f"{tag}.jsonl")
    src = os.path.join(tmp, f"Audit{tag}.lean")
    open(names, "w").write("\n".join(claimed[tag]) + "\n")
    open(src, "w").write(LEAN.replace("@@MODULE@@", module))
    env = dict(os.environ, HW_NAMES=names, HW_OUT=out)
    r = subprocess.run(["lake", "env", "lean", src], cwd=translation, env=env,
                       capture_output=True, text=True)
    if r.returncode != 0 or not os.path.exists(out):
        sys.stderr.write(f"hypothesis-witnesses: the {tag} dump failed (a missing build is not a "
                         f"pass):\n{r.stdout[-2000:]}\n{r.stderr[-2000:]}\n")
        sys.exit(2)
    rows = collections.defaultdict(list)
    thms = collections.OrderedDict()
    for line in open(out):
        line = line.strip()
        if not line:
            continue
        x = json.loads(line)
        if "idx" in x:
            thms[x["thm"]]["binders"].append(x)
        elif "thm" in x:
            thms[x["thm"]] = dict(x, binders=[])
        else:
            for k in ("iff", "exist", "deriv", "trivial"):
                if k in x:
                    rows[k].append(x)
    return thms, rows


problems = []
notes = []
for tag, module in ENVS:
    if len(claimed[tag]) < MIN_CLAIMED[tag]:
        problems.append(f"{tag}: the ledger selects {len(claimed[tag])} claimed theorems, fewer than the "
                        f"{MIN_CLAIMED[tag]} this gate requires; a section heading may have been reworded. "
                        "Selected from: " + "; ".join(f"{h} ({n})" for (e, h), n in headings.items() if e == tag))
        continue
    thms, rows = dump(tag, module)
    trivial = {x["trivial"] for x in rows["trivial"]}
    bridges = collections.defaultdict(list)
    for w in rows["iff"]:
        for p in w["lhs"]:
            bridges[p].append(w)
    derivs = collections.defaultdict(list)
    for d in rows["deriv"]:
        for p in d["concl"]:
            derivs[p].append(d)

    def is_void(w):
        # the right side, read through the hand-written definitions it names, reaches a function the
        # translation defines
        return any(g.endswith(":def") for g in w["rhsGen"])

    def has_existence(w):
        shape = [c for c in w["rhsTac"] if not c.split(".")[-1].startswith("real")]
        return any(e["exist"] != w["iff"] and any(s in e["tac"] for s in shape) for e in rows["exist"])

    memo = {}

    def connection(p, stack=()):
        if p in memo:
            return memo[p]
        if p in stack:
            return None
        res = None
        if p in trivial:
            res = ("trivial", p)
        if res is None:
            for w in bridges.get(p, []):
                if is_void(w):
                    continue
                if set(w["lhs"]) & set(w["rhsClosed"]):
                    continue              # a predicate bridged to itself says nothing
                if w["rhsClosed"]:
                    # P is bridged to other closed predicates: it holds when they do
                    if all(connection(q, stack + (p,)) is not None for q in w["rhsClosed"]):
                        res = ("bridge to predicates", w["iff"])
                        break
                elif has_existence(w):
                    res = ("bridge", w["iff"])
                    break
        if res is None:
            for d in derivs.get(p, []):
                if d["deriv"] not in ledger:
                    continue
                ok = True
                for h in d["hyps"]:
                    # every proposition or instance the derivation takes must be a closed predicate that
                    # is itself connected; one with a free variable is refused
                    if h.startswith("~") or not h.startswith("Tacenta.") or connection(h, stack + (p,)) is None:
                        ok = False
                        break
                if ok:
                    res = ("derivation", d["deriv"])
                    break
        memo[p] = res
        return res

    users = collections.OrderedDict()
    anon = []
    orphans = []
    for tname, t in thms.items():
        if t.get("missing"):
            problems.append(f"{tag}: the claimed theorem `{tname}` is not in the environment")
            continue
        for o in t.get("orphans", []):
            orphans.append((tname, o))
        for b in t["binders"]:
            if b["closed"] and (b["isProp"] or b["bi"] == "inst"):
                if b["head"].startswith("Tacenta."):
                    users.setdefault(b["head"], []).append(tname)
                else:
                    anon.append((tname, b))
    for tname, b in anon:
        problems.append(f"{tag}: `{tname}` takes the closed hypothesis `{b['name']} : {b['pp']}`, which "
                        "names no predicate and so has no witness")
    for tname, o in orphans:
        problems.append(f"{tag}: `{tname}` quantifies over `{o}`, which only hypotheses mention (an orphan "
                        "variable): a hypothesis about it constrains nothing the theorem is about")
    kinds = collections.Counter()
    for p, who in users.items():
        c = connection(p)
        voids = [w["iff"] for w in bridges.get(p, []) if is_void(w)]
        if c is None:
            why = ("it has only a void bridge (" + ", ".join(voids) + ")") if voids else "it has no bridge and no derivation"
            problems.append(f"{tag}: `{p}` (taken by {len(who)} claimed theorems, for example `{who[0]}`) "
                            f"is not connected: {why}")
            kinds["unconnected"] += 1
        else:
            kinds[c[0]] += 1
            if voids:
                notes.append(f"{tag}: `{p}` also has a void bridge ({', '.join(voids)}); it is connected by "
                             f"{c[0]} `{c[1]}`")
    print(f"hypothesis-witnesses: {tag}: {len(thms)} claimed theorems, {len(users)} distinct closed "
          f"predicates ({', '.join(f'{k} {v}' for k, v in sorted(kinds.items()))}), "
          f"{len(anon)} closed hypotheses that name no predicate, {len(orphans)} orphan variables")

for n in notes:
    print("note:", n)
if problems:
    print("hypothesis-witnesses: FAILED", file=sys.stderr)
    for p in problems:
        print("  " + p, file=sys.stderr)
    sys.exit(1)
print("hypothesis-witnesses: every closed hypothesis of the claimed leaf and three-leaf-unit theorems is "
      "connected to a bridge, a derivation or `True`")
PYEOF
