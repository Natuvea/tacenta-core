"""Deterministic re-arrangement of upstream NIST ACVP ML-KEM-1024 sample vectors.
Usage, from this directory: python3 -I extract.py original mlkem1024-acvp-fixture.json
Pure joins by tgId/tcId; no value is computed. Fails loudly on any anomaly."""
import json, sys, os

SEL = {  # directory -> {function-or-None: [(keyFormat-or-None)]}
 "ML-KEM-keyGen-FIPS203": {None: [None]},
 "ML-KEM-encapDecap-FIPS203": {"encapsulation": [None], "decapsulation": [None],
                               "encapsulationKeyCheck": [None], "decapsulationKeyCheck": [None]},
 "ML-KEM-encapDecap-FIPS203-tr1": {"encapsulation": [None], "decapsulation": ["seed", "expanded"],
                               "encapsulationKeyCheck": [None], "decapsulationKeyCheck": ["expanded"]},
}
PS = "ML-KEM-1024"
LEN = {"d": 32, "z": 32, "m": 32, "k": 32, "ek": 1568, "dk": 3168, "c": 1568}
OUT = {"keyGen": ("ek", "dk"), "encapsulation": ("c", "k"), "decapsulation": ("k",),
       "encapsulationKeyCheck": ("testPassed",), "decapsulationKeyCheck": ("testPassed",)}

def die(m): sys.exit("FAIL: " + m)
def load(root, d, f):
    with open(os.path.join(root, d, f + ".json"), encoding="utf-8") as fh: return json.load(fh)

def main(root, out):
    fx = {"source": "usnistgov/ACVP-Server gen-val/json-files (see PROVENANCE.md)", "revisions": {}}
    for d, funcs in SEL.items():
        pr, ex, ip = (load(root, d, f) for f in ("prompt", "expectedResults", "internalProjection"))
        for a in (pr, ex, ip):
            if a["algorithm"] != "ML-KEM" or a["revision"] != pr["revision"] or a["mode"] != pr["mode"]: die(d + " header mismatch")
        exg = {g["tgId"]: g for g in ex["testGroups"]}
        ipg = {g["tgId"]: g for g in ip["testGroups"]}
        rev = {"algorithm": pr["algorithm"], "mode": pr["mode"], "revision": pr["revision"], "groups": []}
        seen = set()
        for g in pr["testGroups"]:
            if g["parameterSet"] != PS: continue
            fn = g.get("function"); kf = g.get("keyFormat")
            if fn not in funcs or kf not in funcs[fn]: die("%s unexpected group %s/%s tg%s" % (d, fn, kf, g["tgId"]))
            seen.add((fn, kf))
            mode_fn = fn if fn else "keyGen"
            if not g["tests"]: die("empty group %s" % g["tgId"])
            e, i = exg.get(g["tgId"]), ipg.get(g["tgId"])
            if e is None or i is None: die("group %s missing in expected/internal" % g["tgId"])
            et = {t["tcId"]: t for t in e["tests"]}; it = {t["tcId"]: t for t in i["tests"]}
            if len(et) != len(g["tests"]) or len(it) != len(g["tests"]): die("case count mismatch tg%s" % g["tgId"])
            cases = []
            for t in g["tests"]:
                tc = t["tcId"]
                if tc not in et or tc not in it: die("case %s lacks expected answer" % tc)
                inputs = {k: v for k, v in t.items() if k != "tcId"}
                outputs = {k: v for k, v in et[tc].items() if k != "tcId"}
                if set(outputs) != set(OUT[mode_fn]): die("tc%s output fields %s" % (tc, sorted(outputs)))
                for k, v in list(inputs.items()) + list(outputs.items()):
                    if k in LEN and (not isinstance(v, str) or len(v) != 2 * LEN[k]): die("tc%s %s length" % (tc, k))
                # cross-check against upstream internalProjection (equality only)
                ipc = it[tc]
                for k, v in list(inputs.items()) + list(outputs.items()):
                    if ipc.get(k) != v: die("tc%s %s differs in internalProjection" % (tc, k))
                c = {"tcId": tc, "inputs": inputs, "expected": outputs}
                if "reason" in ipc: c["reason"] = ipc["reason"]
                cases.append(c)
            grp = {"tgId": g["tgId"], "testType": g["testType"], "parameterSet": PS, "cases": cases}
            if fn: grp["function"] = fn
            if kf: grp["keyFormat"] = kf
            rev["groups"].append(grp)
        want = {(f, k) for f, ks in funcs.items() for k in ks}
        if seen != want: die("%s missing groups %s" % (d, sorted(want - seen, key=str)))
        fx["revisions"][d] = rev
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(fx, fh, sort_keys=True, separators=(",", ":")); fh.write("\n")

main(sys.argv[1], sys.argv[2])
