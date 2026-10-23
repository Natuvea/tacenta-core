#!/usr/bin/env bash
# Port the key derivation's T1 and T3 proofs onto every translation that includes its bodies.
#
#   bash tacenta-proofs/scripts/port-kdf-proofs.sh           write the copies
#   bash tacenta-proofs/scripts/port-kdf-proofs.sh --check   regenerate into a temporary
#                                                            directory and fail on any difference
#
# The proofs that came with `tacenta-kdf`'s copied bodies are in the tree once, against the Session
# unit's translation (`Translation/KdfT1Sha.lean` ... `KdfT3Kdf.lean`, namespace `Tacenta.KdfProof`, about
# `tacenta_session_unit.tacenta_kdf`). Every other translation `run-aeneas.sh` gives `--include-kdf` and
# that has claimed theorems declares the same bodies under its own namespace, and Lean structures are
# nominal, so the proofs cannot be imported across: they are copied. This script writes each copy from
# the Session unit's files by three count-checked rewrites and nothing else: the translated crate's
# namespace, the proofs' namespace (`Tacenta.KdfProof<Suffix>`) and the imports (the translation's
# generated module, and the copies' own module names `Kdf<Suffix>T1Sha` ...). For the session and sparse
# leaves, whose translations call only the HKDF and so do not declare `hmac.hmac_sha256`, the two
# theorems about that function (`hmac_sha256_no_panic`, `hmac_sha256_spec`) are left out, each removed as
# one named block. The model and bridge modules (`KdfModel*`, `KdfBridge*`) mention no translation and
# are shared, not copied. No statement or proof step is otherwise edited. Exact counts make a change in
# the source fail closed instead of producing a partial port.
#
# The lifecycle and Braid-and-erasure translations include the bodies too and have no theorem about
# them, so they get no copy.
set -euo pipefail

cd "$(dirname "$0")/../.."

check=0
if [ "${1:-}" = "--check" ]; then
  check=1
elif [ $# -ne 0 ]; then
  echo "usage: port-kdf-proofs.sh [--check]" >&2
  exit 1
fi

src=tacenta-proofs/translation/Translation
out="$src"
tmp=""
cleanup() { [ -n "$tmp" ] && rm -rf "$tmp"; return 0; }
trap cleanup EXIT INT TERM
if [ "$check" -eq 1 ]; then
  tmp=$(mktemp -d)
  out="$tmp"
fi

python3 - "$src" "$out" <<'PY'
from pathlib import Path
import sys

src, out = map(Path, sys.argv[1:3])

FILES = ["T1Sha", "T1Kdf", "T3Base", "T3Compress", "T3Stream", "T3Kdf"]
# (suffix, the translation's namespace, its generated module, whether it declares hmac.hmac_sha256)
TARGETS = [
    ("Ratchet", "tacenta_ratchet", "TacentaRatchet", True),
    ("Session", "tacenta_session", "TacentaSession", False),
    ("Spqr", "tacenta_spqr", "TacentaSpqr", False),
    ("Braid", "tacenta_braid", "TacentaBraid", True),
    ("TripleUnit", "tacenta_triple_unit", "TacentaTripleUnit", True),
]
# Occurrences in each source file (after the header line is rewritten), so a source that moved fails here rather than porting half.
NS_COUNT = {"T1Sha": 1, "T1Kdf": 2, "T3Base": 1, "T3Compress": 1, "T3Stream": 1, "T3Kdf": 3}
PROOF_COUNT = {"T1Sha": 3, "T1Kdf": 5, "T3Base": 3, "T3Compress": 3, "T3Stream": 3, "T3Kdf": 3}
# The two HMAC-wrapper theorems, each removed whole where the translation does not declare the wrapper.
HMAC_BLOCKS = {
    "T1Kdf": "/-- **T1 for `hmac_sha256`**: never fails, for every key and message. -/\n@[step]\n"
             "theorem hmac_sha256_no_panic (key data : Slice U8) :\n"
             "    hmac.hmac_sha256 key data ⦃ fun _ => True ⦄ := by\n"
             "  unfold hmac.hmac_sha256; step*\n\n",
    "T3Kdf": "@[step]\ntheorem hmac_sha256_spec (key data : Slice U8) :\n"
             "    hmac.hmac_sha256 key data ⦃ r => bytesOf r = hmac (sliceBytes key) (sliceBytes data) ⦄ := by\n"
             "  unfold hmac.hmac_sha256\n  step with hmac_new_spec\n  step with hmac_update_spec\n"
             "  step with hmac_finalize_spec\n  rw [r_post, List.nil_append]\n\n",
}
HEADER_OLD = ("Elaborated\nhere against the Session unit's own translation of those bodies. Changes from the source: the\n"
              "translated crate's namespace is `tacenta_session_unit.tacenta_kdf`, the Session unit's\n"
              "translation of `tacenta-kdf`;")


def sub(text, old, new, expected, where):
    found = text.count(old)
    if found != expected:
        raise SystemExit(f"port-kdf-proofs: {where}: {old!r} occurs {found} time(s), expected {expected}; "
                         "inspect the source proof before changing this count")
    return text.replace(old, new)


for suffix, ns, gen, has_hmac in TARGETS:
    for f in FILES:
        name = f"Kdf{f}"
        text = (src / f"{name}.lean").read_text()
        where = f"{name}.lean -> Kdf{suffix}{f}.lean"
        text = sub(text, HEADER_OLD,
                   "Elaborated\nhere against the " + f"`{gen}` translation of those bodies. Changes from the source: the\n"
                   f"translated crate's namespace is `{ns}.tacenta_kdf`, that translation's\n"
                   "copy of `tacenta-kdf`;", 1, where)
        text = sub(text, "tacenta_session_unit.tacenta_kdf", f"{ns}.tacenta_kdf", NS_COUNT[f], where)
        text = sub(text, "Tacenta.KdfProof", f"Tacenta.KdfProof{suffix}", PROOF_COUNT[f], where)
        text = sub(text, "import Translation.TacentaSessionUnit\n", f"import Translation.{gen}\n",
                   1 if f == "T1Sha" else 0, where)
        for g in FILES:
            text = text.replace(f"import Translation.Kdf{g}\n", f"import Translation.Kdf{suffix}{g}\n")
        if not has_hmac and f in HMAC_BLOCKS:
            text = sub(text, HMAC_BLOCKS[f], "", 1, where)
        note = ("-- Generated by tacenta-proofs/scripts/port-kdf-proofs.sh from\n"
                f"-- Translation/{name}.lean. Do not edit: the script's `--check` mode\n"
                "-- regenerates this count-checked port and rejects drift.\n\n")
        (out / f"Kdf{suffix}{f}.lean").write_text(note + text)
PY

if [ "$check" -eq 0 ]; then
  echo "port-kdf-proofs: wrote the key derivation's proofs for five translations"
  exit 0
fi

status=0
for f in "$tmp"/Kdf*.lean; do
  base=$(basename "$f")
  if ! diff -u "$src/$base" "$f" >/dev/null 2>&1; then
    diff -u "$src/$base" "$f" | head -40 >&2 || true
    echo "port-kdf-proofs: committed copy $base differs; regenerate and rebuild" >&2
    status=1
  fi
done
[ "$status" -eq 0 ] && echo "port-kdf-proofs: the committed copies are deterministic"
exit "$status"
