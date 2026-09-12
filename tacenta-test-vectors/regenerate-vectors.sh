#!/usr/bin/env bash
# Regenerate every protocol vector file from the model. The model is the
# oracle: these vectors are its byte output, and the runners check that the
# implementation reproduces them. Run after any change to the model, and
# commit the result; `tooling/ci.sh` and the public `proofs` CI job run this
# and fail on a difference between the model and the committed files.
#
# Twenty-eight files, all under vectors/: the Double Ratchet scenarios, the
# PQXDH shared secrets, the message and initial-message encodings, the nine
# post-quantum derivation files and the two erasure-code files beside them, the
# erasure coders' two persisted formats and the four persisted states (the two
# ratchets', the Triple Ratchet's and the Braid's),
# the protobuf profile's two readers, the AEAD's two directions, and the three
# decoder files under malformed-input/.
# The AEAD files take their AES-256 block values from NIST SP 800-38A, since
# the model has no AES; their `source` field says so. The primitive vectors
# under vectors/primitives/ are not regenerated: they are standards' known
# answers, plus one project-generated XEdDSA file, and none of them comes from
# the model. Nor is malformed-input/ratchet-reject.json, which is
# hand-authored.
#
# Needs the Lean toolchain the model pins (`tacenta-model/lean-toolchain`,
# installed through elan) and a built model: `lake build` there compiles the
# generator, and `lake exe genvectors` runs it. The README says how.
#
# Each file is written to a temporary path and moved into place only once the
# generator has exited successfully, so a generator that fails part-way
# leaves the committed file as it was rather than truncated.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
model="$here/../tacenta-model"

# One generator invocation, written atomically.
#   generate <genvectors argument or ""> <output path>
generate() {
  local arg="$1" out="$2" tmp
  mkdir -p "$(dirname "$out")"
  tmp="$(mktemp "$out.XXXXXX")"
  if ( cd "$model" && lake exe genvectors $arg ) > "$tmp"; then
    mv "$tmp" "$out"
    echo "wrote ${out#"$here/"} ($(wc -l < "$out" | tr -d ' ') lines)"
  else
    rm -f "$tmp"
    echo "regenerate-vectors: 'lake exe genvectors $arg' failed; $out left unchanged" >&2
    exit 1
  fi
}

generate ""            "$here/vectors/ratchet/double-ratchet.json"
generate pqxdh         "$here/vectors/session-establishment/pqxdh-sk.json"
generate serialization "$here/vectors/serialization/message-encoding.json"
generate initial       "$here/vectors/serialization/initial-message.json"

# The post-quantum derivations. The five crates below them were transcribed by
# hand from these Lean models, and these vectors are what pin the transcription.
for a in gf inv interp spqr braid auth triple split composite erasure-encode erasure-decode; do
  generate "$a" "$here/vectors/post-quantum/$a.json"
done

# The erasure coders' and the two ratchets' persisted formats
# (session-persistence.md), the bounded protobuf profile (protobuf-profile.md),
# and the AEAD (message-format.md).
for a in erasure-encoder-state erasure-decoder-state ratchet-state sparse-ratchet-state \
         triple-ratchet-state braid-state; do
  generate "$a" "$here/vectors/persistence/$a.json"
done
for a in protobuf-ratchet-body protobuf-prekey-envelope; do
  generate "$a" "$here/vectors/protobuf/$a.json"
done
for a in aead-encrypt aead-decrypt; do
  generate "$a" "$here/vectors/aead/$a.json"
done

# The decoders' refusal of a re-spelled curve key (message-format.md, Curve
# public keys), with the canonical spellings they accept.
generate composite-decode "$here/vectors/malformed-input/composite-header-decode.json"
generate bundle-decode    "$here/vectors/malformed-input/prekey-bundle-decode.json"
generate initial-decode   "$here/vectors/malformed-input/initial-message-decode.json"
