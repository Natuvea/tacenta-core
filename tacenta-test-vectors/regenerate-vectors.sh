#!/usr/bin/env bash
# Regenerate the protocol vectors from the model: the Double Ratchet scenarios
# and the PQXDH shared secrets. The model is the oracle: these vectors are its
# byte output, and the runners check each implementation reproduces them. Run
# after any change to the model's ratchet or session establishment.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
model="$here/../tacenta-model"
out="$here/vectors/ratchet/double-ratchet.json"
pq="$here/vectors/session-establishment/pqxdh-sk.json"
( cd "$model" && lake exe genvectors ) > "$out"
( cd "$model" && lake exe genvectors pqxdh ) > "$pq"
ser="$here/vectors/serialization/message-encoding.json"
( cd "$model" && lake exe genvectors serialization ) > "$ser"

init="$here/vectors/serialization/initial-message.json"
( cd "$model" && lake exe genvectors initial ) > "$init"

# The post-quantum derivations. The five crates below them were transcribed by
# hand from these Lean models, and these vectors are what pin the transcription.
mkdir -p "$here/vectors/post-quantum"
for a in gf inv interp spqr braid auth triple split composite; do
  ( cd "$model" && lake exe genvectors "$a" ) > "$here/vectors/post-quantum/$a.json"
  echo "wrote $here/vectors/post-quantum/$a.json"
done
echo "wrote $out ($(wc -l < "$out") lines)"
echo "wrote $pq ($(wc -l < "$pq") lines)"
echo "wrote $ser ($(wc -l < "$ser") lines)"
echo "wrote $init ($(wc -l < "$init") lines)"
