#!/usr/bin/env python3
"""Change one packed source file and bring every digest that mentions it up to date.

    forge-pack-source.py PACK RELATIVE TEXT

The result is a pack that verifies on its own, with a source that is not the
candidate commit's file. The case runners use it to show what checking the pack
against git adds to checking it against itself.
"""
import hashlib
import json
import pathlib
import sys

pack, relative, text = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]


def digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


target = pack / "source" / relative
target.write_text(text)
manifest_path = pack / "assurance-manifest.json"
manifest = json.loads(manifest_path.read_text())
for item in manifest["sources"]:
    if item["path"] == relative:
        item["sha256"], item["bytes"] = digest(target), target.stat().st_size
manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
index_path = pack / "PACK-MANIFEST.json"
index = json.loads(index_path.read_text())
for entry in index["files"]:
    path = pack / entry["path"]
    entry["sha256"], entry["bytes"] = digest(path), path.stat().st_size
index_path.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
