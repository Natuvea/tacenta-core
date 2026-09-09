#!/usr/bin/env python3
"""Every committed vector file validates against its schema.

    python3 tooling/check-vectors.py

The runners parse the vector files with serde, which is lenient in ways the
schemas are not: serde ignores a field it does not know, does not check hex
against a pattern, and cannot see that two vectors in one file share an
identifier. So a file can pass the runner and still be one the schema forbids,
and the next language runner, written to the schema, would be the one to find
out. This makes the schema binding.

Two schemas, chosen by the file's `algorithm` field: `double-ratchet` files
are scripted scenarios (`schema/ratchet-vector.schema.json`); everything else
is a known-answer file (`schema/vector.schema.json`). The schemas' `$id`
values are checked to share one base, so the two cannot drift apart in how
they name themselves.

No dependency. `jsonschema` is not guaranteed on a runner and this check has
to be able to run anywhere `python3` does, so the validator below covers the
subset of JSON Schema the two schemas use (`type`, `required`, `properties`,
`additionalProperties`, `items`, `minItems`, `const`, `enum`, `pattern`,
`minimum`) and refuses a schema keyword it does not implement, so that a
keyword added to a schema without support here fails loudly rather than
being silently ignored.

Beyond the schema: vector `id`s are unique within a file, and `output` is
present exactly when `result` is `valid` (the schema states that rule in prose;
this enforces it).
"""

import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VECTORS = os.path.join(ROOT, "tacenta-test-vectors", "vectors")
SCHEMAS = os.path.join(ROOT, "tacenta-test-vectors", "schema")

# The keywords the validator below understands. Anything else in a schema is
# an error, on the principle that an unimplemented constraint is not a
# constraint. `$schema`, `$id`, `title`, `description` and `default` are
# annotations, not constraints, and are allowed through.
KNOWN = {
    "$schema", "$id", "title", "description", "default",
    "type", "required", "properties", "additionalProperties", "items",
    "minItems", "const", "enum", "pattern", "minimum",
}

TYPES = {
    "object": dict,
    "array": list,
    "string": str,
    "integer": int,
    "boolean": bool,
}


def type_ok(value, name):
    if name == "integer":
        return isinstance(value, int) and not isinstance(value, bool)
    if name == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if name == "null":
        return value is None
    return isinstance(value, TYPES[name])


def validate(value, schema, path, errors):
    """Append a message to `errors` for every constraint `value` breaks."""
    unknown = set(schema) - KNOWN
    if unknown:
        errors.append("%s: schema uses keyword(s) this validator does not "
                      "implement: %s" % (path, ", ".join(sorted(unknown))))
        return

    if "const" in schema and value != schema["const"]:
        errors.append("%s: expected %r, got %r" % (path, schema["const"], value))
        return
    if "enum" in schema and value not in schema["enum"]:
        errors.append("%s: %r is not one of %r" % (path, value, schema["enum"]))
        return

    if "type" in schema:
        names = schema["type"]
        if isinstance(names, str):
            names = [names]
        if not any(type_ok(value, n) for n in names):
            errors.append("%s: expected type %s, got %s"
                          % (path, "/".join(names), type(value).__name__))
            return

    if isinstance(value, str) and "pattern" in schema:
        if not re.search(schema["pattern"], value):
            errors.append("%s: %r does not match /%s/"
                          % (path, value, schema["pattern"]))

    if isinstance(value, int) and not isinstance(value, bool) \
            and "minimum" in schema and value < schema["minimum"]:
        errors.append("%s: %r is below the minimum %r"
                      % (path, value, schema["minimum"]))

    if isinstance(value, dict):
        props = schema.get("properties", {})
        for key in schema.get("required", []):
            if key not in value:
                errors.append("%s: missing required field %r" % (path, key))
        extra = schema.get("additionalProperties", True)
        for key, item in value.items():
            if key in props:
                validate(item, props[key], "%s.%s" % (path, key), errors)
            elif extra is False:
                errors.append("%s: unexpected field %r" % (path, key))
            elif isinstance(extra, dict):
                validate(item, extra, "%s.%s" % (path, key), errors)

    if isinstance(value, list):
        if "minItems" in schema and len(value) < schema["minItems"]:
            errors.append("%s: fewer than %d items" % (path, schema["minItems"]))
        if "items" in schema:
            for i, item in enumerate(value):
                validate(item, schema["items"], "%s[%d]" % (path, i), errors)


def load(path):
    with open(path) as fh:
        return json.load(fh)


def main():
    vector_schema = load(os.path.join(SCHEMAS, "vector.schema.json"))
    ratchet_schema = load(os.path.join(SCHEMAS, "ratchet-vector.schema.json"))

    problems = []

    # The two schemas name themselves under one base, so a reader who
    # resolves one `$id` can resolve the other.
    ids = [vector_schema.get("$id", ""), ratchet_schema.get("$id", "")]
    bases = {i.rsplit("/", 1)[0] for i in ids}
    if len(bases) != 1 or "" in ids:
        problems.append("schema $id values do not share one base: %r" % ids)

    files = sorted(glob.glob(os.path.join(VECTORS, "**", "*.json"), recursive=True))
    if not files:
        problems.append("no vector files found under %s" % VECTORS)

    checked = 0
    for path in files:
        rel = os.path.relpath(path, ROOT)
        try:
            doc = load(path)
        except ValueError as e:
            problems.append("%s: not JSON: %s" % (rel, e))
            continue

        scenario = isinstance(doc, dict) and doc.get("algorithm") == "double-ratchet"
        schema = ratchet_schema if scenario else vector_schema
        errors = []
        validate(doc, schema, rel, errors)
        problems.extend(errors)

        vectors = doc.get("vectors") if isinstance(doc, dict) else None
        if not isinstance(vectors, list):
            continue
        seen = set()
        for i, v in enumerate(vectors):
            if not isinstance(v, dict):
                continue
            vid = v.get("id")
            if vid in seen:
                problems.append("%s: vector id %r is not unique in the file" % (rel, vid))
            seen.add(vid)
            if not scenario:
                valid = v.get("result", "valid") == "valid"
                if valid and "output" not in v:
                    problems.append("%s.vectors[%d] (%s): a valid vector needs an "
                                    "`output`" % (rel, i, vid))
                if not valid and "output" in v:
                    problems.append("%s.vectors[%d] (%s): an invalid vector carries "
                                    "no `output`" % (rel, i, vid))
            checked += 1

    if problems:
        for p in problems:
            print("check-vectors: " + p, file=sys.stderr)
        return 1
    print("check-vectors: %d vectors in %d files validate against their schemas"
          % (checked, len(files)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
