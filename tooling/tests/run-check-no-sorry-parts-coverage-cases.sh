#!/usr/bin/env bash
# Negative controls for `tooling/check-no-sorry-parts-coverage.py`.
#
# The check reads the phases `no-sorry.sh` lists, the parts of `tacenta-proofs/scripts/no-sorry-parts.txt` as a
# part job resolves them, and the part names the workflow gives its matrix and its combining job. It must accept
# the files of the tree and refuse each of these, in a copy of them:
#
#   a phase removed from every part           refused, naming the phase and the partition, with the parts
#                                             file's own refusal in place and again with it taken out
#   a phase in two parts, or both whole and sliced   refused, in both of those ways
#   a slice of the dispatcher in no part, twice, or sliced two ways   refused, in both of those ways
#   a phase the script lists that no part names (the script given one, made for the purpose)   refused
#   a part that names a phase the script does not list   refused
#   a part name in the workflow with no part in the script   refused, for the pull-request list and the push list
#   a part of the script missing from the workflow's list   refused, for an ordinary part and for one declared
#                                             with no phase yet
#   a part named twice in the workflow's list, the two partitions swapped, a matrix or partition expression of
#   a shape the check does not read, a job missing   refused
#   a workflow, a parts file or a phase table that cannot be read   refused (a gate that cannot run fails)
#
# A part declared with no phase (`-`) is in the files of the tree only once one has been added; the cases that
# need one give the copies a part `idle`, declared empty and named in the workflow's list, when the tree has none.
# The "with the parts file's own refusal taken out" cases run the check with a copy of `no-sorry-parts.py` from
# which every `refuse(f'partition ...` of its coverage rules is removed, to show that the count the check makes
# from what `resolve` prints does not rest on the reader's refusals.
#
# A case that goes wrong prints a line that starts `WRONG  ` and stops the run, as in the other runners of this
# directory. It needs PyYAML (the checks job installs it) and no Lean toolchain.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
checker="$root/tooling/check-no-sorry-parts-coverage.py"
scripts="$root/tacenta-proofs/scripts"
work="$(mktemp -d "${TMPDIR:-/tmp}/no-sorry-coverage-cases.XXXXXX")"
work="$(cd "$work" && pwd -P)"
trap 'rm -rf "$work"' EXIT
cases=0

wrong() {  # name message...
  local name="$1"
  shift
  echo "WRONG  coverage control $name: $*" >&2
  if [ -f "$work/out-$name" ]; then
    sed 's/^/    | /' "$work/out-$name" >&2
  fi
  exit 1
}

ok_line="are in exactly one part of each partition, and the workflow runs exactly those parts"

# run <name> args...: the check with those arguments; output to out-<name>, status to rc-<name>.
run() {
  local name="$1"
  shift
  set +e
  env -u NO_SORRY_LIST -u NO_SORRY_PART -u NO_SORRY_PART_DIR -u NO_SORRY_COMBINE -u NO_SORRY_PARTITION \
    python3 -B "$checker" "$@" > "$work/out-$name" 2>&1
  echo $? > "$work/rc-$name"
  set -e
}
accepts() {  # name: the check accepted and printed its line
  cases=$((cases + 1))
  [ "$(cat "$work/rc-$1")" -eq 0 ] || wrong "$1" "expected acceptance, was refused"
  grep -qF -- "$ok_line" "$work/out-$1" || wrong "$1" "accepted without its closing line"
}
refuses() {  # name needle: refused, said the needle, and printed no closing line
  cases=$((cases + 1))
  [ "$(cat "$work/rc-$1")" -ne 0 ] || wrong "$1" "expected refusal containing '$2', was accepted"
  if grep -qF -- "$ok_line" "$work/out-$1"; then wrong "$1" "refused, but printed its closing line"; fi
  grep -qF -- "$2" "$work/out-$1" || wrong "$1" "refused, but without '$2'"
}
not_said() {  # name needle: the output does not hold the needle
  if grep -qF -- "$2" "$work/out-$1"; then wrong "$1" "the output holds '$2'"; fi
}

# ---- the files of the tree, and the table -----------------------------------------------------------------
table="$work/table"
(cd "$root/tacenta-proofs" && env -u NO_SORRY_PART -u NO_SORRY_PART_DIR -u NO_SORRY_COMBINE -u NO_SORRY_PARTITION \
  NO_SORRY_LIST=1 bash scripts/no-sorry.sh) > "$table" 2>&1 || wrong table "no-sorry.sh did not list its phases"
cp "$scripts/no-sorry-parts.txt" "$work/tree.parts"
cp "$root/.github/workflows/ci.yml" "$work/tree.yml"

run tree-files
accepts tree-files
grep -q '^  hosted: ' "$work/out-tree-files" && grep -q '^  single: ' "$work/out-tree-files" \
  || wrong tree-files "the summary does not list both partitions"

# The base the cases edit: the files of the tree, with a part declared empty (and in the workflow) if the tree has none.
python3 - "$work/tree.parts" "$work/tree.yml" "$work/base.parts" "$work/base.yml" <<'PY'
import re, sys
parts, yml, parts_out, yml_out = sys.argv[1:]
l = open(parts).read().split("\n")
empty = [m.group(1) for x in l for m in [re.fullmatch(r"hosted ([a-z][a-z0-9-]*): -", x)] if m]
y = open(yml).read()
if not empty:
    i = next(i for i, x in enumerate(l) if x.startswith("hosted dispatch-0:"))
    l.insert(i, "hosted idle: -")
    empty = ["idle"]
for name in empty:
    if f'"{name}"' not in y:
        assert y.count('"dispatch-0"') == 1
        y = y.replace('"dispatch-0"', f'"{name}", "dispatch-0"')
open(parts_out, "w").write("\n".join(l))
open(yml_out, "w").write(y)
open(parts_out + ".empty", "w").write(empty[0])
PY
empty_part="$(cat "$work/base.parts.empty")"
run base --parts "$work/base.parts" --workflow "$work/base.yml"
accepts base
grep -qF "$empty_part (declared empty)" "$work/out-base" || wrong base "the part declared empty is not listed as such"

# The edits to a copy are python programs read from the standard input of edit_parts (over the lines `l` of the base
# parts file) and edit_yml (over the text `t` of the base workflow; `swap(old, new)` requires `old` to occur once).
cat > "$work/editor.py" <<'PY'
import sys
source, target, kind, program = sys.argv[1:]
text = open(source).read()
if kind == "parts":
    l = text.split("\n")
    exec(open(program).read())
    open(target, "w").write("\n".join(l))
else:
    t = text
    def swap(old, new):
        global t
        assert t.count(old) == 1, (t.count(old), old)
        t = t.replace(old, new)
    exec(open(program).read())
    open(target, "w").write(t)
PY
edit_parts() {  # name < program: base.parts edited into parts-<name>
  cat > "$work/prog-parts-$1"
  python3 -I "$work/editor.py" "$work/base.parts" "$work/parts-$1" parts "$work/prog-parts-$1"
}
edit_yml() {  # name < program: base.yml edited into yml-<name>
  cat > "$work/prog-yml-$1"
  python3 -I "$work/editor.py" "$work/base.yml" "$work/yml-$1" yml "$work/prog-yml-$1"
}
# A copy of the parts reader without the refusals of its coverage rules.
python3 - "$scripts/no-sorry-parts.py" "$work/lenient-reader.py" <<'PY'
import re, sys
text = open(sys.argv[1]).read()
count = 0
while True:
    i = text.find("refuse(f'partition {partition}:")
    if i < 0:
        break
    depth, j = 0, i + len("refuse")
    while True:
        c = text[j]
        depth += (c == "(") - (c == ")")
        j += 1
        if depth == 0:
            break
    text = text[:i] + "pass" + text[j:]
    count += 1
assert count == 6, count   # the six coverage refusals of read_parts; a reader with another number needs this read again
open(sys.argv[2], "w").write(text)
PY

# ---- a phase in no part -------------------------------------------------------------------------------------
edit_parts dropped <<'PY'
l[:] = [x for x in l if x != '  receive-preservation']
assert not any('receive-preservation' in x for x in l if not x.startswith('#'))
PY
run dropped --parts "$work/parts-dropped" --workflow "$work/base.yml"
refuses dropped "partition hosted: phase receive-preservation is in no part"
run dropped-lenient --parts "$work/parts-dropped" --workflow "$work/base.yml" --reader "$work/lenient-reader.py"
refuses dropped-lenient "partition hosted: phase receive-preservation is in no part"
not_said dropped-lenient "does not resolve"
# The partition `single` takes every phase with `*`, so it is the `hosted` partition that notices.
not_said dropped "partition single"

# ---- a phase in two parts -----------------------------------------------------------------------------------
edit_parts twice <<'PY'
i = next(i for i, x in enumerate(l) if x.startswith('hosted kernel:')); l[i] += ' repair'
PY
run twice --parts "$work/parts-twice" --workflow "$work/base.yml"
refuses twice "partition hosted: phase repair is in parts"
run twice-lenient --parts "$work/parts-twice" --workflow "$work/base.yml" --reader "$work/lenient-reader.py"
refuses twice-lenient "partition hosted: phase repair is in parts"
not_said twice-lenient "does not resolve"

# ---- a slice of the dispatcher in no part, and twice --------------------------------------------------------
edit_parts slice-missing <<'PY'
l[:] = [x for x in l if not x.startswith('hosted dispatch-7:')]
PY
# The workflow no longer runs dispatch-7 either, so that the hole in the slices is the only fault.
edit_yml slice-missing <<'PY'
swap('"dispatch-7"', '"dispatch-6"')
t = t.replace('"dispatch-6", "dispatch-6"', '"dispatch-6"')
PY
run slice-missing --parts "$work/parts-slice-missing" --workflow "$work/yml-slice-missing"
refuses slice-missing "slice 7/8 of initial-dispatch is in no part"
run slice-missing-lenient --parts "$work/parts-slice-missing" --workflow "$work/yml-slice-missing" --reader "$work/lenient-reader.py"
refuses slice-missing-lenient "slice 7/8 of initial-dispatch is in no part"
not_said slice-missing-lenient "does not resolve"
# A ninth part holds slice 6/8 again, and is in the workflow, so that the repeated slice is the only fault.
edit_parts slice-twice <<'PY'
i = next(i for i, x in enumerate(l) if x.startswith('hosted dispatch-7:'))
l.insert(i + 1, 'hosted dispatch-8: initial-dispatch@6/8')
PY
edit_yml slice-twice <<'PY'
swap('"dispatch-7"', '"dispatch-7", "dispatch-8"')
PY
run slice-twice --parts "$work/parts-slice-twice" --workflow "$work/yml-slice-twice"
refuses slice-twice "slice 6/8 of initial-dispatch is in parts dispatch-6, dispatch-8"
run slice-twice-lenient --parts "$work/parts-slice-twice" --workflow "$work/yml-slice-twice" --reader "$work/lenient-reader.py"
refuses slice-twice-lenient "slice 6/8 of initial-dispatch is in parts dispatch-6, dispatch-8"
not_said slice-twice-lenient "does not resolve"
edit_parts whole-and-sliced <<'PY'
i = next(i for i, x in enumerate(l) if x.startswith('hosted kernel:')); l[i] += ' initial-dispatch'
PY
run whole-and-sliced-lenient --parts "$work/parts-whole-and-sliced" --workflow "$work/base.yml" --reader "$work/lenient-reader.py"
refuses whole-and-sliced-lenient "partition hosted: phase initial-dispatch is in part kernel and sliced in"
not_said whole-and-sliced-lenient "does not resolve"
edit_parts sliced-two-ways <<'PY'
i = next(i for i, x in enumerate(l) if x.startswith('hosted dispatch-7:')); l[i] = 'hosted dispatch-7: initial-dispatch@7/9'
PY
run sliced-two-ways-lenient --parts "$work/parts-sliced-two-ways" --workflow "$work/base.yml" --reader "$work/lenient-reader.py"
refuses sliced-two-ways-lenient "partition hosted: phase initial-dispatch is sliced 8 and 9 ways"
not_said sliced-two-ways-lenient "does not resolve"

# ---- the script and the parts disagree ----------------------------------------------------------------------
# The script given a phase no part names, made for the purpose.
python3 - "$table" "$work/table-gained" <<'PY'
import sys
lines = open(sys.argv[1]).read().split("\n")
i = next(i for i, x in enumerate(lines) if x.startswith("phase\tkernel-replay-negative\t"))
lines.insert(i, "phase\tnew-phase\tplain\ta new phase")
open(sys.argv[2], "w").write("\n".join(lines))
PY
run gained --table "$work/table-gained" --parts "$work/base.parts" --workflow "$work/base.yml"
refuses gained "partition hosted: phase new-phase is in no part"
# A part that names a phase the script does not list.
python3 - "$table" "$work/table-lost" <<'PY'
import sys
lines = [x for x in open(sys.argv[1]).read().split("\n") if not x.startswith("phase\trepair\t")]
open(sys.argv[2], "w").write("\n".join(lines))
PY
run lost --table "$work/table-lost" --parts "$work/base.parts" --workflow "$work/base.yml"
refuses lost "names repair, which the script does not run"

# ---- the workflow's part names ------------------------------------------------------------------------------
edit_yml ghost <<'PY'
swap('"dispatch-0"', '"ghost", "dispatch-0"')
PY
run ghost --parts "$work/base.parts" --workflow "$work/yml-ghost"
refuses ghost "names ghost, which is not a part of partition hosted"
edit_yml ghost-push <<'PY'
swap("""'["all"]'""", """'["all", "ghost"]'""")
PY
run ghost-push --parts "$work/base.parts" --workflow "$work/yml-ghost-push"
refuses ghost-push "names ghost, which is not a part of partition single"
edit_yml reply-missing <<'PY'
swap('"reply", ', '')
PY
run reply-missing --parts "$work/base.parts" --workflow "$work/yml-reply-missing"
refuses reply-missing "does not run reply, a part of partition hosted"
edit_yml all-missing <<'PY'
swap("""'["all"]'""", """'[]'""")
PY
run all-missing --parts "$work/base.parts" --workflow "$work/yml-all-missing"
refuses all-missing "does not run all, a part of partition single"
edit_yml empty-missing <<PY
swap('"$empty_part", ', '')
PY
run empty-missing --parts "$work/base.parts" --workflow "$work/yml-empty-missing"
refuses empty-missing "does not run $empty_part, a part of partition hosted"
edit_yml kernel-twice <<'PY'
swap('"kernel", ', '"kernel", "kernel", ')
PY
run kernel-twice --parts "$work/base.parts" --workflow "$work/yml-kernel-twice"
refuses kernel-twice "names kernel twice"
edit_yml swapped <<'PY'
swap("'push' && 'single' || 'hosted'", "'push' && 'hosted' || 'single'")
PY
run swapped --parts "$work/base.parts" --workflow "$work/yml-swapped"
refuses swapped "names all, which is not a part of partition hosted"
# Both events run the hosted partition, with its parts in both lists, so that this is the only fault.
edit_yml same-partition <<'PY'
import re
other = re.search(r"\|\| '(\[[^']*\])'\) \}\}", t).group(1)
swap("""'["all"]'""", "'" + other + "'")
swap("'push' && 'single' || 'hosted'", "'push' && 'hosted' || 'hosted'")
PY
run same-partition --parts "$work/base.parts" --workflow "$work/yml-same-partition"
refuses same-partition "names partition hosted for a push and for everything else"
edit_yml unknown-partition <<'PY'
swap("'push' && 'single' || 'hosted'", "'push' && 'single' || 'elsewhere'")
PY
run unknown-partition --parts "$work/base.parts" --workflow "$work/yml-unknown-partition"
refuses unknown-partition "partition elsewhere for a pull request or any other event, which the parts file does not have"

# ---- shapes the check does not read, and files it cannot read -----------------------------------------------
edit_yml matrix-literal <<'PY'
i = t.index("part: ${{ fromJSON(")
j = t.index("\n", i)
t = t[:i] + "part: [kernel, braid]" + t[j:]
PY
run matrix-literal --parts "$work/base.parts" --workflow "$work/yml-matrix-literal"
refuses matrix-literal "the matrix's \`part\` is not"
edit_yml matrix-other-event <<'PY'
swap("fromJSON(github.event_name == 'push' &&", "fromJSON(github.event_name == 'schedule' &&")
PY
run matrix-other-event --parts "$work/base.parts" --workflow "$work/yml-matrix-other-event"
refuses matrix-other-event "the matrix's \`part\` is not"
edit_yml partition-literal <<'PY'
swap("NO_SORRY_PARTITION: ${{ github.event_name == 'push' && 'single' || 'hosted' }}", "NO_SORRY_PARTITION: hosted")
PY
run partition-literal --parts "$work/base.parts" --workflow "$work/yml-partition-literal"
refuses partition-literal "does not name its partition"
edit_yml no-part-job <<'PY'
swap("\n  translation-part:\n", "\n  translation-parts:\n")
PY
run no-part-job --parts "$work/base.parts" --workflow "$work/yml-no-part-job"
refuses no-part-job "lacks the \`translation-part\` job or the \`translation\` job"
run no-workflow --parts "$work/base.parts" --workflow "$work/does-not-exist.yml"
refuses no-workflow "No such file"
run no-parts --parts "$work/does-not-exist.txt" --workflow "$work/base.yml"
refuses no-parts "No such file"
: > "$work/empty-table"
run empty-table --table "$work/empty-table" --parts "$work/base.parts" --workflow "$work/base.yml"
refuses empty-table "the script lists no phase"
run no-script --script "$work/no-such-no-sorry.sh" --parts "$work/base.parts" --workflow "$work/base.yml"
refuses no-script "did not list its phases"

echo "check-no-sorry-parts-coverage-cases: $cases cases (the files of the tree and of a tree with a part declared empty; a phase in no part or in two, and a slice of the dispatcher in none or two, with the parts reader's refusals in place and removed; a phase the script gains or loses; a part name in the workflow with no part, a part missing from the workflow, in the pull-request list, the push list and for the part declared empty; a list that names a part twice, the partitions swapped, an expression or a job of another shape; files that cannot be read) gave the expected result"
