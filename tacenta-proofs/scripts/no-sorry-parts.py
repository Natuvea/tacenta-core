#!/usr/bin/env python3
"""The parts of a split run of `no-sorry.sh`, and the combiner that gives their verdict.

`no-sorry.sh` is one long run of phases. CI runs it split over machines: each job of a matrix runs one
*part* (`NO_SORRY_PART=<part>`), which is the run with every phase that is not the part's own left out,
and one more job runs the *combiner* (`NO_SORRY_COMBINE=<dir>`, `NO_SORRY_PARTITION=<partition>`) over the
directories the parts wrote. `no-sorry.sh` calls this program for both; it is not meant to be run by hand.

The phases are what `no-sorry.sh` itself lists (`NO_SORRY_LIST=1`), not what the parts file says:

  phase  <id>  prelude|plain|sliceable  <label>
  unit   <id>  <name>  <source>              (one line for each control of a sliceable phase, in order)

A prelude phase (the three package builds and their `sorry` scans) runs in every part, since every other
phase reads what it built. Every other phase belongs to exactly one part of a partition. A sliceable phase
may instead be split into S slices, `<id>@k/S`, each its own part: slice k runs the phase's controls whose
place in its list is k modulo S.

The parts file, `tacenta-proofs/scripts/no-sorry-parts.txt`, holds one part per line:

  <partition> <part>: <phase>[@k/S] ...      or      <partition> <part>: *

`*` is every phase that is not a prelude, unsliced. Part names are unique over the file. Each partition
must cover each non-prelude phase of the script exactly once: one part names it, or every slice 0..S-1 of
one S is named once. A phase the script gains and the file does not assign fails every part before it
runs a phase, and fails the combiner.

  resolve   --table T --parts F --part P          print the part's phases as `<id>\\t<slice or ->`
  manifest  --dir D --part P ...                  write D/part.json after a part has run
  combine   --table T --parts F --partition N --dir D   check a set of part directories

What the combiner requires of the directory it is given:

  - exactly one directory for each part of the partition, holding `part.json`, `part.log` and, for a
    sliceable phase, the phase's own directory, all regular files and nothing else;
  - each manifest made on the combiner's own commit and tree, from a clean checkout that the run left
    clean, by the same `no-sorry.sh` and the same parts file (sha256), with one toolchain and one restored
    build cache across all parts, no test seam set, and exit status 0;
  - each part's phases exactly the prelude and the part's own phases, in the script's order, each with
    status 0, and its log carrying one closing line for each of them and no `::error::` or `WRONG` line;
  - for a sliceable phase, the result file of each slice naming its slice and selecting exactly the
    controls k modulo S of the list the script prints now, each refused by Lean, after the unmodified
    copies of their sources were accepted, with one log for each; between the slices every control once.

A manifest is written by the part about itself. A part directory forged to look right by something other
than the script is not detected; what holds that is that the combiner downloads only the artifacts of its
own workflow run, which the parts of that run uploaded.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

NAME = r'[a-z][a-z0-9-]*'
SPEC = re.compile(r'(' + NAME + r')(?:@([0-9]{1,3})/([0-9]{1,3}))?')
LINE = re.compile(r'(' + NAME + r') (' + NAME + r'):((?: \S+)+)')
FORMAT = 'no-sorry-part/1'
MANIFEST_KEYS = {'format', 'partition', 'part', 'commit', 'tree', 'clean', 'script_sha256',
                 'parts_sha256', 'toolchain', 'build_cache', 'seam', 'exit', 'phases'}
RESULT_KEYS = {'source_sha256', 'source_sha256s', 'mutations', 'slice', 'requested_mutations',
               'selected', 'baseline_exits', 'baseline_exit'}
PHASE_LINE = re.compile(r'no-sorry: phase (' + NAME + r')(?: ([0-9]{1,3}/[0-9]{1,3}))? '
                        r'finished with status ([0-9]+) in ([0-9]+)s')
BAD_LINE = re.compile(r'^[ \t]*(?:::error::|WRONG\b)', re.IGNORECASE)


class Refused(Exception):
    pass


def refuse(message):
    raise Refused(message)


def no_repeats(pairs):
    seen = {}
    for key, value in pairs:
        if key in seen:
            refuse(f'the key {key!r} is repeated')
        seen[key] = value
    return seen


def read_json(path):
    if path.is_symlink() or not path.is_file():
        refuse(f'{path} is not a regular file')
    try:
        return json.loads(path.read_bytes().decode('utf-8'), object_pairs_hook=no_repeats)
    except (UnicodeDecodeError, ValueError) as error:
        refuse(f'{path} is not a JSON document: {error}')


def is_int(value):
    return type(value) is int


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


# ---- the phase table, as the script prints it ------------------------------------------------------

def read_table(path):
    phases, kinds, labels, units = [], {}, {}, {}
    for number, line in enumerate(Path(path).read_text().split('\n'), 1):
        if line == '':
            continue
        fields = line.split('\t')
        if fields[0] == 'phase' and len(fields) == 4 and re.fullmatch(NAME, fields[1]) \
                and fields[2] in ('prelude', 'plain', 'sliceable') and fields[3]:
            if fields[1] in kinds:
                refuse(f'the script lists phase {fields[1]} twice')
            phases.append(fields[1])
            kinds[fields[1]] = fields[2]
            labels[fields[1]] = fields[3]
            units[fields[1]] = []
        elif fields[0] == 'unit' and len(fields) == 4 and fields[1] in kinds \
                and kinds[fields[1]] == 'sliceable' and re.fullmatch(NAME, fields[2]) \
                and re.fullmatch(NAME, fields[3]):
            if fields[2] in [u for u, _ in units[fields[1]]]:
                refuse(f'phase {fields[1]} lists control {fields[2]} twice')
            units[fields[1]].append((fields[2], fields[3]))
        else:
            refuse(f'line {number} of the phase table is not a phase or a unit: {line!r}')
    if not phases:
        refuse('the script lists no phase')
    for phase in phases:
        if kinds[phase] == 'sliceable' and not units[phase]:
            refuse(f'sliceable phase {phase} lists no control')
    return phases, kinds, labels, units


# ---- the parts file ------------------------------------------------------------------------------

def read_parts(path, table):
    phases, kinds, _, units = table
    raw = Path(path).read_bytes()
    if b'\r' in raw:
        refuse(f'{path} holds a carriage return')
    try:
        text = raw.decode('utf-8')
    except UnicodeDecodeError:
        refuse(f'{path} is not UTF-8')
    partitions = {}   # partition -> [part]
    owner = {}        # part -> partition
    specs = {}        # part -> [(phase, slice or None)]
    for number, line in enumerate(text.split('\n'), 1):
        if line == '' or line.startswith('#'):
            continue
        found = LINE.fullmatch(line)
        if not found:
            refuse(f'{path}:{number} is not `<partition> <part>: <phase>...`: {line!r}')
        partition, part, rest = found.groups()
        if part in owner:
            refuse(f'{path}:{number}: part {part} is named twice')
        words = rest.split(' ')[1:]
        listed = []
        if words == ['*']:
            listed = [(p, None) for p in phases if kinds[p] != 'prelude']
        else:
            for word in words:
                spec = SPEC.fullmatch(word)
                if not spec:
                    refuse(f'{path}:{number}: {word!r} is not a phase or `<phase>@k/S`')
                phase, k, count = spec.groups()
                if phase not in kinds:
                    refuse(f'{path}:{number}: part {part} names {phase}, which the script does not run')
                if kinds[phase] == 'prelude':
                    refuse(f'{path}:{number}: part {part} names {phase}, a prelude phase every part runs')
                if any(p == phase for p, _ in listed):
                    refuse(f'{path}:{number}: part {part} names {phase} twice')
                if k is None:
                    listed.append((phase, None))
                    continue
                k, count = int(k), int(count)
                if kinds[phase] != 'sliceable':
                    refuse(f'{path}:{number}: part {part} slices {phase}, which the script does not slice')
                if count < 2 or k >= count:
                    refuse(f'{path}:{number}: {word} is not a slice k/S with 0 <= k < S and S >= 2')
                if count > len(units[phase]):
                    refuse(f'{path}:{number}: {phase} has {len(units[phase])} controls, too few for '
                           f'{count} slices')
                listed.append((phase, (k, count)))
        owner[part] = partition
        specs[part] = listed
        partitions.setdefault(partition, []).append(part)
    if not partitions:
        refuse(f'{path} names no part')
    for partition, parts in partitions.items():
        for phase in phases:
            if kinds[phase] == 'prelude':
                continue
            whole = [part for part in parts for p, s in specs[part] if p == phase and s is None]
            sliced = [(part, s) for part in parts for p, s in specs[part] if p == phase and s is not None]
            if not whole and not sliced:
                refuse(f'partition {partition}: phase {phase} is in no part')
            if len(whole) > 1:
                refuse(f'partition {partition}: phase {phase} is in parts {", ".join(whole)}')
            if whole and sliced:
                refuse(f'partition {partition}: phase {phase} is in part {whole[0]} and sliced in '
                       f'{", ".join(p for p, _ in sliced)}')
            if sliced:
                counts = sorted({s[1] for _, s in sliced})
                if len(counts) > 1:
                    refuse(f'partition {partition}: phase {phase} is sliced {" and ".join(map(str, counts))} ways')
                count = counts[0]
                for k in range(count):
                    holders = [part for part, s in sliced if s[0] == k]
                    if not holders:
                        refuse(f'partition {partition}: slice {k}/{count} of {phase} is in no part')
                    if len(holders) > 1:
                        refuse(f'partition {partition}: slice {k}/{count} of {phase} is in parts '
                               f'{", ".join(holders)}')
    return partitions, owner, specs


def selection(table, specs, part):
    """[(phase, slice text or '-')] of a part, in the script's order. An unsliced sliceable phase is 0/1."""
    phases, kinds, _, _ = table
    own = dict(specs[part])
    out = []
    for phase in phases:
        if phase in own:
            s = own[phase]
            if s is not None:
                out.append((phase, f'{s[0]}/{s[1]}'))
            elif kinds[phase] == 'sliceable':
                out.append((phase, '0/1'))
            else:
                out.append((phase, '-'))
    return out


def run_order(table, specs, part):
    """[(phase, slice text or '-')] the part runs: the prelude and its own phases, in the script's order."""
    phases, kinds, _, _ = table
    own = dict(selection(table, specs, part))
    return [(p, '-' if kinds[p] == 'prelude' else own[p]) for p in phases
            if kinds[p] == 'prelude' or p in own]


# ---- resolve ---------------------------------------------------------------------------------------

def cmd_resolve(args):
    table = read_table(args.table)
    _, owner, specs = read_parts(args.parts, table)
    if args.part not in owner:
        refuse(f'{args.parts} has no part {args.part!r}')
    for phase, s in selection(table, specs, args.part):
        print(f'{phase}\t{s}')
    print(f'partition\t{owner[args.part]}', file=sys.stderr)


# ---- manifest --------------------------------------------------------------------------------------

def git(*argv):
    return subprocess.run(['git', *argv], capture_output=True, text=True, check=True).stdout.strip()


def tree_state():
    return git('rev-parse', 'HEAD'), git('rev-parse', 'HEAD^{tree}'), \
        git('status', '--porcelain', '--untracked-files=no') == ''


def cmd_manifest(args):
    table = read_table(args.table)
    _, owner, _ = read_parts(args.parts, table)
    phases = []
    for line in Path(args.status).read_text().split('\n'):
        if line == '':
            continue
        fields = line.split('\t')
        if len(fields) != 4 or not re.fullmatch(r'-?[0-9]+', fields[2]) or not re.fullmatch(r'[0-9]+', fields[3]):
            refuse(f'the status file has a malformed line: {line!r}')
        phases.append({'id': fields[0], 'slice': None if fields[1] == '-' else fields[1],
                       'status': int(fields[2]), 'seconds': int(fields[3])})
    commit, tree, clean = tree_state()
    start_commit, start_tree, start_clean = args.start.split(' ')
    manifest = {
        'format': FORMAT,
        'partition': owner[args.part],
        'part': args.part,
        'commit': start_commit,
        'tree': start_tree,
        'clean': start_clean == 'clean' and clean and commit == start_commit and tree == start_tree,
        'script_sha256': sha256(args.script),
        'parts_sha256': sha256(args.parts),
        'toolchain': args.toolchain,
        'build_cache': args.build_cache,
        'seam': sorted(args.seam.split()) if args.seam else [],
        'exit': args.exit,
        'phases': phases,
    }
    (Path(args.dir) / 'part.json').write_text(json.dumps(manifest, indent=2) + '\n')


# ---- combine ---------------------------------------------------------------------------------------

def check_result(where, path, k, count, units, files):
    """The result file of one slice of a sliceable phase, and the files beside it."""
    result = read_json(path / 'result.json')
    if not isinstance(result, dict) or set(result) != RESULT_KEYS:
        refuse(f'{where}: result.json does not hold exactly the fields {", ".join(sorted(RESULT_KEYS))}')
    if result['slice'] != f'{k}/{count}':
        refuse(f'{where}: the result is of slice {result["slice"]!r}, not {k}/{count}')
    if result['requested_mutations'] != 'all':
        refuse(f'{where}: the run named its controls ({result["requested_mutations"]!r}) rather than slicing them')
    expected = [name for index, (name, _) in enumerate(units) if index % count == k]
    if result['selected'] != expected:
        refuse(f'{where}: slice {k}/{count} selected {result["selected"]!r}, not the controls '
               f'{k} modulo {count} of the {len(units)} the script lists: {expected!r}')
    mutations = result['mutations']
    if not isinstance(mutations, dict) or sorted(mutations) != sorted(expected):
        refuse(f'{where}: the result records the controls {sorted(mutations) if isinstance(mutations, dict) else mutations!r}, '
               f'not the {len(expected)} it selected')
    for name, record in mutations.items():
        if not isinstance(record, dict) or set(record) != {'exit', 'premise'} \
                or not is_int(record['exit']) or record['exit'] != 1 or not isinstance(record['premise'], str):
            refuse(f'{where}: control {name} is not recorded as refused by Lean (exit 1, a premise)')
    sources = sorted({source for index, (_, source) in enumerate(units) if index % count == k})
    baselines = result['baseline_exits']
    if not isinstance(baselines, dict) or sorted(baselines) != sources \
            or any(not is_int(v) or v != 0 for v in baselines.values()) \
            or not is_int(result['baseline_exit']) or result['baseline_exit'] != 0:
        refuse(f'{where}: the unmodified sources {sources} were not each accepted first '
               f'(baselines {baselines!r})')
    want = {'result.json'} | {f'{name}.log' for name in expected} | {f'baseline-{s}.log' for s in sources}
    if files != want:
        extra, missing = sorted(files - want), sorted(want - files)
        refuse(f'{where}: the phase directory holds {"extra " + ", ".join(extra) if extra else ""}'
               f'{"; " if extra and missing else ""}{"missing " + ", ".join(missing) if missing else ""}')
    return expected


def regular_files(where, path):
    """The names of the regular files directly in a directory, refusing anything else."""
    names = set()
    for entry in sorted(path.iterdir()):
        if entry.is_symlink() or not entry.is_file():
            refuse(f'{where}: {entry.name} is not a regular file')
        names.add(entry.name)
    return names


def cmd_combine(args):
    table = read_table(args.table)
    phases, kinds, _, units = table
    partitions, _, specs = read_parts(args.parts, table)
    if args.partition not in partitions:
        refuse(f'{args.parts} has no partition {args.partition!r}')
    parts = partitions[args.partition]
    root = Path(args.dir)
    if root.is_symlink() or not root.is_dir():
        refuse(f'{root} is not a directory')
    commit, tree, _ = tree_state()
    script_sha, parts_sha = sha256(args.script), sha256(args.parts)
    entries = sorted(root.iterdir())
    for entry in entries:
        if entry.is_symlink() or not entry.is_dir():
            refuse(f'{entry} is not a part directory')
    if len(entries) != len(parts):
        refuse(f'{root} holds {len(entries)} part directories, not the {len(parts)} of partition '
               f'{args.partition} ({", ".join(parts)})')
    seen = {}
    toolchains, caches = set(), set()
    slices_run = {}
    for entry in entries:
        where = entry.name
        manifest = read_json(entry / 'part.json')
        if not isinstance(manifest, dict) or set(manifest) != MANIFEST_KEYS:
            refuse(f'{where}: part.json does not hold exactly the fields {", ".join(sorted(MANIFEST_KEYS))}')
        if manifest['format'] != FORMAT:
            refuse(f'{where}: part.json is not of format {FORMAT}')
        part = manifest['part']
        if manifest['partition'] != args.partition or part not in parts:
            refuse(f'{where}: part {part!r} of partition {manifest["partition"]!r} is not a part of '
                   f'partition {args.partition}')
        if part in seen:
            refuse(f'{where} and {seen[part]} are both part {part}')
        seen[part] = where
        where = f'part {part} ({entry.name})'
        if manifest['commit'] != commit:
            refuse(f'{where} ran on commit {manifest["commit"]}, not {commit}')
        if manifest['tree'] != tree:
            refuse(f'{where} ran on tree {manifest["tree"]}, not {tree}')
        if manifest['clean'] is not True:
            refuse(f'{where} ran in a checkout with changes to tracked files, or left one')
        if manifest['script_sha256'] != script_sha:
            refuse(f'{where} was run by a no-sorry.sh of sha256 {manifest["script_sha256"]}, not {script_sha}')
        if manifest['parts_sha256'] != parts_sha:
            refuse(f'{where} was run with a parts file of sha256 {manifest["parts_sha256"]}, not {parts_sha}')
        if manifest['seam'] != []:
            refuse(f'{where} ran with the test seam {manifest["seam"]!r}, so it is not the gate')
        if not is_int(manifest['exit']) or manifest['exit'] != 0:
            refuse(f'{where} exited with status {manifest["exit"]!r}')
        for key in ('toolchain', 'build_cache'):
            if not isinstance(manifest[key], str) or not manifest[key]:
                refuse(f'{where}: {key} is not a non-empty string')
        toolchains.add(manifest['toolchain'])
        caches.add(manifest['build_cache'])
        order = run_order(table, specs, part)
        recorded = manifest['phases']
        if not isinstance(recorded, list) or any(
                not isinstance(r, dict) or set(r) != {'id', 'slice', 'status', 'seconds'} for r in recorded):
            refuse(f'{where}: its phases are not a list of id, slice, status and seconds')
        got = [(r['id'], '-' if r['slice'] is None else r['slice']) for r in recorded]
        if got != order:
            refuse(f'{where} ran the phases {got}, not the prelude and its own phases {order}')
        for r in recorded:
            if not is_int(r['status']) or r['status'] != 0:
                refuse(f'{where}: phase {r["id"]} finished with status {r["status"]!r}')
            if not is_int(r['seconds']) or r['seconds'] < 0:
                refuse(f'{where}: phase {r["id"]} has no time')
        # The files: the manifest, the log and one directory for each sliceable phase.
        sliceable = [p for p, _ in order if kinds[p] == 'sliceable']
        names = set()
        for item in sorted(entry.iterdir()):
            if item.is_symlink():
                refuse(f'{where}: {item.name} is a link')
            if item.is_dir():
                if item.name not in sliceable:
                    refuse(f'{where}: {item.name} is not the directory of one of its sliceable phases')
            elif not item.is_file():
                refuse(f'{where}: {item.name} is not a regular file')
            names.add(item.name)
        want = {'part.json', 'part.log'} | set(sliceable)
        if names != want:
            refuse(f'{where}: holds {sorted(names)}, not {sorted(want)}')
        # The log: one closing line per phase, in order, each status 0, and no failure line.
        text = (entry / 'part.log').read_bytes().decode('utf-8', errors='replace')
        lines = re.split(r'[\r\n]', text)
        bad = [line for line in lines if BAD_LINE.search(line)]
        if bad:
            refuse(f'{where}: its log has {len(bad)} failure line(s), the first: {bad[0][:160]!r}')
        closing = [m.groups() for m in (PHASE_LINE.fullmatch(line) for line in lines) if m]
        if len([line for line in lines if line.startswith('no-sorry: phase ')]) != len(closing):
            refuse(f'{where}: its log has a phase line that is not a closing line')
        if [(p, s or '-') for p, s, _, _ in closing] != order or any(st != '0' for _, _, st, _ in closing):
            refuse(f'{where}: its log closes the phases {closing}, not each of {order} with status 0')
        for phase in sliceable:
            s = dict(order)[phase]
            k, count = map(int, s.split('/'))
            directory = entry / phase
            files = regular_files(f'{where}: {phase}', directory)
            selected = check_result(f'{where}: {phase} {s}', directory, k, count, units[phase], files)
            slices_run.setdefault(phase, []).extend(selected)
    absent = [part for part in parts if part not in seen]
    if absent:
        refuse(f'no directory is part {", ".join(absent)} of partition {args.partition}')
    if len(toolchains) != 1:
        refuse(f'the parts ran on {len(toolchains)} toolchains: {sorted(toolchains)}')
    if len(caches) != 1:
        refuse(f'the parts restored {len(caches)} different build caches: {sorted(caches)}')
    for phase in phases:
        if kinds[phase] != 'sliceable':
            continue
        ran = slices_run.get(phase, [])
        names = [name for name, _ in units[phase]]
        twice = sorted({n for n in ran if ran.count(n) > 1})
        if twice:
            refuse(f'{phase}: controls run by two slices: {", ".join(twice)}')
        if sorted(ran) != sorted(names):
            refuse(f'{phase}: controls run by no slice: {", ".join(sorted(set(names) - set(ran)))}')
    sliced = {p: len(set(n for n, _ in units[p])) for p in phases if kinds[p] == 'sliceable'}
    print(f'no-sorry: {len(parts)} part(s) of partition {args.partition} on {commit[:7]} ran the '
          f'{len([p for p in phases if kinds[p] != "prelude"])} phases that are not the prelude once each, '
          f'and the prelude in every part'
          + ''.join(f'; {p}: {n} controls, each once' for p, n in sliced.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    sub = parser.add_subparsers(dest='command', required=True)
    r = sub.add_parser('resolve')
    r.add_argument('--table', required=True)
    r.add_argument('--parts', required=True)
    r.add_argument('--part', required=True)
    m = sub.add_parser('manifest')
    for name in ('--table', '--parts', '--part', '--dir', '--status', '--script', '--start',
                 '--toolchain', '--build-cache'):
        m.add_argument(name, required=True)
    m.add_argument('--seam', default='')
    m.add_argument('--exit', type=int, required=True)
    c = sub.add_parser('combine')
    for name in ('--table', '--parts', '--partition', '--dir', '--script'):
        c.add_argument(name, required=True)
    args = parser.parse_args()
    try:
        {'resolve': cmd_resolve, 'manifest': cmd_manifest, 'combine': cmd_combine}[args.command](args)
    except Refused as error:
        print(f'::error::no-sorry parts: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
