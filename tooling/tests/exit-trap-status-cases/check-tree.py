"""The tree check of tooling/tests/run-exit-trap-status-cases.sh, whose header says what it reads and refuses.

    python3 -I check-tree.py GUARD_FILE [--exempt PATH]... (--tree | --files FILE...)

GUARD_FILE holds the exit-status guard word for word, as the runner reads it from itself. It is a textual
tripwire, conservative by design: a file that holds a `trap` in command position it cannot read as a plain
`trap HANDLER SIGNAL...` line of its own is refused, whatever the trap does, and the exemptions by name are the
only way past it.
"""
import os
import re
import subprocess
import sys

guard = open(sys.argv[1], encoding="utf-8").read().rstrip("\n").split("\n")
args = sys.argv[2:]
exempt = []
while args[:1] == ["--exempt"]:
    exempt.append(args[1])
    args = args[2:]
SHELLS = {"sh", "bash", "dash", "ksh", "zsh"}
# A `trap` in command position: at the start of a line or after a separator, a keyword, or a prefix builtin.
TRAP_CMD = re.compile(r"(?:^|[;&|{(!]|\bthen\b|\bdo\b|\belse\b|\bcommand\b|\bbuiltin\b|\bexec\b|\btime\b)\s*trap(?=\s|$)")
PLAIN = re.compile(r"^\s*trap\s+('[^']*'|[^\s'\"]+)((?:\s+[A-Za-z0-9+-]+)*)\s*(?:#.*)?$")
GUARDED = re.compile(r"""^'exit_guard_rc=\$\?; set \+e; ([^']+); exit_guard "\$exit_guard_rc"'$""")
FORM = "the trap is not `trap 'exit_guard_rc=$?; set +e; <cleanup>; exit_guard \"$exit_guard_rc\"' EXIT`"
UNREAD = ("a trap command the check cannot classify (it reads only a plain `trap HANDLER SIGNAL...` line of "
          "its own); write it so, or exempt the script by name")


def interpreter(first):
    """The program a `#!` line runs (through env, with its options), "" for an unreadable one, None for no `#!`."""
    if not first.startswith("#!"):
        return None
    words = first[2:].split()
    if not words:
        return ""
    prog, rest = os.path.basename(words[0]), words[1:]
    if prog == "env":
        while rest and (rest[0].startswith("-") or "=" in rest[0]):
            option = rest.pop(0)
            if option in ("-u", "--unset", "-C", "--chdir"):
                rest = rest[1:]
        prog = os.path.basename(rest[0]) if rest else ""
    return prog


def is_shell(path, executable):
    if os.path.islink(path) or not os.path.isfile(path):
        return False
    if path.endswith((".sh", ".bash")) or path.startswith(".githooks/"):
        return True
    with open(path, "rb") as handle:
        first = handle.readline(400).decode("utf-8", "replace").rstrip("\n")
    prog = interpreter(first)
    if prog is None:
        return executable  # an executable with no `#!` runs under the shell
    return prog in SHELLS or prog == ""


def dequoted(line):
    """The line with the quoting the shell removes from a command word taken out: a backslash before a letter,
    empty quotes, and quotes around a whole word."""
    line = re.sub(r"\\(?=[A-Za-z])", "", line).replace("''", "").replace('""', "")
    return re.sub(r"(['\"])([A-Za-z]+)\1", r"\2", line)


def signal_names(words):
    names = []
    for w in words:
        u = w.upper()
        u = u[3:] if u.startswith("SIG") else u
        names.append("EXIT" if u == "0" else u)
    return names


def problems(lines):
    """None when the file sets no trap the check must hold to the guard, else its problems as (index, text)."""
    exit_traps, unread, guarded_traps = [], [], []
    for i, line in enumerate(lines):
        if line.lstrip().startswith("#"):
            continue
        if not TRAP_CMD.search(line) and TRAP_CMD.search(dequoted(line)):
            unread.append(i)  # a quoted or escaped spelling of trap: \trap, "trap", t''rap
            continue
        for m in TRAP_CMD.finditer(line):
            plain = PLAIN.match(line)
            if not plain or line[:m.start()].strip():
                unread.append(i)
                break
            handler, words = plain.group(1), plain.group(2).split()
            if handler.startswith("-"):
                break  # trap - SIGNALS clears; trap -p and -l print
            if "EXIT" in signal_names(words):
                exit_traps.append(i)
                g = GUARDED.match(handler)
                if g and words == ["EXIT"]:
                    guarded_traps.append((i, g.group(1)))
            break
    if not exit_traps and not unread:
        return None
    found = [(i, UNREAD) for i in unread]
    has_guard = any(re.match(r"^\s*exit_guard\s*\(\)", l) for l in lines)
    if not has_guard:
        return sorted(found + [(i, "an EXIT trap without the exit-status guard") for i in exit_traps])
    first = min(exit_traps + unread)
    at = next((i for i in range(len(lines) - len(guard) + 1) if lines[i:i + len(guard)] == guard), None)
    if at is None or at > first:
        found.append((first, "the exit-status guard, word for word, is not above the first EXIT trap"))
    guard_lines = set(range(at, at + len(guard))) if at is not None else set()
    cleanups = dict(guarded_traps)
    for i in exit_traps:
        if i not in cleanups:
            found.append((i, FORM))
        elif re.search(r"\b(exit|exec|return)\b", cleanups[i]):
            found.append((i, "the guarded trap's cleanup leaves through exit, exec or return, past the guard"))
    code = [i for i, l in enumerate(lines) if l.strip() and not l.lstrip().startswith("#")]
    finishes = 0
    for i, line in enumerate(lines):
        if i in guard_lines or line.lstrip().startswith("#"):
            continue
        if re.search(r"(^|[\s;{(&|])done_ok(\s*$|\s*[;)}&|])", line) and i > first:
            finishes += 1
        if re.search(r"\bfinished=", line) and not re.match(r"^\s*(finished=no\s*$|done_ok\s*\(\))", line):
            later = [k for k in code if k > i]
            if (re.match(r"^\s*finished=yes\s*$", line)
                    and (not later or re.match(r"^\s*exit(\s|$)", lines[later[0]]))):
                finishes += i > first
            else:
                found.append((i, "`finished=yes` is set before the end and not right before an exit, so an abort "
                                 "after it would pass"))
    if exit_traps and not finishes:
        found.append((first, "no `finished=yes` and no done_ok after the trap"))
    return sorted(found)


if args[:1] == ["--tree"]:
    listed = subprocess.run(["git", "ls-files", "-s", "-z"], check=True, capture_output=True).stdout
    files = []
    for entry in listed.decode("utf-8", "replace").split("\0"):
        if not entry:
            continue
        meta, path = entry.split("\t", 1)
        if is_shell(path, meta.split()[0] == "100755"):
            files.append(path)
elif args[:1] == ["--files"] and args[1:]:
    files = args[1:]
else:
    print("exit-trap tree check: --tree or --files FILE...", file=sys.stderr)
    sys.exit(2)
bad = exposed = 0
for path in files:
    lines = open(path, encoding="utf-8", errors="replace").read().split("\n")
    found = problems(lines)
    if found is None:
        if path in exempt:
            bad += 1
            print(f"{path}: exempt by name, but it sets no EXIT trap; drop the exemption", file=sys.stderr)
        continue
    exposed += 1
    if path in exempt:
        if not found:
            bad += 1
            print(f"{path}: exempt by name, but it carries the guard; drop the exemption", file=sys.stderr)
        continue
    for i, message in found:
        bad += 1
        print(f"{path}:{i + 1}: {message}", file=sys.stderr)
for path in exempt:
    if path not in files:
        bad += 1
        print(f"{path}: exempt by name, but it is not a file this check reads; drop the exemption", file=sys.stderr)
if bad:
    print(f"exit-trap tree check: {bad} problem(s); see the header of tooling/tests/run-exit-trap-status-cases.sh",
          file=sys.stderr)
    sys.exit(1)
print(f"exit-trap tree check: {len(files)} file(s) read, {exposed} with an EXIT trap, "
      f"{exposed - len(exempt)} guarded, {len(exempt)} exempt by name")