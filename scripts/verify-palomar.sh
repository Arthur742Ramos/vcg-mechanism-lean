#!/usr/bin/env bash
set -euo pipefail

repository_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repository_root"

if [ -d "$HOME/.elan/bin" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi

command -v lake >/dev/null 2>&1 || {
  echo "error: lake is required" >&2
  exit 1
}
command -v python3 >/dev/null 2>&1 || {
  echo "error: python3 is required" >&2
  exit 1
}
command -v elan >/dev/null 2>&1 || {
  echo "error: elan is required to locate the pinned Lean toolchain" >&2
  exit 1
}

toolchain_entry=$(tr -d '[:space:]' < lean-toolchain)
toolchain_lean=$(elan which lean)
toolchain_root=$(dirname -- "$(dirname -- "$toolchain_lean")")
export LAKE_HOME="$toolchain_root"
export LEAN_SYSROOT="$toolchain_root"
export LEAN="$toolchain_root/bin/lean"
export PATH="$toolchain_root/bin:$HOME/.elan/bin:$PATH"

for required_file in \
  lakefile.toml lean-toolchain comparator.json \
  formalization.yaml Challenge.lean Solution.lean README.md LICENSE; do
  if [ ! -f "$required_file" ] || [ -L "$required_file" ]; then
    echo "error: required Palomar file is missing or not regular: $required_file" >&2
    exit 1
  fi
done

check_tmpdir=$(mktemp -d)
trap 'rm -rf -- "$check_tmpdir"' EXIT

# In the managed exec namespace Lean may see a host PID in /proc/<pid>/exe.
# Redirect those reads to the current process so Lean can locate its sysroot.
cat >"$check_tmpdir/lean-proc-self.c" <<'C'
#define _GNU_SOURCE
#include <dlfcn.h>
#include <fcntl.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>

static int is_proc_pid_exe(const char *path) {
  if (path == NULL || strncmp(path, "/proc/", 6) != 0) return 0;
  const char *p = path + 6;
  if (*p < '0' || *p > '9') return 0;
  while (*p >= '0' && *p <= '9') ++p;
  return strcmp(p, "/exe") == 0;
}

ssize_t readlink(const char *path, char *buffer, size_t size) {
  static ssize_t (*real_readlink)(const char *, char *, size_t);
  if (real_readlink == NULL) real_readlink = dlsym(RTLD_NEXT, "readlink");
  if (is_proc_pid_exe(path)) path = "/proc/self/exe";
  return real_readlink(path, buffer, size);
}

ssize_t readlinkat(int dirfd, const char *path, char *buffer, size_t size) {
  static ssize_t (*real_readlinkat)(int, const char *, char *, size_t);
  if (real_readlinkat == NULL) real_readlinkat = dlsym(RTLD_NEXT, "readlinkat");
  if (dirfd == AT_FDCWD && is_proc_pid_exe(path)) path = "/proc/self/exe";
  return real_readlinkat(dirfd, path, buffer, size);
}
C
command -v cc >/dev/null 2>&1 || {
  echo "error: cc is required to prepare the local Lean process shim" >&2
  exit 1
}
cc -shared -fPIC -o "$check_tmpdir/lean-proc-self.so" \
  "$check_tmpdir/lean-proc-self.c" -ldl
export LD_PRELOAD="$check_tmpdir/lean-proc-self.so${LD_PRELOAD:+:$LD_PRELOAD}"

expected_version=${toolchain_entry#*:}
expected_lean_version=${expected_version#v}
lake_version=$(lake --version)
case "$lake_version" in
  *"$expected_version"*|*"Lean version $expected_lean_version"*) ;;
  *)
    echo "error: lake does not match lean-toolchain $toolchain_entry: $lake_version" >&2
    exit 1
    ;;
esac
if [ ! -x "$toolchain_root/bin/lean" ]; then
  echo "error: pinned toolchain Lean binary is missing: $toolchain_root/bin/lean" >&2
  exit 1
fi

python3 - <<'PY'
import json
import pathlib
import re

config = json.loads(pathlib.Path("comparator.json").read_text(encoding="utf-8"))
expected_definitions = [
    "VCG.Valuation",
    "VCG.welfare",
    "VCG.xstar",
    "VCG.othersWelfare",
    "VCG.pivotTerm",
    "VCG.clarkePayment",
    "VCG.utility",
    "VCG.trueUtility",
]
expected_theorems = [
    "VCG.vcg_efficient",
    "VCG.vcg_truthful",
    "VCG.vcg_individualRational",
    "VCG.vcg_noDeficit",
]
if config.get("challenge_module") != "Challenge":
    raise SystemExit("error: comparator challenge_module must be Challenge")
if config.get("solution_module") != "Solution":
    raise SystemExit("error: comparator solution_module must be Solution")
if config.get("definition_names") != expected_definitions:
    raise SystemExit(f"error: unexpected definition_names: {config.get('definition_names')}")
if config.get("theorem_names") != expected_theorems:
    raise SystemExit(f"error: unexpected theorem_names: {config.get('theorem_names')}")
if config.get("enable_nanoda") is not True:
    raise SystemExit("error: enable_nanoda must be true")
if set(config.get("permitted_axioms", [])) != {
    "propext", "Classical.choice", "Quot.sound"
}:
    raise SystemExit("error: permitted_axioms must be propext, Classical.choice, and Quot.sound")

challenge = pathlib.Path("Challenge.lean").read_text(encoding="utf-8")
sorry_count = len(re.findall(r"\bsorry\b", challenge))
if sorry_count != 11:
    raise SystemExit(f"error: Challenge.lean must contain exactly 11 sorry holes, found {sorry_count}")
if re.search(r"\b(admit|axiom|unsafe)\b", challenge):
    raise SystemExit("error: Challenge.lean contains admit, axiom, or unsafe")

for path in [pathlib.Path("Solution.lean"), *sorted(pathlib.Path("VCG").rglob("*.lean"))]:
    source = path.read_text(encoding="utf-8")
    found = re.findall(r"\b(sorry|admit|axiom|unsafe)\b", source)
    if found:
        raise SystemExit(f"error: forbidden token(s) {sorted(set(found))} found in {path}")
print("Challenge placeholder count passed (11); VCG/ and Solution.lean contain no forbidden placeholders or declarations.")
PY

lake build

# Reproduce Palomar's standalone Challenge compilation without project modules.
lake_lean_path=$(lake env printenv LEAN_PATH)
restricted_lean_path=$(python3 - "$repository_root/.lake/build/lib/lean" "$lake_lean_path" <<'PY'
import os
import pathlib
import sys

project_lib = pathlib.Path(sys.argv[1]).resolve()
entries = sys.argv[2].split(os.pathsep)
kept = []
removed = 0
for entry in entries:
    if pathlib.Path(entry or ".").resolve() == project_lib:
        removed += 1
    elif entry:
        kept.append(entry)
if not removed:
    raise SystemExit(f"error: project Lean library path was not present in lake LEAN_PATH: {project_lib}")
print(os.pathsep.join(kept))
PY
)
standalone_tmpdir="$check_tmpdir/standalone-challenge"
mkdir "$standalone_tmpdir"
cp Challenge.lean "$standalone_tmpdir/Challenge.lean"
echo "Standalone Challenge compilation:"
if ! (cd "$standalone_tmpdir" && LEAN_PATH="$restricted_lean_path" "$toolchain_root/bin/lean" Challenge.lean) \
    >"$check_tmpdir/standalone-challenge.out" 2>&1; then
  cat "$check_tmpdir/standalone-challenge.out" >&2
  exit 1
fi
cat "$check_tmpdir/standalone-challenge.out"
echo "Standalone Challenge compilation passed."

if ! lake env lean --src-deps Challenge.lean >"$check_tmpdir/challenge-src-deps.txt" 2>&1; then
  cat "$check_tmpdir/challenge-src-deps.txt" >&2
  exit 1
fi
python3 - "$check_tmpdir/challenge-src-deps.txt" <<'PY'
import pathlib
import re
import sys

paths = [line.strip() for line in pathlib.Path(sys.argv[1]).read_text(encoding="utf-8").splitlines() if line.strip()]
if not paths:
    raise SystemExit("error: lake reported no Challenge source dependencies")
bad = []
for raw in paths:
    path = pathlib.Path(raw).resolve().as_posix()
    if not (re.search(r"/src/lean/", path) or re.search(r"/.lake/packages/mathlib/", path)):
        bad.append(raw)
if bad:
    raise SystemExit("error: Challenge imports source files outside the Lean/Mathlib allowlist:\n" + "\n".join(bad))
print(f"Challenge import-source allowlist passed ({len(paths)} source files).")
PY

python3 - "$check_tmpdir" <<'PY'
import json
import pathlib
import sys

config = json.loads(pathlib.Path("comparator.json").read_text(encoding="utf-8"))
temp = pathlib.Path(sys.argv[1])
names = config["definition_names"] + config["theorem_names"]

for module in ("Challenge", "Solution"):
    checks = temp / f"{module}Check.lean"
    lines = [f"import {module}", ""]
    lines.extend(f"#check @{name}" for name in names)
    lines.extend(["", "open Lean", "", "run_cmd do", "  let env ← getEnv"])
    for name in config["definition_names"]:
        lines.extend([
            f"  match env.find? `{name} with",
            "  | some (.defnInfo _) => pure ()",
            f"  | some _ => throwError \"comparator definition is not a def: {name}\"",
            f"  | none => throwError \"missing comparator definition: {name}\"",
        ])
    for name in config["theorem_names"]:
        lines.extend([
            f"  match env.find? `{name} with",
            "  | some (.thmInfo _) => pure ()",
            f"  | some _ => throwError \"comparator theorem is not a theorem: {name}\"",
            f"  | none => throwError \"missing comparator theorem: {name}\"",
        ])
    checks.write_text("\n".join(lines) + "\n", encoding="utf-8")

axioms = temp / "AxiomCheck.lean"
axiom_lines = ["import Solution", ""]
axiom_lines.extend(f"#print axioms {name}" for name in config["theorem_names"])
axioms.write_text("\n".join(axiom_lines) + "\n", encoding="utf-8")
PY

lake env lean "$check_tmpdir/ChallengeCheck.lean"
lake env lean "$check_tmpdir/SolutionCheck.lean"

if ! lake env lean "$check_tmpdir/AxiomCheck.lean" >"$check_tmpdir/axioms.out" 2>&1; then
  cat "$check_tmpdir/axioms.out" >&2
  exit 1
fi
cat "$check_tmpdir/axioms.out"

python3 - "$check_tmpdir/axioms.out" <<'PY'
import json
import pathlib
import re
import sys

config = json.loads(pathlib.Path("comparator.json").read_text(encoding="utf-8"))
output = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
allowed = set(config["permitted_axioms"])
for theorem in config["theorem_names"]:
    quoted_name = re.escape(theorem)
    no_axioms = re.search(rf"'{quoted_name}' does not depend on any axioms", output)
    report = re.search(rf"'{quoted_name}' depends on axioms:\s*\[([^\]]*)\]", output)
    if bool(no_axioms) == bool(report):
        raise SystemExit(f"error: missing or duplicate #print axioms report for {theorem}")
    raw_axioms = "" if no_axioms else report.group(1)
    axioms = {name.strip() for name in raw_axioms.split(",") if name.strip()}
    extra = axioms - allowed
    if extra:
        raise SystemExit(f"error: {theorem} uses disallowed axioms: {sorted(extra)}")
    print(f"Axiom audit passed for {theorem}: {', '.join(sorted(axioms)) or 'none'}")
PY

comparator_status=0
lake comparator --config=comparator.json --inadvisably-no-sandbox 2>&1 | tee "$check_tmpdir/comparator.out" || comparator_status=$?
if [ "$comparator_status" -ne 0 ]; then
  echo "error: lake comparator exited with status $comparator_status" >&2
  exit "$comparator_status"
fi

git diff --check
echo "Local Palomar declaration, build, axiom, sorry, comparator, and whitespace checks passed."
