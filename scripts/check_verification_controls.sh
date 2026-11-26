#!/usr/bin/env bash
# Positive and negative controls for the verification checks (issue 6).
#
# Run from the repository root:  scripts/check_verification_controls.sh
#
# Each control works in its own temporary copy of the checkout (tracked and
# untracked, non-ignored files plus the existing .lake build directory), so
# the copy has its own Lake build directory. The script applies one mutation,
# requires the mutated module to compile, and requires the designated check
# to fail with the expected diagnostic. The copies are removed on exit and the
# caller's `git status` (including untracked files) is compared before and
# after. Exit status 0 means every control behaved as specified.
set -u -o pipefail

ROOT=$(git rev-parse --show-toplevel)
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

STATUS_BEFORE=$(git status --porcelain=v1 --untracked-files=all)
WORK=$(mktemp -d "${TMPDIR:-/tmp}/newton-controls.XXXXXX")
cleanup() { rm -rf "$WORK"; }
trap cleanup EXIT

FAILED=0
pass() { printf 'PASS  %s\n' "$1"; }
fail() { printf 'FAIL  %s\n' "$1"; FAILED=1; }

# Fresh copy of the caller's sources and build directory.
make_copy() {
  local dest="$WORK/$1"
  mkdir -p "$dest"
  git ls-files -z --cached --others --exclude-standard |
    tar --null -T - -cf - | tar -xf - -C "$dest"
  if [ -d .lake ]; then cp -a .lake "$dest/.lake"; fi
  printf '%s\n' "$dest"
}

# edit FILE OLD NEW: replace exactly one occurrence of OLD by NEW.
edit() {
  python3 - "$1" "$2" "$3" <<'PY'
import sys
path, old, new = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(path, encoding="utf-8").read()
if text.count(old) != 1:
    sys.exit(f"mutation anchor occurs {text.count(old)} times in {path}: {old!r}")
open(path, "w", encoding="utf-8").write(text.replace(old, new))
PY
}

# expect_success NAME DIR CMD...
expect_success() {
  local name=$1 dir=$2; shift 2
  if (cd "$dir" && "$@") >"$dir/.control.log" 2>&1; then
    return 0
  fi
  fail "$name: '$*' should succeed"; tail -n 20 "$dir/.control.log"; return 1
}

# expect_failure NAME DIR PATTERN CMD...
expect_failure() {
  local name=$1 dir=$2 pattern=$3; shift 3
  if (cd "$dir" && "$@") >"$dir/.control.log" 2>&1; then
    fail "$name: '$*' should fail"; return 1
  fi
  if grep -Eq -- "$pattern" "$dir/.control.log"; then
    pass "$name: rejected ($(grep -Eo -m1 -- "$pattern" "$dir/.control.log"))"
    return 0
  else
    fail "$name: failed without the expected diagnostic /$pattern/"
    tail -n 20 "$dir/.control.log"
    return 1
  fi
}

AREAL=ModernLib/Diagnostic/ArealBounds.lean
LAWI=NewtonLimitDynamics/Historical/LawI.lean

# 0. Positive control: the unchanged sources pass every check.
D=$(make_copy positive)
if expect_success "positive build" "$D" lake build &&
   expect_success "positive NewtonLimitDynamics" "$D" lake build NewtonLimitDynamics &&
   expect_success "positive references" "$D" lake env lean research/CheckReferences.lean; then
  pass "positive control: unchanged sources build, freeze and pass CheckReferences"
fi

# 1. A changed statement: the frozen type rejects it.
D=$(make_copy statement)
edit "$D/$AREAL" 'theorem different_polygons :
    ¬ pointEquiv (schedule freeField [Fraction.ofInt 1, Fraction.ofInt 1] start).1
        (schedule hookeField [Fraction.ofInt 1, Fraction.ofInt 1] start).1 := by
  decide' 'theorem different_polygons : True := True.intro'
expect_success "changed statement compiles" "$D" lake build ModernLib.Diagnostic.ArealBounds &&
  expect_failure "changed statement" "$D" "different_polygons" \
    lake build research.FrozenStatements

# 2. A changed definition: the polygon inequality still compiles; the frozen
#    initial-state equation fails.
D=$(make_copy definition)
edit "$D/$AREAL" '((Fraction.ofInt 1, Fraction.ofInt 0), (Fraction.ofInt 0, Fraction.ofInt 1))' \
  '((Fraction.ofInt 2, Fraction.ofInt 0), (Fraction.ofInt 0, Fraction.ofInt 1))'
expect_success "changed definition compiles" "$D" lake build ModernLib.Diagnostic.ArealBounds &&
  expect_failure "changed definition" "$D" \
    "start = \(\(Fraction\.ofInt 1, Fraction\.ofInt 0\)" \
    lake build research.FrozenStatements

# 3. An added sorry: CheckReferences reports sorryAx.
D=$(make_copy sorry)
edit "$D/$AREAL" '(schedule hookeField [Fraction.ofInt 1, Fraction.ofInt 1] start).1 := by
  decide' '(schedule hookeField [Fraction.ofInt 1, Fraction.ofInt 1] start).1 := by
  sorry'
expect_success "sorry compiles" "$D" lake build NewtonLimitDynamics &&
  expect_failure "added sorry" "$D" "forbidden axiom sorryAx" \
    lake env lean research/CheckReferences.lean

# 4. A fresh project axiom used by a separate proof: reported by name.
D=$(make_copy axiom)
printf '%s\n' '' \
  'namespace NewtonLimitDynamics.Diagnostic.ArealBounds' \
  'axiom controlAxiom : Polygon.CentralSchedule.central freeField' \
  'theorem controlUsesAxiom : Polygon.CentralSchedule.central freeField := controlAxiom' \
  'end NewtonLimitDynamics.Diagnostic.ArealBounds' >>"$D/$AREAL"
expect_success "axiom compiles" "$D" lake build NewtonLimitDynamics &&
  expect_failure "forbidden axiom" "$D" \
    "forbidden axiom NewtonLimitDynamics\.Diagnostic\.ArealBounds\.controlAxiom" \
    lake env lean research/CheckReferences.lean

# 5. An anachronical import alone passes; a primary use is reported with its path.
D=$(make_copy anachronical)
edit "$D/$LAWI" 'import BarrowLib.Polygon.ZeroForce' \
  'import BarrowLib.Polygon.ZeroForce
import ModernLib.Diagnostic.ArealBounds'
if expect_success "anachronical import compiles" "$D" lake build NewtonLimitDynamics &&
   expect_success "anachronical import alone" "$D" lake env lean research/CheckReferences.lean; then
  pass "anachronical import alone: provenance check passes"
fi
edit "$D/$LAWI" 'end Principia1687.Laws' \
  'theorem controlPrimaryUse :
    NewtonLimitDynamics.Polygon.CentralSchedule.central
      NewtonLimitDynamics.Diagnostic.ArealBounds.freeField :=
  NewtonLimitDynamics.Diagnostic.ArealBounds.freeField_central
end Principia1687.Laws'
expect_success "anachronical use compiles" "$D" lake build NewtonLimitDynamics &&
  expect_failure "anachronical use" "$D" \
    "anachronical dependency in primary declaration Principia1687\.Laws\.controlPrimaryUse: \[Principia1687\.Laws\.controlPrimaryUse," \
    lake env lean research/CheckReferences.lean &&
  if grep -Eq "^ NewtonLimitDynamics\.Diagnostic\.ArealBounds\.(freeField|freeField_central)\]" "$D/.control.log"; then
    pass "anachronical use: the reported path ends in $(grep -Eo -m1 'NewtonLimitDynamics\.Diagnostic\.ArealBounds\.freeField[a-z_]*' "$D/.control.log")"
  else
    fail "anachronical use: the reported path does not reach ArealBounds"
  fi

STATUS_AFTER=$(git status --porcelain=v1 --untracked-files=all)
if [ "$STATUS_BEFORE" = "$STATUS_AFTER" ]; then
  pass "caller checkout unchanged (git status, including untracked files)"
else
  fail "caller checkout changed"; diff <(printf '%s\n' "$STATUS_BEFORE") <(printf '%s\n' "$STATUS_AFTER")
fi
exit "$FAILED"
