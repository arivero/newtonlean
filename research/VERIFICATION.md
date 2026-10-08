# Verification checklist

Use Lean 4.19.0 core/Std only, with no mathlib, sorry or project axioms.
Run from the repository root:

```sh
lake build
lake build BarrowLib
lake build ClassicsLib
lake build ModernLib
lake build NewtonLimitDynamics
lake env lean research/CheckReferences.lean
lake env lean scripts/inspect_graphs.lean
sha256sum -c docs/SHA256SUMS
git diff HEAD --check
```

The default build alone is insufficient. `CheckReferences.lean` inspects
compiled project constants: it permits only propext, Classical.choice and
Quot.sound in safe declarations, propagates anachronical use through types,
bodies and private helpers, classifies historical sections by source position
relative to the five-line `ANACHRONICAL PROOFS` header, and verifies the
opening `Modern dependency score` comments against compiled transitive
dependencies. Passing does not discharge geometric or mechanical premises.
Compiler-generated auxiliaries, including the equation lemmas that `simp`,
`rw` and `unfold` realize on demand, are classified at their parent
declaration's source position; they depend only on that declaration.

After changing a proof, build, refresh the score comments, rebuild (inserted
comments shift source positions) and check:

```sh
lake build
lake build BarrowLib
lake build ClassicsLib
lake build ModernLib
lake build NewtonLimitDynamics
NEWTON_WRITE_PROOF_SCORES=1 lake env lean research/CheckReferences.lean
lake build
lake build BarrowLib
lake build ClassicsLib
lake build ModernLib
lake build NewtonLimitDynamics
lake env lean research/CheckReferences.lean
```

The refresh edits proof comments in place. Types and private helpers are
traversed; Lean infrastructure, generated auxiliaries and the proof itself are
excluded. A score describes repository classification; it cannot establish
the original attribution of a result.

`inspect_graphs.lean` regenerates `research/figures.md`, distinguishing
witness-specific source evidence, editorial comparisons, library imports and
direct formal uses. A missing source-comment edge does not establish
historical absence. Compare historical Latin with its named archived TEI,
including additions/deletions, omitted forme-work, source hashes and
witness-specific wording.

## Proof scope controls

```sh
for check in research/verification/*.lean; do
  lake env lean "$check" || exit 1
done
lake env lean research/verification/harmonic-cover-2026-10-04/reference.lean
lake env lean research/verification/harmonic-cover-2026-10-04/comparator.lean
```

The deliberate corruption must fail:

```sh
lake env lean research/verification/harmonic-cover-2026-10-04/corrupted-comparator.lean
```

The expected rejection is `decide` refuting the radius equality whose
numerator was increased by one; treat an import error or timeout as a broken
control. The reference/comparator share the model and Lean kernel, so they
check the proposed formula's implementation rather than independent geometry.

Each harness's opening docstring states what it controls. An `AreaRules` or
`DifferenceAreaRules` argument is an explicit geometric premise; a control
with that argument does not prove that such a convention exists. Complete
hypotheses live in the owning declarations. Results, the latest verification
record and open obligations live in [STATE.md](STATE.md).

`sector-difference-2026-10-07.lean` checks actual fan, connector and filled-strip
membership/exclusion, equivalent point displays, the strict half-plane bound
and unsigned areas for reversed/collapsed triangles. Its written rational-root
argument is not a Lean-certified exclusion of every matched parameter.
`motion-sampling-2026-10-07.lean` checks a displaced terminal connector and its
nonzero area, zero-time/inertial controls and the filled cover. Its compiled
dependency checks require each new historical client to use its own canonical
polygon, and each eventual sector-area client its own finite geometric proof;
foreign witnesses and ModernLib dependencies are rejected. Each new eventual
sector-difference client must also use its own triangle chain to derive
orientation and the proved FanDifference inclusion. The separate
full-turn union/multiplicity falsifier remains in `sector-unions-2026-10-07.lean`.

`triangle-exchange-2026-10-08.lean` checks finite simplex exit with signed
inserted coordinates, rejects an excessive scale and an invalid total, and
exercises independent, collinear, reversed radial order and coincident rays.
Its displaced one-cell difference point belongs to neither the mechanical
sector nor terminal connector; the derived cover therefore supplies actual
square membership. The general many-cell inclusion is checked separately.

`fan-difference-2026-10-08.lean` exercises the general geometric inclusion
with both strict orders of boundary-crossing cells, a collapsed first cell,
and a terminal-only point proved to lie outside every filled cell. The
symmetric form, nonmonotone intermediate radii and zero-group-weight
convexity are included. These shared-kernel controls do not assign an area
to the sector-union difference or the square-cover union.
