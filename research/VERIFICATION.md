# Current verification

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

The default build alone is insufficient. `CheckReferences.lean` inspects actual
compiled project constants, permitting only propext, Classical.choice and
Quot.sound in safe declarations. It propagates anachronical use through types,
bodies and private helpers, using source positions to classify the five-line
`ANACHRONICAL PROOFS` sections. Compiler-generated unsafe implementation
placeholders cannot enter safe mathematical proofs; their dependencies remain
in the graph. Passing does not discharge geometric or mechanical premises.

`CheckReferences.lean` also verifies the opening `Modern dependency score`
comments against compiled transitive project theorem/axiom dependencies.
After changing a proof, build first so the refresh reads its current compiled
body and source positions. Then refresh comments, rebuild to update positions
shifted by inserted comments, and check:

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

The refresh edits proof comments in place, without a catalog or ledger.
Counts distinguish modern and historical support by current compiled
classification. Types and private helpers are traversed; standard Lean
infrastructure, generated auxiliaries and the proof itself are excluded.
Known-answer controls check duplicate dependencies and a transitive modern
dependency behind an uncounted definition. Source verification remains
separate: a score cannot establish the original attribution of a result.

The graph inspector distinguishes witness-specific source evidence, editorial
comparisons, library imports and direct formal uses. A missing source-comment
edge does not establish historical absence. Compare historical Latin with its
named archived TEI, including additions/deletions, omitted forme-work, source
hashes and witness-specific wording.

## Proof scope controls

Run the retained positive Lean harnesses:

```sh
for check in research/verification/*.lean; do
  lake env lean "$check" || exit 1
done
lake env lean research/verification/harmonic-cover-2026-10-04/reference.lean
lake env lean research/verification/harmonic-cover-2026-10-04/comparator.lean
```

The deliberate corruption is separate:

```sh
lake env lean research/verification/harmonic-cover-2026-10-04/corrupted-comparator.lean
```

It must fail because the radius numerator was increased by one and `decide`
rejects that equality. An import error or timeout is not the expected rejection.
The reference/comparator use a distinct exact-arithmetic state representation
but share the model and Lean kernel. Their radius/budget comparisons check the
proposed formula's implementation, not independently derived geometry.

Other harnesses check confinement, candidate residuals, given-curve premises,
interval fans, composition, chords, supporting segments and monotone rectangles.
They retain nondegeneracy/regularity controls and print axiom reports where
relevant. Complete hypotheses live in the owning declarations; remaining
obligations live in [STATE.md](STATE.md).

`historical-groundwork-2026-10-07.lean` checks the positive before-end window,
zero-duration vacuity, terminal fraction aliases, missing impulse-additivity
and a vertical rational curve. The monotone-rectangle harness also exercises
the new primary unequal-width exhaustion and conditional actual-union areas.
An `AreaRules` argument is an explicit geometric premise; a control with that
argument does not prove that such a convention exists.

`sector-unions-2026-10-07.lean` tests actual filled-triangle membership and
radial separation for a nonconstant central polygon, including its shared
radial boundary. It also exhibits a complete turn followed by a repeated
triangle: the fan sum grows while the union stays fixed. Consecutive positive
determinants alone therefore cannot justify unrestricted union identification.

`historical-sector-construction-2026-10-07.lean` instantiates both printed
editions' law-driven construction with altered fraction displays. It checks
the derived equal-triangle and actual local union-area results, exercising
the source-local Laws' Corollary I dependency without assuming equal areas.

## Current verified increment

The radial-sector increment derives actual set enclosures for a given positive
monotone rational radial graph and its chord polygon, finite triangle-union
areas, chord-area errors, and shrinking covers of their symmetric difference.
The chart is `(x,y)=(g(t),g(t)*t)`: `t=y/x` is slope, and `g(t)` is the
positive x-coordinate. Subtraction of nested assigned areas is an additional
explicit geometric rule; it assumes no curve agreement or limiting area.
Each printed edition actually uses its own Lemmas III/I. Force-polygon
identification and slope-parameter mesh exhaustion for the mechanical
construction remain open.

`radial-sector-2026-10-07.lean` checks a nonlinear curve point outside its chord,
actual finite sums, the between-region cover, collapsed slope intervals and
the failure of the increasing ray-scale premise for a decreasing graph.
`historical-radial-sector-2026-10-07.lean` constructs shrinking dyadic slope
partitions for a nonconstant graph and exercises both printed-edition chains.
The area convention and any assigned curved/between areas stay explicit.

All five builds, all positive controls, source hashes and whitespace passed.
The compiled checker verified 1,181 opening score comments and 6,561 project
constants, with no project axioms, sorry or primary modern dependency. The
corrupted comparator failed at its intended false equality. The current
diagrams recover 62 source edges and 15 formal cross-file uses across 19
historical files. Archived Newton sources and exact Latin are unchanged.

The authorized Astra review found no blocking mathematical or attribution
defect. Its slope-chart clarification is applied above and in the owning
Lean files. This verifies the stated local conditional approximation and
retained finite construction, not complete historical Proposition I or
complete exact-source coverage of the existing libraries. Library extensions
and historical proof applications are committed separately.

## Retained consolidation

The refactor/source-only cleanup was verified and pushed as `60180f2`.
The subsequent consolidation removes Python/plots, the whole-library interleaved
document, rendered reference PDFs and session/checkpoint logs. Substantive
Markdown and primary TEI/HTML/PDF originals remain. Previous commands and API
inventories are available in Git, outside the current checklist.
All five builds, compiled reference/axiom inspection, 15 positive Lean controls,
source hashes and whitespace checks passed on 6 October. The corrupted control
failed on the intended false equality. Historical Latin is unchanged.
Four unused Contact/comparison modules were removed; given-trajectory, completed
rectangle and supporting-boundary results now have checked applications below
the anachronical separators. The historical swept-sector proof remains open.
