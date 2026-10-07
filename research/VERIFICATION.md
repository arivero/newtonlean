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

## Current verified increment

On 7 October, all five builds and all positive Lean controls passed for the
Lemma I–III, Corollaries I–IV and Laws' Corollary I increment. Compiled
reference inspection found no project axioms, sorry or primary anachronical
dependency. Graphs were regenerated from current source and compiled uses.
Archive hashes and whitespace checks passed. The deliberate corrupted control
failed at the intended false equality. The new Latin passages are NATP00090
par12–13 and the two printed Law II explanations (par4); archived sources are
unchanged. See [STATE.md](STATE.md) for the conditional scope and open claims.

The authorized Astra review found no blocking defects. Its two wording
corrections are applied: De Motu's statement/proof folios are distinguished,
and the mechanical control is described as a concrete model instance rather
than an independent implementation. The review checked the added Latin against
archived TEI and confirmed the stated restrictions; it does not certify full
historical completion.

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
