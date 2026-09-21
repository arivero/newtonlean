# Research state

## Current milestone

**M1 — Quadratic Deflection Genealogy.** The question is how the status of
`s ∝ t^2` changes from the 1684 *De motu* hypothesis to the 1687 Lemma X
architecture and the 1713 strengthening.

## Completed in this initial skeleton

- Archived Newton Project NATP00089 diplomatic, normalized, and TEI/XML sources.
- Indexed the 1846 Motte opening material and the Motte/Wilkins Section I
  excerpt already available in `../navstokgap/docs/`.
- Added a machine-readable M1 dependency DAG.
- Added minimal Lean 4 statements for the historical hypothesis and a modern
  constant-force consequence.

## Boundary and next stop

Lean 4.19.0 and Lake 5.0.0 are installed through `elan`; `lake build` succeeds
for the current skeleton. Mathlib is not yet a project dependency because M1's
initial statements use only core Lean. Next, extract the exact 1687 and 1713
Lemma X witnesses and add their passage-level comparison before expanding the
formal model.
