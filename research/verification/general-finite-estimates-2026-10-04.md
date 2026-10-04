# General finite estimates: checked increment (4 October 2026)

Specification: extract the minimal generic rational foundation into `BarrowLib`, preserving the old fully qualified names. Prove estimates for the actual finite triangular map `y = x + h v`, `v' = v + h a(y)`. Bounds use the coordinate L1 magnitude, arbitrary point maps, an explicit Lipschitz coefficient `L`, and an additive sampling discrepancy `E`. No trajectory, physical force, or historical proposition is assumed in the foundation.

## Result and actual premises

The minimal bootstrap places `Magnitudes`/`Fraction` in `BarrowLib/Common`, point algebra plus `det`/`closedBoundaryTwice` in `BarrowLib/Polygon/PointAlgebra.lean`, and the coordinate L1 bounds in `BarrowLib/Polygon/PointBounds.lean`. These files retain the original `NewtonLimitDynamics.*` namespaces. Old fully migrated files are import facades; `TimeSubdivision` keeps only its scheduling and example declarations. `BarrowLib.lean` imports the bootstrap and finite estimates, and `lakefile.lean` declares a separate `lean_lib BarrowLib`. No BarrowLib source imports a NewtonLimitDynamics module.

`FiniteEstimates.cell` is the actual triangular map on arbitrary rational point maps. `cell_state_growth` assumes only a bound `pointNorm (a y) ≤ B` at its sampled arrival `y`. `cell_state_perturbation_closed` assumes the cross-map comparison contract `pointDistance (a p) (b q) ≤ L pointDistance p q + E` and `0 ≤ L`; its conclusion bounds the actual output state distance by the input position and velocity distances, with `|h|E` in the velocity term. The contract permits rounded maps with additive sampling discrepancy. The component theorem `cell_velocity_perturbation` retains the sampled arrival displacement before the closed recurrence substitutes its position bound.

`twoHalf_position_identity` derives the exact defect `h² a(y₁)` from the one-full/two-half map. `twoHalf_position_error` assumes `pointNorm (a y₁) ≤ B`. `twoHalf_velocity_difference` derives the exact two-sample velocity defect; `twoHalf_velocity_error_closed` and `twoHalf_state_error_closed` assume that same bound, `0 ≤ L`, and the same-map comparison contract. Their closed velocity cap is

`|h|[(L |h| |v| + E) + (L |h²| B + E)]`.

These are finite local estimates. No finite accumulation, mesh-uniform bound, polygon-family convergence, partition independence, or continuous trajectory is asserted. Those require further confinement and recurrence work.

## Exact controls and checks

Lean checks `linear_sample_control` for `p ↦ -p`, `h=1/8`, start `((1,0),(0,1))`, yielding `((1,1/8),(-1/8,63/64))`; `constant_sample_control` for `(0,-1)`, `h=1/2`, zero state; `unequal_sample_control` for `(0,-1)` versus `(0,-2)` with state distance `1/2`; `unequal_sample_control_nonzero` refutes a zero output bound; and `zero_duration_control` holds for every map and state. `L=0` is admitted by the general contract and estimates. These checks exercise exact rational arithmetic, not floating-point tests.

`lake build BarrowLib`, `lake build`, and `lake build NewtonLimitDynamics` completed successfully with Lean 4.19.0. A direct `lake env lean` file checked the old `HarmonicComparison.cell_bound` and `cell_perturbation` names and printed axioms for representative new theorems: only Lean core `propext`, `Classical.choice`, and `Quot.sound` occur in the general bounds; the finite arithmetic controls report `propext` only. No new axiom, `sorry`, external dependency, or mathlib import was added.
