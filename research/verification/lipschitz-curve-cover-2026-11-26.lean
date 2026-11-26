import NewtonLimitDynamics

/-! Controls for the Lipschitz curve-cover route (issue 3). The nonmonotone quadratic
chart `g(θ) = 1 + θ - θ²` is Lipschitz with constant 1 on `[0,1]`, and the Lipschitz
bound gives its uniform modulus independently of `quadratic_uniform`. On the partition
`0, 1/2, 1/2, 1` the cell bounds hold on the rising cell, on the repeated-node cell
(tolerance 0) and on the falling cell `g(1/2) = 5/4 > g(1) = 1`, for the tolerance
`K · width`. The one-cell partition with tolerance `1/10` violates the Lipschitz
tolerance premise, and the cell bound then fails at `θ = 1/2`; the existing
`coarse_partition_fails` exhibits the corresponding sector point outside the upper cap.
These controls share the kernel and the rational definitions with the theorems. -/
namespace NewtonLimitDynamics.Polygon.LipschitzCurveCoverControls
open NewtonLimitDynamics TimeSubdivision MonotoneRectangles RadialSector QuadraticSector
open LipschitzCurveCover UniformRadialSector

example : LipschitzOn quadraticChart (Fraction.ofInt 0) (Fraction.ofInt 1) (Fraction.ofInt 1) :=
  quadratic_lipschitz
example : RationalBoundary.UniformOn (fun t => (t, quadraticChart t))
    (Fraction.ofInt 0) (Fraction.ofInt 1) :=
  uniform_of_lipschitz _ _ _ _ (by decide) quadratic_lipschitz

-- The partition `0, 1/2, 1/2, 1`: rising cell 0, repeated node 1, falling cell 2.
example : Fraction.lt (quadraticChart (repeatedNode.nodes 3))
    (quadraticChart (repeatedNode.nodes 2)) := by
  unfold Fraction.lt; decide
example : Fraction.equiv (width repeatedNode 1) (Fraction.ofInt 0) := by decide

-- Rising cell, tolerance `1/2`.
example (t : Fraction) (hl : Fraction.le (repeatedNode.nodes 0) t)
    (hr : Fraction.le t (repeatedNode.nodes 1)) :
    Fraction.le (lowerScales quadraticChart repeatedNode ⟨1,2,by decide⟩ 0) (quadraticChart t) ∧
      Fraction.le (quadraticChart t) (upperScales quadraticChart repeatedNode ⟨1,2,by decide⟩ 0) :=
  cell_bounds (by decide) quadratic_lipschitz repeatedNode _ 0 (by decide)
    (by unfold Fraction.le; decide) t hl hr
-- Repeated node, tolerance `0`: the chart is pinned to its node value on the collapsed cell.
example (t : Fraction) (hl : Fraction.le (repeatedNode.nodes 1) t)
    (hr : Fraction.le t (repeatedNode.nodes 2)) :
    Fraction.le (lowerScales quadraticChart repeatedNode (Fraction.ofInt 0) 1) (quadraticChart t) ∧
      Fraction.le (quadraticChart t) (upperScales quadraticChart repeatedNode (Fraction.ofInt 0) 1) :=
  cell_bounds (by decide) quadratic_lipschitz repeatedNode _ 1 (by decide)
    (by unfold Fraction.le; decide) t hl hr
-- Falling cell, tolerance `1/2`.
example (t : Fraction) (hl : Fraction.le (repeatedNode.nodes 2) t)
    (hr : Fraction.le t (repeatedNode.nodes 3)) :
    Fraction.le (lowerScales quadraticChart repeatedNode ⟨1,2,by decide⟩ 2) (quadraticChart t) ∧
      Fraction.le (quadraticChart t) (upperScales quadraticChart repeatedNode ⟨1,2,by decide⟩ 2) :=
  cell_bounds (by decide) quadratic_lipschitz repeatedNode _ 2 (by decide)
    (by unfold Fraction.le; decide) t hl hr

-- Coarse partition: tolerance `1/10` on the one-cell partition breaks the Lipschitz
-- tolerance premise, and the upper cell bound fails at the interior point `θ = 1/2`.
example : ¬ Fraction.le (Fraction.mul (Fraction.ofInt 1) (width oneCell 0)) ⟨1,10,by decide⟩ := by
  unfold Fraction.le; decide
example : ¬ Fraction.le (quadraticChart ⟨1,2,by decide⟩)
    (upperScales quadraticChart oneCell ⟨1,10,by decide⟩ 0) := by
  unfold Fraction.le; decide
example : ∃ x, sector quadraticChart (Fraction.ofInt 0) (Fraction.ofInt 1) x ∧
    ¬ upperCaps quadraticChart oneCell ⟨1,10,by decide⟩ x :=
  coarse_partition_fails

#print axioms quadratic_lipschitz
#print axioms LipschitzCurveCover.assigned_between_areas_vanish
end NewtonLimitDynamics.Polygon.LipschitzCurveCoverControls
