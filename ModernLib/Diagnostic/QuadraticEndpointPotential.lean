import ModernLib.Diagnostic.DeflectionPotential
import ModernLib.Polygon.ParallelQuadraticEndpoint

/-! The half-coefficient deflection triangle and Galilean potential relation
at actual constructed rational endpoint values. The completed endpoint is
derived from the constant-force polygons. This is not D_mesh or a universal
action scale, and no general curved potential expansion is assumed. -/

namespace NewtonLimitDynamics.Diagnostic.QuadraticEndpointPotential
open NewtonLimitDynamics
open Polygon.TimeSubdivision Polygon.HarmonicStability Polygon.TriangleBounds
open Polygon.QuadraticEstimates Polygon.PositionValues Polygon.ParallelQuadraticEndpoint
open DeflectionPotential

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem quadratic_deflection_triangle (h : Fraction) (B v a : Point) :
    Fraction.equiv (triangleTwice B (inertial h B v) (quadraticPosition h (B,v) a))
      (Fraction.mul (Fraction.mul (Fraction.mul h h) h) (det v a)).half := by
  simp only [triangleTwice,inertial,quadraticPosition,det,pointSub,pointNeg,
    pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.half,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
  ac_nf <;> omega

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem galilean_quadratic_potential_step (m g h : Fraction) (B v : Point) :
    Fraction.equiv
      (potentialStep (linearPotential m g) (inertial h B v)
        (quadraticPosition h (B,v) (fallAcceleration g)))
      (negF (Fraction.mul (Fraction.mul m (Fraction.mul g g)) (Fraction.mul h h))).half := by
  simp only [potentialStep,linearPotential,inertial,quadraticPosition,fallAcceleration,
    negF,pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.half,
    Fraction.ofInt,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,
    Int.zero_mul,Int.mul_zero,Int.mul_one,Int.one_mul]
  ac_nf <;> omega

/-- Both triangle and potential drop acquire the same half, so the motion-
dependent time ratio is unchanged from the finite kick comparison. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem galilean_quadratic_cross_relation (m g h : Fraction) (B v : Point) :
    Fraction.equiv
      (Fraction.mul (Fraction.mul m g)
        (triangleTwice B (inertial h B v) (quadraticPosition h (B,v) (fallAcceleration g))))
      (Fraction.mul (Fraction.mul h v.1)
        (potentialStep (linearPotential m g) (inertial h B v)
          (quadraticPosition h (B,v) (fallAcceleration g)))) := by
  simp only [potentialStep,linearPotential,triangleTwice,inertial,quadraticPosition,
    fallAcceleration,det,negF,pointSub,pointNeg,pointAdd,pointScale,
    Fraction.equiv,Fraction.add,Fraction.mul,Fraction.half,Fraction.ofInt,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,
    Int.zero_mul,Int.mul_zero,Int.mul_one,Int.one_mul]
  ac_nf <;> omega

/-- The point in the potential/triangle formulas is the actual completed
endpoint, rather than a supplied quadratic curve point. -/
-- Modern dependency score: 19/88 (M=19, H=69; transitive project theorems/axioms).
theorem galilean_constructed_endpoint_relation (m g h : Fraction) (B v : Point)
    (hh : 0 ≤ h.num) :
    ∃ C : Point,
      asPosition (endpointValue (fallAcceleration g) h (B,v) hh)=embedPosition C ∧
      Fraction.equiv (triangleTwice B (inertial h B v) C)
        (Fraction.mul (Fraction.mul (Fraction.mul h h) h) (det v (fallAcceleration g))).half ∧
      Fraction.equiv (potentialStep (linearPotential m g) (inertial h B v) C)
        (negF (Fraction.mul (Fraction.mul m (Fraction.mul g g)) (Fraction.mul h h))).half ∧
      Fraction.equiv (Fraction.mul (Fraction.mul m g) (triangleTwice B (inertial h B v) C))
        (Fraction.mul (Fraction.mul h v.1) (potentialStep (linearPotential m g) (inertial h B v) C)) := by
  refine ⟨quadraticPosition h (B,v) (fallAcceleration g),?_,
    quadratic_deflection_triangle h B v (fallAcceleration g),
    galilean_quadratic_potential_step m g h B v,galilean_quadratic_cross_relation m g h B v⟩
  rw [endpointValue_eq]
  rfl

end NewtonLimitDynamics.Diagnostic.QuadraticEndpointPotential
