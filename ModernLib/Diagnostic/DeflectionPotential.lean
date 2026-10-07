import ModernLib.Polygon.ForceClasses
import BarrowLib.Polygon.TriangleBounds

/-!
Exact finite deflection-triangle/potential identities. These compare the next
polygon point to its inertial continuation, not a polygon to a completed
curve. The kick at B changes the next position by h² a(B). This diagnostic
is neither a historical proof nor a universal action-constant argument.
-/

namespace NewtonLimitDynamics.Diagnostic.DeflectionPotential

open NewtonLimitDynamics
open Polygon.TimeSubdivision Polygon.HarmonicStability Polygon.TriangleBounds

def inertial (h : Fraction) (B v : Point) : Point := pointAdd B (pointScale h v)
def deflected (h : Fraction) (B v a : Point) : Point :=
  pointAdd (inertial h B v) (pointScale (Fraction.mul h h) a)

def potentialStep (V : Point → Fraction) (c C : Point) : Fraction :=
  Fraction.add (V C) (negF (V c))

def linearPotential (m g : Fraction) (p : Point) : Fraction :=
  Fraction.mul (Fraction.mul m g) p.2

def quadraticPotential (m w : Fraction) (p : Point) : Fraction :=
  (Fraction.mul (Fraction.mul m w) (dot p p)).half

/-- Signed doubled area; the unsigned triangle uses its absolute value. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem deflection_triangle (h : Fraction) (B v a : Point) :
    Fraction.equiv (triangleTwice B (inertial h B v) (deflected h B v a))
      (Fraction.mul (Fraction.mul (Fraction.mul h h) h) (det v a)) := by
  simp only [triangleTwice, inertial, deflected, det, pointSub, pointNeg,
    pointAdd, pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf <;> omega

-- Modern dependency score: 1/2 (M=1, H=1; transitive project theorems/axioms).
theorem unsigned_deflection_triangle (h : Fraction) (B v a : Point) :
    Fraction.equiv (triangleMagnitude B (inertial h B v) (deflected h B v a))
      (Fraction.mul (Fraction.mul (Fraction.mul h h) h) (det v a)).abs :=
  Fraction.abs_equiv (deflection_triangle h B v a)

def fallAcceleration (g : Fraction) : Point := (Fraction.ofInt 0, negF g)

/-- The potential at C minus its value at c, exactly for Galilean fall. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem galilean_potential_step (m g h : Fraction) (B v : Point) :
    Fraction.equiv
      (potentialStep (linearPotential m g) (inertial h B v)
        (deflected h B v (fallAcceleration g)))
      (negF (Fraction.mul (Fraction.mul m (Fraction.mul g g)) (Fraction.mul h h))) := by
  simp only [potentialStep, linearPotential, inertial, deflected, fallAcceleration,
    negF, pointAdd, pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
    Fraction.ofInt, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.zero_mul, Int.mul_zero, Int.mul_one, Int.one_mul]
  ac_nf <;> omega

/-- A division-free exact proportionality. For m,g,h,v_x ≥ 0 and g>0,
halving absolute doubled area gives tau=v_x/(2g). -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem galilean_area_potential_cross_relation (m g h : Fraction) (B v : Point) :
    Fraction.equiv
      (Fraction.mul (Fraction.mul m g)
        (triangleTwice B (inertial h B v) (deflected h B v (fallAcceleration g))))
      (Fraction.mul (Fraction.mul h v.1)
        (potentialStep (linearPotential m g) (inertial h B v)
          (deflected h B v (fallAcceleration g)))) := by
  simp only [potentialStep, linearPotential, triangleTwice, inertial, deflected,
    fallAcceleration, det, negF, pointSub, pointNeg, pointAdd, pointScale,
    Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.zero_mul, Int.mul_zero, Int.mul_one, Int.one_mul]
  ac_nf <;> omega

/-- Exact harmonic correction terms: the leading potential drop is
-m h² |a(B)|², followed by a cubic tangent term and a quartic term. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem harmonic_potential_step (m w h : Fraction) (B v : Point) :
    Fraction.equiv
      (potentialStep (quadraticPotential m w) (inertial h B v)
        (deflected h B v (linearField w B)))
      (Fraction.add
        (negF (Fraction.mul (Fraction.mul m (Fraction.mul w w))
          (Fraction.mul (Fraction.mul h h) (dot B B))))
        (Fraction.add
          (negF (Fraction.mul (Fraction.mul m (Fraction.mul w w))
            (Fraction.mul (Fraction.mul (Fraction.mul h h) h) (dot B v))))
          (Fraction.mul (Fraction.mul m (Fraction.mul (Fraction.mul w w) w))
            (Fraction.mul (Fraction.mul (Fraction.mul h h) (Fraction.mul h h))
              (dot B B))).half)) := by
  simp only [potentialStep, quadraticPotential, inertial, deflected, linearField,
    dot, negF, pointAdd, pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
    Fraction.half, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  simp only [show (2 : Int) = 1 + 1 by rfl, Int.add_mul, Int.mul_add]
  ac_nf <;> omega

/-- Dropping the correction terms is false at a finite nonzero step. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem harmonic_leading_term_not_exact :
    let one := Fraction.ofInt 1
    let zero := Fraction.ofInt 0
    let h : Fraction := ⟨1, 2, by decide⟩
    let B : Point := (one, zero)
    let v : Point := (zero, one)
    ¬ Fraction.equiv
      (potentialStep (quadraticPotential one one) (inertial h B v)
        (deflected h B v (linearField one B)))
      (negF (Fraction.mul h h)) := by
  decide

end NewtonLimitDynamics.Diagnostic.DeflectionPotential
