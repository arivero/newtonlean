import BarrowLib.Polygon.PointBounds

/-!
Unsigned doubled triangle magnitudes for finite rational path patches.
These estimates concern area between compared paths, separately from their
Kepler swept areas. A sum counts patches with multiplicity; interpreting it
as a union's area still needs the geometric decomposition or enclosure.
No limiting trajectory is supplied or constructed here.
-/

namespace NewtonLimitDynamics.Polygon.TriangleBounds

open NewtonLimitDynamics
open TimeSubdivision
open PointBounds

/-- Determinant magnitude is bounded by the product of coordinate L1
magnitudes. The determinant is a doubled oriented area, not a distance. -/
theorem det_abs_le_product (p q : Point) :
    Fraction.le (det p q).abs (Fraction.mul (pointNorm p) (pointNorm q)) := by
  let a := Fraction.mul p.1 q.2
  let b := Fraction.mul p.2 q.1
  let nb : Fraction := ⟨-b.num, b.den, b.den_pos⟩
  let cross := Fraction.add (Fraction.mul p.1.abs q.2.abs)
    (Fraction.mul p.2.abs q.1.abs)
  let diagonal := Fraction.add (Fraction.mul p.1.abs q.1.abs)
    (Fraction.mul p.2.abs q.2.abs)
  have h₀ := Fraction.abs_add_le a nb
  have he : Fraction.equiv (Fraction.add a.abs nb.abs) cross :=
    Fraction.add_equiv (Fraction.abs_mul _ _)
      (Fraction.equiv_trans (Fraction.abs_neg b) (Fraction.abs_mul _ _))
  have h₁ : Fraction.le (det p q).abs cross := Fraction.le_equiv_right h₀ he
  have hd : 0 ≤ diagonal.num :=
    Fraction.nonnegative_add _ _
      (Int.mul_nonneg (Fraction.abs_num_nonnegative _) (Fraction.abs_num_nonnegative _))
      (Int.mul_nonneg (Fraction.abs_num_nonnegative _) (Fraction.abs_num_nonnegative _))
  have h₂ := Fraction.le_add_nonnegative cross diagonal hd
  have hchain := Fraction.magnitudes.le_trans h₁ h₂
  apply Fraction.le_equiv_right hchain
  simp only [cross, diagonal, pointNorm, Fraction.equiv, Fraction.add, Fraction.mul]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

def triangleTwice (p q r : Point) : Fraction :=
  det (pointSub q p) (pointSub r p)

/-- A nonzero areal product and bounded second vector give a radial lower bound.
This is finite determinant arithmetic, without a force or motion premise. -/
theorem radius_lower_of_areal_bound (p v : Point) (r V : Fraction)
    (hV : 0 < V.num) (hv : Fraction.le (pointNorm v) V)
    (ha : Fraction.le (Fraction.mul r V) (det p v).abs) :
    Fraction.le r (pointNorm p) := by
  have hd := Fraction.magnitudes.le_trans (det_abs_le_product p v)
    (Fraction.mul_le_mul_nonnegative_left hv (pointNorm p) (pointNorm_nonnegative p))
  exact Fraction.mul_le_cancel_positive_right V hV (Fraction.magnitudes.le_trans ha hd)

def triangleMagnitude (p q r : Point) : Fraction := (triangleTwice p q r).abs

theorem triangleMagnitude_nonnegative (p q r : Point) :
    0 ≤ (triangleMagnitude p q r).num := Fraction.abs_num_nonnegative _

theorem triangleMagnitude_le_product (p q r : Point) :
    Fraction.le (triangleMagnitude p q r)
      (Fraction.mul (pointNorm (pointSub q p)) (pointNorm (pointSub r p))) :=
  det_abs_le_product _ _

/-- The same triangle can be estimated using its two consecutive edges. -/
theorem triangleTwice_consecutive (p q r : Point) :
    Fraction.equiv (triangleTwice p q r)
      (det (pointSub q p) (pointSub r q)) := by
  simp only [triangleTwice, det, pointSub, pointNeg, pointAdd, Fraction.equiv,
    Fraction.add, Fraction.mul, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf <;> omega

theorem triangleMagnitude_le_consecutive (p q r : Point) :
    Fraction.le (triangleMagnitude p q r)
      (Fraction.mul (pointNorm (pointSub q p)) (pointNorm (pointSub r q))) :=
  Fraction.le_equiv_left (Fraction.abs_equiv (triangleTwice_consecutive p q r))
    (det_abs_le_product _ _)

theorem triangleTwice_translation (origin p q r : Point) :
    Fraction.equiv
      (triangleTwice (pointSub p origin) (pointSub q origin) (pointSub r origin))
      (triangleTwice p q r) := by
  simp only [triangleTwice, det, pointSub, pointNeg, pointAdd, Fraction.equiv,
    Fraction.add, Fraction.mul, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf <;> omega

theorem triangleMagnitude_translation (origin p q r : Point) :
    Fraction.equiv
      (triangleMagnitude (pointSub p origin) (pointSub q origin) (pointSub r origin))
      (triangleMagnitude p q r) :=
  Fraction.abs_equiv (triangleTwice_translation origin p q r)

theorem triangleTwice_swap (p q r : Point) :
    Fraction.equiv (triangleTwice p r q)
      (⟨-(triangleTwice p q r).num,
        (triangleTwice p q r).den, (triangleTwice p q r).den_pos⟩ : Fraction) := by
  simp only [triangleTwice, det, pointSub, pointNeg, pointAdd, Fraction.equiv,
    Fraction.add, Fraction.mul, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf <;> omega

theorem triangleMagnitude_swap (p q r : Point) :
    Fraction.equiv (triangleMagnitude p r q) (triangleMagnitude p q r) :=
  Fraction.equiv_trans (Fraction.abs_equiv (triangleTwice_swap p q r))
    (Fraction.abs_neg _)

private def zero : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1
private def p : Point := (zero, zero)
private def q : Point := (one, zero)
private def r : Point := (zero, one)

theorem sample_signed_positive : Fraction.equiv (triangleTwice p q r) one := by decide
theorem sample_signed_negative :
    Fraction.equiv (triangleTwice p r q) (Fraction.ofInt (-1)) := by decide
theorem sample_opposite_unsigned_sum :
    Fraction.equiv
      (Fraction.add (triangleMagnitude p q r) (triangleMagnitude p r q))
      (Fraction.ofInt 2) := by decide
theorem sample_opposite_signed_sum :
    Fraction.equiv (Fraction.add (triangleTwice p q r) (triangleTwice p r q)) zero := by decide
theorem sample_unsigned_not_signed :
    ¬ Fraction.equiv (triangleMagnitude p r q) (triangleTwice p r q) := by decide

end NewtonLimitDynamics.Polygon.TriangleBounds
