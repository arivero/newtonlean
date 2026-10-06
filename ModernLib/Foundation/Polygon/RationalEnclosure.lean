import ModernLib.Foundation.Polygon.ScalarOrder
import ModernLib.Foundation.Polygon.ScaledTolerance

/-! Rational enclosures of rational or completed nonnegative magnitudes.
The completed instance uses the actual scalar value and a proved closed
distance bound to zero. It does not replace an irrational area by a rational
cover budget. Positive rational mesh parameters select dyadic levels whose
unit mesh is at most the parameter, independently of its representation. -/

namespace NewtonLimitDynamics.Polygon.RationalEnclosure
open NewtonLimitDynamics
open HarmonicDyadic HarmonicTimeRealization CauchyValues BinaryTime ScalarOrder

/-- The comparisons needed by a rational squeeze. `small` is strict; for a
completed magnitude it means containment in a smaller rational radius. -/
class Magnitude (A : Type) where
  nonnegative : A → Prop
  bounded : A → Fraction → Prop
  small : A → Fraction → Prop
  bounded_mono : ∀ x R S, bounded x R → Fraction.le R S → bounded x S
  small_of_bound : ∀ x R eps, bounded x R → Fraction.lt R eps → small x eps

instance : Magnitude Fraction where
  nonnegative := Fraction.le (Fraction.ofInt 0)
  bounded := Fraction.le
  small := Fraction.lt
  bounded_mono := fun _ _ _ hx hRS => Fraction.magnitudes.le_trans hx hRS
  small_of_bound := fun _ _ _ hx he => Fraction.magnitudes.lt_of_le_lt hx he

instance : Magnitude ScalarValue where
  nonnegative := fun x => Below (Fraction.ofInt 0) x.val
  bounded := fun x R => Within x.val (embed (scalarState (Fraction.ofInt 0))) R
  small := fun x eps => ∃ R, Fraction.lt R eps ∧
    Within x.val (embed (scalarState (Fraction.ofInt 0))) R
  bounded_mono := fun _ _ _ hx hRS => within_mono _ _ _ _ hRS hx
  small_of_bound := fun _ R _ hx he => ⟨R,he,hx⟩

/-- A selected level, not a claim that every rational parameter is dyadic.
All positive representatives select a family mesh no larger than the parameter. -/
def level (mesh : Fraction) : Nat := mesh.den.toNat

theorem selected_duration_bound (A mesh : Fraction) (hA : 0 ≤ A.num)
    (hm : Fraction.positive mesh) :
    Fraction.le (duration A (level mesh)) (Fraction.mul mesh A) := by
  have hd : (mesh.den.toNat : Int) = mesh.den := Int.toNat_of_nonneg (Int.le_of_lt mesh.den_pos)
  have hp : mesh.den ≤ (2 : Int) ^ level mesh := by
    have h := two_pow_ge_succ mesh.den.toNat
    rw [hd] at h
    exact Int.le_trans (by omega) h
  have hunit : Fraction.le (duration (Fraction.ofInt 1) (level mesh)) mesh := by
    simp only [Fraction.le,duration,Fraction.ofInt,Int.one_mul]
    exact Int.le_trans hp (by
      have hnum : (1 : Int) ≤ mesh.num := by exact hm
      have h := Int.mul_le_mul_of_nonneg_right hnum
        (Int.le_of_lt (Int.pow_pos (m := level mesh) (by decide : (0 : Int) < 2)))
      simpa only [Int.one_mul] using h)
  have hb := Fraction.mul_le_mul_nonnegative hunit A hA
  apply Fraction.le_equiv_left (b := Fraction.mul (duration (Fraction.ofInt 1) (level mesh)) A) _ hb
  apply Fraction.equiv_symm
  simp only [duration,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul]
  ac_nf

end NewtonLimitDynamics.Polygon.RationalEnclosure
