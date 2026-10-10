import BarrowLib.Common.RationalMagnitudes
import BarrowLib.Polygon.FiniteRecurrence

namespace NewtonLimitDynamics.Polygon.HarmonicAccumulation
open NewtonLimitDynamics
/-- Finite rational powers, avoiding any completeness premise. -/
def fpower (a : Fraction) : Nat → Fraction
  | 0 => Fraction.ofInt 1
  | n + 1 => Fraction.mul a (fpower a n)

theorem fpower_nonnegative (a : Fraction) (ha : 0 ≤ a.num) :
    (n : Nat) → 0 ≤ (fpower a n).num
  | 0 => by simp [fpower, Fraction.ofInt]
  | n + 1 => Fraction.nonnegative_mul _ _ ha (fpower_nonnegative a ha n)

/-- TEMPORARY MIGRATION BRIDGE: project encoding correspondence derived here
(Sol 6.1, 10 October 2026). Convert only scalar values; no actual state input
is normalized. Delete this correspondence when the legacy fpower migrates. -/
theorem toRat_fpower (r : Fraction) :
    (n : Nat) → (fpower r n).toRat = r.toRat ^ n
  | 0 => by simp [fpower, Fraction.toRat_ofInt]
  | n+1 => by
      simp only [fpower, Fraction.toRat_mul, toRat_fpower r n, Rat.pow_succ]
      grind

end NewtonLimitDynamics.Polygon.HarmonicAccumulation

-- TEMPORARY MIGRATION BRIDGE
/- Shared scalar-bound adapter for the still-legacy state modules. Derived
here (Sol 6.1, 10 October 2026); its exact statement and proof are provenance,
without historical attribution or priority. It normalizes a numerical bound,
never an input to a state recurrence or arbitrary force map. -/
namespace NewtonLimitDynamics.Polygon.FiniteRecurrence
open NewtonLimitDynamics

theorem legacy_sourceBudget_two_count (r C : Fraction) (n : Nat)
    (hr : 0 ≤ r.num) (hC : 0 ≤ C.num)
    (hone : Fraction.le (Fraction.ofInt 1) r)
    (hp : Fraction.le (HarmonicAccumulation.fpower r n) (Fraction.ofInt 2)) :
    Fraction.le (Fraction.ofRat (sourceBudget r.toRat C.toRat n))
      (Fraction.mul (Fraction.ofInt (2 * (n : Int))) C) := by
  have hone' : 1 ≤ r.toRat := by
    simpa only [Fraction.toRat_ofInt, Rat.intCast_one] using
      (Fraction.le_iff_toRat _ _).mp hone
  have hp' : r.toRat ^ n ≤ 2 := by
    rw [← HarmonicAccumulation.toRat_fpower]
    simpa only [Fraction.toRat_ofInt, Rat.intCast_ofNat] using
      (Fraction.le_iff_toRat _ _).mp hp
  have hb := sourceBudget_two_count r.toRat C.toRat n
    ((Fraction.nonnegative_iff_toRat _).mp hr)
    ((Fraction.nonnegative_iff_toRat _).mp hC) hone' hp'
  apply (Fraction.le_iff_toRat _ _).mpr
  simpa only [Fraction.toRat_ofRat, Fraction.toRat_mul, Fraction.toRat_ofInt,
    Rat.intCast_mul, Rat.intCast_ofNat, Rat.intCast_natCast] using hb

end NewtonLimitDynamics.Polygon.FiniteRecurrence
