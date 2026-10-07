import BarrowLib.Polygon.IntegerSchedule
import BarrowLib.Polygon.IntegerRefinement
import ModernLib.Foundation.Polygon.BinaryTime
import BarrowLib.Common.FiniteGrowth

/-! Rational binary-time and integer-duration bridges. Retained namespaces
are compatibility names; no harmonic field or mechanical premise occurs. -/

namespace NewtonLimitDynamics.Polygon.HarmonicIntegerSubdivision
open NewtonLimitDynamics HarmonicDyadic HarmonicBinaryPrefix BinaryTime IntegerSchedule
-- Modern dependency score: 0/10 (M=0, H=10; transitive project theorems/axioms).
theorem dyadic_integer_duration (b : Nat → Bool) (T : Fraction) (m j : Nat) :
    Fraction.equiv (integerDuration (duration T (m+j)) (ticks b m))
      (duration (timeApprox b T m) j) := by
  have he := integerDuration_closed (duration T (m+j)) (ticks b m)
  apply Fraction.equiv_trans he
  simp only [timeApprox, duration, Fraction.equiv, Fraction.mul, Fraction.ofInt,
    FiniteGrowth.denominator_power_add]
  ac_nf

-- Modern dependency score: 1/14 (M=1, H=13; transitive project theorems/axioms).
theorem dyadic_fullTime (b : Nat → Bool) (T : Fraction) (m j : Nat) :
    Fraction.equiv
      (fullTime (integerDuration (duration T (m+j)) (ticks b m)) (blocks j))
      (timeApprox b T m) := by
  have hd := Fraction.mul_equiv (Fraction.equiv_refl (Fraction.ofInt (blocks j:Int)))
    (dyadic_integer_duration b T m j)
  apply Fraction.equiv_trans hd
  simp only [fullTime,duration,blocks,Fraction.equiv,Fraction.mul,Fraction.ofInt,
    Int.natCast_pow]
  ac_nf

end NewtonLimitDynamics.Polygon.HarmonicIntegerSubdivision

namespace NewtonLimitDynamics.Polygon.BinaryTime
open NewtonLimitDynamics HarmonicDyadic
-- Modern dependency score: 0/1 (M=0, H=1; transitive project theorems/axioms).
theorem timeApprox_nonnegative (b : Nat → Bool) (T : Fraction) (m : Nat)
    (hT : 0 ≤ T.num) : 0 ≤ (timeApprox b T m).num :=
  Fraction.nonnegative_mul _ _ (Int.ofNat_nonneg _) hT

end NewtonLimitDynamics.Polygon.BinaryTime
