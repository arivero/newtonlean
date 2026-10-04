import BarrowLib.Common.RationalMagnitudes

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

end NewtonLimitDynamics.Polygon.HarmonicAccumulation
