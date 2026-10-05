import BarrowLib.Polygon.DyadicArithmetic
import BarrowLib.Common.FiniteGrowth

/-! Elementary binary tick arithmetic for a finite address followed by zero bits. -/

namespace NewtonLimitDynamics.Polygon.HarmonicBinaryPrefix

open HarmonicDyadic

/-- After a finite binary address, zero bits only double the existing tick count. -/
theorem ticks_zero_tail (b : Nat → Bool) (m : Nat)
    (hz : ∀ j, m ≤ j → b j = false) :
    (j : Nat) → ticks b (m + j) = ticks b m * blocks j
  | 0 => by simp [blocks]
  | j + 1 => by
      have ih := ticks_zero_tail b m hz j
      have hbit : bit b (m + j) = 0 := by
        simp [bit, hz (m + j) (Nat.le_add_right m j)]
      rw [Nat.add_succ, ticks, hbit, ih, blocks_succ]
      simp only [Nat.mul_add]
      omega

end NewtonLimitDynamics.Polygon.HarmonicBinaryPrefix

namespace NewtonLimitDynamics.Polygon.HarmonicDyadic

open NewtonLimitDynamics

/-- Dividing a dyadic duration twice adds the exponents. -/
theorem duration_nested (T : Fraction) (m j : Nat) :
    Fraction.equiv (duration (duration T m) j) (duration T (m + j)) := by
  simp only [duration, Fraction.equiv, FiniteGrowth.denominator_power_add]
  ac_nf

end NewtonLimitDynamics.Polygon.HarmonicDyadic
