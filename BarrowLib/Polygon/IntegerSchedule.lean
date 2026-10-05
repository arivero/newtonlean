import BarrowLib.Common.RationalMagnitudes

/-! Elementary rational duration arithmetic for an integer number of cells. -/

namespace NewtonLimitDynamics.Polygon.IntegerSchedule

open NewtonLimitDynamics

def integerDuration (h : Fraction) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | k + 1 => Fraction.add (integerDuration h k) h

theorem integerDuration_closed (h : Fraction) :
    (k : Nat) → Fraction.equiv (integerDuration h k)
      (Fraction.mul (Fraction.ofInt (k : Int)) h)
  | 0 => by
      simp only [integerDuration, Fraction.equiv, Fraction.mul, Fraction.ofInt]
      simp
  | k + 1 => by
      have hi := integerDuration_closed h k
      have ha := Fraction.add_equiv hi (Fraction.equiv_refl h)
      apply Fraction.equiv_trans ha
      simp only [Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
        Int.natCast_add, Int.natCast_one]
      simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
      ac_nf

theorem integerDuration_nonnegative (h : Fraction) (hh : 0 ≤ h.num) :
    (k : Nat) → 0 ≤ (integerDuration h k).num
  | 0 => by simp [integerDuration, Fraction.ofInt]
  | k + 1 => Fraction.nonnegative_add _ _
      (integerDuration_nonnegative h hh k) hh

end NewtonLimitDynamics.Polygon.IntegerSchedule
