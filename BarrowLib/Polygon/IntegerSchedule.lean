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

theorem integerDuration_le (h : Fraction) (hh : 0 ≤ h.num)
    (i k : Nat) (hik : i ≤ k) :
    Fraction.le (integerDuration h i) (integerDuration h k) := by
  have hc : Fraction.le (Fraction.ofInt (i : Int))
      (Fraction.ofInt (k : Int)) := by
    unfold Fraction.le Fraction.ofInt
    dsimp
    simpa only [Int.mul_one] using Int.ofNat_le.mpr hik
  have hm := Fraction.mul_le_mul_nonnegative hc h hh
  exact Fraction.le_equiv_left (integerDuration_closed h i)
    (Fraction.le_equiv_right hm
      (Fraction.equiv_symm (integerDuration_closed h k)))

end NewtonLimitDynamics.Polygon.IntegerSchedule

namespace NewtonLimitDynamics.Polygon.HarmonicUniform
open NewtonLimitDynamics
/-- Actual represented total time `T=2nh` and the smallness hypothesis
`T(1+|w|) ≤ 1/2`. Zero cell count and zero duration are included. -/
def totalTime (h : Fraction) (n : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt (2 * (n : Int))) h

end NewtonLimitDynamics.Polygon.HarmonicUniform

namespace NewtonLimitDynamics.Polygon.HarmonicIntegerSubdivision
open NewtonLimitDynamics IntegerSchedule HarmonicUniform
def fullTime (d : Fraction) (N : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt (N : Int)) d

theorem half_totalTime (d : Fraction) (N : Nat) :
    Fraction.equiv (totalTime d.half N) (fullTime d N) := by
  simp only [totalTime, fullTime, Fraction.half, Fraction.equiv,
    Fraction.mul, Fraction.ofInt]
  ac_nf

theorem integer_fullTime (h : Fraction) (k N : Nat) :
    Fraction.equiv (fullTime h (k * N))
      (fullTime (integerDuration h k) N) := by
  have hc := integerDuration_closed h k
  have hmul := Fraction.mul_equiv
    (Fraction.equiv_refl (Fraction.ofInt (N : Int))) hc
  have he : Fraction.equiv (fullTime h (k * N))
      (Fraction.mul (Fraction.ofInt (N : Int))
        (Fraction.mul (Fraction.ofInt (k : Int)) h)) := by
    simp only [fullTime, Fraction.equiv, Fraction.mul, Fraction.ofInt,
      Int.natCast_mul]
    ac_nf
  exact Fraction.equiv_trans he (Fraction.equiv_symm hmul)

end NewtonLimitDynamics.Polygon.HarmonicIntegerSubdivision
