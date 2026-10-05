import BarrowLib.Common.RationalMagnitudes

namespace NewtonLimitDynamics.Polygon.HarmonicStability
open NewtonLimitDynamics
def negF (w : Fraction) : Fraction := ⟨-w.num, w.den, w.den_pos⟩

end NewtonLimitDynamics.Polygon.HarmonicStability

namespace NewtonLimitDynamics.Polygon.HarmonicDyadic
open NewtonLimitDynamics
def blocks (j : Nat) : Nat := 2 ^ j

def duration (T : Fraction) (j : Nat) : Fraction :=
  ⟨T.num, T.den * (2 : Int) ^ j,
    Int.mul_pos T.den_pos (Int.pow_pos (by decide))⟩

theorem blocks_succ (j : Nat) : blocks (j + 1) = blocks j + blocks j := by
  unfold blocks
  rw [Nat.pow_succ]
  omega

theorem duration_halving (T : Fraction) (j : Nat) :
    Fraction.equiv (duration T j)
      (Fraction.add (duration T (j + 1)) (duration T (j + 1))) := by
  simp only [duration, Fraction.equiv, Fraction.add, Int.pow_succ]
  simp only [show (2 : Int) = 1 + 1 by rfl, Int.add_mul, Int.mul_add]
  ac_nf

theorem two_pow_ge_succ (N : Nat) :
    (N : Int) + 1 ≤ (2 : Int) ^ N := by
  induction N with
  | zero => decide
  | succ n ih =>
      rw [Int.pow_succ]
      have hp : 0 ≤ (2 : Int) ^ n := Int.le_of_lt (Int.pow_pos (by decide))
      omega

end NewtonLimitDynamics.Polygon.HarmonicDyadic

namespace NewtonLimitDynamics.Polygon.HarmonicBinaryPrefix
open HarmonicDyadic
def bit (b : Nat → Bool) (j : Nat) : Nat := if b j then 1 else 0

def ticks (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * ticks b j + bit b j

theorem bit_le_one (b : Nat → Bool) (j : Nat) : bit b j ≤ 1 := by
  unfold bit
  split <;> omega

theorem ticks_lt_blocks (b : Nat → Bool) :
    (j : Nat) → ticks b j < blocks j
  | 0 => by simp [ticks, blocks]
  | j + 1 => by
      have ih := ticks_lt_blocks b j
      have hb := bit_le_one b j
      rw [ticks, blocks_succ]
      omega

theorem ticks_le_blocks (b : Nat → Bool) (j : Nat) :
    ticks b j ≤ blocks j := Nat.le_of_lt (ticks_lt_blocks b j)

theorem ticks_next (b : Nat → Bool) (j : Nat) :
    ticks b (j + 1) = ticks b j + ticks b j + bit b j := by
  simp only [ticks]
  omega

end NewtonLimitDynamics.Polygon.HarmonicBinaryPrefix

namespace NewtonLimitDynamics.Polygon.HarmonicTimeComparison
open NewtonLimitDynamics
open HarmonicStability
def durationDifference (sigma tau : Fraction) : Fraction :=
  Fraction.add tau (negF sigma)

theorem durationDifference_chain (a b c : Fraction) :
    Fraction.equiv (durationDifference a c)
      (Fraction.add (durationDifference a b) (durationDifference b c)) := by
  simp only [durationDifference, negF, Fraction.equiv, Fraction.add,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

end NewtonLimitDynamics.Polygon.HarmonicTimeComparison
