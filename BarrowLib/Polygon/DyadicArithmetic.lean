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

theorem neg_equiv {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv ⟨-a.num, a.den, a.den_pos⟩ ⟨-b.num, b.den, b.den_pos⟩ := by
  unfold Fraction.equiv at *
  dsimp
  simp only [Int.neg_mul, h]

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

theorem add_difference_cancel (a b : Fraction) :
    Fraction.equiv (Fraction.add a (durationDifference a b)) b := by
  simp only [durationDifference, negF, Fraction.equiv, Fraction.add,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

theorem difference_nonnegative_iff (a b : Fraction) :
    0 ≤ (durationDifference a b).num ↔ Fraction.le a b := by
  simp only [durationDifference, negF, Fraction.add, Fraction.le, Int.neg_mul]
  omega

theorem difference_add_bound (a b H : Fraction)
    (h : Fraction.le (durationDifference a b) H) :
    Fraction.le b (Fraction.add a H) :=
  Fraction.le_equiv_left (Fraction.equiv_symm (add_difference_cancel a b))
    (Fraction.add_le_add_left h a)

theorem difference_congr {a b c d : Fraction}
    (hac : Fraction.equiv a c) (hbd : Fraction.equiv b d) :
    Fraction.equiv (durationDifference a b) (durationDifference c d) :=
  Fraction.add_equiv hbd (HarmonicDyadic.neg_equiv hac)

theorem phase_end_difference (a H t : Fraction) :
    Fraction.equiv (durationDifference (durationDifference a t) H)
      (durationDifference t (Fraction.add a H)) := by
  simp only [durationDifference, negF, Fraction.equiv, Fraction.add,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

theorem difference_interval_gaps (a e c : Fraction)
    (ha : Fraction.le a e) (hc : Fraction.le e c) :
    Fraction.le (durationDifference a e).abs (durationDifference a c).abs ∧
    Fraction.le (durationDifference e c).abs (durationDifference a c).abs := by
  have hae := (difference_nonnegative_iff a e).mpr ha
  have hec := (difference_nonnegative_iff e c).mpr hc
  have hac := (difference_nonnegative_iff a c).mpr
    (Fraction.magnitudes.le_trans ha hc)
  have he := durationDifference_chain a e c
  have hb1 := Fraction.le_add_nonnegative (durationDifference a e)
    (durationDifference e c) hec
  have hb2 := Fraction.le_equiv_right
    (Fraction.le_add_nonnegative (durationDifference e c)
      (durationDifference a e) hae)
    (Fraction.add_comm _ _)
  have h1 := Fraction.le_equiv_right hb1 (Fraction.equiv_symm he)
  have h2 := Fraction.le_equiv_right hb2 (Fraction.equiv_symm he)
  constructor
  · exact Fraction.le_equiv_right
      (Fraction.le_equiv_left (Fraction.abs_of_nonnegative _ hae) h1)
      (Fraction.equiv_symm (Fraction.abs_of_nonnegative _ hac))
  · exact Fraction.le_equiv_right
      (Fraction.le_equiv_left (Fraction.abs_of_nonnegative _ hec) h2)
      (Fraction.equiv_symm (Fraction.abs_of_nonnegative _ hac))
end NewtonLimitDynamics.Polygon.HarmonicTimeComparison
