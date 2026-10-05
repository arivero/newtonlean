import BarrowLib.Polygon.StateDistance
import BarrowLib.Polygon.DyadicArithmetic

/-! Rational geometric-tail estimates for an arbitrary sequence of states.
The coefficient and adjacent-error premise are supplied separately. -/

namespace NewtonLimitDynamics.Polygon.GeometricTail

open NewtonLimitDynamics
open TimeSubdivision
open FiniteEstimates
open HarmonicDyadic

def tailCap (A : Fraction) (j : Nat) : Fraction :=
  ⟨A.num, A.den * (2 : Int) ^ j,
    Int.mul_pos A.den_pos (Int.pow_pos (by decide))⟩

def doubleTail (A : Fraction) (j : Nat) : Fraction :=
  ⟨2 * A.num, A.den * (2 : Int) ^ j,
    Int.mul_pos A.den_pos (Int.pow_pos (by decide))⟩

theorem tail_halving (A : Fraction) (j : Nat) :
    Fraction.equiv
      (Fraction.add (tailCap A (j + 1)) (tailCap A (j + 1)))
      (tailCap A j) := by
  simp only [tailCap, Fraction.equiv, Fraction.add, Int.pow_succ]
  simp only [show (2 : Int) = 1 + 1 by rfl, Int.add_mul, Int.mul_add]
  ac_nf

theorem tail_double (A : Fraction) (j : Nat) :
    Fraction.equiv (Fraction.add (tailCap A j) (tailCap A j))
      (doubleTail A j) := by
  simp only [tailCap, doubleTail, Fraction.equiv, Fraction.add]
  simp only [show (2 : Int) = 1 + 1 by rfl, Int.add_mul, Int.mul_add]
  ac_nf

theorem tail_add (A B : Fraction) (n : Nat) :
    Fraction.equiv (Fraction.add (tailCap A n) (tailCap B n))
      (tailCap (Fraction.add A B) n) := by
  simp only [tailCap,Fraction.equiv,Fraction.add,Int.add_mul,Int.mul_add]
  ac_nf

theorem finite_gap (x : Nat → Point × Point) (A : Fraction)
    (hA : 0 ≤ A.num)
    (hadj : ∀ j, Fraction.le (stateDistance (x (j + 1)) (x j))
      (tailCap A (j + 1))) :
    (k j : Nat) → Fraction.le (stateDistance (x (j + k)) (x j))
      (tailCap A j)
  | 0, j => by
      have hz : Fraction.le (Fraction.ofInt 0) (tailCap A j) := by
        simp only [Fraction.le, Fraction.ofInt, tailCap]
        simp only [Int.zero_mul, Int.mul_one]
        exact hA
      simpa only [Nat.add_zero] using
        Fraction.le_equiv_left (stateDistance_self_zero (x j)) hz
  | k + 1, j => by
      have htri := stateDistance_triangle
        (x (j + (k + 1))) (x (j + 1)) (x j)
      have hk : Fraction.le
          (stateDistance (x (j + (k + 1))) (x (j + 1)))
          (tailCap A (j + 1)) := by
        simpa only [Nat.add_succ, Nat.succ_add, Nat.add_assoc] using
          finite_gap x A hA hadj k (j + 1)
      have hsum := Fraction.add_le_add hk (hadj j)
      exact Fraction.le_equiv_right (Fraction.magnitudes.le_trans htri hsum)
        (tail_halving A j)

theorem two_sided (x : Nat → Point × Point) (A : Fraction)
    (hA : 0 ≤ A.num)
    (hadj : ∀ j, Fraction.le (stateDistance (x (j + 1)) (x j))
      (tailCap A (j + 1)))
    (N m n : Nat) (hm : N ≤ m) (hn : N ≤ n) :
    Fraction.le (stateDistance (x m) (x n)) (doubleTail A N) := by
  have hm' : N + (m - N) = m := by omega
  have hn' : N + (n - N) = n := by omega
  have hfirst := finite_gap x A hA hadj (m - N) N
  have hsecond := finite_gap x A hA hadj (n - N) N
  rw [hm'] at hfirst
  rw [hn'] at hsecond
  have hsecond' := Fraction.le_equiv_left (stateDistance_symm (x N) (x n)) hsecond
  have htri := stateDistance_triangle (x m) (x N) (x n)
  exact Fraction.le_equiv_right
    (Fraction.magnitudes.le_trans htri (Fraction.add_le_add hfirst hsecond'))
    (tail_double A N)

def modulus (A eps : Fraction) : Nat := (2 * A.num * eps.den).toNat

theorem doubleTail_lt_tolerance (A eps : Fraction)
    (hA : 0 ≤ A.num) (heps : 0 < eps.num) :
    Fraction.lt (doubleTail A (modulus A eps)) eps := by
  let N := modulus A eps
  have hL : 0 ≤ 2 * A.num * eps.den :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) hA) (Int.le_of_lt eps.den_pos)
  have hN : (N : Int) = 2 * A.num * eps.den := Int.toNat_of_nonneg hL
  have hpow := two_pow_ge_succ N
  have hp : 0 ≤ (2 : Int) ^ N := Int.le_of_lt (Int.pow_pos (by decide))
  have hfactor : 1 ≤ eps.num * A.den := by
    have hmul := Int.mul_pos heps A.den_pos
    omega
  have hmult := Int.mul_le_mul_of_nonneg_right hfactor hp
  simp only [Int.one_mul] at hmult
  unfold Fraction.lt doubleTail
  dsimp
  change 2 * A.num * eps.den < eps.num * (A.den * (2 : Int) ^ N)
  rw [← Int.mul_assoc]
  omega

end NewtonLimitDynamics.Polygon.GeometricTail

namespace NewtonLimitDynamics.Polygon.HarmonicTimeRealization
open NewtonLimitDynamics HarmonicDyadic

theorem duration_eventually_small (T eps : Fraction)
    (hT : 0 ≤ T.num) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ j : Nat, N ≤ j →
      Fraction.lt (duration T j) eps := by
  let N := (T.num * eps.den).toNat
  have hL : 0 ≤ T.num * eps.den :=
    Int.mul_nonneg hT (Int.le_of_lt eps.den_pos)
  have hN : (N : Int) = T.num * eps.den := Int.toNat_of_nonneg hL
  refine ⟨N, ?_⟩
  intro j hj
  have hpow := two_pow_ge_succ j
  have hp : 0 ≤ (2 : Int) ^ j := Int.le_of_lt (Int.pow_pos (by decide))
  have hfactor : 1 ≤ eps.num * T.den := by
    have hmul := Int.mul_pos heps T.den_pos
    omega
  have hmult := Int.mul_le_mul_of_nonneg_right hfactor hp
  simp only [Int.one_mul] at hmult
  unfold Fraction.lt duration
  dsimp
  change T.num * eps.den < eps.num * (T.den * (2 : Int) ^ j)
  rw [← Int.mul_assoc]
  omega

end NewtonLimitDynamics.Polygon.HarmonicTimeRealization
