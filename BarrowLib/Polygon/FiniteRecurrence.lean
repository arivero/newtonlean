import BarrowLib.Polygon.FiniteAccumulation
import BarrowLib.Polygon.FinitePower

/-! Finite rational recurrence with a constant nonnegative source. -/

namespace NewtonLimitDynamics.Polygon.FiniteRecurrence

open NewtonLimitDynamics
open HarmonicAccumulation

def sourceBudget (r C : Fraction) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | n + 1 => Fraction.add (Fraction.mul r (sourceBudget r C n)) C

/-- Compatibility between the two pre-existing public finite-power names. -/
theorem factorPower_fpower (r : Fraction) :
    (n : Nat) → Fraction.equiv (FiniteAccumulation.factorPower r n) (fpower r n)
  | n => FiniteAccumulation.factorPower_fpower r n

/-- Reuse the pre-existing generic power lower bound. -/
theorem one_le_fpower (r : Fraction) (hr : 0 ≤ r.num)
    (hone : Fraction.le (Fraction.ofInt 1) r) (n : Nat) :
    Fraction.le (Fraction.ofInt 1) (fpower r n) :=
  Fraction.le_equiv_right (FiniteAccumulation.one_le_factorPower r hr hone n)
    (factorPower_fpower r n)

theorem fpower_add (r : Fraction) (m : Nat) :
    (n : Nat) → Fraction.equiv (fpower r (m + n))
      (Fraction.mul (fpower r m) (fpower r n))
  | 0 => by
      simp only [Nat.add_zero, fpower, Fraction.equiv, Fraction.mul,
        Fraction.ofInt]
      simp
  | n + 1 => by
      have ih := fpower_add r m n
      have hm := Fraction.mul_equiv (Fraction.equiv_refl r) ih
      apply Fraction.equiv_trans hm
      simp only [Nat.add_succ, fpower, Fraction.equiv, Fraction.mul]
      ac_nf

theorem fpower_congr {r q : Fraction} (hrq : Fraction.equiv r q) :
    (n : Nat) → Fraction.equiv (fpower r n) (fpower q n)
  | n => FiniteFactorProducts.fpower_congr hrq n

theorem fpower_integer_blocks (r : Fraction) (k : Nat) :
    (N : Nat) → Fraction.equiv (fpower (fpower r k) N)
      (fpower r (k * N))
  | 0 => by simp [fpower, Fraction.equiv, Fraction.ofInt, Fraction.mul]
  | N + 1 => by
      have ih := fpower_integer_blocks r k N
      have hm := Fraction.mul_equiv (Fraction.equiv_refl (fpower r k)) ih
      have ha := fpower_add r k (k * N)
      have he : k * (N + 1) = k + k * N := by
        simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [he]
      exact Fraction.equiv_trans hm (Fraction.equiv_symm ha)

theorem fpower_prefix_le (r : Fraction) (hr : 0 ≤ r.num)
    (hone : Fraction.le (Fraction.ofInt 1) r)
    (i N : Nat) (hi : i ≤ N) :
    Fraction.le (fpower r i) (fpower r N) := by
  have htail := one_le_fpower r hr hone (N - i)
  have hm := Fraction.mul_le_mul_nonnegative_left htail (fpower r i)
    (fpower_nonnegative r hr i)
  have hleft : Fraction.equiv
      (Fraction.mul (fpower r i) (Fraction.ofInt 1)) (fpower r i) := by
    simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
    simp
  have hright := fpower_add r i (N - i)
  have he : i + (N - i) = N := by omega
  rw [he] at hright
  exact Fraction.le_equiv_right
    (Fraction.le_equiv_left (Fraction.equiv_symm hleft) hm)
    (Fraction.equiv_symm hright)

theorem sourceBudget_nonnegative (r C : Fraction)
    (hr : 0 ≤ r.num) (hC : 0 ≤ C.num) :
    (n : Nat) → 0 ≤ (sourceBudget r C n).num
  | 0 => by simp [sourceBudget, Fraction.ofInt]
  | n + 1 => Fraction.nonnegative_add _ _
      (Fraction.nonnegative_mul _ _ hr
        (sourceBudget_nonnegative r C hr hC n)) hC

theorem sourceBudget_power (r C : Fraction)
    (hr : 0 ≤ r.num) (hC : 0 ≤ C.num)
    (hone : Fraction.le (Fraction.ofInt 1) r) :
    (n : Nat) → Fraction.le (sourceBudget r C n)
      (Fraction.mul (Fraction.ofInt (n : Int))
        (Fraction.mul C (fpower r n)))
  | 0 => by
      apply Fraction.le_of_equiv
      simp only [sourceBudget, fpower, Fraction.equiv, Fraction.ofInt,
        Fraction.mul]
      simp
  | n + 1 => by
      have hi := sourceBudget_power r C hr hC hone n
      have hpow := one_le_fpower r hr hone (n + 1)
      have h₁ := Fraction.mul_le_mul_nonnegative_left hi r hr
      have h₂ : Fraction.le C
          (Fraction.mul C (fpower r (n + 1))) := by
        have hm := Fraction.mul_le_mul_nonnegative_left hpow C hC
        exact Fraction.le_equiv_left (by
          simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
          simp) hm
      have h₂' := Fraction.add_le_add h₁ h₂
      have h₃ : Fraction.le
          (Fraction.add
            (Fraction.mul r (sourceBudget r C n)) C)
          (Fraction.add
            (Fraction.mul (Fraction.ofInt (n : Int))
              (Fraction.mul C (fpower r (n + 1))))
            (Fraction.mul C (fpower r (n + 1)))) := by
        apply Fraction.le_equiv_right h₂'
        simp only [fpower, Fraction.equiv, Fraction.mul]
        ac_nf
      apply Fraction.le_equiv_right h₃
      simp only [sourceBudget, fpower, Fraction.equiv,
        Fraction.add, Fraction.mul, Fraction.ofInt,
        Int.natCast_add, Int.natCast_one]
      simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
      ac_nf

/-- Shared closing step for any actual recurrence with a finite factor ≤2. -/
theorem sourceBudget_two_count (r C : Fraction) (n : Nat)
    (hr : 0 ≤ r.num) (hC : 0 ≤ C.num)
    (hone : Fraction.le (Fraction.ofInt 1) r)
    (hp : Fraction.le (fpower r n) (Fraction.ofInt 2)) :
    Fraction.le (sourceBudget r C n)
      (Fraction.mul (Fraction.ofInt (2*(n : Int))) C) := by
  have hb := sourceBudget_power r C hr hC hone n
  have hm := Fraction.mul_le_mul_nonnegative_left
    (Fraction.mul_le_mul_nonnegative_left hp C hC)
    (Fraction.ofInt (n : Int)) (Int.ofNat_nonneg n)
  apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans hb hm)
  simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt]
  ac_nf

end NewtonLimitDynamics.Polygon.FiniteRecurrence
