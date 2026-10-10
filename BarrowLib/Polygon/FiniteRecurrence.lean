import BarrowLib.Common.FinitePowers

/-! Finite rational recurrence with a constant nonnegative source.
Project derivation (Sol 6.1, 10 October 2026): the exact statement and finite
induction below give the provenance of this formulation, without historical
textual attribution or priority. No limit or completeness premise is used. -/

namespace NewtonLimitDynamics.Polygon.FiniteRecurrence

def sourceBudget (r C : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => r * sourceBudget r C n + C

theorem sourceBudget_power (r C : Rat) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hone : 1 ≤ r) : (n : Nat) → sourceBudget r C n ≤ (n : Rat) * C * r ^ n
  | 0 => by simp [sourceBudget]
  | n + 1 => by
      have hm := Rat.mul_le_mul_of_nonneg_left
        (sourceBudget_power r C hr hC hone n) hr
      have hc := Rat.mul_le_mul_of_nonneg_left
        (FinitePowers.one_le_power r hr hone (n + 1)) hC
      simp only [sourceBudget, Rat.pow_succ]
      simp only [Rat.pow_succ] at hc
      grind

/-- Shared finite closing step. Core plus one grind does not close the
product-order argument at its several legacy call sites. -/
theorem sourceBudget_two_count (r C : Rat) (n : Nat) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hone : 1 ≤ r) (hp : r ^ n ≤ 2) :
    sourceBudget r C n ≤ (2 * (n : Rat)) * C := by
  have hb := sourceBudget_power r C hr hC hone n
  have hm := Rat.mul_le_mul_of_nonneg_left hp
    (Rat.mul_nonneg (Rat.natCast_nonneg (a := n)) hC)
  grind

end NewtonLimitDynamics.Polygon.FiniteRecurrence
