/-! Finite scalar powers over Lean core Rat. Project derivation (Sol 6.1,
10 October 2026): the exact statement and checked induction below give the
provenance of this formulation, without historical attribution or priority.
No limit or completeness premise is used. -/

namespace NewtonLimitDynamics.FinitePowers

theorem one_le_power (r : Rat) (hr : 0 ≤ r) (h1 : 1 ≤ r) :
    (n : Nat) → 1 ≤ r ^ n
  | 0 => by simp
  | n + 1 => by
      have hi := one_le_power r hr h1 n
      have hm := Rat.mul_le_mul_of_nonneg_left h1 (Rat.pow_nonneg (n := n) hr)
      simp only [Rat.mul_one] at hm
      simpa only [Rat.pow_succ] using Rat.le_trans hi hm

end NewtonLimitDynamics.FinitePowers
