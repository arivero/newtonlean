import BarrowLib.Common.RatMagnitudes

/-! Rational exhaustion of a closed order bound, proved by the explicit
half-gap witness. No completeness, real order or calculus theorem is imported.
Source: the original statement and checked half-gap derivation below;
this records the formulation, without a historical attribution or priority claim. -/
namespace NewtonLimitDynamics.Rational

theorem le_of_enlargements (a b : Rat)
    (h : ∀ eps : Rat, 0 < eps → a ≤ b + eps) : a ≤ b := by
  have := h ((a - b) / 2)
  grind

end NewtonLimitDynamics.Rational
