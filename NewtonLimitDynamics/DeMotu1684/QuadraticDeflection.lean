namespace DeMotu1684

/- Historical statement: this is the quadratic-deflection premise isolated for
   M1. It deliberately does not encode Newton's surrounding geometry. -/
def QuadraticInitialDeflection (s : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ t : ℝ, s t = c * t ^ 2

theorem quadratic_deflection_historical
    (s : ℝ → ℝ) (h : QuadraticInitialDeflection s) :
    ∃ c : ℝ, ∀ t : ℝ, s t = c * t ^ 2 := h

end DeMotu1684
