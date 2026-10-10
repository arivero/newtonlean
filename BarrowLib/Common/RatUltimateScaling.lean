import BarrowLib.Common.RatMagnitudes

/-!
Ultimate enclosure under multiplication or division by a fixed positive
rational, and under a fixed positive rescaling of the vanishing argument.
Source of these formulations: the exact English statements and checked
proofs below, corresponding to the finite-order derivations in UltimateScaling.
This records proof provenance, without historical attribution or mathematical
priority. Core Rat arithmetic is encoding infrastructure.

These results are proved directly for arbitrary Rat → Rat functions. They do
not assert a reverse bridge for arbitrary Fraction → Fraction functions:
normalized sampling forgets values at noncanonical representatives. The legacy
API stays beside this one until its historical callers migrate together.
-/

namespace NewtonLimitDynamics.Rational

/-- Multiply the varying ratio and its ultimate value by a fixed positive rational. -/
theorem ultimate_scale {r : Rat → Rat} {c : Rat} (m : Rat)
    (hm : 0 < m) (hr : Ultimate magnitudes r c) :
    Ultimate magnitudes (fun t => m * r t) (m * c) := by
  intro a b hac hcb
  change a < m * c at hac
  change m * c < b at hcb
  have ha : a / m < c := by grind only [Rat.div_lt_iff]
  have hb : c < b / m := by grind only [Rat.lt_div_iff]
  obtain ⟨d, hd, hp⟩ := hr (a / m) (b / m) ha hb
  refine ⟨d, hd, ?_⟩
  intro t ht htd
  have hs := hp t ht htd
  change a / m < r t ∧ r t < b / m at hs
  change a < m * r t ∧ m * r t < b
  grind only [Rat.div_lt_iff, Rat.lt_div_iff]

/-- Divide the varying ratio and its ultimate value by a fixed positive rational. -/
theorem ultimate_quotient {r : Rat → Rat} {c : Rat} (m : Rat)
    (hm : 0 < m) (hr : Ultimate magnitudes r c) :
    Ultimate magnitudes (fun t => r t / m) (c / m) := by
  have hi : 0 < 1 / m := by grind only [Rat.div_def, Rat.inv_pos, Rat.mul_pos]
  simpa only [Rat.div_def, Rat.one_mul, Rat.mul_one, Rat.mul_comm] using ultimate_scale (1 / m) hi hr

/-- Read the vanishing argument in a fixed positive proportion. -/
theorem ultimate_time_scale {r : Rat → Rat} {c : Rat} (q : Rat)
    (hq : 0 < q) (hr : Ultimate magnitudes r c) :
    Ultimate magnitudes (fun t => r (q * t)) c := by
  intro a b hac hcb
  obtain ⟨d, hd, hp⟩ := hr a b hac hcb
  change 0 < d at hd
  refine ⟨d / q, ?_, ?_⟩
  · change 0 < d / q
    grind only [Rat.div_def, Rat.inv_pos, Rat.mul_pos]
  intro t ht htd
  change 0 < t at ht
  change t < d / q at htd
  apply hp (q * t)
  · change 0 < q * t
    exact Rat.mul_pos hq ht
  · change q * t < d
    grind only [Rat.lt_div_iff]

end NewtonLimitDynamics.Rational
