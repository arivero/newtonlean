/-! Finite rational barycentric elimination. Source: the original English
statement and Lean proof in this file. A nonnegative triple of total one and
an arbitrary signed triple of total one determine a rational scale at which
one residual coordinate becomes zero while all remain nonnegative. No area,
continuity, simplex-exchange inclusion or nonnegative inserted triple is
assumed. This records project proof provenance without historical textual
attribution or priority. Core Rat arithmetic is encoding infrastructure, not historical attestation. -/

namespace NewtonLimitDynamics.SimplexExit
private def candidate (x p : Rat) : Rat := if 0 < p then x / p else 2

private theorem below_candidate (t x p : Rat) (ht : 0 ≤ t) (hx : 0 ≤ x)
    (h : t ≤ candidate x p) : t * p ≤ x := by
  by_cases hp : 0 < p
  · have he : x / p * p = x := Rat.div_mul_cancel (by grind)
    have hm := Rat.mul_le_mul_of_nonneg_right
      (show t ≤ x / p by simpa only [candidate, ite_eq_left hp] using h)
      (show 0 ≤ p by grind)
    grind
  · have hm := Rat.mul_le_mul_of_nonneg_left (show p ≤ 0 by grind) ht
    grind

/-- A rational ray from an arbitrary signed barycentric triple exits a facet.
The nonnegative triple has total one. Every coordinate of t*p is at most x,
and at least one equals x; no region or area premise is supplied. -/
theorem simplex_exit (x0 x1 x2 p0 p1 p2 : Rat)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (hx : x0 + x1 + x2 = 1) (hp : p0 + p1 + p2 = 1) :
    ∃ t : Rat, 0 ≤ t ∧ t ≤ 1 ∧ t * p0 ≤ x0 ∧ t * p1 ≤ x1 ∧ t * p2 ≤ x2 ∧
      (t * p0 = x0 ∨ t * p1 = x1 ∨ t * p2 = x2) := by
  let c0 := candidate x0 p0
  let c1 := candidate x1 p1
  let c2 := candidate x2 p2
  let t := min (min c0 c1) c2
  have hc0 : 0 ≤ c0 := by grind [candidate, Rat.div_def, Rat.inv_pos, Rat.mul_nonneg]
  have hc1 : 0 ≤ c1 := by grind [candidate, Rat.div_def, Rat.inv_pos, Rat.mul_nonneg]
  have hc2 : 0 ≤ c2 := by grind [candidate, Rat.div_def, Rat.inv_pos, Rat.mul_nonneg]
  have ht0 : 0 ≤ t := by grind
  have h0 := below_candidate t x0 p0 ht0 hx0 (by grind)
  have h1 := below_candidate t x1 p1 ht0 hx1 (by grind)
  have h2 := below_candidate t x2 p2 ht0 hx2 (by grind)
  have he : t * p0 + t * p1 + t * p2 = t := by grind
  have ht1 : t ≤ 1 := by grind
  refine ⟨t, ht0, ht1, h0, h1, h2, ?_⟩
  have hchoice : t = c0 ∨ t = c1 ∨ t = c2 := by grind
  rcases hchoice with h | h | h
  · left; grind [candidate]
  · right; left; grind [candidate]
  · right; right; grind [candidate]
end NewtonLimitDynamics.SimplexExit
