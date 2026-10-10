import BarrowLib.Common.RationalMagnitudes

/-! Finite rational barycentric elimination. Source: the original English
statement and Lean proof in this file. A nonnegative triple of total one and
an arbitrary signed triple of total one determine a rational scale at which
one residual coordinate becomes zero while all remain nonnegative. No area,
continuity, simplex-exchange inclusion or nonnegative inserted triple is
assumed. This records project proof provenance without historical textual
attribution or priority. Its dependencies are elementary Barrow arithmetic. -/

namespace NewtonLimitDynamics.SimplexExit
open Fraction

private def one : Fraction := Fraction.ofInt 1
private def two : Fraction := Fraction.ofInt 2

private def minF (a b : Fraction) : Fraction :=
  if a.num * b.den ≤ b.num * a.den then a else b

private theorem le_total (a b : Fraction) : Fraction.le a b ∨ Fraction.le b a := by
  unfold Fraction.le
  omega

private theorem min_le_left (a b : Fraction) : Fraction.le (minF a b) a := by
  unfold minF
  split
  · exact Fraction.magnitudes.le_refl _
  · exact (le_total a b).resolve_left ‹¬Fraction.le a b›

private theorem min_le_right (a b : Fraction) : Fraction.le (minF a b) b := by
  unfold minF
  split
  · assumption
  · exact Fraction.magnitudes.le_refl _

private theorem min_nonneg (a b : Fraction) (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) :
    0 ≤ (minF a b).num := by
  unfold minF
  split <;> assumption

private theorem min_choice (a b : Fraction) : minF a b = a ∨ minF a b = b := by
  unfold minF
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private def candidate (x p : Fraction) : Fraction :=
  if hp : Fraction.positive p then Fraction.quotient x p hp else two

private theorem candidate_nonneg (x p : Fraction) (hx : 0 ≤ x.num) :
    0 ≤ (candidate x p).num := by
  unfold candidate
  split
  · exact Int.mul_nonneg hx (Int.le_of_lt p.den_pos)
  · decide

private theorem candidate_pos_eq (x p : Fraction) (hp : Fraction.positive p) :
    Fraction.equiv (Fraction.mul (candidate x p) p) x := by
  simp only [candidate, dite_eq_left hp]
  unfold Fraction.equiv Fraction.mul Fraction.quotient
  dsimp
  ac_nf

private theorem below_candidate (t x p : Fraction) (ht : 0 ≤ t.num)
    (hx : 0 ≤ x.num) (h : Fraction.le t (candidate x p)) :
    Fraction.le (Fraction.mul t p) x := by
  by_cases hp : Fraction.positive p
  · exact Fraction.le_equiv_right
      (Fraction.mul_le_mul_positive (by simpa only [candidate, dite_eq_left hp] using h) p hp)
      (by simpa only [candidate, dite_eq_left hp] using candidate_pos_eq x p hp)
  · have hpn : p.num ≤ 0 := by unfold Fraction.positive at hp; omega
    have hmul : t.num * p.num ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos ht hpn
    have hright : 0 ≤ x.num * (t.den * p.den) :=
      Int.mul_nonneg hx (Int.le_of_lt (Int.mul_pos t.den_pos p.den_pos))
    have hleft : t.num * p.num * x.den ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg hmul (Int.le_of_lt x.den_pos)
    unfold Fraction.le Fraction.mul
    dsimp
    omega

private theorem sum_mul_equiv (t p0 p1 p2 : Fraction) :
    Fraction.equiv
      (Fraction.add (Fraction.add (Fraction.mul t p0) (Fraction.mul t p1)) (Fraction.mul t p2))
      (Fraction.mul t (Fraction.add (Fraction.add p0 p1) p2)) := by
  apply Fraction.equiv_trans
  · exact Fraction.add_equiv_right (Fraction.mul t p2)
      (Fraction.equiv_symm (Fraction.mul_add t p0 p1))
  · exact Fraction.equiv_symm (Fraction.mul_add t (Fraction.add p0 p1) p2)

private theorem sum_bound (t x0 x1 x2 p0 p1 p2 : Fraction)
    (hx : Fraction.equiv (Fraction.add (Fraction.add x0 x1) x2) one)
    (hp : Fraction.equiv (Fraction.add (Fraction.add p0 p1) p2) one)
    (h0 : Fraction.le (Fraction.mul t p0) x0)
    (h1 : Fraction.le (Fraction.mul t p1) x1)
    (h2 : Fraction.le (Fraction.mul t p2) x2) : Fraction.le t one := by
  have hs := Fraction.add_le_add (Fraction.add_le_add h0 h1) h2
  have h := Fraction.le_equiv_left (Fraction.equiv_symm (sum_mul_equiv t p0 p1 p2))
    (Fraction.le_equiv_right hs hx)
  have he := Fraction.mul_equiv_left t hp
  have hm : Fraction.equiv (Fraction.mul t one) t := by
    unfold Fraction.equiv Fraction.mul one Fraction.ofInt
    dsimp
    simp
  exact Fraction.le_equiv_left (Fraction.equiv_symm (Fraction.equiv_trans he hm)) h


private theorem two_not_le_one : ¬ Fraction.le two one := by
  intro h
  change (2 : Int) ≤ 1 at h
  omega

private theorem chosen_positive (t x p : Fraction)
    (h : t = candidate x p) (hp : Fraction.positive p) :
    Fraction.equiv (Fraction.mul t p) x := by
  rw [h]
  exact candidate_pos_eq x p hp

private theorem chosen_positive_or_contra (t x p : Fraction)
    (h : t = candidate x p) (ht : Fraction.le t one) :
    Fraction.positive p := by
  by_cases hp : Fraction.positive p
  · exact hp
  · have he : candidate x p = two := by simp only [candidate, dite_eq_right hp]
    apply False.elim (two_not_le_one ?_)
    rw [h, he] at ht
    exact ht

/-- A rational ray from an arbitrary barycentric triple exits through a facet.
The conclusion is expressed without subtraction: every coordinate of t*p
is at most x, and at least one equals x as a represented rational. -/
theorem simplex_exit (x0 x1 x2 p0 p1 p2 : Fraction)
    (hx0 : 0 ≤ x0.num) (hx1 : 0 ≤ x1.num) (hx2 : 0 ≤ x2.num)
    (hx : Fraction.equiv (Fraction.add (Fraction.add x0 x1) x2) one)
    (hp : Fraction.equiv (Fraction.add (Fraction.add p0 p1) p2) one) :
    ∃ t : Fraction, 0 ≤ t.num ∧ Fraction.le t one ∧
      Fraction.le (Fraction.mul t p0) x0 ∧
      Fraction.le (Fraction.mul t p1) x1 ∧
      Fraction.le (Fraction.mul t p2) x2 ∧
      (Fraction.equiv (Fraction.mul t p0) x0 ∨
       Fraction.equiv (Fraction.mul t p1) x1 ∨
       Fraction.equiv (Fraction.mul t p2) x2) := by
  let c0 := candidate x0 p0
  let c1 := candidate x1 p1
  let c2 := candidate x2 p2
  let t := minF (minF c0 c1) c2
  have ht0 : 0 ≤ t.num := min_nonneg _ _
    (min_nonneg _ _ (candidate_nonneg x0 p0 hx0) (candidate_nonneg x1 p1 hx1))
    (candidate_nonneg x2 p2 hx2)
  have hc0 : Fraction.le t c0 :=
    Fraction.magnitudes.le_trans (min_le_left _ _) (min_le_left _ _)
  have hc1 : Fraction.le t c1 :=
    Fraction.magnitudes.le_trans (min_le_left _ _) (min_le_right _ _)
  have hc2 : Fraction.le t c2 := min_le_right _ _
  have h0 : Fraction.le (Fraction.mul t p0) x0 :=
    below_candidate t x0 p0 ht0 hx0 hc0
  have h1 : Fraction.le (Fraction.mul t p1) x1 :=
    below_candidate t x1 p1 ht0 hx1 hc1
  have h2 : Fraction.le (Fraction.mul t p2) x2 :=
    below_candidate t x2 p2 ht0 hx2 hc2
  have ht1 : Fraction.le t one := sum_bound t x0 x1 x2 p0 p1 p2 hx hp h0 h1 h2
  refine ⟨t,ht0,ht1,h0,h1,h2,?_⟩
  rcases min_choice (minF c0 c1) c2 with hleft | hright
  · rcases min_choice c0 c1 with hfirst | hsecond
    · left
      have he : t = candidate x0 p0 := by simp only [t,c0,hleft,hfirst]
      exact chosen_positive t x0 p0 he (chosen_positive_or_contra t x0 p0 he ht1)
    · right; left
      have he : t = candidate x1 p1 := by simp only [t,c1,hleft,hsecond]
      exact chosen_positive t x1 p1 he (chosen_positive_or_contra t x1 p1 he ht1)
  · right; right
    have he : t = candidate x2 p2 := by simp only [t,c2,hright]
    exact chosen_positive t x2 p2 he (chosen_positive_or_contra t x2 p2 he ht1)

end NewtonLimitDynamics.SimplexExit
