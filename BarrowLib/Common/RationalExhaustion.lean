import BarrowLib.Common.RationalMagnitudes

/-! Rational exhaustion of a closed order bound, proved by the explicit
half-gap witness. No completeness, real order or calculus theorem is imported. -/
namespace NewtonLimitDynamics.Fraction

theorem le_of_enlargements (a b : Fraction)
    (h : ∀ eps : Fraction, 0 < eps.num → le a (add b eps)) : le a b := by
  apply Classical.byContradiction
  intro hn
  have hd : 0 < a.num * b.den - b.num * a.den := by
    unfold le at hn
    omega
  let eps : Fraction := ⟨a.num * b.den - b.num * a.den,
    2 * a.den * b.den,Int.mul_pos (Int.mul_pos (by decide) a.den_pos) b.den_pos⟩
  have hh := h eps hd
  change a.num * (b.den * (2 * a.den * b.den)) ≤
    (b.num * (2 * a.den * b.den) +
      (a.num * b.den - b.num * a.den) * b.den) * a.den at hh
  have hp : 0 < (a.num * b.den - b.num * a.den) * (a.den * b.den) :=
    Int.mul_pos hd (Int.mul_pos a.den_pos b.den_pos)
  have he : a.num * (b.den * (2 * a.den * b.den)) =
      (b.num * (2 * a.den * b.den) +
        (a.num * b.den - b.num * a.den) * b.den) * a.den +
      (a.num * b.den - b.num * a.den) * (a.den * b.den) := by
    simp only [show (2 : Int) = 1+1 by rfl,Int.sub_mul,Int.add_mul,Int.mul_sub,
      Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
    omega
  rw [he] at hh
  omega

end NewtonLimitDynamics.Fraction
