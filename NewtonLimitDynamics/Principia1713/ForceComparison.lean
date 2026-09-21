import NewtonLimitDynamics.Common.RationalMagnitudes

namespace Principia1713
open NewtonLimitDynamics NewtonLimitDynamics.Fraction

/-- Division of represented magnitudes requires a positive divisor. -/
def quotient (a b : Fraction) (hb : positive b) : Fraction :=
  ⟨a.num * b.den, a.den * b.num, Int.mul_pos a.den_pos hb⟩

/-- Exact coefficient model of Corollary 3, NOT an assertion that variable
    force has this finite-time law. k is shared calibration, and f denotes
    accelerative force (or motive force with matched mass). -/
def generated (k f t : Fraction) : Fraction := mul (mul k f) (mul t t)

theorem corollary4_coefficient_reconstruction (k f t : Fraction)
    (hk : positive k) (ht : positive t) :
    equiv (quotient (generated k f t) (mul k (mul t t))
      (positive_mul k _ hk (positive_mul t t ht ht))) f := by
  unfold equiv quotient generated mul
  dsimp
  ac_rfl

/-- Unlike Corollary 4, this rearrangement excludes zero force. -/
theorem corollary5_coefficient_reconstruction (k f t : Fraction)
    (hk : positive k) (hf : positive f) :
    equiv (quotient (generated k f t) (mul k f) (positive_mul k f hk hf))
      (mul t t) := by
  unfold equiv quotient generated mul
  dsimp
  ac_rfl

end Principia1713
