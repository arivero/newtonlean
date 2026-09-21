import NewtonLimitDynamics.Common.RationalMagnitudes

namespace NewtonLimitDynamics.Comparison
open Fraction

def negate (a : Fraction) : Fraction := ⟨-a.num, a.den, a.den_pos⟩
def twice (t : Fraction) : Fraction := mul (ofInt 2) t

theorem twice_positive (t : Fraction) (ht : positive t) : positive (twice t) :=
  positive_mul (ofInt 2) t (by unfold positive ofInt; decide) ht

/-- Constant accelerative force, zero initial normal velocity. The tangential
    coordinate does not enter the normal sagitta. Its area interpretation is
    a separate mechanical/geometric premise. -/
def parabolaHeight (acc time : Fraction) : Fraction := half (mul acc (mul time time))
def midpointHeight (y₁ y₂ : Fraction) : Fraction := half (add y₁ y₂)

theorem symmetric_parabola_sagitta (acc time : Fraction) :
    equiv (midpointHeight (parabolaHeight acc (negate time)) (parabolaHeight acc time))
      (parabolaHeight acc time) := by
  unfold equiv midpointHeight parabolaHeight negate half add mul
  dsimp
  simp only [Int.neg_mul_neg, Int.add_mul, Int.mul_add]
  have htwo : ∀ x : Int, 2*x = x+x := by intro x; omega
  simp only [htwo, Int.mul_add, Int.add_mul]
  ac_rfl

/-- Calibrated force comparison on matched spatial quantities: the generated
    displacement uses one-sided duration t, the symmetric sagitta uses the
    full arc duration 2t. Thus the calibration factors are 2 and 8 respectively.
    For general curves, matching their limiting coefficients remains an input;
    this theorem does not assert equality of arbitrary finite displacements. -/
theorem generated_sagitta_commute (displacement time : Fraction) (ht : positive time) :
    equiv
      (mul (ofInt 8) (deflectionRatio displacement (twice time) (twice_positive time ht)))
      (mul (ofInt 2) (deflectionRatio displacement time ht)) := by
  simp only [equiv, deflectionRatio, twice, mul, ofInt]
  simp only [Int.one_mul, Int.mul_one]
  have eight : (8 : Int) = 2 * (2 * 2) := by decide
  rw [eight]
  ac_rfl

/-- The finite constant-force model gives its acceleration by the generated
    route, independently of the prior commutation identity. -/
theorem constant_force_generated (acc time : Fraction) (ht : positive time) :
    equiv (mul (ofInt 2) (deflectionRatio (parabolaHeight acc time) time ht)) acc := by
  unfold equiv deflectionRatio parabolaHeight half mul ofInt
  dsimp
  simp only [Int.one_mul, Int.mul_one]
  ac_rfl

end NewtonLimitDynamics.Comparison
