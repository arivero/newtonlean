import BarrowLib.Common.RationalMagnitudes

/-!
PHYSICAL STAGE:
  Nonrelativistic limit of one free body's energy, invC → 0.
MATHEMATICAL CONTENT:
  The relativistic relation E² = m²c⁴ + p²c² with E = m c² + K becomes, after
  expanding and multiplying by invC² = 1/c²,
    K · (K · invC² + 2m) = p².
  This square-root-free form is exact for every finite c and extends to the
  fibre invC = 0, where it reads 2mK = p². Everything below is elementary
  rational algebra on that relation; no square root is taken.
INPUT PARAMETERS:
  u = invC², the body's mass m, the squared momentum magnitude p².
OUTPUT PARAMETERS:
  The rest-subtracted kinetic energy K.
PROVED HERE:
  `newtonian_fibre`: on the fibre u = 0, 2mK = p².
  `kinetic_energy_at_zero_invC`: hence K = p²/(2m) for positive m.
  `fibre_solvable`: the Newtonian value satisfies the fibre relation, so the
    fibre relation is solvable inside the rationals. Off the fibre a square
    root is needed, which `Fraction` lacks: the limit removes a structural
    requirement in addition to changing a formula.
  `defect_identity`: for every u, 2mK + K²u = p².
  `newtonian_below`: for u ≥ 0 and K ≥ 0, 2mK ≤ p².
  `defect_bounded`: for 0 ≤ K ≤ B and u ≥ 0, the defect K²u is at most B²u,
    so it is linear in invC² with constant B².
ASSUMED HERE:
  The dispersion relation is a premise of every theorem; its origin is the
  Poincaré kinematics of a stable composite, see `Reverse/RelativisticQM`.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/NonRelativistic/Limit.lean` applies these results to the stable
  composite sector on the fibre.

STATUS: theorem.
-/

namespace Reverse.NonRelativistic
open NewtonLimitDynamics

/-- Rest-subtracted dispersion relation K · (K u + 2 m) = p², with u = invC²
and `psq` the squared momentum magnitude. -/
def RestSubtractedDispersion (u m psq K : Fraction) : Prop :=
  Fraction.equiv
    (Fraction.mul K (Fraction.add (Fraction.mul K u) (Fraction.mul (Fraction.ofInt 2) m)))
    psq

/-- Twice the mass, the Newtonian denominator. -/
def twice (m : Fraction) : Fraction := Fraction.mul (Fraction.ofInt 2) m

theorem twice_positive {m : Fraction} (hm : Fraction.positive m) :
    Fraction.positive (twice m) :=
  Fraction.positive_mul _ _ (by decide) hm

/-- On the fibre u = 0 the relation collapses to 2mK = p². -/
theorem newtonian_fibre {u m psq K : Fraction} (hu : u.num = 0)
    (h : RestSubtractedDispersion u m psq K) :
    Fraction.equiv (Fraction.mul (twice m) K) psq := by
  unfold RestSubtractedDispersion at h
  unfold twice
  simp only [Fraction.equiv, Fraction.mul, Fraction.add, Fraction.ofInt, hu,
    Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul, Int.zero_add, Int.add_zero] at h ⊢
  apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (Int.mul_pos K.den_pos u.den_pos))
  ac_nf at h ⊢

/-- The Newtonian kinetic energy p²/(2m) on the fibre. -/
theorem kinetic_energy_at_zero_invC {u m psq K : Fraction} (hm : Fraction.positive m)
    (hu : u.num = 0) (h : RestSubtractedDispersion u m psq K) :
    Fraction.equiv K (Fraction.quotient psq (twice m) (twice_positive hm)) := by
  have h2 := newtonian_fibre hu h
  simp only [Fraction.equiv, Fraction.mul, Fraction.quotient, twice, Fraction.ofInt,
    Int.mul_one, Int.one_mul] at h2 ⊢
  ac_nf at h2 ⊢

/-- The fibre relation is solvable in the rationals: p²/(2m) satisfies it. -/
theorem fibre_solvable {u m psq : Fraction} (hm : Fraction.positive m) (hu : u.num = 0) :
    RestSubtractedDispersion u m psq (Fraction.quotient psq (twice m) (twice_positive hm)) := by
  unfold RestSubtractedDispersion twice
  simp only [Fraction.equiv, Fraction.mul, Fraction.add, Fraction.quotient, Fraction.ofInt, hu,
    Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul, Int.zero_add, Int.add_zero]
  ac_nf

/-- Exact rearrangement for every u: 2mK + K²u = p². -/
theorem defect_identity {u m psq K : Fraction} (h : RestSubtractedDispersion u m psq K) :
    Fraction.equiv
      (Fraction.add (Fraction.mul (twice m) K) (Fraction.mul (Fraction.mul K K) u)) psq := by
  refine Fraction.equiv_trans ?_ h
  refine Fraction.equiv_trans ?_
    (Fraction.equiv_symm (Fraction.mul_add K (Fraction.mul K u) (Fraction.mul (Fraction.ofInt 2) m)))
  refine Fraction.equiv_trans (Fraction.add_comm _ _) ?_
  exact Fraction.add_equiv (Fraction.mul_assoc K K u) (Fraction.mul_comm (twice m) K)

/-- With u ≥ 0 and K ≥ 0 the Newtonian expression underestimates p²: 2mK ≤ p². -/
theorem newtonian_below {u m psq K : Fraction} (hu : 0 ≤ u.num) (hK : 0 ≤ K.num)
    (h : RestSubtractedDispersion u m psq K) :
    Fraction.le (Fraction.mul (twice m) K) psq :=
  Fraction.le_equiv_right
    (Fraction.le_add_nonnegative _ _
      (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hK hK) hu))
    (defect_identity h)

/-- The defect K²u is bounded by B²u on 0 ≤ K ≤ B, so it vanishes linearly
with invC² for bounded kinetic energies. -/
theorem defect_bounded {u K B : Fraction} (hu : 0 ≤ u.num) (hK : 0 ≤ K.num)
    (hKB : Fraction.le K B) :
    Fraction.le (Fraction.mul (Fraction.mul K K) u) (Fraction.mul (Fraction.mul B B) u) := by
  have hB : 0 ≤ B.num := Fraction.nonnegative_of_le hK hKB
  have h1 : Fraction.le (Fraction.mul K K) (Fraction.mul B K) :=
    Fraction.mul_le_mul_nonnegative hKB K hK
  have h2 : Fraction.le (Fraction.mul B K) (Fraction.mul B B) :=
    Fraction.mul_le_mul_nonnegative_left hKB B hB
  exact Fraction.mul_le_mul_nonnegative (Fraction.magnitudes.le_trans h1 h2) u hu

end Reverse.NonRelativistic
