import BarrowLib.Common.RationalMagnitudes

/-!
PHYSICAL STAGE:
  Nonrelativistic limit of one free body's energy, invC → 0.
MATHEMATICAL CONTENT:
  The relativistic relation E² = m²c⁴ + p²c² with E = m c² + K becomes, after
  expanding and multiplying by kappa = invC² = 1/c²,
    K · (K · kappa + 2m) = p².
  Notation throughout Reverse/: invC = 1/c, kappa = invC², v and w are
  velocities, p a momentum, K the rest-subtracted kinetic energy, m a mass.
  This square-root-free form is exact for every finite c and extends to the
  fibre invC = 0, where it reads 2mK = p². Everything below is elementary
  rational algebra on that relation; no square root is taken.
INPUT PARAMETERS:
  kappa = invC², the body's mass m, the squared momentum magnitude p².
OUTPUT PARAMETERS:
  The rest-subtracted kinetic energy K.
PROVED HERE:
  `newtonian_fibre`: on the fibre kappa = 0, 2mK = p².
  `kinetic_energy_at_zero_invC`: hence K = p²/(2m) for positive m.
  `fibre_solvable`: the Newtonian value satisfies the fibre relation, so the
    fibre relation is solvable inside the rationals. Off the fibre a square
    root is needed, which `Fraction` lacks: the limit removes a structural
    requirement in addition to changing a formula.
  `defect_identity`: for every kappa, 2mK + K² kappa = p².
  `newtonian_below`: for kappa ≥ 0 and K ≥ 0, 2mK ≤ p².
  `defect_bounded`: for 0 ≤ K ≤ B and kappa ≥ 0, the defect K² kappa is at
    most B² kappa, so it is linear in kappa with constant B².
ASSUMED HERE:
  The dispersion relation is a premise of every theorem; its origin is the
  Poincaré kinematics of a stable composite, see `Reverse/RelativisticQM`.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/NonRelativistic/ZeroInvCFibre.lean` applies these results to the
  stable composite sector on the fibre.

STATUS: theorem.
-/

namespace Reverse.NonRelativistic
open NewtonLimitDynamics

/-- Rest-subtracted dispersion relation K · (K kappa + 2 m) = p², with
kappa = invC² and `psq` the squared momentum magnitude. -/
def RestSubtractedDispersion (kappa m psq K : Fraction) : Prop :=
  Fraction.equiv
    (Fraction.mul K (Fraction.add (Fraction.mul K kappa) (Fraction.mul (Fraction.ofInt 2) m)))
    psq

/-- Twice the mass, the Newtonian denominator. -/
def twice (m : Fraction) : Fraction := Fraction.mul (Fraction.ofInt 2) m

theorem twice_positive {m : Fraction} (hm : Fraction.positive m) :
    Fraction.positive (twice m) :=
  Fraction.positive_mul _ _ (by decide) hm

/-- On the fibre kappa = 0 the relation collapses to 2mK = p². -/
theorem newtonian_fibre {kappa m psq K : Fraction} (hkappa : kappa.num = 0)
    (h : RestSubtractedDispersion kappa m psq K) :
    Fraction.equiv (Fraction.mul (twice m) K) psq := by
  unfold RestSubtractedDispersion at h
  unfold twice
  simp only [Fraction.equiv, Fraction.mul, Fraction.add, Fraction.ofInt, hkappa,
    Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul, Int.zero_add, Int.add_zero] at h ⊢
  apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (Int.mul_pos K.den_pos kappa.den_pos))
  ac_nf at h ⊢

/-- The Newtonian kinetic energy p²/(2m) on the fibre. -/
theorem kinetic_energy_at_zero_invC {kappa m psq K : Fraction} (hm : Fraction.positive m)
    (hkappa : kappa.num = 0) (h : RestSubtractedDispersion kappa m psq K) :
    Fraction.equiv K (Fraction.quotient psq (twice m) (twice_positive hm)) := by
  have h2 := newtonian_fibre hkappa h
  simp only [Fraction.equiv, Fraction.mul, Fraction.quotient, twice, Fraction.ofInt,
    Int.mul_one, Int.one_mul] at h2 ⊢
  ac_nf at h2 ⊢

/-- The fibre relation is solvable in the rationals: p²/(2m) satisfies it. -/
theorem fibre_solvable {kappa m psq : Fraction} (hm : Fraction.positive m) (hkappa : kappa.num = 0) :
    RestSubtractedDispersion kappa m psq (Fraction.quotient psq (twice m) (twice_positive hm)) := by
  unfold RestSubtractedDispersion twice
  simp only [Fraction.equiv, Fraction.mul, Fraction.add, Fraction.quotient, Fraction.ofInt, hkappa,
    Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul, Int.zero_add, Int.add_zero]
  ac_nf

/-- Exact rearrangement for every kappa: 2mK + K² kappa = p². -/
theorem defect_identity {kappa m psq K : Fraction} (h : RestSubtractedDispersion kappa m psq K) :
    Fraction.equiv
      (Fraction.add (Fraction.mul (twice m) K) (Fraction.mul (Fraction.mul K K) kappa)) psq := by
  refine Fraction.equiv_trans ?_ h
  refine Fraction.equiv_trans ?_
    (Fraction.equiv_symm (Fraction.mul_add K (Fraction.mul K kappa) (Fraction.mul (Fraction.ofInt 2) m)))
  refine Fraction.equiv_trans (Fraction.add_comm _ _) ?_
  exact Fraction.add_equiv (Fraction.mul_assoc K K kappa) (Fraction.mul_comm (twice m) K)

/-- With kappa ≥ 0 and K ≥ 0 the Newtonian expression underestimates p²: 2mK ≤ p². -/
theorem newtonian_below {kappa m psq K : Fraction} (hkappa : 0 ≤ kappa.num) (hK : 0 ≤ K.num)
    (h : RestSubtractedDispersion kappa m psq K) :
    Fraction.le (Fraction.mul (twice m) K) psq :=
  Fraction.le_equiv_right
    (Fraction.le_add_nonnegative _ _
      (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hK hK) hkappa))
    (defect_identity h)

/-- The defect K² kappa is bounded by B² kappa on 0 ≤ K ≤ B, so it vanishes
linearly with kappa for bounded kinetic energies. -/
theorem defect_bounded {kappa K B : Fraction} (hkappa : 0 ≤ kappa.num) (hK : 0 ≤ K.num)
    (hKB : Fraction.le K B) :
    Fraction.le (Fraction.mul (Fraction.mul K K) kappa) (Fraction.mul (Fraction.mul B B) kappa) := by
  have hB : 0 ≤ B.num := Fraction.nonnegative_of_le hK hKB
  have h1 : Fraction.le (Fraction.mul K K) (Fraction.mul B K) :=
    Fraction.mul_le_mul_nonnegative hKB K hK
  have h2 : Fraction.le (Fraction.mul B K) (Fraction.mul B B) :=
    Fraction.mul_le_mul_nonnegative_left hKB B hB
  exact Fraction.mul_le_mul_nonnegative (Fraction.magnitudes.le_trans h1 h2) kappa hkappa

end Reverse.NonRelativistic
