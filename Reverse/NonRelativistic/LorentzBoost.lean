import BarrowLib.Common.RationalMagnitudes

/-!
PHYSICAL STAGE:
  Lorentz boost between two inertial frames in relative motion along one
  axis, and its Galilean limit: the Galilean frame transformation and the
  common absolute time.
MATHEMATICAL CONTENT:
  With kappa = 1/c², the Lorentz factor gamma satisfies
    gamma² (1 − kappa frameV²) = 1,  gamma > 0,
  and the boost of an event (x, t) to (x', t') reads
    x' = gamma (x − frameV t),   t' = gamma (t − kappa frameV x).
  All relations are relational and square-root-free, so they are meaningful
  on the fibre kappa = 0, where gamma = 1, x' = x − frameV t and t' = t.
  Notation: invC = 1/c, kappa = invC², frameV the relative frame velocity,
  gamma the Lorentz factor, (x, t) and (x', t') the coordinates of one
  event in the two frames. These theorems are standalone: wiring frames into
  the stable-particle sector is a later step.
INPUT PARAMETERS:
  kappa, frameV.
OUTPUT PARAMETERS:
  The transformed coordinates.
PROVED HERE:
  `gamma_fibre`: on kappa = 0 the Lorentz factor is 1.
  `factor_fibre_solvable`: gamma = 1 satisfies the fibre factor relation.
  `boost_space_fibre`: on kappa = 0, x' = x − frameV t.
  `boost_time_fibre`: on kappa = 0, t' = t: time is common to the frames.
ASSUMED HERE:
  The factor and boost relations are premises of each theorem.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  Attach frames to `Reverse/RelativisticQM/StableParticleSector.lean` so
  that absolute time on the fibre is consumed by the centre-of-mass stage.

STATUS: theorem.
-/

namespace Reverse.NonRelativistic.Boost
open NewtonLimitDynamics

def neg (a : Fraction) : Fraction := ⟨-a.num, a.den, a.den_pos⟩
def sub (a b : Fraction) : Fraction := Fraction.add a (neg b)

/-- Lorentz factor relation gamma² (1 − kappa frameV²) = 1 with gamma > 0. -/
def IsLorentzFactor (kappa frameV gamma : Fraction) : Prop :=
  Fraction.positive gamma ∧
    Fraction.equiv
      (Fraction.mul (Fraction.mul gamma gamma)
        (sub (Fraction.ofInt 1) (Fraction.mul kappa (Fraction.mul frameV frameV))))
      (Fraction.ofInt 1)

/-- Boost relations x' = gamma (x − frameV t), t' = gamma (t − kappa frameV x). -/
def IsLorentzBoost (kappa frameV gamma x t x' t' : Fraction) : Prop :=
  Fraction.equiv x' (Fraction.mul gamma (sub x (Fraction.mul frameV t))) ∧
    Fraction.equiv t' (Fraction.mul gamma (sub t (Fraction.mul kappa (Fraction.mul frameV x))))

theorem one_mul_equiv (a : Fraction) :
    Fraction.equiv (Fraction.mul (Fraction.ofInt 1) a) a := by
  simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt, Int.one_mul]

theorem mul_self_eq_of_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) (h : a * a = b * b) :
    a = b := by
  rcases Int.lt_trichotomy a b with hlt | heq | hgt
  · have := Int.mul_self_lt_mul_self (Int.le_of_lt ha) hlt
    omega
  · exact heq
  · have := Int.mul_self_lt_mul_self (Int.le_of_lt hb) hgt
    omega

/-- On the fibre the Lorentz factor is 1. -/
theorem gamma_fibre {kappa frameV gamma : Fraction} (hkappa : kappa.num = 0)
    (h : IsLorentzFactor kappa frameV gamma) : Fraction.equiv gamma (Fraction.ofInt 1) := by
  obtain ⟨hpos, hrel⟩ := h
  simp only [Fraction.equiv, Fraction.mul, Fraction.add, sub, neg, Fraction.ofInt, hkappa,
    Int.mul_zero, Int.zero_mul, Int.neg_zero, Int.mul_one, Int.one_mul, Int.zero_add,
    Int.add_zero] at hrel ⊢
  have hD : (0 : Int) < kappa.den * (frameV.den * frameV.den) :=
    Int.mul_pos kappa.den_pos (Int.mul_pos frameV.den_pos frameV.den_pos)
  have hsq : gamma.num * gamma.num = gamma.den * gamma.den := by
    apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hD)
    ac_nf at hrel ⊢
    try exact hrel
  exact mul_self_eq_of_pos hpos gamma.den_pos hsq

/-- gamma = 1 satisfies the fibre factor relation. -/
theorem factor_fibre_solvable {kappa : Fraction} (frameV : Fraction) (hkappa : kappa.num = 0) :
    IsLorentzFactor kappa frameV (Fraction.ofInt 1) := by
  refine ⟨by decide, ?_⟩
  simp only [Fraction.equiv, Fraction.mul, Fraction.add, sub, neg, Fraction.ofInt, hkappa,
    Int.mul_zero, Int.zero_mul, Int.neg_zero, Int.mul_one, Int.one_mul, Int.zero_add,
    Int.add_zero]

/-- On the fibre the spatial boost is Galilean: x' = x − frameV t. -/
theorem boost_space_fibre {kappa frameV gamma x t x' t' : Fraction} (hkappa : kappa.num = 0)
    (hg : IsLorentzFactor kappa frameV gamma)
    (h : IsLorentzBoost kappa frameV gamma x t x' t') :
    Fraction.equiv x' (sub x (Fraction.mul frameV t)) :=
  Fraction.equiv_trans h.1
    (Fraction.equiv_trans (Fraction.mul_equiv_right _ (gamma_fibre hkappa hg)) (one_mul_equiv _))

/-- On the fibre time is common to both frames: t' = t. -/
theorem boost_time_fibre {kappa frameV gamma x t x' t' : Fraction} (hkappa : kappa.num = 0)
    (hg : IsLorentzFactor kappa frameV gamma)
    (h : IsLorentzBoost kappa frameV gamma x t x' t') : Fraction.equiv t' t := by
  have h2 := Fraction.mul_equiv_right (sub t (Fraction.mul kappa (Fraction.mul frameV x)))
    (gamma_fibre hkappa hg)
  have h3 : Fraction.equiv
      (Fraction.mul (Fraction.ofInt 1) (sub t (Fraction.mul kappa (Fraction.mul frameV x)))) t := by
    simp only [Fraction.equiv, Fraction.mul, Fraction.add, sub, neg, Fraction.ofInt, hkappa,
      Int.mul_zero, Int.zero_mul, Int.neg_zero, Int.mul_one, Int.one_mul, Int.zero_add,
      Int.add_zero]
    ac_nf
  exact Fraction.equiv_trans h.2 (Fraction.equiv_trans h2 h3)

end Reverse.NonRelativistic.Boost
