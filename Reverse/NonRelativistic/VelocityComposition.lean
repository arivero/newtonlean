import BarrowLib.Common.RationalMagnitudes

/-!
PHYSICAL STAGE:
  Composition of collinear particle velocities and its Galilean limit. This
  is the composition of velocities of a particle seen from two frames in
  relative motion along the same line; it coincides with the composition of
  collinear boosts, but the general boost group law is a separate matter
  and is not treated here.
MATHEMATICAL CONTENT:
  With kappa = 1/c², the relativistic law v ⊕_kappa w = (v + w)/(1 + kappa v w)
  is written in the square-root-free relational form
    composed · (1 + kappa v w) = v + w,
  exact for every finite c and meaningful on the fibre kappa = 0. All
  statements are rational algebra on that relation.
  Notation: invC = 1/c, kappa = invC², v and w are velocities, `composed`
  is v ⊕_kappa w, B a velocity bound.
INPUT PARAMETERS:
  kappa, the two velocities.
OUTPUT PARAMETERS:
  The composed velocity.
PROVED HERE:
  `galilean_fibre`: on kappa = 0, composed = v + w.
  `fibre_solvable`: v + w satisfies the fibre relation.
  `of_quotient`: for a positive denominator the usual quotient formula
    satisfies the relation, so the relation is the graph of the textbook
    law there.
  `defect_identity`: for every kappa, composed + kappa v w · composed = v + w,
    the exact form of (v ⊕ w) − (v + w) = − kappa v w (v + w)/(1 + kappa v w).
  `galilean_above`: for nonnegative data the relativistic composition is at
    most the Galilean sum.
  `defect_bounded`: on 0 ≤ v, w, composed ≤ B the defect kappa v w · composed
    is at most kappa B³, so it is linear in kappa with constant B³.
ASSUMED HERE:
  The relation itself is a premise of each theorem; its origin is the
  Lorentz boost, see `Reverse/RelativisticQM`.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/NonRelativistic/ZeroInvCFibre.lean` applies these results to the
  stable composite sector on the fibre.

The declarations live in `Reverse.NonRelativistic.Composition`, beside the
kinetic-energy theorems of `Reverse.NonRelativistic`, which use the same
theorem names for the analogous statements.

STATUS: theorem.
-/

namespace Reverse.NonRelativistic.Composition
open NewtonLimitDynamics

/-- Relational collinear velocity composition at kappa:
composed · (1 + kappa v w) = v + w. -/
def IsCollinearComposition (kappa v w composed : Fraction) : Prop :=
  Fraction.equiv
    (Fraction.mul composed
      (Fraction.add (Fraction.ofInt 1) (Fraction.mul kappa (Fraction.mul v w))))
    (Fraction.add v w)

/-- The denominator 1 + kappa v w of the textbook formula. -/
def compositionDenominator (kappa v w : Fraction) : Fraction :=
  Fraction.add (Fraction.ofInt 1) (Fraction.mul kappa (Fraction.mul v w))

theorem mul_one_equiv (a : Fraction) :
    Fraction.equiv (Fraction.mul a (Fraction.ofInt 1)) a := by
  simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt, Int.mul_one]

theorem quotient_mul_cancel (a d : Fraction) (hd : Fraction.positive d) :
    Fraction.equiv (Fraction.mul (Fraction.quotient a d hd) d) a := by
  simp only [Fraction.equiv, Fraction.mul, Fraction.quotient]
  ac_nf

/-- On the fibre kappa = 0 the composition is Galilean: composed = v + w. -/
theorem galilean_fibre {kappa v w composed : Fraction} (hkappa : kappa.num = 0)
    (h : IsCollinearComposition kappa v w composed) :
    Fraction.equiv composed (Fraction.add v w) := by
  unfold IsCollinearComposition at h
  simp only [Fraction.equiv, Fraction.mul, Fraction.add, Fraction.ofInt, hkappa,
    Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul, Int.zero_add, Int.add_zero] at h ⊢
  apply Int.eq_of_mul_eq_mul_right
    (Int.ne_of_gt (Int.mul_pos kappa.den_pos (Int.mul_pos v.den_pos w.den_pos)))
  ac_nf at h ⊢

/-- The Galilean sum satisfies the fibre relation. -/
theorem fibre_solvable {kappa : Fraction} (v w : Fraction) (hkappa : kappa.num = 0) :
    IsCollinearComposition kappa v w (Fraction.add v w) := by
  unfold IsCollinearComposition
  simp only [Fraction.equiv, Fraction.mul, Fraction.add, Fraction.ofInt, hkappa,
    Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul, Int.zero_add, Int.add_zero]
  ac_nf

/-- For a positive denominator the quotient formula satisfies the relation. -/
theorem of_quotient (kappa v w : Fraction)
    (hd : Fraction.positive (compositionDenominator kappa v w)) :
    IsCollinearComposition kappa v w
      (Fraction.quotient (Fraction.add v w) (compositionDenominator kappa v w) hd) :=
  quotient_mul_cancel _ _ hd

/-- Exact rearrangement: composed + kappa v w · composed = v + w. -/
theorem defect_identity {kappa v w composed : Fraction}
    (h : IsCollinearComposition kappa v w composed) :
    Fraction.equiv
      (Fraction.add composed (Fraction.mul (Fraction.mul kappa (Fraction.mul v w)) composed))
      (Fraction.add v w) := by
  refine Fraction.equiv_trans ?_ h
  refine Fraction.equiv_trans ?_
    (Fraction.equiv_symm
      (Fraction.mul_add composed (Fraction.ofInt 1) (Fraction.mul kappa (Fraction.mul v w))))
  exact Fraction.add_equiv (Fraction.equiv_symm (mul_one_equiv composed))
    (Fraction.mul_comm _ composed)

/-- For nonnegative data the relativistic composition is below the Galilean
sum. -/
theorem galilean_above {kappa v w composed : Fraction} (hkappa : 0 ≤ kappa.num)
    (hv : 0 ≤ v.num) (hw : 0 ≤ w.num) (hc : 0 ≤ composed.num)
    (h : IsCollinearComposition kappa v w composed) :
    Fraction.le composed (Fraction.add v w) :=
  Fraction.le_equiv_right
    (Fraction.le_add_nonnegative _ _
      (Fraction.nonnegative_mul _ _
        (Fraction.nonnegative_mul _ _ hkappa (Fraction.nonnegative_mul _ _ hv hw)) hc))
    (defect_identity h)

/-- The defect kappa v w · composed is at most kappa B³ on 0 ≤ v, w, composed ≤ B. -/
theorem defect_bounded {kappa v w composed B : Fraction} (hkappa : 0 ≤ kappa.num)
    (hv : 0 ≤ v.num) (hw : 0 ≤ w.num) (hc : 0 ≤ composed.num)
    (hvB : Fraction.le v B) (hwB : Fraction.le w B) (hcB : Fraction.le composed B) :
    Fraction.le (Fraction.mul (Fraction.mul kappa (Fraction.mul v w)) composed)
      (Fraction.mul (Fraction.mul kappa (Fraction.mul B B)) B) := by
  have hB : 0 ≤ B.num := Fraction.nonnegative_of_le hv hvB
  have s1 : Fraction.le (Fraction.mul v w) (Fraction.mul B w) :=
    Fraction.mul_le_mul_nonnegative hvB w hw
  have s2 : Fraction.le (Fraction.mul B w) (Fraction.mul B B) :=
    Fraction.mul_le_mul_nonnegative_left hwB B hB
  have s3 : Fraction.le (Fraction.mul kappa (Fraction.mul v w))
      (Fraction.mul kappa (Fraction.mul B B)) :=
    Fraction.mul_le_mul_nonnegative_left (Fraction.magnitudes.le_trans s1 s2) kappa hkappa
  have s4 : Fraction.le (Fraction.mul (Fraction.mul kappa (Fraction.mul v w)) composed)
      (Fraction.mul (Fraction.mul kappa (Fraction.mul B B)) composed) :=
    Fraction.mul_le_mul_nonnegative s3 composed hc
  have s5 : Fraction.le (Fraction.mul (Fraction.mul kappa (Fraction.mul B B)) composed)
      (Fraction.mul (Fraction.mul kappa (Fraction.mul B B)) B) :=
    Fraction.mul_le_mul_nonnegative_left hcB _
      (Fraction.nonnegative_mul _ _ hkappa (Fraction.nonnegative_mul _ _ hB hB))
  exact Fraction.magnitudes.le_trans s4 s5

end Reverse.NonRelativistic.Composition
