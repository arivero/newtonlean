import NewtonLimitDynamics

/-! Controls for the primary exhaustion, boundary and mechanical premises.
These check their logical scope; no area-rule existence is inferred. -/
namespace NewtonLimitDynamics.Polygon.HistoricalGroundworkControls
open NewtonLimitDynamics TimeSubdivision Exhaustion RationalBoundary
open FiniteEstimates PointBounds HarmonicTimeComparison

private def z : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1
private def p (x y : Int) : Point := (Fraction.ofInt x, Fraction.ofInt y)

private theorem zero_vanishes : VanishingDifference Fraction.magnitudes (fun _ => z) := by
  intro d hd
  exact ⟨0, fun _ _ => (Fraction.positive_iff_zero_lt d).mp hd⟩

-- Fraction displays need not be identical for the zero-terminal conclusion.
example : Fraction.equiv (⟨0,7,by decide⟩ : Fraction) z :=
  Principia1687.LemmaI.ultimate_difference_zero (fun _ => z) _ (by decide)
    zero_vanishes (by
      intro d hd hlt
      have h := Int.mul_pos hd (by decide : (0 : Int) < 7)
      change d.num * 7 < 0 * d.den at hlt
      simp only [Int.zero_mul] at hlt
      omega)

example : ¬ TerminalLower Fraction.magnitudes (fun _ => z) one := by
  intro h
  exact Principia1713.LemmaI.no_positive_ultimate_difference Fraction.magnitudes _ _
    zero_vanishes h (by change (0 : Int) < 1; decide)

-- At T=0 even False holds "before the end": the positive-window premise matters.
example : BeforeEnd Fraction.magnitudes z (fun _ => False) := by
  refine ⟨one, by change (0 : Int) < 1; decide, ?_⟩
  intro h hh _ hzero
  change 0 < h.num at hh
  change h.num * 1 < 0 * h.den at hzero
  simp only [Int.mul_one, Int.zero_mul] at hzero
  omega

example : ∃ h : Fraction, 0 < h.num ∧ Fraction.lt h one ∧ True :=
  before_end_has_witness Fraction.magnitudes one _ (by change (0 : Int) < 1; decide)
    ⟨one, by change (0 : Int) < 1; decide, fun _ _ _ _ => trivial⟩

example : Fraction.equiv
    (RectangleContent.ratioTo (Fraction.ofInt 2) (by decide) one) one.half := by decide
example : Fraction.equiv
    (durationDifference (RectangleContent.ratioTo (Fraction.ofInt 2) (by decide) one) one).abs
    one.half := by decide

-- Concrete implementations witness the law predicates.
private theorem inertial1687 : Principia1687.Laws.InertialMotion ZeroForce.inertialAt :=
  fun _ _ _ => ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩
private theorem additive1687 : Principia1687.Laws.AdditiveImpulse pointAdd :=
  fun _ _ => ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩
example : pointEquiv (ZeroForce.inertialAt (p 3 4) (pointAdd (p 2 1) (p (-1) 3)) one.half)
    (Parallelogram.diagonal (p 3 4) (pointScale one.half (p 2 1))
      (pointScale one.half (p (-1) 3))) :=
  Principia1687.Laws.corollary1_from_laws _ _ inertial1687 additive1687 _ _ _ _

-- Dropping the additive-change law permits a wrong diagonal.
example : ¬ Principia1713.Laws.AdditiveImpulse (fun u _ => u) := by
  intro h
  have hx := (h (p 0 0) (p 1 0)).1
  have hn : ¬ Fraction.equiv (Fraction.ofInt 0) (Fraction.ofInt 1) := by decide
  exact hn hx
example : ¬ pointEquiv (ZeroForce.inertialAt (p 0 0) (p 0 0) one)
    (Parallelogram.diagonal (p 0 0) (p 0 0) (p 1 0)) := by decide

-- A vertical curve is allowed by the rational boundary theorem.
private def vertical (t : Fraction) : Point := (z,t)
private theorem vertical_distance (s t : Fraction) :
    Fraction.equiv (pointDistance (vertical s) (vertical t))
      (durationDifference s t).abs := by
  apply Fraction.equiv_trans (pointDistance_symm _ _)
  simp only [pointDistance, pointNorm, vertical, z, pointSub, pointAdd, pointNeg,
    durationDifference, HarmonicStability.negF, Fraction.abs, Fraction.add,
    Fraction.ofInt, Fraction.equiv, Int.neg_zero, Int.zero_mul, Int.mul_zero,
    Int.add_zero, Int.zero_add, Int.natAbs_zero, Int.natCast_zero,
    Int.mul_one, Int.one_mul]

private theorem vertical_uniform : UniformOn vertical z one := by
  intro eps heps
  refine ⟨eps.half, heps, ?_⟩
  intro s t _ _ _ _ hst
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_equiv_left (vertical_distance s t) hst)
    (Fraction.half_lt eps heps)

example (parts : Nat → MonotoneRectangles.Partition z one)
    (hmesh : VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    Approaches (fun m => ChordTrace vertical (parts m)) (CurveTrace vertical z one) :=
  Principia1713.LemmaIII.corollary2_chord_boundary vertical z one parts vertical_uniform hmesh

#print axioms Principia1687.LemmaI.given_time_exhaustion
#print axioms Principia1713.LemmaII.equal_width_ultimate_gap_zero
#print axioms Principia1687.LemmaIII.unequal_width_curved_area_approximation
#print axioms Principia1713.LemmaIII.corollary4_rational_perimeters
#print axioms Principia1713.Laws.corollary1_from_laws
end NewtonLimitDynamics.Polygon.HistoricalGroundworkControls
