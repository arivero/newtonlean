import NewtonLimitDynamics

/-!
Scope control for Lemma III Corollaries III-IV's contact-tangent increment.
Target: derive supporting cells and boundary approximation from independent
secant concavity and two-sided tangent contact; neither enclosure nor boundary
convergence may be supplied as a premise.

Pre-registered nonlinear instance: g(x)=4-x² on [-2,-1], tangent slope -2x.
At the endpoints the two tangents meet at (-3/2,2), the curve there is 7/4,
and the chord there is 3/2. The tangent polygon must enclose this curved point;
the chord must not coincide with it. The line of slope 3 at x=-2 passes through
both endpoints but is not the contact tangent (whose slope is 4).
These are exact rational controls, not a numerical source or a proof of
unrestricted curve regularity, area existence, arclength or Proposition I.
-/

namespace TangentContactVerification

open NewtonLimitDynamics NewtonLimitDynamics.Polygon
open NewtonLimitDynamics.Polygon.TangentContact
open TimeSubdivision HarmonicTimeComparison
open HarmonicStability
open ConvexCover

private def q (n : Int) (d : Int) (hd : 0 < d) : Fraction := ⟨n, d, hd⟩
private def minusTwo : Fraction := Fraction.ofInt (-2)
private def minusOne : Fraction := Fraction.ofInt (-1)
private def midpoint : Fraction := ⟨-3, 2, by decide⟩
private def two : Fraction := Fraction.ofInt 2
private def sevenFourths : Fraction := ⟨7, 4, by decide⟩
private def threeHalves : Fraction := ⟨3, 2, by decide⟩

private def g (x : Fraction) : Fraction :=
  ⟨4 * (x.den * x.den) - x.num * x.num,
    x.den * x.den, Int.mul_pos x.den_pos x.den_pos⟩

private def d (x : Fraction) : Fraction :=
  ⟨-2 * x.num, x.den, x.den_pos⟩

example : Fraction.equiv (g midpoint) sevenFourths := by
  unfold Fraction.equiv g midpoint sevenFourths
  decide

example : Fraction.equiv (g minusTwo) (Fraction.ofInt 0) := by
  unfold Fraction.equiv g minusTwo Fraction.ofInt
  decide

example : Fraction.equiv (g minusOne) (Fraction.ofInt 3) := by
  unfold Fraction.equiv g minusOne Fraction.ofInt
  decide

example : Fraction.equiv (line g d minusTwo midpoint) two := by
  unfold Fraction.equiv line g d minusTwo midpoint two durationDifference negF Fraction.add Fraction.mul Fraction.ofInt
  decide

example : Fraction.equiv (line g d minusOne midpoint) two := by
  unfold Fraction.equiv line g d minusOne midpoint two durationDifference negF Fraction.add Fraction.mul Fraction.ofInt
  decide

example : Fraction.lt sevenFourths two := by unfold Fraction.lt sevenFourths two Fraction.ofInt; decide
example : Fraction.lt threeHalves sevenFourths := by unfold Fraction.lt threeHalves sevenFourths; decide

private theorem right_formula (x h : Fraction) (hh : Fraction.positive h) :
    Fraction.equiv (rightSlope g x h)
      (Fraction.add (d x) (negF h)) := by
  simp only [rightSlope, dite_eq_left hh, g, d, durationDifference, negF,
    Fraction.equiv, Fraction.quotient, Fraction.add, Fraction.mul, Fraction.ofInt]
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg]
  ac_nf
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  simp only [← Int.mul_assoc]
  omega

private theorem left_formula (x h : Fraction) (hh : Fraction.positive h) :
    Fraction.equiv (leftSlope g x h)
      (Fraction.add (d x) h) := by
  simp only [leftSlope, dite_eq_left hh, g, d, durationDifference, negF,
    Fraction.equiv, Fraction.quotient, Fraction.add, Fraction.mul, Fraction.ofInt]
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg]
  ac_nf
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  simp only [← Int.mul_assoc]
  omega

private theorem d_congr (x y : Fraction) (h : Fraction.equiv x y) :
    Fraction.equiv (d x) (d y) := by
  unfold Fraction.equiv d at *
  dsimp at *
  simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using
    congrArg (fun z : Int => -2 * z) h

private theorem g_congr (x y : Fraction) (h : Fraction.equiv x y) :
    Fraction.equiv (g x) (g y) := by
  unfold Fraction.equiv g at *
  dsimp at *
  have h2 := congrArg (fun z : Int => z * z) h
  simp only [Int.sub_mul, Int.mul_sub] at *
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at h2 ⊢
  simp only [← Int.mul_assoc] at h2 ⊢
  omega

private theorem neg_le {h k : Fraction} (hhk : Fraction.le h k) :
    Fraction.le (negF k) (negF h) := by
  unfold Fraction.le negF at *
  dsimp at *
  simp only [Int.neg_mul]
  omega

private theorem right_concave (x h k : Fraction)
    (hh : Fraction.positive h) (hk : Fraction.positive k)
    (hhk : Fraction.le h k) :
    Fraction.le (rightSlope g x k) (rightSlope g x h) := by
  exact Fraction.le_equiv_left (right_formula x k hk)
    (Fraction.le_equiv_right
      (Fraction.add_le_add_left (neg_le hhk) (d x))
      (Fraction.equiv_symm (right_formula x h hh)))

private theorem left_concave (x h k : Fraction)
    (hh : Fraction.positive h) (hk : Fraction.positive k)
    (hhk : Fraction.le h k) :
    Fraction.le (leftSlope g x h) (leftSlope g x k) := by
  exact Fraction.le_equiv_left (left_formula x h hh)
    (Fraction.le_equiv_right
      (Fraction.add_le_add_left hhk (d x))
      (Fraction.equiv_symm (left_formula x k hk)))

private theorem zero_lt {h : Fraction} (hh : Fraction.positive h) :
    Fraction.lt (Fraction.ofInt 0) h := (Fraction.positive_iff_zero_lt h).mp hh

private theorem neg_lt {h k : Fraction} (hhk : Fraction.lt h k) :
    Fraction.lt (negF k) (negF h) := by
  unfold Fraction.lt negF at *
  dsimp at *
  simp only [Int.neg_mul]
  omega

private theorem plus_contact (c : Fraction) :
    Ultimate Fraction.magnitudes (fun h => Fraction.add c h) c := by
  intro a b hac hcb
  let δ := durationDifference c b
  have hδ : Fraction.positive δ := difference_positive c b hcb
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd
  constructor
  · exact Fraction.magnitudes.lt_of_lt_le hac
      (Fraction.le_equiv_right
        (Fraction.le_equiv_left (Fraction.equiv_symm (Fraction.add_zero c))
          (Fraction.magnitudes.lt_implies_le (Fraction.add_lt_add_left (zero_lt hh) c)))
        (Fraction.equiv_refl _))
  · exact Fraction.magnitudes.lt_of_lt_le
      (Fraction.add_lt_add_left hhd c)
      (Fraction.le_of_equiv (add_difference_cancel c b))

private theorem minus_contact (c : Fraction) :
    Ultimate Fraction.magnitudes (fun h => Fraction.add c (negF h)) c := by
  intro a b hac hcb
  let δ := durationDifference a c
  have hδ : Fraction.positive δ := difference_positive a c hac
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd
  constructor
  · have hneg := Fraction.add_lt_add_left (neg_lt hhd) c
    have he : Fraction.equiv (Fraction.add c (negF δ)) a := by
      simp only [δ, durationDifference, negF, Fraction.equiv, Fraction.add,
        Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
      ac_nf
      omega
    exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv (Fraction.equiv_symm he)) hneg
  · have hneg := neg_lt (zero_lt hh)
    exact Fraction.magnitudes.lt_of_lt_le
      (Fraction.magnitudes.lt_of_lt_le (Fraction.add_lt_add_left hneg c)
        (Fraction.le_of_equiv (Fraction.add_zero c)))
      (Fraction.magnitudes.lt_implies_le hcb)

/-- A nonlinear graph whose secant concavity and contact are proved from
the rational formulas above; support and convergence are not fields. -/
private theorem quadratic_patch : Patch g d minusTwo minusOne := by
  refine ⟨g_congr, d_congr, ?_, ?_, ?_, ?_, ?_⟩
  · intro x h k _ _ hh hk hhk
    exact right_concave x h k hh hk hhk
  · intro x h k _ _ hh hk hhk
    exact left_concave x h k hh hk hhk
  · intro x _ _
    exact Fraction.ultimate_congr _ _ (d x) (fun h hh => right_formula x h hh)
      (minus_contact (d x))
  · intro x _ _
    exact Fraction.ultimate_congr _ _ (d x) (fun h hh => left_formula x h hh)
      (plus_contact (d x))
  · intro x _ hxb
    unfold d
    dsimp
    unfold Fraction.le minusOne Fraction.ofInt at hxb
    dsimp at hxb
    have hxden := x.den_pos
    omega

private def meetingPoint : Point := (midpoint, two)

private theorem ha : Fraction.le minusTwo minusTwo := by unfold Fraction.le minusTwo Fraction.ofInt; decide
private theorem hb : Fraction.le minusTwo minusOne := by unfold Fraction.le minusTwo minusOne Fraction.ofInt; decide
private theorem hc : Fraction.le minusOne minusOne := by unfold Fraction.le minusOne Fraction.ofInt; decide

private theorem actual_meeting :
    SupportingTangents.Meeting (graph g minusTwo) (graph g minusOne)
      (cell quadratic_patch minusTwo minusOne ha hb hc)
      meetingPoint := by
  refine ⟨⟨1, 2, by decide⟩, by unfold UnitInterval; decide, ?_, ?_⟩
  · unfold pointEquiv meetingPoint midpoint two graph cell
      lerp complement pointAdd pointScale
      g line d minusTwo minusOne durationDifference negF
      Fraction.equiv Fraction.add Fraction.mul Fraction.ofInt
    decide
  · unfold pointEquiv meetingPoint midpoint two graph cell
      lerp complement pointAdd pointScale
      g line d minusTwo minusOne durationDifference negF
      Fraction.equiv Fraction.add Fraction.mul Fraction.ofInt
    decide

private theorem on_both_contact_lines :
    OnTangent g d minusTwo meetingPoint ∧
    OnTangent g d minusOne meetingPoint :=
  meeting_on_tangents quadratic_patch minusTwo minusOne ha hb hc meetingPoint actual_meeting

private theorem curve_below_meeting :
    Fraction.lt (g midpoint) meetingPoint.2 := by
  unfold Fraction.lt g midpoint meetingPoint two
  decide

private theorem chord_below_curve :
    Fraction.lt
      (lerp ⟨1, 2, by decide⟩ (graph g minusTwo) (graph g minusOne)).2
      (g midpoint) := by
  unfold Fraction.lt lerp complement pointAdd pointScale graph g
    minusTwo minusOne midpoint Fraction.add Fraction.mul Fraction.ofInt
  decide

private theorem chord_exact :
    Fraction.equiv
      (lerp ⟨1, 2, by decide⟩ (graph g minusTwo) (graph g minusOne)).2
      threeHalves := by
  unfold Fraction.equiv lerp complement pointAdd pointScale graph g
    minusTwo minusOne threeHalves Fraction.add Fraction.mul Fraction.ofInt
  decide

private theorem tangent_figure_contains_curved_point :
    0 ≤ (g midpoint).num ∧
    Fraction.le (g midpoint) (line g d minusTwo midpoint) ∧
    Fraction.le (g midpoint) (line g d minusOne midpoint) := by
  constructor
  · unfold g midpoint; decide
  constructor
  · unfold Fraction.le g line d minusTwo midpoint durationDifference negF
      Fraction.add Fraction.mul Fraction.ofInt
    decide
  · unfold Fraction.le g line d minusOne midpoint durationDifference negF
      Fraction.add Fraction.mul Fraction.ofInt
    decide

private theorem opposite_endpoint_only :
    Fraction.equiv
      (Fraction.add (g minusTwo)
        (Fraction.mul (Fraction.ofInt 3) (durationDifference minusTwo minusOne)))
      (g minusOne) := by
  unfold Fraction.equiv g minusTwo minusOne durationDifference negF
    Fraction.add Fraction.mul Fraction.ofInt
  decide

private theorem slope_three_not_contact :
    ¬ Ultimate Fraction.magnitudes (rightSlope g minusTwo) (Fraction.ofInt 3) := by
  intro hbad
  have hgood : Ultimate Fraction.magnitudes (rightSlope g minusTwo) (d minusTwo) :=
    quadratic_patch.right_contact minusTwo ha (by
      unfold Fraction.lt minusTwo minusOne Fraction.ofInt; decide)
  have hnear := hgood ⟨7, 2, by decide⟩ (Fraction.ofInt 5)
    (by change Fraction.lt (⟨7, 2, by decide⟩ : Fraction) (d minusTwo)
        unfold Fraction.lt d minusTwo; decide)
    (by change Fraction.lt (d minusTwo) (Fraction.ofInt 5)
        unfold Fraction.lt d minusTwo Fraction.ofInt; decide)
  have hv : Near Fraction.magnitudes
      (fun h => Fraction.le (⟨7, 2, by decide⟩ : Fraction) (rightSlope g minusTwo h)) := by
    obtain ⟨δ, hδ, hbound⟩ := hnear
    exact ⟨δ, hδ, fun h hh hhd => Fraction.magnitudes.lt_implies_le (hbound h hh hhd).1⟩
  have hfalse := ultimate_lower hbad hv
  exact (by unfold Fraction.le Fraction.ofInt; decide :
    ¬ Fraction.le (⟨7, 2, by decide⟩ : Fraction) (Fraction.ofInt 3)) hfalse

private theorem no_slope_three_patch :
    ¬ Patch g (fun _ => Fraction.ofInt 3) minusTwo minusOne := by
  intro C
  exact slope_three_not_contact (C.right_contact minusTwo ha (by
    unfold Fraction.lt minusTwo minusOne Fraction.ofInt; decide))

/-- Both witness-specific corollaries accept the proved nonlinear patch for
every sequence of finite partitions with shrinking maximum width. -/
private theorem both_editions_boundary
    (parts : Nat → MonotoneRectangles.Partition minusTwo minusOne)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => Trace quadratic_patch (parts m))
      (RationalBoundary.CurveTrace (graph g) minusTwo minusOne) ∧
    RationalBoundary.Approaches (fun m => Trace quadratic_patch (parts m))
      (RationalBoundary.CurveTrace (graph g) minusTwo minusOne) :=
  ⟨Principia1687.LemmaIII.corollary3_tangent_boundary quadratic_patch parts hmesh,
    Principia1713.LemmaIII.corollary3_tangent_boundary quadratic_patch parts hmesh⟩

private theorem both_editions_perimeters
    (parts : Nat → MonotoneRectangles.Partition minusTwo minusOne)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches
      (fun m => RationalBoundary.ChordTrace (graph g) (parts m))
      (RationalBoundary.CurveTrace (graph g) minusTwo minusOne) ∧
    RationalBoundary.Approaches (fun m => Trace quadratic_patch (parts m))
      (RationalBoundary.CurveTrace (graph g) minusTwo minusOne) :=
  Principia1687.LemmaIII.corollary4_tangent_perimeters quadratic_patch parts hmesh

private theorem edition_1713_perimeters
    (parts : Nat → MonotoneRectangles.Partition minusTwo minusOne)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches
      (fun m => RationalBoundary.ChordTrace (graph g) (parts m))
      (RationalBoundary.CurveTrace (graph g) minusTwo minusOne) ∧
    RationalBoundary.Approaches (fun m => Trace quadratic_patch (parts m))
      (RationalBoundary.CurveTrace (graph g) minusTwo minusOne) :=
  Principia1713.LemmaIII.corollary4_tangent_perimeters quadratic_patch parts hmesh

private theorem both_editions_area_conditional
    (area : RectangleContent.AreaRules)
    (parts : Nat → MonotoneRectangles.Partition minusTwo minusOne)
    (A : Fraction) (P : Nat → Fraction)
    (hA : area.HasArea (MonotoneRectangles.figure g minusTwo minusOne) A)
    (hP : ∀ m, area.HasArea (figure g d (parts m)) (P m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, Fraction.le A (P m)) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (durationDifference A (P m)).abs) :=
  Principia1687.LemmaIII.corollary3_tangent_area_approximation
    area quadratic_patch parts A P (by unfold g minusTwo; decide) hA hP hmesh

private theorem edition_1713_area_conditional
    (area : RectangleContent.AreaRules)
    (parts : Nat → MonotoneRectangles.Partition minusTwo minusOne)
    (A : Fraction) (P : Nat → Fraction)
    (hA : area.HasArea (MonotoneRectangles.figure g minusTwo minusOne) A)
    (hP : ∀ m, area.HasArea (figure g d (parts m)) (P m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, Fraction.le A (P m)) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (durationDifference A (P m)).abs) :=
  Principia1713.LemmaIII.corollary3_tangent_area_approximation
    area quadratic_patch parts A P (by unfold g minusTwo; decide) hA hP hmesh

private theorem repeated_node_meeting :
    SupportingTangents.Meeting (graph g minusTwo) (graph g minusTwo)
      (cell quadratic_patch minusTwo minusTwo ha ha hb) (graph g minusTwo) := by
  refine ⟨Fraction.ofInt 0, by unfold UnitInterval Fraction.ofInt; decide, ?_, ?_⟩
  · unfold pointEquiv graph cell lerp complement pointAdd pointScale
      g line d minusTwo durationDifference negF
      Fraction.equiv Fraction.add Fraction.mul Fraction.ofInt
    decide
  · unfold pointEquiv graph cell lerp complement pointAdd pointScale
      g line d minusTwo durationDifference negF
      Fraction.equiv Fraction.add Fraction.mul Fraction.ofInt
    decide

private def oneCell : MonotoneRectangles.Partition minusTwo minusOne where
  count := 1
  positive_count := by omega
  nodes := fun i => if i = 0 then minusTwo else minusOne
  first := by simp [Fraction.equiv, minusTwo, Fraction.ofInt]
  last := by simp [Fraction.equiv, minusOne, Fraction.ofInt]
  ordered := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa using hb

private theorem one_cell_curved_point_enclosed :
    figure g d oneCell (graph g midpoint) := by
  refine ⟨0, by decide, ?_, ?_, tangent_figure_contains_curved_point.1,
    tangent_figure_contains_curved_point.2.1,
    tangent_figure_contains_curved_point.2.2⟩
  · unfold graph Fraction.le midpoint oneCell minusTwo Fraction.ofInt
    decide
  · unfold graph Fraction.le midpoint oneCell minusOne Fraction.ofInt
    decide

private theorem one_cell_meeting_enclosed :
    figure g d oneCell meetingPoint := by
  refine ⟨0, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · unfold meetingPoint Fraction.le midpoint oneCell minusTwo Fraction.ofInt; decide
  · unfold meetingPoint Fraction.le midpoint oneCell minusOne Fraction.ofInt; decide
  · unfold meetingPoint two Fraction.ofInt; decide
  · exact Fraction.le_of_equiv on_both_contact_lines.1
  · exact Fraction.le_of_equiv on_both_contact_lines.2

end TangentContactVerification
