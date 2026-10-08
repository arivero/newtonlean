import BarrowLib.Polygon.AreaDomain
import BarrowLib.Polygon.BoxCoverArea

/-! Exact controls for the partial-area domain obstruction.
The supplied area convention is not constructed here. Its restricted form
retains every elementary rule, triangle and cover assignment, but omits the
displayed nested-triangle difference. The existing subtraction convention
assigns that same difference area 1/2. A bounded predicate sensitive to raw
fraction displays falsifies minimum-preserving translation without the
representative-invariance condition. These controls share the Lean kernel
and rational definitions; they are not an initial area-consistency model.
-/
namespace NewtonLimitDynamics.Polygon.AreaDomainControls
open NewtonLimitDynamics TimeSubdivision HarmonicTimeComparison HarmonicStability
open TriangleContent AreaDomain ConvexCover RadialSector

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))
local instance (a b : Fraction) : Decidable (Fraction.lt a b) :=
  inferInstanceAs (Decidable (a.num*b.den < b.num*a.den))

private def z := Fraction.ofInt 0
private def one := Fraction.ofInt 1
private def two := Fraction.ofInt 2
private def half : Fraction := ⟨1,2,by decide⟩
private def quarter : Fraction := ⟨1,4,by decide⟩

example : difference (ray half two) := difference_ray half ⟨by decide,by decide⟩ (by decide)
example : difference (ray quarter two) := difference_ray quarter ⟨by decide,by decide⟩ (by decide)
example : Fraction.lt (ray quarter two).1 (ray half two).1 := by decide
example : ¬ difference (z,z) := by
  intro h
  have hp := difference_positive _ h
  change 0 < (0 : Int) at hp
  omega

example (area : TriangleContent.AreaRules) :
    (restrict area).HasArea lowerTriangle one.half ∧
      (restrict area).HasArea upperTriangle one ∧
      ¬ ∃ A, (restrict area).HasArea difference A := by
  refine ⟨(restrict area).congr_value _ _ _ (by decide)
    ((restrict area).triangle (ray one z) (ray one one) (by decide)),
    (restrict area).congr_value _ _ _ (by decide)
      ((restrict area).triangle (ray one z) (ray one two) (by decide)),difference_unassigned area⟩

example (area : DifferenceAreaRules) : area.HasArea difference half :=
  area.congr_value _ _ _ (by decide) (difference_area_of_subtraction area)

example (area : DifferenceAreaRules) : ¬ area.HasArea difference one := by
  intro h
  have hle := area.monotone difference difference one half (fun _ h => h) h
    (area.congr_value _ _ _ (by decide) (difference_area_of_subtraction area))
  change (1 : Int) * 2 ≤ 1 * 1 at hle
  omega

private def nonlinear (t : Fraction) : Fraction := Fraction.add one t
example (area : TriangleContent.AreaRules) (A : Fraction)
    (hA : area.HasArea (sector nonlinear z one) A) :
    (restrict area).HasArea (sector nonlinear z one) A := by
  apply retain_sector area nonlinear z one A (by decide) _ hA
  intro t ht _
  have hn : 0 ≤ t.num := by
    simpa only [Fraction.le,z,Fraction.ofInt,Int.zero_mul,Int.mul_one] using ht
  exact Fraction.nonnegative_add one t (by decide) hn

example (area : TriangleContent.AreaRules) :
    ∃ A, (restrict area).HasArea (SquareCover (fun _ => (z,z)) one 2) A ∧
      0 ≤ A.num ∧ Fraction.le A (PolygonFanArea.sum
        (fun _ => Fraction.mul (Fraction.ofInt 4) (Fraction.mul one one)) 2) :=
  BoxCoverArea.square_cover_area (restrict area) (fun _ => (z,z)) one (by decide) 2

/- A bounded version of the adversary's failed invariant: the left endpoint
has only the exact 0/1 display, whereas positive points have all displays.
This is a line segment, so no unbounded-area objection masks the defect. -/
private def shift : Point := (half,z)
def rawSegment (x : Point) : Prop :=
  ((x.1.num = 0 ∧ x.1.den = 1) ∨
    (0 < x.1.num ∧ Fraction.le x.1 one)) ∧ x.2.num = 0

theorem raw_minimum : Minimum rawSegment := by
  refine Or.inr ⟨(z,z),⟨Or.inl ⟨rfl,rfl⟩,rfl⟩,?_⟩
  intro x hx
  rcases hx.1 with hzero | hpos
  · simp only [Fraction.le,z,Fraction.ofInt,Int.zero_mul,Int.mul_one]
    omega
  · simp only [Fraction.le,z,Fraction.ofInt,Int.zero_mul,Int.mul_one]
    omega

theorem raw_not_respects : ¬ RespectsPoints rawSegment := by
  intro h
  let z2 : Fraction := ⟨0,2,by decide⟩
  have he : pointEquiv (z,z) (z2,z) := by decide
  have h2 := h _ _ he ⟨Or.inl ⟨rfl,rfl⟩,rfl⟩
  rcases h2.1 with hrep | hpos
  · have hd := hrep.2
    change (2 : Int) = 1 at hd
    omega
  · have hp := hpos.1
    change 0 < (0 : Int) at hp
    omega

private theorem translated_raw (x : Point) :
    translate shift rawSegment x ↔
      0 < (pointSub x shift).1.num ∧
      Fraction.le (pointSub x shift).1 one ∧ x.2.num = 0 := by
  change rawSegment (pointSub x shift) ↔ _
  have hy : (pointSub x shift).2.num = x.2.num := by
    simp [pointSub,pointAdd,pointNeg,Fraction.add,shift,z,Fraction.ofInt]
  constructor
  · intro hx
    rcases hx.1 with ⟨_,hden⟩ | hpos
    · have hd : (pointSub x shift).1.den = x.1.den*2 := rfl
      have hp := x.1.den_pos
      omega
    · exact ⟨hpos.1,hpos.2,hy ▸ hx.2⟩
  · intro hx
    exact ⟨Or.inr ⟨hx.1,hx.2.1⟩,hy.symm ▸ hx.2.2⟩

theorem translated_raw_no_minimum : ¬ Minimum (translate shift rawSegment) := by
  rintro (he | ⟨m,hm,hmin⟩)
  · apply he (Fraction.ofInt 1,z)
    apply (translated_raw _).mpr
    exact ⟨by decide,by decide,rfl⟩
  · have hm' := (translated_raw m).mp hm
    let d := durationDifference half m.1
    have hd : 0 < d.num := hm'.1
    have hd1 : Fraction.le d one := hm'.2.1
    let y : Point := (Fraction.add half d.half,m.2)
    have hde : Fraction.equiv (pointSub y shift).1 d.half := by
      simp only [y,shift,pointSub,pointAdd,pointNeg,durationDifference,negF,
        Fraction.equiv,Fraction.add,Fraction.half,half,Fraction.ofInt,
        Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
      ac_nf
      omega
    have hdh : 0 < d.half.num := by unfold Fraction.half; exact hd
    have hdy : 0 < (pointSub y shift).1.num :=
      (Fraction.positive_iff_zero_lt _).mpr (Fraction.magnitudes.lt_of_lt_le
        ((Fraction.positive_iff_zero_lt _).mp hdh)
        (Fraction.le_of_equiv (Fraction.equiv_symm hde)))
    have hdy1 : Fraction.le (pointSub y shift).1 one :=
      Fraction.le_equiv_left hde (Fraction.magnitudes.le_trans
        (Fraction.magnitudes.lt_implies_le (Fraction.half_lt d hd)) hd1)
    have hy : translate shift rawSegment y :=
      (translated_raw y).mpr ⟨hdy,hdy1,hm'.2.2⟩
    have hyx : Fraction.lt y.1 m.1 :=
      Fraction.magnitudes.lt_of_lt_le (Fraction.add_lt_add_left (Fraction.half_lt d hd) half)
        (Fraction.le_of_equiv (add_difference_cancel half m.1))
    exact Fraction.magnitudes.lt_irrefl m.1
      (Fraction.magnitudes.lt_of_le_lt (hmin y hy) hyx)

#print axioms relative_countermodel
#print axioms difference_area_of_subtraction

end NewtonLimitDynamics.Polygon.AreaDomainControls

/- Independent instantiations of the restricted partial area convention.
   The file introduces no additional geometric axioms. -/
namespace AreaDomainReviewControls

open NewtonLimitDynamics
open NewtonLimitDynamics.Polygon
open NewtonLimitDynamics.Polygon.TimeSubdivision
open NewtonLimitDynamics.Polygon.AreaDomain

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))

private def z : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1
private def minusOne : Fraction := Fraction.ofInt (-1)

-- A negative orientation is handled by swapping vertices, then retaining
-- the same filled triangle in the restricted convention.
example (area : TriangleContent.AreaRules) :
    (restrict area).HasArea
      (SectorFan.Triangle (minusOne,z) (z,one))
      (TimeSubdivision.det (minusOne,z) (z,one)).abs.half := by
  exact SectorFan.unsigned_triangle_area (restrict area).toSectorRules
    (minusOne,z) (z,one)

-- A collapsed triangle is still assigned zero through the triangle rule.
example (area : TriangleContent.AreaRules) :
    (restrict area).HasArea (SectorFan.Triangle (z,z) (z,z)) z := by
  exact (restrict area).congr_value _ _ _ (by decide)
    ((restrict area).triangle (z,z) (z,z) (by decide))

-- The translating vector deliberately uses noncanonical rational displays.
private def c : Point := (⟨2,2,by decide⟩,⟨-3,3,by decide⟩)

example (area : TriangleContent.AreaRules) :
    (restrict area).HasArea
      (TriangleContent.translate c (MonotoneRectangles.rectangle z one one))
      (Fraction.mul (HarmonicTimeComparison.durationDifference z one) one) := by
  exact (restrict area).translation _ _ c
    ((restrict area).rectangle z one one (by decide) (by decide))

example :
    Minimum (TriangleContent.translate c (MonotoneRectangles.rectangle z one one)) := by
  exact (admissible_translation (admissible_rectangle z one one
    (by decide) (by decide)) c).2

-- Exercise both empty branches and the two-nonempty branch of finite union.
example : Minimum (fun x : Point => False ∨
    MonotoneRectangles.rectangle z one one x) := by
  exact minimum_union admissible_empty.2
    (admissible_rectangle z one one (by decide) (by decide)).2

example : Minimum (fun x : Point =>
    MonotoneRectangles.rectangle z one one x ∨ False) := by
  exact minimum_union
    (admissible_rectangle z one one (by decide) (by decide)).2
    admissible_empty.2

example : Minimum (fun x : Point =>
    SectorFan.Triangle (minusOne,z) (z,one) x ∨
    MonotoneRectangles.rectangle z one one x) := by
  exact minimum_union (admissible_triangle (minusOne,z) (z,one)).2
    (admissible_rectangle z one one (by decide) (by decide)).2

-- Empty-set normalization plus monotonicity rejects an incorrect value.
example (area : TriangleContent.AreaRules) :
    ¬ (restrict area).HasArea (fun _ : Point => False) one := by
  intro hwrong
  have hzero := (restrict area).empty
  have hle := (restrict area).monotone (fun _ : Point => False)
    (fun _ : Point => False) one z (fun _ h => h.elim) hwrong hzero
  change (1 : Int) ≤ 0 at hle
  omega

-- The concrete nested difference cannot be assigned even its expected
-- subtraction value by this restricted convention.
example (area : TriangleContent.AreaRules) :
    ¬ (restrict area).HasArea difference one.half := by
  intro h
  exact difference_no_minimum h.2.2

end AreaDomainReviewControls
