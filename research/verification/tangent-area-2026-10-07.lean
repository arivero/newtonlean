import NewtonLimitDynamics

/-!
Target: derive an assigned rational area of the actual finite contact-tangent
polygon from elementary triangle, dissection and translation rules. Do not
assume the polygon's area or the desired trapezoid normalization.

May assume an explicit geometric area convention extending SectorFan.AreaRules
by invariance under translation, and the existing contact Patch. Triangle
normalization and cut additivity are geometric premises, not area-existence
theorems for arbitrary figures. No curved-area existence or arclength claim.

Acceptance: prove the actual cell-region dissection at its constructed tangent
meeting and finite partition additivity; both printed Corollary III area-error
theorems must apply without supplying a polygon-area assignment. Keep any
curved-area assignment and shrinking mesh explicit. Coincident lines, zero
slopes, zero-width cells and equivalent representatives must remain allowed.

Exact control: g(x)=4-x² on [-2,-1], contact slopes -2x. The tangents meet at
(-3/2,2). Their two trapezoids have areas 1/2 and 5/4; total 7/4, distinct
from the chord region's 3/2. A flat height-1 polygon on the same interval has
area 1; an inserted repeated node contributes zero. These finite values do
not assign or establish the curved region's area.
-/

namespace NewtonLimitDynamics.Polygon.TangentPolygonArea.Verification
open NewtonLimitDynamics TimeSubdivision HarmonicTimeComparison HarmonicStability
open TangentContact TangentPolygonArea TriangleContent SupportingTangents ConvexCover

private def a : Fraction := ⟨-2, 1, by decide⟩
private def b : Fraction := ⟨-1, 1, by decide⟩
private def mid : Fraction := ⟨-3, 2, by decide⟩
private def two : Fraction := Fraction.ofInt 2
private def half : Fraction := ⟨1, 2, by decide⟩
private def fiveFourths : Fraction := ⟨5, 4, by decide⟩
private def sevenFourths : Fraction := ⟨7, 4, by decide⟩
private def threeHalves : Fraction := ⟨3, 2, by decide⟩

private def g (x : Fraction) : Fraction :=
  Fraction.add (Fraction.ofInt 4) (negF (Fraction.mul x x))
private def d (x : Fraction) : Fraction := Fraction.mul (Fraction.ofInt (-2)) x
private def r : Point := (mid,two)

private theorem ha : Fraction.le a a := by unfold Fraction.le a; decide
private theorem hab : Fraction.le a b := by unfold Fraction.le a b; decide
private theorem hb : Fraction.le b b := by unfold Fraction.le b; decide
private theorem hbase : 0 ≤ (g a).num := by decide

private theorem actual_meeting (C : Patch g d a b) :
    Meeting (graph g a) (graph g b) (cell C a b ha hab hb) r := by
  refine ⟨⟨1, 2, by decide⟩, by unfold UnitInterval; decide, ?_, ?_⟩
  · change pointEquiv r
      (lerp ⟨1, 2, by decide⟩ (graph g a) (b,line g d a b))
    unfold pointEquiv r mid two graph lerp complement pointAdd pointScale
      g line d a b durationDifference negF Fraction.equiv Fraction.add
      Fraction.mul Fraction.ofInt
    decide
  · change pointEquiv r
      (lerp ⟨1, 2, by decide⟩ (a,line g d b a) (graph g b))
    unfold pointEquiv r mid two graph lerp complement pointAdd pointScale
      g line d a b durationDifference negF Fraction.equiv Fraction.add
      Fraction.mul Fraction.ofInt
    decide

private theorem exact_trapezoids :
    Fraction.equiv (trapezoid (graph g a) r) half ∧
    Fraction.equiv (trapezoid r (graph g b)) fiveFourths ∧
    Fraction.equiv (Fraction.add half fiveFourths) sevenFourths ∧
    Fraction.equiv (trapezoid (graph g a) (graph g b)) threeHalves ∧
    ¬ Fraction.equiv sevenFourths threeHalves := by
  unfold trapezoid graph r mid two g a b half fiveFourths sevenFourths threeHalves
    durationDifference negF Fraction.equiv Fraction.add Fraction.mul Fraction.half
    Fraction.ofInt
  decide

private theorem nonlinear_cell_area (area : TriangleContent.AreaRules)
    (C : Patch g d a b) :
    area.HasArea (CellRegion g d a b)
      (Fraction.add (trapezoid (graph g a) r) (trapezoid r (graph g b))) :=
  cell_area area C a b ha hab hb hbase r (actual_meeting C)

private theorem nonlinear_area_seven_fourths (area : TriangleContent.AreaRules)
    (C : Patch g d a b) :
    area.HasArea (CellRegion g d a b) sevenFourths := by
  have hv : Fraction.equiv
      (Fraction.add (trapezoid (graph g a) r) (trapezoid r (graph g b)))
      sevenFourths := by
    unfold trapezoid graph r mid two g a b sevenFourths durationDifference
      negF Fraction.equiv Fraction.add Fraction.mul Fraction.half Fraction.ofInt
    decide
  exact area.congr_value _ _ _ hv (nonlinear_cell_area area C)

private theorem ramp_zero_slope (area : TriangleContent.AreaRules) :
    area.HasArea (Ramp (Fraction.ofInt 0) (Fraction.ofInt 1))
      (Fraction.mul (Fraction.ofInt 1)
        (Fraction.mul (Fraction.ofInt 0) (Fraction.ofInt 1))).half :=
  ramp_area area _ _ (by decide) (by decide)

private theorem ramp_zero_width (area : TriangleContent.AreaRules) :
    area.HasArea (Ramp (Fraction.ofInt 4) (Fraction.ofInt 0))
      (Fraction.mul (Fraction.ofInt 0)
        (Fraction.mul (Fraction.ofInt 4) (Fraction.ofInt 0))).half :=
  ramp_area area _ _ (by decide) (by decide)

private theorem repeated_cell_area (area : TriangleContent.AreaRules)
    (C : Patch g d a b) :
    area.HasArea (CellRegion g d a a)
      (Fraction.add (trapezoid (graph g a) (graph g a))
        (trapezoid (graph g a) (graph g a))) := by
  have hm : Meeting (graph g a) (graph g a) (cell C a a ha ha hab) (graph g a) := by
    refine ⟨Fraction.ofInt 0, by unfold UnitInterval Fraction.ofInt; decide, ?_, ?_⟩
    · change pointEquiv (graph g a)
        (lerp (Fraction.ofInt 0) (graph g a) (a,line g d a a))
      unfold pointEquiv graph lerp complement pointAdd pointScale
        g line d a durationDifference negF Fraction.equiv Fraction.add
        Fraction.mul Fraction.ofInt
      decide
    · change pointEquiv (graph g a)
        (lerp (Fraction.ofInt 0) (a,line g d a a) (graph g a))
      unfold pointEquiv graph lerp complement pointAdd pointScale
        g line d a durationDifference negF Fraction.equiv Fraction.add
        Fraction.mul Fraction.ofInt
      decide
  exact cell_area area C a a ha ha hab hbase (graph g a) hm

private theorem repeated_value_zero :
    Fraction.equiv
      (Fraction.add (trapezoid (graph g a) (graph g a))
        (trapezoid (graph g a) (graph g a))) (Fraction.ofInt 0) := by
  unfold trapezoid graph g a durationDifference negF Fraction.equiv
    Fraction.add Fraction.mul Fraction.half Fraction.ofInt
  decide

private theorem repeated_area_zero (area : TriangleContent.AreaRules)
    (C : Patch g d a b) :
    area.HasArea (CellRegion g d a a) (Fraction.ofInt 0) :=
  area.congr_value _ _ _ repeated_value_zero (repeated_cell_area area C)

private def flat (_ : Fraction) : Fraction := Fraction.ofInt 1
private def flatSlope (_ : Fraction) : Fraction := Fraction.ofInt 0
private def flatMeet : Point := (mid,Fraction.ofInt 1)

private theorem flat_meeting (C : Patch flat flatSlope a b) :
    Meeting (graph flat a) (graph flat b) (cell C a b ha hab hb) flatMeet := by
  refine ⟨⟨1, 2, by decide⟩, by unfold UnitInterval; decide, ?_, ?_⟩
  · change pointEquiv flatMeet
      (lerp ⟨1, 2, by decide⟩ (graph flat a) (b,line flat flatSlope a b))
    unfold pointEquiv flatMeet mid graph flat flatSlope lerp complement
      pointAdd pointScale line a b durationDifference negF Fraction.equiv
      Fraction.add Fraction.mul Fraction.ofInt
    decide
  · change pointEquiv flatMeet
      (lerp ⟨1, 2, by decide⟩ (a,line flat flatSlope b a) (graph flat b))
    unfold pointEquiv flatMeet mid graph flat flatSlope lerp complement
      pointAdd pointScale line a b durationDifference negF Fraction.equiv
      Fraction.add Fraction.mul Fraction.ofInt
    decide

private theorem flat_area_one (area : TriangleContent.AreaRules)
    (C : Patch flat flatSlope a b) :
    area.HasArea (CellRegion flat flatSlope a b) (Fraction.ofInt 1) := by
  have hc := cell_area area C a b ha hab hb (by decide) flatMeet (flat_meeting C)
  have hv : Fraction.equiv
      (Fraction.add (trapezoid (graph flat a) flatMeet)
        (trapezoid flatMeet (graph flat b)))
      (Fraction.ofInt 1) := by
    unfold trapezoid graph flat flatMeet a b mid durationDifference negF
      Fraction.equiv Fraction.add Fraction.mul Fraction.half Fraction.ofInt
    decide
  exact area.congr_value _ _ _ hv hc

private def oneCell : MonotoneRectangles.Partition a b where
  count := 1
  positive_count := by decide
  nodes := fun i => if i = 0 then a else b
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa using hab

private theorem chosen_meeting (C : Patch g d a b) :
    pointEquiv r (meeting C oneCell 0) := by
  have hm := meeting_spec C oneCell 0
  simp only [partitionCells, dite_eq_left (show 0 < oneCell.count by decide)] at hm
  have hd :
      (TimeSubdivision.det (pointSub (cell C a b ha hab hb).leftEnd (graph g a))
        (pointSub (graph g b) (cell C a b ha hab hb).rightStart)).num ≠ 0 := by
    change (TimeSubdivision.det (pointSub (b,line g d a b) (graph g a))
      (pointSub (graph g b) (a,line g d b a))).num ≠ 0
    unfold TimeSubdivision.det pointSub pointAdd pointNeg graph line g d a b
      durationDifference negF Fraction.add Fraction.mul Fraction.ofInt
    decide
  have hlines := meeting_on_lines (graph g a) (graph g b)
    (cell C a b ha hab hb) r (actual_meeting C)
  exact meeting_unique (graph g a) (graph g b) (cell C a b ha hab hb)
    (meeting C oneCell 0) r (by simpa only [oneCell] using! hm) hd hlines.1 hlines.2

private theorem chosen_value (C : Patch g d a b) :
    Fraction.equiv (value C oneCell) sevenFourths := by
  have he := chosen_meeting C
  have hleft := trapezoid_congr (p:=graph g a) (p':=graph g a)
    (q:=meeting C oneCell 0) (q':=r)
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (pointEquiv_symm he)
  have hright := trapezoid_congr (p:=meeting C oneCell 0) (p':=r)
    (q:=graph g b) (q':=graph g b)
    (pointEquiv_symm he) ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hsum := Fraction.add_equiv hleft hright
  have hnumeric : Fraction.equiv
      (Fraction.add (Fraction.ofInt 0)
        (Fraction.add (trapezoid (graph g a) r) (trapezoid r (graph g b))))
      sevenFourths := by
    unfold trapezoid graph r mid two g a b sevenFourths durationDifference
      negF Fraction.equiv Fraction.add Fraction.mul Fraction.half Fraction.ofInt
    decide
  have hraw : Fraction.equiv (value C oneCell)
      (Fraction.add (Fraction.ofInt 0)
        (Fraction.add (trapezoid (graph g a) r) (trapezoid r (graph g b)))) := by
    simpa only [value, oneCell, PolygonFanArea.sum, cellValue, dite_eq_left (show 0 = 0 by rfl)]
      using! Fraction.add_equiv_left (Fraction.ofInt 0) hsum
  exact Fraction.equiv_trans hraw hnumeric

private theorem chosen_polygon_area (area : TriangleContent.AreaRules)
    (C : Patch g d a b) :
    area.HasArea (TangentContact.figure g d oneCell) sevenFourths :=
  area.congr_value _ _ _ (chosen_value C) (polygon_area area C oneCell hbase)

/-- Both printed witnesses consume the derived finite polygon value. The
curved area and shrinking mesh remain explicit premises. -/
private theorem printed_interfaces (area : TriangleContent.AreaRules)
    {f s : Fraction → Fraction} {l u : Fraction}
    (C : Patch f s l u)
    (parts : Nat → MonotoneRectangles.Partition l u) (A : Fraction)
    (h0 : 0 ≤ (f l).num)
    (hA : area.HasArea (MonotoneRectangles.figure f l u) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    ((∀ m, Fraction.le A (value C (parts m))) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes
        (fun m => (durationDifference A (value C (parts m))).abs)) ∧
    ((∀ m, Fraction.le A (value C (parts m))) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes
        (fun m => (durationDifference A (value C (parts m))).abs)) :=
  ⟨Principia1687.LemmaIII.corollary3_constructed_tangent_area
      area C parts A h0 hA hmesh,
    Principia1713.LemmaIII.corollary3_constructed_tangent_area
      area C parts A h0 hA hmesh⟩

end NewtonLimitDynamics.Polygon.TangentPolygonArea.Verification
