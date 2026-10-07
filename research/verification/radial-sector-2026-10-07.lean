import BarrowLib

/-! Actual radial-sector controls. The nonlinear graph and its chord are
geometrically different, yet their enclosures and finite areas are derived.
AreaRules remains an explicit partial geometric convention. -/
namespace NewtonLimitDynamics.Polygon.RadialSectorControls
open NewtonLimitDynamics TimeSubdivision MonotoneRectangles RadialSector

private def f (n : Int) (d : Nat) : Fraction := ⟨n,d+1,by omega⟩
private def z := Fraction.ofInt 0
private def o := Fraction.ofInt 1
private def g (t : Fraction) := Fraction.add o t
private def cell : Partition z o where
  count := 1
  positive_count := by decide
  nodes := fun i => if i=0 then z else o
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    have he : i=0 := by omega
    subst i
    change (0 : Int) ≤ 1
    decide
private theorem hg : MonotoneOn g z o := by
  intro s t _ hst _
  exact Fraction.add_le_add_left hst o
private theorem hbase : 0 < (g z).num := by decide

-- A genuine point of the nonlinear curve, with no area or limit premise.
example : sector g z o (f 3 1,f 3 3) := by
  refine ⟨f 1 1,?_,?_,o,⟨by decide,by decide⟩,?_⟩
  · change (0 : Int) ≤ 1; decide
  · change (1 : Int) ≤ 2; decide
  · constructor <;> decide

-- It lies outside the one-cell chord triangle, so point-set equality is
-- not hidden in the approximation theorem.
example : ¬ chordFigure g cell (f 3 1,f 3 3) := by
  rintro ⟨i,hi,u,v,hu,hv,hsum,hx,hy⟩
  change i < 1 at hi
  have he : i=0 := by omega
  subst i
  simp [cell,g,z,o,f,ray,pointAdd,pointScale,Fraction.add,Fraction.mul,
    Fraction.ofInt,Fraction.equiv,Int.mul_add,Int.add_mul,Int.mul_assoc] at hx hy
  simp only [Fraction.le,Fraction.add,Fraction.ofInt,Int.mul_one,Int.one_mul] at hsum
  have hden : 0 < u.den * v.den := Int.mul_pos u.den_pos v.den_pos
  ac_nf at hx hy hsum hden
  simp only [← Int.mul_assoc] at hx hy
  omega

example : Fraction.equiv (lowerSum (density g) cell) (f 1 1) := by decide
example : Fraction.equiv (chordArea g cell) o := by decide
example : Fraction.equiv (upperSum (density g) cell) (Fraction.ofInt 2) := by decide

example (area : SectorFan.AreaRules) : area.HasArea (chordFigure g cell) o :=
  area.congr_value _ _ _ (by decide) (chord_area area g cell hg hbase)
example (area : DifferenceAreaRules) : area.HasArea (collar g cell) (f 3 1) :=
  area.congr_value _ _ _ (by decide) (collar_area area g cell hg hbase)
example : ∀ x, between g cell x → collar g cell x :=
  between_subset_collar g cell hg hbase

-- A collapsed slope cell is allowed; the filled cap has zero area.
example : Fraction.equiv (TimeSubdivision.det (ray o z) (ray o z)).half z := by decide
example : ∃ u, ConvexCover.UnitInterval u ∧ Fraction.equiv (SupportingTangents.affine u z z) z :=
  interval_parameter z z z (Fraction.magnitudes.le_refl _) (Fraction.magnitudes.le_refl _)

-- A decreasing ray scale is not covered by the increasing ray-scale premise.
example : ¬ MonotoneOn (fun t => HarmonicTimeComparison.durationDifference t (Fraction.ofInt 2)) z o := by
  intro h
  have hn := h z o (Fraction.magnitudes.le_refl _) (by change (0 : Int) ≤ 1; decide)
    (Fraction.magnitudes.le_refl _)
  change (2 : Int) ≤ 1 at hn
  omega

#print axioms RadialSector.sector_enclosure
#print axioms RadialSector.chord_enclosure
#print axioms RadialSector.chord_errors_vanish
#print axioms RadialSector.between_areas_vanish
end NewtonLimitDynamics.Polygon.RadialSectorControls
