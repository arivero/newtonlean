import BarrowLib
import ClassicsLib

/-! Finite geometric controls: actual triangle membership and separation,
shared radial boundaries, a central polygon, and repeated coverage. -/
namespace NewtonLimitDynamics.Polygon.SectorUnionControls
open NewtonLimitDynamics TimeSubdivision SectorFan CentralSchedule

private def f (x : Int) (d : Nat) : Fraction := ⟨x,d+1,by omega⟩
private def p (x y : Int) : Point := (Fraction.ofInt x,Fraction.ofInt y)
private def h : Fraction := f 1 1
private def s : Point × Point := (p 1 0,p 0 1)
private def vertices (a : Field) (d : Fraction) (initial : Point × Point) (i : Nat) : Point :=
  (BoundedIteration.run a d initial i).1

example : Fraction.equiv (areaSum (vertices harmonic h s) 2) (f 1 1) := by decide

-- The first and second triangles share a radial boundary point.
example : Triangle (vertices harmonic h s 0) (vertices harmonic h s 1) (f 1 1,f 1 3) := by
  refine ⟨Fraction.ofInt 0,h,by decide,by decide,?_,?_⟩
  · change (0 : Int) ≤ 1; decide
  · constructor <;> decide
example : Triangle (vertices harmonic h s 1) (vertices harmonic h s 2) (f 1 1,f 1 3) := by
  refine ⟨h,Fraction.ofInt 0,by decide,by decide,?_,?_⟩
  · change (1 : Int) ≤ 2; decide
  · constructor <;> decide

-- An interior point of the first triangle is excluded from the second by
-- its independently calculated transverse coordinate.
example : Triangle (vertices harmonic h s 0) (vertices harmonic h s 1) (f 1 1,f 1 7) := by
  refine ⟨f 1 3,f 1 3,by decide,by decide,?_,?_⟩
  · change (8 : Int) ≤ 16; decide
  · constructor <;> decide
example : ¬ Triangle (vertices harmonic h s 1) (vertices harmonic h s 2) (f 1 1,f 1 7) := by
  intro hx
  have hn := triangle_right _ _ (vertices harmonic h s 1) _ hx
    (Fraction.nonnegative_equiv (det_self _) (by decide)) (by decide)
  have hfalse : ¬ 0 ≤ (TimeSubdivision.det (vertices harmonic h s 1) (f 1 1,f 1 7)).num := by decide
  exact hfalse hn

example (area : AreaRules) : area.HasArea (Region (vertices harmonic h s) 2) (f 1 1) := by
  have ha := region_area area (vertices harmonic h s) 2
    (by
      intro i hi
      have he : i=0 ∨ i=1 ∨ i=2 := by omega
      rcases he with rfl | rfl | rfl <;> decide)
    (by
      intro i hi
      have he : i=0 ∨ i=1 := by omega
      rcases he with rfl | rfl <;> decide)
  exact area.congr_value _ _ _ (by decide) ha

-- After a complete turn, revisiting a triangle enlarges the fan sum while
-- leaving its union unchanged. This rejects global union identification.
private def cycle (i : Nat) : Point :=
  if i=0 ∨ i=4 then p 1 0 else if i=1 ∨ i=5 then p 0 1
  else if i=2 then p (-1) 0 else p 0 (-1)

example : ∀ i, i<5 → 0 < (TimeSubdivision.det (cycle i) (cycle (i+1))).num := by
  intro i hi
  have he : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl <;> decide
example : ¬ (∀ i, i≤5 → 0 < (cycle i).1.num) := by
  intro hp
  have hn := hp 2 (by decide)
  change (0 : Int) < -1 at hn
  omega
example : ∀ x, Region cycle 5 x ↔ Region cycle 4 x := by
  intro x
  constructor
  · rintro ⟨i,hi,hx⟩
    by_cases h : i<4
    · exact ⟨i,h,hx⟩
    · have he : i=4 := by omega
      subst i
      exact ⟨0,by decide,hx⟩
  · rintro ⟨i,hi,hx⟩
    exact ⟨i,by omega,hx⟩
example : ¬ Fraction.equiv (areaSum cycle 5) (areaSum cycle 4) := by decide

#print axioms SectorFan.pairwise_orientation
#print axioms SectorFan.region_area
end NewtonLimitDynamics.Polygon.SectorUnionControls
