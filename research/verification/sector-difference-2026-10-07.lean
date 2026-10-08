import NewtonLimitDynamics

/-! Target pin: bridge the actual mechanical and sampled-chord sector unions.
Given finite point sequences p,q with a common initial point, positive first
coordinates and nonnegative consecutive determinants, prove their sector-union
symmetric difference lies in finite filled edge strips plus terminal radial
connector triangles. Derive the strips' shrinking square-cover budgets and
connector bounds from existing MotionSampling.Conditions, not from an assumed B.

Do not assume the desired set inclusion, region area, polygon agreement or
full-curve temporal continuity. Supplied elementary partial area conventions
remain separate from geometric covers. No modern topology or completion.
Keep NATP00090, 1687 and 1713 clients distinct; NATP00089 stays separate.

Formulation check: ConvexCover.MatchedRegion uses two rational interpolation
parameters. It is not automatically the full rational quadrilateral. A filled
triangulated/convex edge strip is licensed if the old bilinear locus is too
small; its square enclosure and the actual sector inclusion must be derived.
Acceptance requires actual geometric set membership, not scalar fan proximity.

Controls must include a displaced terminal endpoint, central versus noncentral
motion, a collapsed cell, equivalent fractions, and the retained full-turn
counterexample that rules out unrestricted multiplicity/union identification.
Stop with the precise geometric sublemma still open if a proposed cover fails;
preserve any proved prerequisites without claiming B is complete. -/

/-! Exact adversarial geometry. The point below lies in the q fan, outside
the p fan and terminal connector, but in a filled edge strip. A written
coordinate check of the narrower second matched patch gives
  1 = lambda*(1+theta), 1 = theta*(1+lambda),
hence theta^2+theta-1=0. For a reduced rational theta=a/b the equation
a^2+a*b-b^2=0 forces b=1, and neither integer root candidate ±1 works.
The first matched patch has nonpositive y. This rational-root exclusion is
a written argument, not a Lean theorem asserted by this control. The exact
memberships and exclusions tested below are kernel checked.

The fixed-ray collar/triangle-exchange inclusion is still open. These tests
certify neither that inclusion nor an area of a finite union. Direct values
and the general results share the Lean kernel and coordinate definitions.
The full-turn union/multiplicity falsifier remains in sector-unions. -/
namespace NewtonLimitDynamics.Polygon.SectorDifferenceControls
open NewtonLimitDynamics TimeSubdivision SectorFan ConvexCover MotionSampling
local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))
local instance (a b : Fraction) : Decidable (Fraction.lt a b) :=
  inferInstanceAs (Decidable (a.num*b.den < b.num*a.den))
private def z := Fraction.ofInt 0
private def o := Fraction.ofInt 1
private def pt (x y : Int) : Point := (Fraction.ofInt x,Fraction.ofInt y)
private def half : Fraction := ⟨1,2,by decide⟩
private def quarter : Fraction := ⟨1,4,by decide⟩
private def p (k : Nat) : Point := (o,if k=0 then Fraction.ofInt (-1) else if k=1 then z else o)
private def q (k : Nat) : Point := if k=0 then pt 1 (-1) else if k=1 then pt 2 0 else pt 3 2
private def x : Point := pt 2 1

example : p 0 = q 0 := rfl
example : ∀ k, k≤2 → 0 < (p k).1.num := by
  intro _ _
  change (0 : Int) < 1
  decide
example : ∀ k, k≤2 → 0 < (q k).1.num := by
  intro k hk
  have he : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases he with rfl | rfl | rfl <;> decide
example : ∀ k, k<2 → 0 ≤ (TimeSubdivision.det (p k) (p (k+1))).num := by
  intro k hk
  have he : k=0 ∨ k=1 := by omega
  rcases he with rfl | rfl <;> decide
example : ∀ k, k<2 → 0 ≤ (TimeSubdivision.det (q k) (q (k+1))).num := by
  intro k hk
  have he : k=0 ∨ k=1 := by omega
  rcases he with rfl | rfl <;> decide
example : Region q 2 x := by
  exact ⟨1,by decide,quarter,half,by decide,by decide,by decide,by constructor <;> decide⟩
example : ¬ Region p 2 x := by
  rintro ⟨k,_,u,v,_,_,hs,hx⟩
  have he : Fraction.equiv x.1 (Fraction.add u v) := Fraction.equiv_trans hx.1 (by
    simp only [p,pointAdd,pointScale,o,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.one_mul,Int.mul_one])
  have hb := Fraction.le_equiv_left he hs
  have hn : ¬ Fraction.le x.1 (Fraction.ofInt 1) := by decide
  exact hn hb
example : ¬ Triangle (p 2) (q 2) x := by
  intro hx
  have hb := triangle_right _ _ (q 2) _ hx (by decide) (by decide)
  have hn : ¬ 0 ≤ (TimeSubdivision.det (q 2) x).num := by decide
  exact hn hb
example : FilledRegion p q 2 x := by
  exact ⟨1,by decide,z,o,half,⟨by decide,by decide⟩,⟨by decide,by decide⟩,
    ⟨by decide,by decide⟩,by constructor <;> decide⟩
example : FilledRegion p q 2 (⟨4,2,by decide⟩,⟨3,3,by decide⟩) := by
  exact ⟨1,by decide,z,o,half,⟨by decide,by decide⟩,⟨by decide,by decide⟩,
    ⟨by decide,by decide⟩,by constructor <;> decide⟩
example : SquareContains (q 1) (Fraction.ofInt 3)
    (filledPatch z o half (p 1) (p 2) (q 1) (q 2)) :=
  filledPatch_square z o half ⟨by decide,by decide⟩ ⟨by decide,by decide⟩
    ⟨by decide,by decide⟩ (q 1) (p 1) (p 2) (q 1) (q 2) (Fraction.ofInt 3)
    (by decide) (by decide) (by decide) (by decide)
example : ¬ FilledRegion p q 0 x := by rintro ⟨k,hk,_⟩; omega

-- The strict near-bound is necessary for deriving a positive coordinate.
example : 0 < (half,z).1.num :=
  positive_first_of_near_lower (half,z) (o,z) o (by decide) (by decide)
example : ¬ Fraction.lt (FiniteEstimates.pointDistance (z,z) (o,z)) o := by decide
example : ¬ Fraction.lt (FiniteEstimates.pointDistance (pt (-1) 0) (o,z)) o := by decide

-- Positive, reversed and collapsed connectors use one area interface.
example (area : AreaRules) : area.HasArea (Triangle (pt 1 0) (pt 1 1)) half :=
  area.congr_value _ _ _ (by decide) (unsigned_triangle_area area _ _)
example (area : AreaRules) : area.HasArea (Triangle (pt 1 1) (pt 1 0)) half :=
  area.congr_value _ _ _ (by decide) (unsigned_triangle_area area _ _)
example (area : AreaRules) : area.HasArea (Triangle (pt 1 1) (pt 1 1)) z :=
  area.congr_value _ _ _ (by decide) (unsigned_triangle_area area _ _)

#print axioms SectorFan.unsigned_triangle_area
#print axioms ConvexCover.filledPatch_square
#print axioms MotionSampling.sampled_filled_cover
#print axioms MotionSampling.terminal_connector_areas_vanish
#print axioms MotionSampling.polygon_eventually_positive
end NewtonLimitDynamics.Polygon.SectorDifferenceControls
