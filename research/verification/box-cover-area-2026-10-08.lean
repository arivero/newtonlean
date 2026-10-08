import BarrowLib.Polygon.BoxCoverArea
import BarrowLib.Polygon.MotionSampling

/-! Actual square-union area controls, under the explicit existing
TriangleContent.AreaRules translation-and-cut convention. A vertical split
different from the general union induction assigns area 6 to two overlapping
unit-radius squares; the summed budget is 8, and an area assignment of 8 is
rejected. Duplicate squares, zero radius, negative centres, a closed lower
edge, reversed boxes and the empty cover are included. The motion client
constructs vanishing assigned cover areas from nonnegative C,T,V alone.
These controls share the Lean kernel and coordinate definitions; they do
not construct a model of the area convention, prove subtraction-only
sufficiency or assign the actual mechanical/curve difference area B. -/

namespace NewtonLimitDynamics.Polygon.BoxCoverControls
open NewtonLimitDynamics TimeSubdivision HarmonicTimeComparison HarmonicStability HarmonicDyadic
open BoxCoverArea PolygonFanArea

private def o (z : Int) : Fraction := Fraction.ofInt z
private def leftBox : Box := ⟨o (-1),o 0,o (-1),o 1⟩
private def rightBox : Box := ⟨o 0,o 2,o (-1),o 1⟩
private def leftSquare : Box := square (o 0,o 0) (o 1)
private def rightSquare : Box := square (o 1,o 0) (o 1)

private theorem first_square_region (x : Point) :
    region leftSquare x ↔ Fraction.le (o (-1)) x.1 ∧ Fraction.le x.1 (o 1) ∧
      Fraction.le (o (-1)) x.2 ∧ Fraction.le x.2 (o 1) := by
  unfold leftSquare square region o durationDifference negF Fraction.add Fraction.ofInt
  simp only [Fraction.le, Int.mul_one, Int.one_mul, Int.zero_mul, Int.mul_zero,
    Int.zero_add, Int.add_zero]
  all_goals omega

private theorem second_square_region (x : Point) :
    region rightSquare x ↔ Fraction.le (o 0) x.1 ∧ Fraction.le x.1 (o 2) ∧
      Fraction.le (o (-1)) x.2 ∧ Fraction.le x.2 (o 1) := by
  unfold rightSquare square region o durationDifference negF Fraction.add Fraction.ofInt
  simp only [Fraction.le, Int.mul_one, Int.one_mul, Int.zero_mul, Int.mul_zero,
    Int.zero_add, Int.add_zero]
  all_goals omega

private theorem split_union (x : Point) :
    (region leftSquare x ∨ region rightSquare x) ↔
      (region leftBox x ∨ region rightBox x) := by
  rw [first_square_region, second_square_region]
  unfold region leftBox rightBox o
  simp only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul]
  omega

private def qOverlap (k : Nat) : Point :=
  if k = 0 then (o 0,o 0) else (o 1,o 0)

private theorem overlap_cover_split (x : Point) :
    ConvexCover.SquareCover qOverlap (o 1) 2 x ↔
      region leftBox x ∨ region rightBox x := by
  rw [← square_cover]
  have hs := (cover_succ (fun k => square (qOverlap k) (o 1)) 1 x)
  rw [hs]
  have hs0 := (cover_succ (fun k => square (qOverlap k) (o 1)) 0 x)
  rw [hs0]
  have he : ¬ cover (fun k => square (qOverlap k) (o 1)) 0 x := by
    rintro ⟨k,hk,_⟩
    omega
  simp only [he,false_or]
  change (region leftSquare x ∨ region rightSquare x) ↔
    (region leftBox x ∨ region rightBox x)
  exact split_union x

theorem overlapping_squares_area_six (area : TriangleContent.AreaRules) :
    area.HasArea (ConvexCover.SquareCover qOverlap (o 1) 2) (o 6) := by
  have hleft := area.congr_value _ _ (o 2) (by decide : Fraction.equiv (value leftBox) (o 2))
    (box_area area leftBox)
  have hright := area.congr_value _ _ (o 4) (by decide : Fraction.equiv (value rightBox) (o 4))
    (box_area area rightBox)
  have hsplit := area.separated_union (region leftBox) (region rightBox) (o 2) (o 4)
    (o 0) (by intro x hx; exact hx.2.1) (by intro x hx; exact hx.1)
    hleft hright
  have hsum := area.congr_value _ _ (o 6)
    (by decide : Fraction.equiv (Fraction.add (o 2) (o 4)) (o 6)) hsplit
  exact area.congr_set _ _ _ (fun x => (overlap_cover_split x).symm) hsum

theorem overlapping_squares_any_area_six (area : TriangleContent.AreaRules) (A : Fraction)
    (hA : area.HasArea (ConvexCover.SquareCover qOverlap (o 1) 2) A) :
    Fraction.equiv A (o 6) :=
  (Fraction.equiv_iff_mutual_le _ _).mpr
    ⟨area.monotone _ _ _ _ (fun _ h => h) hA (overlapping_squares_area_six area),
      area.monotone _ _ _ _ (fun _ h => h) (overlapping_squares_area_six area) hA⟩

theorem overlapping_squares_constructed_area (area : TriangleContent.AreaRules) :
    ∃ A, area.HasArea (ConvexCover.SquareCover qOverlap (o 1) 2) A ∧
      Fraction.equiv A (o 6) ∧ Fraction.le A (o 8) := by
  obtain ⟨A,hA,_,hbound⟩ := square_cover_area area qOverlap (o 1) (by decide) 2
  refine ⟨A,hA,overlapping_squares_any_area_six area A hA,?_⟩
  exact Fraction.le_equiv_right hbound (by decide)

theorem overlapping_squares_reject_budget_as_area (area : TriangleContent.AreaRules) :
    ¬ area.HasArea (ConvexCover.SquareCover qOverlap (o 1) 2) (o 8) := by
  intro h
  have hle := area.monotone _ _ _ _ (fun _ hx => hx) h
    (overlapping_squares_area_six area)
  change (8 : Int) ≤ 6 at hle
  omega

theorem closed_lower_edge_included :
    ConvexCover.SquareCover qOverlap (o 1) 2 (o 0,o (-1)) := by
  rw [← square_cover]
  refine ⟨0,by decide,?_⟩
  change region leftSquare (o 0,o (-1))
  rw [first_square_region]
  unfold o Fraction.le Fraction.ofInt
  decide

private theorem one_cover (q : Point) (R : Fraction) (x : Point) :
    ConvexCover.SquareCover (fun _ => q) R 1 x ↔ region (square q R) x := by
  rw [← square_cover,cover_succ]
  have he : ¬ cover (fun _ => square q R) 0 x := by
    rintro ⟨k,hk,_⟩
    omega
  simp only [he,false_or]

theorem one_square_area (area : TriangleContent.AreaRules) (q : Point) (R : Fraction)
    (hR : 0 ≤ R.num) :
    area.HasArea (ConvexCover.SquareCover (fun _ => q) R 1)
      (Fraction.mul (o 4) (Fraction.mul R R)) := by
  have h := box_area area (square q R)
  have hv := square_value q R hR
  have h' := area.congr_value _ _ _ hv h
  exact area.congr_set _ _ _ (fun x => (one_cover q R x).symm) h'

private theorem two_duplicate_cover (q : Point) (R : Fraction) (x : Point) :
    ConvexCover.SquareCover (fun _ => q) R 2 x ↔
      ConvexCover.SquareCover (fun _ => q) R 1 x := by
  rw [← square_cover,← square_cover,cover_succ]
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact ⟨0,by decide,h⟩
  · exact Or.inl

theorem duplicate_squares_area_four (area : TriangleContent.AreaRules) :
    area.HasArea (ConvexCover.SquareCover (fun _ => (o 0,o 0)) (o 1) 2) (o 4) := by
  have h := one_square_area area (o 0,o 0) (o 1) (by decide)
  have h' := area.congr_value _ _ (o 4)
    (by decide : Fraction.equiv (Fraction.mul (o 4) (Fraction.mul (o 1) (o 1))) (o 4)) h
  exact area.congr_set _ _ _ (fun x => (two_duplicate_cover _ _ x).symm) h'

theorem zero_radius_square_area_zero (area : TriangleContent.AreaRules) :
    area.HasArea (ConvexCover.SquareCover (fun _ => (o (-3),o 2)) (o 0) 1) (o 0) := by
  have h := one_square_area area (o (-3),o 2) (o 0) (by decide)
  exact area.congr_value _ _ _
    (by decide : Fraction.equiv (Fraction.mul (o 4) (Fraction.mul (o 0) (o 0))) (o 0)) h

theorem negative_center_square_area_four (area : TriangleContent.AreaRules) :
    area.HasArea (ConvexCover.SquareCover (fun _ => (o (-3),o (-2))) (o 1) 1) (o 4) := by
  have h := one_square_area area (o (-3),o (-2)) (o 1) (by decide)
  exact area.congr_value _ _ _
    (by decide : Fraction.equiv (Fraction.mul (o 4) (Fraction.mul (o 1) (o 1))) (o 4)) h

private def reversedBox : Box := ⟨o 1,o 0,o 0,o 1⟩

theorem reversed_box_empty (x : Point) : ¬ region reversedBox x :=
  region_empty reversedBox (by
    intro h
    have hl := h.1
    change (1 : Int) ≤ 0 at hl
    omega) x

theorem reversed_box_area_zero (area : TriangleContent.AreaRules) :
    area.HasArea (region reversedBox) (o 0) := by
  have h := box_area area reversedBox
  apply area.congr_value _ _ _ ?_ h
  unfold value
  rw [if_neg (by
    intro h
    have hl := h.1
    change (1 : Int) ≤ 0 at hl
    omega)]
  exact Fraction.equiv_refl _

theorem empty_cover_area_zero (area : TriangleContent.AreaRules) (q : Nat → Point)
    (R : Fraction) : area.HasArea (ConvexCover.SquareCover q R 0) (o 0) := by
  apply area.congr_set (fun _ => False) _ _ _ area.empty
  intro x
  rw [← square_cover]
  constructor
  · exact False.elim
  · rintro ⟨k,hk,_⟩
    omega

example (area : TriangleContent.AreaRules) (C T V : Fraction)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hV : 0 ≤ V.num)
    (u : Fraction → Point × Point) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea
        (ConvexCover.SquareCover (fun k => (MotionSampling.samples u T j k).1)
          (MotionSampling.chordRadius C T V j) (blocks j)) (A j) ∧
        0 ≤ (A j).num ∧ Fraction.le (A j) (MotionSampling.chordCoverBudget C T V j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A :=
  MotionSampling.sampled_chord_cover_areas area C T V hC hT hV u

end NewtonLimitDynamics.Polygon.BoxCoverControls
