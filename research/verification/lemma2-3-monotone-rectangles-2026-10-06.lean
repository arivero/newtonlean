import NewtonLimitDynamics

namespace NewtonLimitDynamics.Polygon.MonotoneRectangleControls
open NewtonLimitDynamics TimeSubdivision PositionValues CompletionGeometry
open MonotoneRectangles HarmonicTimeComparison HarmonicTimeRealization HarmonicDyadic

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den≤b.num*a.den))
local instance (a b : Fraction) : Decidable (Fraction.lt a b) :=
  inferInstanceAs (Decidable (a.num*b.den<b.num*a.den))
local instance (a b h : Fraction) (x : Point) : Decidable (rectangle a b h x) :=
  inferInstanceAs (Decidable (Fraction.le a x.1 ∧ Fraction.le x.1 b ∧
    0≤x.2.num ∧ Fraction.le x.2 h))
local instance (g : Fraction → Fraction) (a b : Fraction) (x : Point) : Decidable (figure g a b x) :=
  inferInstanceAs (Decidable (Fraction.le a x.1 ∧ Fraction.le x.1 b ∧
    0≤x.2.num ∧ Fraction.le x.2 (g x.1)))

private def p (x y : Int) : Point := (Fraction.ofInt x,Fraction.ofInt y)
private def squareGraph (x : Fraction) : Fraction := Fraction.mul x x
private theorem square_monotone (b : Fraction) : MonotoneOn squareGraph (Fraction.ofInt 0) b := by
  intro x y hx hxy _
  have hx0 : 0≤x.num := Fraction.nonnegative_of_le (by decide) hx
  have hy0 : 0≤y.num := Fraction.nonnegative_of_le hx0 hxy
  exact Fraction.magnitudes.le_trans (Fraction.mul_le_mul_nonnegative hxy x hx0)
    (Fraction.mul_le_mul_nonnegative_left hxy y hy0)

private def unequal : Partition (Fraction.ofInt 0) (Fraction.ofInt 3) where
  count := 2
  positive_count := by decide
  nodes := fun i => if i=0 then Fraction.ofInt 0 else if i=1 then Fraction.ofInt 1 else Fraction.ofInt 3
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    by_cases he : i=0
    · subst i; decide
    · have he' : i=1 := by omega
      subst i
      decide

-- A point in the curved figure can be outside the lower rectangles but inside the upper.
example : figure squareGraph (Fraction.ofInt 0) (Fraction.ofInt 3) (p 2 3) := by decide
example : upperFigure squareGraph unequal (p 2 3) := by
  exact ⟨1,by decide,by decide⟩
example : ¬ lowerFigure squareGraph unequal (p 2 3) := by
  intro h
  obtain ⟨i,hi,hx⟩ := h
  by_cases he : i=0
  · subst i
    have hn : ¬ rectangle (unequal.nodes 0) (unequal.nodes 1) (squareGraph (unequal.nodes 0)) (p 2 3) := by decide
    exact hn hx
  · have he' : i=1 := by change i<2 at hi; omega
    subst i
    have hn : ¬ rectangle (unequal.nodes 1) (unequal.nodes 2) (squareGraph (unequal.nodes 1)) (p 2 3) := by decide
    exact hn hx

-- Actual finite areas and an unequal-width gap strictly below the maximum-width budget.
example : Fraction.equiv (lowerSum squareGraph unequal) (Fraction.ofInt 2) := by decide
example : Fraction.equiv (upperSum squareGraph unequal) (Fraction.ofInt 19) := by decide
example : Fraction.equiv (gap squareGraph unequal) (Fraction.ofInt 17) := by decide
example : Fraction.equiv (maxWidth unequal) (Fraction.ofInt 2) := by
  have hs := maxWidth_bounds unequal
  apply (Fraction.equiv_iff_mutual_le _ _).mpr
  constructor
  · apply hs.2
    intro i hi
    by_cases he : i=0
    · subst i; decide
    · have he' : i=1 := by change i<2 at hi; omega
      subst i
      decide
  · exact hs.1 1 (by decide)
example : Fraction.lt (gap squareGraph unequal) (Fraction.ofInt 18) := by decide

-- All completed figure points inherit the set enclosure, not just vertices.
example (x : PositionValue) (hx : completed (figure squareGraph (Fraction.ofInt 0) (Fraction.ofInt 3)) x) :
    completed (upperFigure squareGraph unequal) x :=
  (completed_enclosure squareGraph unequal (square_monotone _)).2 x hx

-- Raw endpoint representations can differ: graph endpoint values and total height transport.
private def aliases : Partition (Fraction.ofInt 0) (Fraction.ofInt 1) where
  count := 2
  positive_count := by decide
  nodes := fun i => ⟨(i : Int),2,by decide⟩
  first := by decide
  last := by decide
  ordered := by
    intro i _
    simp only [Fraction.le,Int.natCast_add,Int.natCast_one]
    omega
example : aliases.nodes 0 ≠ Fraction.ofInt 0 := by
  intro h
  have he := congrArg Fraction.den h
  change (2 : Int)=1 at he
  omega
example : Fraction.equiv (gap squareGraph aliases) (Fraction.ofInt 1).half := by
  have he := Principia1687.LemmaII.lemma2_equal_width_gap squareGraph _ _ (Fraction.ofInt 1).half aliases (square_monotone _)
    (fun i hi => by
      simp only [aliases,width,durationDifference,HarmonicStability.negF,Fraction.equiv,Fraction.add,
        Fraction.half,Fraction.ofInt,Int.natCast_add,Int.natCast_one,Int.neg_mul]
      omega)
  exact Fraction.equiv_trans he (by decide)

private theorem grid_width (m i : Nat) : Fraction.equiv
    (durationDifference (countTime (Fraction.ofInt 1) m i) (countTime (Fraction.ofInt 1) m (i+1)))
    (duration (Fraction.ofInt 1) m) :=
  Fraction.equiv_trans (countTime_difference (Fraction.ofInt 1) m i 1)
    (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one,Int.natCast_one])

private def dyadic (m : Nat) : Partition (Fraction.ofInt 0) (Fraction.ofInt 1) where
  count := blocks m
  positive_count := by unfold blocks; exact Nat.pow_pos (by decide)
  nodes := countTime (Fraction.ofInt 1) m
  first := by simp only [countTime,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_zero,Int.zero_mul,Int.mul_zero]
  last := blocks_duration (Fraction.ofInt 1) m
  ordered := by
    intro i _
    exact (difference_nonnegative_iff _ _).mp
      (Fraction.nonnegative_equiv (grid_width m i) (by change (0 : Int)≤1; decide))

private theorem dyadic_mesh : ∀ delta : Fraction, 0<delta.num → ∃ N : Nat, ∀ m, N≤m →
    Fraction.lt (maxWidth (dyadic m)) delta := by
  intro delta hd
  obtain ⟨N,hN⟩ := duration_eventually_small (Fraction.ofInt 1) delta (by decide) hd
  refine ⟨N,fun m hm => Fraction.magnitudes.lt_of_le_lt ?_ (hN m hm)⟩
  exact (maxWidth_bounds (dyadic m)).2 _ (fun i _ => Fraction.le_of_equiv (grid_width m i))

-- A constructed, nonconstant curved example instantiates the whole reconstruction;
-- no desired rectangle enclosure, area-gap budget or convergence is supplied.
example : ∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
    Fraction.lt (gap squareGraph (dyadic m)) eps :=
  gaps_vanish squareGraph dyadic (square_monotone _) dyadic_mesh
example : Fraction.equiv (gap squareGraph (dyadic 0)) (Fraction.ofInt 1) := by decide

-- Dropping graph monotonicity would make the claimed geometric enclosure false:
-- the polynomial hump has zero endpoint rectangle gap and a positive interior ordinate.
private def hump (x : Fraction) : Fraction :=
  Fraction.mul (Fraction.ofInt 4) (Fraction.mul x (ConvexCover.complement x))
private def humpPoint : Point := ((Fraction.ofInt 1).half,Fraction.ofInt 1)
example : figure hump (Fraction.ofInt 0) (Fraction.ofInt 1) humpPoint := by decide
example : Fraction.equiv (gap hump (dyadic 0)) (Fraction.ofInt 0) := by decide
example : ¬ upperFigure hump (dyadic 0) humpPoint := by
  intro h
  obtain ⟨i,hi,hx⟩ := h
  have he : i=0 := by change i<1 at hi; omega
  subst i
  have hn : ¬ rectangle ((dyadic 0).nodes 0) ((dyadic 0).nodes 1)
      (hump ((dyadic 0).nodes 1)) humpPoint := by decide
  exact hn hx
example : ¬ MonotoneOn hump (Fraction.ofInt 0) (Fraction.ofInt 1) := by
  intro h
  have hb := h (Fraction.ofInt 1).half (Fraction.ofInt 1) (by decide) (by decide) (by decide)
  have hn : ¬ Fraction.le (hump (Fraction.ofInt 1).half) (hump (Fraction.ofInt 1)) := by decide
  exact hn hb

-- 1713 has its own source-local wrapper with the same satisfiable geometric premises.
example : (∀ m, (∀ x, completed (lowerFigure squareGraph (dyadic m)) x →
      completed (figure squareGraph (Fraction.ofInt 0) (Fraction.ofInt 1)) x) ∧
    (∀ x, completed (figure squareGraph (Fraction.ofInt 0) (Fraction.ofInt 1)) x →
      completed (upperFigure squareGraph (dyadic m)) x)) :=
  (ModernLib.Reconstruction.Principia1713.LemmaIIIII.lemmas2_3_monotone_rectangle_reconstruction squareGraph _ _ dyadic
    (square_monotone _) (by decide) dyadic_mesh).1

-- Zero horizontal span and positive constant height still have zero rectangle-sum gap.
private def zeroWidth : Partition (Fraction.ofInt 0) (Fraction.ofInt 0) :=
  ⟨1,by decide,fun _ => Fraction.ofInt 0,by decide,by decide,fun _ _ => Fraction.magnitudes.le_refl _⟩
example : Fraction.equiv (gap (fun _ => Fraction.ofInt 5) zeroWidth) (Fraction.ofInt 0) := by decide
example : rectangle (Fraction.ofInt 0) (Fraction.ofInt 0) (Fraction.ofInt 5) (p 0 3) := by decide

#print axioms MonotoneRectangles.completed_enclosure
#print axioms MonotoneRectangles.maxWidth_bounds
#print axioms MonotoneRectangles.gap_equal_width
#print axioms MonotoneRectangles.gap_bound
#print axioms MonotoneRectangles.gaps_vanish
#print axioms ModernLib.Reconstruction.Principia1687.LemmaIIIII.lemmas2_3_monotone_rectangle_reconstruction
#print axioms Principia1713.LemmaII.lemma2_equal_width_gap
end NewtonLimitDynamics.Polygon.MonotoneRectangleControls
