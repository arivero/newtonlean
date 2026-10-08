import NewtonLimitDynamics
import Lean

/-! Rectangle controls, including the 8 October mutual-ratio increment.
The nonconstant positive graph, aliases and repeated nodes exercise derived
denominator bounds. Shrinking positive magnitudes with constant ratio 1/2
falsify the claim without a uniform lower bound. These exact controls share
the rational definitions and Lean kernel; supplied area rules remain premises. -/

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

-- Finite side-product sums and a gap strictly below the maximum-width budget.
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

-- Primary historical exhaustion uses the independently supplied shrinking mesh.
example : Exhaustion.VanishingDifference Fraction.magnitudes
    (fun m => gap squareGraph (dyadic m)) :=
  Principia1687.LemmaIII.unequal_width_gap_vanishes squareGraph _ _ dyadic
    (square_monotone _) dyadic_mesh

-- The geometric area convention is explicit. The actual finite union, rather
-- than a renamed sum, acquires its side-product area through its additivity rules.
example (area : RectangleContent.AreaRules) :
    area.HasArea (lowerFigure squareGraph unequal) (Fraction.ofInt 2) :=
  area.congr_value _ _ _ (by decide)
    (RectangleContent.lower_upper_areas area squareGraph _ _ unequal
      (square_monotone _) (by decide)).1

example (area : RectangleContent.AreaRules) (A : Fraction)
    (hA : area.HasArea (figure squareGraph (Fraction.ofInt 0) (Fraction.ofInt 1)) A) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (durationDifference (lowerSum squareGraph (dyadic m)) A).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (durationDifference A (upperSum squareGraph (dyadic m))).abs) :=
  Principia1713.LemmaIII.corollary1_area_approximation area squareGraph _ _ A
    dyadic (square_monotone _) (by decide) hA dyadic_mesh

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

private def raisedGraph (x : Fraction) : Fraction := Fraction.add (Fraction.ofInt 1) (squareGraph x)
private theorem raised_monotone (b : Fraction) : MonotoneOn raisedGraph (Fraction.ofInt 0) b := by
  intro x y hx hxy hy
  exact Fraction.add_le_add_left (square_monotone b x y hx hxy hy) (Fraction.ofInt 1)
private theorem uniform_mesh : Exhaustion.VanishingDifference Fraction.magnitudes
    (fun m => duration (Fraction.ofInt 1) m) :=
  fun delta hd => duration_eventually_small (Fraction.ofInt 1) delta (by decide) hd

-- The raw endpoint aliases do not affect the base rectangle or either ratio.
example : Fraction.le (Fraction.ofInt 1) (lowerSum raisedGraph aliases) :=
  lower_sum_base_bound raisedGraph aliases (raised_monotone _)
example : Fraction.equiv (lowerSum raisedGraph aliases) (⟨9,8,by decide⟩ : Fraction) := by decide
example : Fraction.equiv (upperSum raisedGraph aliases) (⟨13,8,by decide⟩ : Fraction) := by decide
example : Fraction.equiv
    (RectangleContent.ratioTo (upperSum raisedGraph aliases) (by decide) (lowerSum raisedGraph aliases))
    (⟨9,13,by decide⟩ : Fraction) := by decide
example : Fraction.equiv
    (RectangleContent.ratioTo (lowerSum raisedGraph aliases) (by decide) (upperSum raisedGraph aliases))
    (⟨13,9,by decide⟩ : Fraction) := by decide
example : ¬ Fraction.equiv
    (RectangleContent.ratioTo (upperSum raisedGraph aliases) (by decide) (lowerSum raisedGraph aliases))
    (⟨10,13,by decide⟩ : Fraction) := by decide

-- An actual zero-width cell is allowed alongside two positive-width cells.
private def repeated : Partition (Fraction.ofInt 0) (Fraction.ofInt 1) where
  count := 3
  positive_count := by decide
  nodes := fun i => if i ≤ 1 then Fraction.ofInt 0 else if i = 2 then (Fraction.ofInt 1).half else Fraction.ofInt 1
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    by_cases h0 : i=0
    · subst i; decide
    · by_cases h1 : i=1
      · subst i; decide
      · have h2 : i=2 := by omega
        subst i; decide
example : Fraction.equiv (width repeated 0) (Fraction.ofInt 0) := by decide
example : Fraction.equiv (lowerSum raisedGraph repeated) (⟨9,8,by decide⟩ : Fraction) := by decide
example : Fraction.le (Fraction.ofInt 1) (lowerSum raisedGraph repeated) :=
  lower_sum_base_bound raisedGraph repeated (raised_monotone _)
example : Fraction.equiv (lowerSum raisedGraph unequal) (Fraction.ofInt 5) := by decide
example : Fraction.equiv (upperSum raisedGraph unequal) (Fraction.ofInt 22) := by decide
example : Fraction.le (Fraction.ofInt 3) (lowerSum raisedGraph unequal) :=
  lower_sum_base_bound raisedGraph unequal (raised_monotone _)

-- Neither denominator positivity nor an area for the curved figure is assumed.
example (area : RectangleContent.AreaRules) : RectangleContent.MutualRatiosOne
    (fun m => lowerSum raisedGraph (dyadic m)) (fun m => upperSum raisedGraph (dyadic m)) :=
  (Principia1687.LemmaII.equal_width_mutual_area_ratios area raisedGraph _ _ dyadic
    (raised_monotone _) (by decide) (by decide) _
    (fun m i _ => grid_width m i) uniform_mesh).2
example (area : RectangleContent.AreaRules) : RectangleContent.MutualRatiosOne
    (fun m => lowerSum raisedGraph (dyadic m)) (fun m => upperSum raisedGraph (dyadic m)) :=
  (Principia1713.LemmaII.equal_width_mutual_area_ratios area raisedGraph _ _ dyadic
    (raised_monotone _) (by decide) (by decide) _
    (fun m i _ => grid_width m i) uniform_mesh).2
example (area : RectangleContent.AreaRules) : RectangleContent.MutualRatiosOne
    (fun m => lowerSum raisedGraph (dyadic m)) (fun m => upperSum raisedGraph (dyadic m)) :=
  (Principia1687.LemmaIII.unequal_width_mutual_area_ratios area raisedGraph _ _ dyadic
    (raised_monotone _) (by decide) (by decide) dyadic_mesh).2
example (area : RectangleContent.AreaRules) : RectangleContent.MutualRatiosOne
    (fun m => lowerSum raisedGraph (dyadic m)) (fun m => upperSum raisedGraph (dyadic m)) :=
  (Principia1713.LemmaIII.unequal_width_mutual_area_ratios area raisedGraph _ _ dyadic
    (raised_monotone _) (by decide) (by decide) dyadic_mesh).2
example (area : RectangleContent.AreaRules) :
    area.HasArea (lowerFigure raisedGraph (dyadic 1)) (⟨9,8,by decide⟩ : Fraction) :=
  area.congr_value _ _ _ (by decide)
    ((Principia1713.LemmaIII.unequal_width_mutual_area_ratios area raisedGraph _ _ dyadic
      (raised_monotone _) (by decide) (by decide) dyadic_mesh).1 1).1

-- Degenerate patches have zero lower area, so the strict premises are needed.
example : (lowerSum squareGraph (dyadic 0)).num = 0 := by decide
example : (lowerSum (fun _ => Fraction.ofInt 5) zeroWidth).num = 0 := by decide
example : Fraction.equiv
    (RectangleContent.ratioTo (lowerSum (fun _ => Fraction.ofInt 5) (dyadic 0)) (by decide)
      (upperSum (fun _ => Fraction.ofInt 5) (dyadic 0))) (Fraction.ofInt 1) := by decide

-- Both magnitudes are positive and their absolute gap vanishes, but L/U=1/2.
private def shrinking (m : Nat) : Fraction := duration (Fraction.ofInt 1) m
private def doubled (m : Nat) : Fraction := Fraction.mul (Fraction.ofInt 2) (shrinking m)
private theorem doubled_gap (m : Nat) :
    Fraction.equiv (durationDifference (shrinking m) (doubled m)) (shrinking m) := by
  simp only [doubled,shrinking,duration,durationDifference,HarmonicStability.negF,Fraction.equiv,Fraction.add,
    Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one,Int.add_mul,Int.mul_add,Int.neg_mul]
  ac_nf
  omega
private theorem shrinking_ratio (m : Nat) (h : 0 < (doubled m).num) :
    Fraction.equiv (RectangleContent.ratioTo (doubled m) h (shrinking m)) (Fraction.ofInt 1).half := by
  simp only [doubled,RectangleContent.ratioTo,Fraction.equiv,Fraction.mul,Fraction.half,
    Fraction.ofInt,Int.mul_one,Int.one_mul]
  ac_nf
example : (∀ m, 0 < (shrinking m).num ∧ 0 < (doubled m).num) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (durationDifference (shrinking m) (doubled m)).abs) ∧
    ¬ RectangleContent.MutualRatiosOne shrinking doubled := by
  refine ⟨fun _ => ⟨by change (0 : Int) < 1; decide, by change (0 : Int) < 2; decide⟩, ?_, ?_⟩
  · intro eps heps
    obtain ⟨N,hN⟩ := uniform_mesh eps heps
    exact ⟨N,fun m hm => Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (Fraction.equiv_trans (Fraction.abs_equiv (doubled_gap m))
        (Fraction.abs_of_nonnegative _ (by change (0 : Int) ≤ 1; decide)))) (hN m hm)⟩
  · rintro ⟨_,hU,hsmall,_⟩
    obtain ⟨N,hN⟩ := hsmall (Fraction.ofInt 1).half (by change (0 : Int) < 1; decide)
    have he : Fraction.equiv
        (durationDifference (RectangleContent.ratioTo (doubled N) (hU N) (shrinking N))
          (Fraction.ofInt 1)).abs (Fraction.ofInt 1).half :=
      Fraction.equiv_trans (Fraction.abs_equiv
        (difference_congr (shrinking_ratio N (hU N)) (Fraction.equiv_refl _))) (by decide)
    exact Fraction.magnitudes.lt_irrefl _ (Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (Fraction.equiv_symm he)) (hN N (Nat.le_refl _)))

#print axioms RectangleContent.rectangle_mutual_ratios
#print axioms Principia1687.LemmaII.equal_width_mutual_area_ratios
#print axioms Principia1713.LemmaIII.unequal_width_mutual_area_ratios
#print axioms MonotoneRectangles.completed_enclosure
#print axioms MonotoneRectangles.maxWidth_bounds
#print axioms MonotoneRectangles.gap_equal_width
#print axioms MonotoneRectangles.gap_bound
#print axioms MonotoneRectangles.gaps_vanish
#print axioms ModernLib.Reconstruction.Principia1687.LemmaIIIII.lemmas2_3_monotone_rectangle_reconstruction
#print axioms Principia1713.LemmaII.lemma2_equal_width_gap
end NewtonLimitDynamics.Polygon.MonotoneRectangleControls

-- Inspect proof terms and types, including private helpers, rather than imports.
open Lean in
run_elab do
  let env ← getEnv
  for (edition, foreign) in #[(`Principia1687, "Principia1713."), (`Principia1713, "Principia1687.")] do
    for (root, required) in #[
        (edition ++ `LemmaII.equal_width_mutual_area_ratios,
          #[edition ++ `LemmaII.rectangle_mutual_ratios_from_gap,
            edition ++ `LemmaII.equal_width_gap_vanishes]),
        (edition ++ `LemmaIII.unequal_width_mutual_area_ratios,
          #[edition ++ `LemmaII.rectangle_mutual_ratios_from_gap,
            edition ++ `LemmaIII.unequal_width_gap_vanishes])] do
      unless (env.find? root).isSome do throwError "missing mutual-ratio client {root}"
      let mut todo := #[root]
      let mut used : NameSet := {}
      while !todo.isEmpty do
        let name := todo.back!
        todo := todo.pop
        unless used.contains name do
          used := used.insert name
          if let some info := env.find? name then
            todo := todo ++ info.type.getUsedConstants ++
              ((info.value? true).map Expr.getUsedConstants |>.getD #[])
      for dependency in required do
        unless used.contains dependency do throwError "{root} omits {dependency}"
      for dependency in used do
        let name := ((privateToUserName? dependency).getD dependency).toString
        if #[foreign, "DeMotu1684.", "ModernLib."].any name.startsWith then
          throwError "{root} uses forbidden witness/modern declaration {dependency}"
  logInfo "Checked four mutual-ratio clients: own-edition reduction/exhaustion, no foreign witness or ModernLib."
