import NewtonLimitDynamics.Historical.LemmaIII.CorollaryI
import Lean

/-! Explicit staircase controls. A nonzero identity graph with actual dyadic
partitions realizes the continuity and shrinking-mesh premises. One-cell
controls distinguish the step edges from their filled endpoint box and reject
the false final lower rise. Adjacent/repeated cells and equivalent rational
representatives exercise the internal joins. No geometric area assignment is
used. These controls share the rational definitions and Lean kernel. -/

namespace NewtonLimitDynamics.Polygon.StaircaseControls
open NewtonLimitDynamics TimeSubdivision MonotoneRectangles RationalBoundary
open HarmonicTimeComparison HarmonicTimeRealization HarmonicDyadic PointBounds FiniteEstimates SupportingTangents

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den≤b.num*a.den))
local instance (a x b : Fraction) : Decidable (Between a x b) :=
  inferInstanceAs (Decidable ((Fraction.le a x ∧ Fraction.le x b) ∨
    (Fraction.le b x ∧ Fraction.le x a)))
local instance (l r H : Fraction) (x : Point) : Decidable (RectangleTop l r H x) :=
  inferInstanceAs (Decidable (Fraction.le l x.1 ∧ Fraction.le x.1 r ∧ Fraction.equiv x.2 H))
local instance (c u v : Fraction) (x : Point) : Decidable (VerticalJoin c u v x) :=
  inferInstanceAs (Decidable (Fraction.equiv x.1 c ∧ Between u x.2 v))
local instance (l r H : Fraction) (x : Point) : Decidable (rectangle l r H x) :=
  inferInstanceAs (Decidable (Fraction.le l x.1 ∧ Fraction.le x.1 r ∧
    0≤x.2.num ∧ Fraction.le x.2 H))

private def z : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1
private def half : Fraction := ⟨1,2,by decide⟩

private def single : Partition z one where
  count := 1
  positive_count := by decide
  nodes := fun i => if i=0 then z else one
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    have he : i=0 := by change i<1 at hi; omega
    subst i
    decide

-- A filled endpoint box has interior points absent from both step traces.
example : RectangleTrace (fun t => (t,t)) single (half,half) :=
  ⟨0,by decide,Or.inl ⟨by decide,by decide⟩,Or.inl ⟨by decide,by decide⟩⟩
example : ¬ LowerStaircase id single (half,half) := by
  rintro ⟨i,hi,hx⟩
  have he : i=0 := by change i<1 at hi; omega
  subst i
  rcases hx with hx | ⟨hn,_⟩
  · exact (by decide : ¬ RectangleTop (single.nodes 0) (single.nodes 1)
      (single.nodes 0) (half,half)) hx
  · change 1<1 at hn; omega
example : ¬ UpperStaircase id single (half,half) := by
  rintro ⟨i,hi,hx⟩
  have he : i=0 := by change i<1 at hi; omega
  subst i
  rcases hx with hx | hx
  · exact (by decide : ¬ VerticalJoin (single.nodes 0) (single.nodes 0)
      (single.nodes 1) (half,half)) hx
  · exact (by decide : ¬ RectangleTop (single.nodes 0) (single.nodes 1)
      (single.nodes 1) (half,half)) hx

-- The final rise is in the endpoint box, but outside the actual lower union.
example : RectangleTrace (fun t => (t,t)) single (one,half) :=
  ⟨0,by decide,Or.inl ⟨by decide,by decide⟩,Or.inl ⟨by decide,by decide⟩⟩
example : ¬ lowerFigure id single (one,half) := by
  rintro ⟨i,hi,hx⟩
  have he : i=0 := by change i<1 at hi; omega
  subst i
  exact (by decide : ¬ rectangle (single.nodes 0) (single.nodes 1)
    (single.nodes 0) (one,half)) hx
example : ¬ LowerStaircase id single (one,half) := by
  intro hx
  have h := lower_staircase_in_figure id single (fun _ _ _ h _ => h) (by decide) _ hx
  obtain ⟨i,hi,hx⟩ := h
  have he : i=0 := by change i<1 at hi; omega
  subst i
  exact (by decide : ¬ rectangle (single.nodes 0) (single.nodes 1)
    (single.nodes 0) (one,half)) hx

-- Nontrivial horizontal tops and the upper construction's initial side.
example : LowerStaircase id single (half,z) := ⟨0,by decide,Or.inl (by decide)⟩
example : UpperStaircase id single (z,half) := ⟨0,by decide,Or.inl (by decide)⟩
example : UpperStaircase id single (half,one) := ⟨0,by decide,Or.inr (by decide)⟩

private def repeated : Partition z (Fraction.ofInt 2) where
  count := 3
  positive_count := by decide
  nodes := fun i => if i=0 then ⟨0,2,by decide⟩ else
    if i≤2 then ⟨2,2,by decide⟩ else ⟨4,2,by decide⟩
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    by_cases he : i=0
    · subst i; decide
    · by_cases he' : i=1
      · subst i; decide
      · have he'' : i=2 := by change i<3 at hi; omega
        subst i; decide

-- The internal lower riser belongs to the next rectangle, even at a zero-width cell.
example : LowerStaircase id repeated (one,half) :=
  ⟨0,by decide,Or.inr ⟨by decide,by decide⟩⟩
example : lowerFigure id repeated (one,half) :=
  lower_staircase_in_figure id repeated (fun _ _ _ h _ => h) (by decide) _
    ⟨0,by decide,Or.inr ⟨by decide,by decide⟩⟩
example : UpperStaircase id repeated ((⟨2,2,by decide⟩ : Fraction),(⟨3,2,by decide⟩ : Fraction)) :=
  ⟨2,by decide,Or.inl (by decide)⟩
example : upperFigure id repeated (one,(⟨3,2,by decide⟩ : Fraction)) :=
  upper_staircase_in_figure id repeated (fun _ _ _ h _ => h) (by decide) _
    ⟨2,by decide,Or.inl (by decide)⟩
example : LowerStaircase id repeated (one,one) :=
  ⟨1,by decide,Or.inl (by decide)⟩

-- Flat graphs and a wholly collapsed interval need no strict inequalities.
example : LowerStaircase (fun _ => one) single (half,one) ∧
    UpperStaircase (fun _ => one) single (half,one) :=
  ⟨⟨0,by decide,Or.inl (by decide)⟩,⟨0,by decide,Or.inr (by decide)⟩⟩
private def collapsed : Partition z z :=
  ⟨1,by decide,fun _ => z,by decide,by decide,fun _ _ => Fraction.magnitudes.le_refl _⟩
private theorem collapsed_mesh : Exhaustion.VanishingDifference Fraction.magnitudes
    (fun _ => maxWidth collapsed) := by
  intro eps heps
  have hmax : Fraction.le (maxWidth collapsed) z :=
    (maxWidth_bounds collapsed).2 z (fun i _ => Fraction.le_of_equiv
      (by rfl : Fraction.equiv (width collapsed i) z))
  exact ⟨0,fun _ _ => Fraction.magnitudes.lt_of_le_lt hmax
    ((Fraction.positive_iff_zero_lt eps).mp heps)⟩

private theorem identity_uniform (a b : Fraction) : UniformOn (fun t => (t,t)) a b := by
  intro eps heps
  refine ⟨eps.half.half,heps,?_⟩
  intro s t _ _ _ _ hst
  have hd : Fraction.equiv (pointDistance (s,s) (t,t))
      (Fraction.add (durationDifference s t).abs (durationDifference s t).abs) := by
    apply Fraction.equiv_trans (pointDistance_symm _ _)
    exact Fraction.equiv_refl _
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_equiv_left hd (Fraction.le_equiv_right
      (Fraction.add_le_add hst hst) (Fraction.half_add_self eps.half)))
    (Fraction.half_lt eps heps)

private theorem grid_width (m i : Nat) :
    Fraction.equiv (durationDifference (countTime one m i) (countTime one m (i+1)))
      (duration one m) := by
  exact Fraction.equiv_trans (countTime_difference one m i 1)
    (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one,Int.natCast_one])

private def dyadic (m : Nat) : Partition z one where
  count := blocks m
  positive_count := by unfold blocks; exact Nat.pow_pos (by decide)
  nodes := countTime one m
  first := by simp [countTime,Fraction.equiv,Fraction.mul,one,Fraction.ofInt,z]
  last := blocks_duration one m
  ordered := by
    intro i _
    exact (difference_nonnegative_iff _ _).mp
      (Fraction.nonnegative_equiv (grid_width m i)
        (by change (0 : Int)≤1; decide))

private theorem dyadic_mesh : Exhaustion.VanishingDifference Fraction.magnitudes
    (fun m => maxWidth (dyadic m)) := by
  intro eps heps
  obtain ⟨N,hN⟩ := duration_eventually_small one eps (by decide) heps
  refine ⟨N,fun m hm => Fraction.magnitudes.lt_of_le_lt ?_ (hN m hm)⟩
  exact (maxWidth_bounds (dyadic m)).2 _ (fun i _ => Fraction.le_of_equiv (grid_width m i))

example : Approaches (fun _ => LowerStaircase id collapsed)
    (CurveTrace (fun t => (t,t)) z z) :=
  (Principia1687.LemmaIII.corollary1_staircase_boundaries id z z (fun _ => collapsed)
    (fun _ _ _ h _ => h) (by decide) (identity_uniform z z) collapsed_mesh).1

example : Approaches (fun m => LowerStaircase id (dyadic m)) (CurveTrace (fun t => (t,t)) z one) :=
  (Principia1687.LemmaIII.corollary1_staircase_boundaries id z one dyadic
    (fun _ _ _ h _ => h) (by decide) (identity_uniform z one) dyadic_mesh).1
example : Approaches (fun m => UpperStaircase id (dyadic m)) (CurveTrace (fun t => (t,t)) z one) :=
  (Principia1713.LemmaIII.corollary1_staircase_boundaries id z one dyadic
    (fun _ _ _ h _ => h) (by decide) (identity_uniform z one) dyadic_mesh).2.1

-- The lower trace omits the final graph endpoint but approaches it on a usable tail.
example : ∃ N, ∀ m, N≤m → ∃ x, LowerStaircase id (dyadic m) x ∧
    Fraction.lt (pointDistance (one,one) x) half := by
  have h := (Principia1713.LemmaIII.corollary1_staircase_boundaries id z one dyadic
    (fun _ _ _ h _ => h) (by decide) (identity_uniform z one) dyadic_mesh).1
  obtain ⟨N,hN⟩ := h half (by decide)
  exact ⟨N,fun m hm => (hN m hm).2 (one,one)
    ⟨one,by decide,Fraction.magnitudes.le_refl _,Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

end NewtonLimitDynamics.Polygon.StaircaseControls

open Lean in
run_elab do
  let env ← getEnv
  for (edition,foreign) in #[(`Principia1687,"Principia1713."),(`Principia1713,"Principia1687.")] do
    let root := edition ++ `LemmaIII.corollary1_staircase_boundaries
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
    for dependency in #[edition ++ `LemmaIII.corollary1_rectangle_boundary,
        `NewtonLimitDynamics.Polygon.RationalBoundary.nodes_approach,
        `NewtonLimitDynamics.Polygon.RationalBoundary.trace_sandwich,
        `NewtonLimitDynamics.Polygon.RationalBoundary.nodes_in_lower_staircase,
        `NewtonLimitDynamics.Polygon.RationalBoundary.nodes_in_upper_staircase,
        `NewtonLimitDynamics.Polygon.RationalBoundary.lower_staircase_in_rectangles,
        `NewtonLimitDynamics.Polygon.RationalBoundary.upper_staircase_in_rectangles,
        `NewtonLimitDynamics.Polygon.RationalBoundary.lower_staircase_in_figure,
        `NewtonLimitDynamics.Polygon.RationalBoundary.upper_staircase_in_figure] do
      unless used.contains dependency do throwError "{root} omits {dependency}"
    for dependency in used do
      let name := ((privateToUserName? dependency).getD dependency).toString
      if #[foreign,"DeMotu1684."].any (fun rootName => name.startsWith rootName) then
        throwError "{root} uses foreign witness {dependency}"
      if let some idx := env.getModuleIdxFor? dependency then
        if env.header.moduleNames[idx]!.toString.startsWith "ModernLib" then
          throwError "{root} uses modern module through {dependency}"
  logInfo "Checked both staircase clients: own-edition cover, two-sided sandwich and actual rectangle-union inclusion; no foreign witness or modern module."
