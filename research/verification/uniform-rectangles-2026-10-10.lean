import NewtonLimitDynamics.Historical.LemmaIII.CorollaryI
import Lean

/-! Nonmonotone rectangular-exhaustion controls. The graph |t-1/2| on [0,1]
decreases to zero and rises again. Its continuity and actual shrinking dyadic
partitions are proved here; the arbitrary assigned curved area and partial
area convention remain supplied. Finite controls exercise lower-height
clipping and reject the old endpoint lower rectangle on this graph. Compiled
traversal checks all six edition-local clients and rejects foreign witnesses
and modern support. These controls share the rational arithmetic and kernel;
they construct neither general curved areas nor a nonrational area model. -/

namespace NewtonLimitDynamics.Polygon.UniformRectangleControls
open NewtonLimitDynamics TimeSubdivision MonotoneRectangles UniformRectangles
open HarmonicTimeComparison HarmonicTimeRealization HarmonicDyadic PolygonFanArea

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den≤b.num*a.den))
local instance (a b : Fraction) : Decidable (Fraction.lt a b) :=
  inferInstanceAs (Decidable (a.num*b.den<b.num*a.den))

private def z : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1
private def half : Fraction := ⟨1,2,by decide⟩
private def quarter : Fraction := ⟨1,4,by decide⟩
private def valley (t : Fraction) : Fraction := (durationDifference half t).abs

private theorem valley_nonnegative (t : Fraction) : 0≤(valley t).num :=
  Fraction.abs_num_nonnegative _

private theorem valley_lipschitz (s t : Fraction) :
    Fraction.le (durationDifference (valley s) (valley t)).abs
      (durationDifference s t).abs := by
  have he : Fraction.equiv
      (durationDifference (durationDifference half s) (durationDifference half t))
      (durationDifference s t) := by
    simp only [durationDifference,HarmonicStability.negF,Fraction.equiv,
      Fraction.add,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.neg_add]
    ac_nf
    omega
  exact Fraction.le_equiv_right (duration_abs_reverse _ _) (Fraction.abs_equiv he)

private theorem valley_uniform : RationalBoundary.UniformOn (fun t => (t,valley t)) z one := by
  intro eps heps
  refine ⟨eps.half.half,heps,?_⟩
  intro s t _ _ _ _ hst
  have hd : Fraction.equiv (FiniteEstimates.pointDistance (s,valley s) (t,valley t))
      (Fraction.add (durationDifference s t).abs (durationDifference (valley s) (valley t)).abs) :=
    Fraction.equiv_trans (FiniteEstimates.pointDistance_symm _ _) (Fraction.equiv_refl _)
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_equiv_left hd (Fraction.le_equiv_right
      (Fraction.add_le_add hst (Fraction.magnitudes.le_trans (valley_lipschitz s t) hst))
      (Fraction.half_add_self eps.half))) (Fraction.half_lt eps heps)

-- The graph is outside the earlier increasing-graph scope.
example : ¬ MonotoneOn valley z one := by
  intro h
  exact (by decide : ¬ Fraction.le (valley z) (valley half))
    (h z half (by decide) (by decide) (by decide))

-- Clipping is essential at a zero and ordinary subtraction applies above eps.
example : Fraction.equiv (lower z quarter) z := by
  classical
  simp only [lower,show ¬ Fraction.le quarter z by decide,ite_false]
  decide
example : Fraction.equiv (lower half quarter) quarter := by
  classical
  simp only [lower,show Fraction.le quarter half by decide,ite_true]
  decide
example : Fraction.equiv (upper z quarter) quarter := by decide

private theorem grid_width (m i : Nat) :
    Fraction.equiv (durationDifference (countTime one m i) (countTime one m (i+1)))
      (duration one m) :=
  Fraction.equiv_trans (countTime_difference one m i 1)
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
      (Fraction.nonnegative_equiv (grid_width m i) (by change (0 : Int)≤1; decide))

private theorem dyadic_mesh : Exhaustion.VanishingDifference Fraction.magnitudes
    (fun m => maxWidth (dyadic m)) := by
  intro eps heps
  obtain ⟨N,hN⟩ := duration_eventually_small one eps (by decide) heps
  exact ⟨N,fun m hm => Fraction.magnitudes.lt_of_le_lt
    ((maxWidth_bounds (dyadic m)).2 _ (fun i _ => Fraction.le_of_equiv (grid_width m i)))
    (hN m hm)⟩

-- The old endpoint lower rectangle contains a point above the valley.
example : lowerFigure valley (dyadic 0) (half,quarter) :=
  ⟨0,by decide,by decide,by decide,by decide,by decide⟩
example : ¬ figure valley z one (half,quarter) := by
  rintro ⟨_,_,_,hy⟩
  exact (by decide : ¬ Fraction.le quarter (valley half)) hy

-- All six clients accept the nonmonotone graph with arbitrary supplied A : Q.
example {Q : Type} (area : MagnitudeContent.AreaRules Q) (A : Q)
    (hA : area.HasArea (figure valley z one) A) : Exhausts area valley z one A :=
  Principia1687.LemmaII.uniform_graph_rectangle_exhaustion area valley z one A
    (by decide) (fun t _ _ => valley_nonnegative t) valley_uniform hA
example {Q : Type} (area : MagnitudeContent.AreaRules Q) (A : Q)
    (hA : area.HasArea (figure valley z one) A) : Exhausts area valley z one A :=
  Principia1713.LemmaII.uniform_graph_rectangle_exhaustion area valley z one A
    (by decide) (fun t _ _ => valley_nonnegative t) valley_uniform hA
example {Q : Type} (area : MagnitudeContent.AreaRules Q) (A : Q)
    (hA : area.HasArea (figure valley z one) A) : Exhausts area valley z one A :=
  Principia1687.LemmaIII.uniform_graph_rectangle_exhaustion area valley z one A
    (by decide) (fun t _ _ => valley_nonnegative t) valley_uniform hA
example {Q : Type} (area : MagnitudeContent.AreaRules Q) (A : Q)
    (hA : area.HasArea (figure valley z one) A) : Exhausts area valley z one A :=
  Principia1713.LemmaIII.uniform_graph_rectangle_exhaustion area valley z one A
    (by decide) (fun t _ _ => valley_nonnegative t) valley_uniform hA
example {Q : Type} (area : MagnitudeContent.AreaRules Q) (A : Q)
    (hA : area.HasArea (figure valley z one) A) : Exhausts area valley z one A :=
  Principia1687.LemmaIII.corollary1_uniform_graph_area_exhaustion area valley z one A
    (by decide) (fun t _ _ => valley_nonnegative t) valley_uniform hA
example {Q : Type} (area : MagnitudeContent.AreaRules Q) (A : Q)
    (hA : area.HasArea (figure valley z one) A) : Exhausts area valley z one A :=
  Principia1713.LemmaIII.corollary1_uniform_graph_area_exhaustion area valley z one A
    (by decide) (fun t _ _ => valley_nonnegative t) valley_uniform hA

-- A returned delta has actual fine partitions, and both errors hold on their tail.
example {Q : Type} (area : MagnitudeContent.AreaRules Q) (A d : Q)
    (hA : area.HasArea (figure valley z one) A) (hd : area.magnitudes.order.positive d) :
    ∃ eps : Fraction, 0<eps.num ∧ ∃ N, ∀ m, N≤m →
      Encloses area valley z one A (dyadic m)
        (lowerHeights valley (dyadic m) eps) (upperHeights valley (dyadic m) eps) ∧
      area.magnitudes.order.lt A (area.magnitudes.add
        (area.magnitudes.embed (value (dyadic m) (lowerHeights valley (dyadic m) eps))) d) ∧
      area.magnitudes.order.lt
        (area.magnitudes.embed (value (dyadic m) (upperHeights valley (dyadic m) eps)))
        (area.magnitudes.add A d) := by
  obtain ⟨eps,delta,heps,hdelta,hfine⟩ :=
    Principia1713.LemmaIII.corollary1_uniform_graph_area_exhaustion area valley z one A
      (by decide) (fun t _ _ => valley_nonnegative t) valley_uniform hA d hd
  obtain ⟨N,hN⟩ := dyadic_mesh delta hdelta
  exact ⟨eps,heps,N,fun m hm => ⟨(hfine _ (hN m hm)).1,(hfine _ (hN m hm)).2.2⟩⟩

end NewtonLimitDynamics.Polygon.UniformRectangleControls

open Lean in
run_elab do
  let env ← getEnv
  for (edition,foreign) in #[(`Principia1687,"Principia1713."),(`Principia1713,"Principia1687.")] do
    for (root,required) in #[
        (edition ++ `LemmaII.uniform_graph_rectangle_exhaustion,#[]),
        (edition ++ `LemmaIII.uniform_graph_rectangle_exhaustion,
          #[edition ++ `LemmaII.uniform_graph_rectangle_exhaustion]),
        (edition ++ `LemmaIII.corollary1_uniform_graph_area_exhaustion,
          #[edition ++ `LemmaII.uniform_graph_rectangle_exhaustion,
            edition ++ `LemmaIII.uniform_graph_rectangle_exhaustion])
      ] do
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
      for dependency in required ++ #[
          `NewtonLimitDynamics.Polygon.UniformRectangles.exhaustion,
          `NewtonLimitDynamics.Polygon.UniformRectangles.fine_rectangles,
          `NewtonLimitDynamics.Polygon.UniformRectangles.rectangle_enclosure,
          `NewtonLimitDynamics.Polygon.RectangleContent.strips_area,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.enclosure_errors_lt,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.Rules.unit_halves_exhaust] do
        unless used.contains dependency do throwError "{root} omits {dependency}"
      unless used.toArray.any (fun n => ((privateToUserName? n).getD n) ==
          `NewtonLimitDynamics.Polygon.UniformRectangles.value_gap_bound) do
        throwError "{root} omits the finite sum gap bound"
      for dependency in used do
        let name := ((privateToUserName? dependency).getD dependency).toString
        if #[foreign,"DeMotu1684."].any name.startsWith then
          throwError "{root} uses foreign witness {dependency}"
        if let some idx := env.getModuleIdxFor? dependency then
          if env.header.moduleNames[idx]!.toString.startsWith "ModernLib" then
            throwError "{root} uses modern module through {dependency}"
  logInfo "Checked six nonmonotone exhaustion clients: own-edition chains, finite rectangle areas, sum gap, classical halving and error comparison; no foreign witness or modern module."
