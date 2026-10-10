import NewtonLimitDynamics.Historical.LemmaIII.CorollaryI
import Lean

/-! Nonmonotone rectangular-exhaustion controls. The graph |t-1/2| on [0,1]
decreases to zero and rises again. Its continuity and actual shrinking dyadic
partitions are proved here; the arbitrary assigned curved area and partial
area convention remain supplied. Finite controls exercise lower-height
clipping and reject the old endpoint lower rectangle on this graph. Compiled
traversal checks all six edition-local clients and rejects foreign witnesses
and modern support. Four further clients give all three multiple-ratio
comparisons for every sufficiently small height tolerance. An actual dyadic
tail checks that their mesh cutoffs are usable; zero and fixed 1:2 brackets
are rejected. Nonmonotone free-step traces now approach the graph in both
directions while remaining in their actual rectangle unions; falling/rising
joins and a nonvanishing-height falsifier exercise that separate argument.
These controls share the rational arithmetic and kernel;
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
      Fraction.add,Int.add_mul,Int.neg_mul,Int.neg_add]
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
    (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.natCast_one])

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

-- A concrete interior rectangle remains below the decreasing valley branch.
-- Its area and the n=2 construction constants are exact rational values.
private def edge : Fraction := ⟨9,32,by decide⟩
private def eighth : Fraction := ⟨1,8,by decide⟩
private def rectArea : Fraction := Fraction.mul (durationDifference quarter edge) eighth
example : Fraction.equiv rectArea ⟨1,256,by decide⟩ := by decide
example : Fraction.equiv rectArea.half ⟨1,512,by decide⟩ := by decide
example : rectArea.toRat / (2*(2 : Rat)+2) = (1 : Rat)/1536 := by decide +kernel
example : (rectArea.toRat / (2*(2 : Rat)+2)) / (2*(1 : Rat)+1) =
    (1 : Rat)/4608 := by decide +kernel
example (x : Point) (hx : rectangle quarter edge eighth x) : figure valley z one x := by
  rcases hx with ⟨hl,hr,hzero,hy⟩
  have hleft := (Fraction.le_iff_toRat _ _).mp hl
  have hright := (Fraction.le_iff_toRat _ _).mp hr
  have hheight := (Fraction.le_iff_toRat _ _).mp hy
  change (1/4 : Rat)≤x.1.toRat at hleft
  change x.1.toRat≤(9/32 : Rat) at hright
  change x.2.toRat≤(1/8 : Rat) at hheight
  refine ⟨(Fraction.le_iff_toRat _ _).mpr ?_,
    (Fraction.le_iff_toRat _ _).mpr ?_,hzero,(Fraction.le_iff_toRat _ _).mpr ?_⟩
  · simpa only [z,Fraction.toRat_ofInt,Rat.intCast_zero] using
      (show (0 : Rat)≤x.1.toRat by grind)
  · simpa only [one,Fraction.toRat_ofInt,Rat.intCast_one] using
      (show x.1.toRat≤(1 : Rat) by grind)
  · simp only [valley,Fraction.toRat_abs,Fraction.toRat_durationDifference]
    change x.2.toRat≤(x.1.toRat-(1/2 : Rat)).abs
    rw [Rat.abs_of_nonpos (by grind)]
    grind

-- Positive ordinate is not inferred at the valley's zero.
example : ¬ 0<(valley half).num := by decide

-- All four edition-local clients admit the interior-positive valley.
example {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes) (A : Q)
    (hA : area.HasArea (figure valley z one) A) : RatiosExhaust area valley z one A :=
  Principia1687.LemmaII.uniform_graph_assigned_magnitude_ratios area multiples
    valley z one quarter A (by decide) (by decide) (by decide)
    (fun t _ _ => valley_nonnegative t) valley_uniform hA
example {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes) (A : Q)
    (hA : area.HasArea (figure valley z one) A) : RatiosExhaust area valley z one A :=
  Principia1713.LemmaII.uniform_graph_assigned_magnitude_ratios area multiples
    valley z one quarter A (by decide) (by decide) (by decide)
    (fun t _ _ => valley_nonnegative t) valley_uniform hA
example {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes) (A : Q)
    (hA : area.HasArea (figure valley z one) A) : RatiosExhaust area valley z one A :=
  Principia1687.LemmaIII.uniform_graph_assigned_magnitude_ratios area multiples
    valley z one quarter A (by decide) (by decide) (by decide)
    (fun t _ _ => valley_nonnegative t) valley_uniform hA
example {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes) (A : Q)
    (hA : area.HasArea (figure valley z one) A) : RatiosExhaust area valley z one A :=
  Principia1713.LemmaIII.uniform_graph_assigned_magnitude_ratios area multiples
    valley z one quarter A (by decide) (by decide) (by decide)
    (fun t _ _ => valley_nonnegative t) valley_uniform hA

-- The cutoff works for every smaller positive height tolerance, and each
-- resulting mesh threshold has actual dyadic partitions on a returned tail.
example {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes) (A : Q)
    (hA : area.HasArea (figure valley z one) A) :
    ∃ cutoff : Fraction, 0<cutoff.num ∧ ∀ eps : Fraction,
      0<eps.num → Fraction.le eps cutoff → ∃ N, ∀ k, N≤k →
        ∃ L U : Fraction, Encloses area valley z one A (dyadic k)
          (lowerHeights valley (dyadic k) eps) (upperHeights valley (dyadic k) eps) ∧
          L=value (dyadic k) (lowerHeights valley (dyadic k) eps) ∧
          U=value (dyadic k) (upperHeights valley (dyadic k) eps) ∧
          (let M := area.magnitudes
           let compare := fun X Y => M.order.lt (MagnitudeContent.multiple M 2 X)
             (MagnitudeContent.multiple M 3 Y) ∧
             M.order.lt (MagnitudeContent.multiple M 2 Y) (MagnitudeContent.multiple M 3 X)
           compare (M.embed L) (M.embed U) ∧ compare (M.embed L) A ∧ compare (M.embed U) A) := by
  obtain ⟨cutoff,hcutoff,hsmall⟩ :=
    Principia1713.LemmaIII.uniform_graph_assigned_magnitude_ratios area multiples
      valley z one quarter A (by decide) (by decide) (by decide)
      (fun t _ _ => valley_nonnegative t) valley_uniform hA 2 3 (by decide) (by decide)
  refine ⟨cutoff,hcutoff,fun eps heps hcut => ?_⟩
  obtain ⟨delta,hdelta,hfine⟩ := hsmall eps heps hcut
  obtain ⟨N,hN⟩ := dyadic_mesh delta hdelta
  refine ⟨N,fun k hk => ?_⟩
  obtain ⟨henclose,hcompare⟩ := hfine (dyadic k) (hN k hk)
  let L := value (dyadic k) (lowerHeights valley (dyadic k) eps)
  let U := value (dyadic k) (upperHeights valley (dyadic k) eps)
  have hAenc := henclose.2.2.2.2
  have hLU := area.magnitudes.order.le_trans hAenc.1 hAenc.2
  have hLenc := And.intro (area.magnitudes.order.le_refl (area.magnitudes.embed L)) hLU
  have hUenc := And.intro hLU (area.magnitudes.order.le_refl (area.magnitudes.embed U))
  exact ⟨L,U,henclose,rfl,rfl,hcompare _ _ hLenc hUenc,
    hcompare _ _ hLenc hAenc,hcompare _ _ hUenc hAenc⟩

-- Corrupted comparisons: zero and constant 1:2 brackets cannot pass.
example : ¬ MagnitudeContent.BracketComparisons MagnitudeContent.rational 2 3 z z := by
  intro h
  have hh := h z z ⟨Fraction.magnitudes.le_refl _,Fraction.magnitudes.le_refl _⟩
    ⟨Fraction.magnitudes.le_refl _,Fraction.magnitudes.le_refl _⟩
  exact (by decide : ¬ Fraction.lt (MagnitudeContent.multiple MagnitudeContent.rational 2 z)
    (MagnitudeContent.multiple MagnitudeContent.rational 3 z)) hh.1
example : ¬ MagnitudeContent.BracketComparisons MagnitudeContent.rational 2 3
    one (Fraction.ofInt 2) := by
  intro h
  have hh := h one (Fraction.ofInt 2)
    ⟨Fraction.magnitudes.le_refl _,by change Fraction.le one (Fraction.ofInt 2); decide⟩
    ⟨by change Fraction.le one (Fraction.ofInt 2); decide,Fraction.magnitudes.le_refl _⟩
  exact (by decide : ¬ Fraction.lt
    (MagnitudeContent.multiple MagnitudeContent.rational 2 (Fraction.ofInt 2))
    (MagnitudeContent.multiple MagnitudeContent.rational 3 one)) hh.2

private def errors (m : Nat) : Fraction := duration (Fraction.ofInt 8) m
private theorem errors_vanish : Exhaustion.VanishingDifference Fraction.magnitudes errors := by
  intro eps heps
  exact duration_eventually_small (Fraction.ofInt 8) eps (by decide) heps

-- Both witnesses accept actual shrinking partitions and height tolerances;
-- no area assignment or monotonicity is supplied to the boundary theorem.
example : StaircaseApproximation valley z one dyadic errors :=
  Principia1687.LemmaIII.corollary1_uniform_graph_staircases valley z one dyadic errors
    (fun _ => by change (0 : Int)≤8; decide) (fun t _ _ => valley_nonnegative t)
    valley_uniform dyadic_mesh errors_vanish
example : StaircaseApproximation valley z one dyadic errors :=
  Principia1713.LemmaIII.corollary1_uniform_graph_staircases valley z one dyadic errors
    (fun _ => by change (0 : Int)≤8; decide) (fun t _ _ => valley_nonnegative t)
    valley_uniform dyadic_mesh errors_vanish

-- Falling joins must select the taller LEFT rectangle; rising joins select
-- the taller RIGHT one. The helper handles both without ordering the graph.
example : RationalBoundary.LowerStaircase valley (dyadic 1) (half,quarter) :=
  ⟨0,by decide,Or.inr ⟨by decide,by decide,Or.inr (by decide)⟩⟩
example : RectangleContent.strips (dyadic 1) (fun i => valley ((dyadic 1).nodes i))
    (dyadic 1).count (half,quarter) :=
  staircase_in_strips valley (dyadic 1) (fun i _ => valley_nonnegative _) _
    ⟨0,by decide,Or.inr ⟨by decide,by decide,Or.inr (by decide)⟩⟩
example : ¬ rectangle ((dyadic 1).nodes 1) ((dyadic 1).nodes 2)
    (valley ((dyadic 1).nodes 1)) (half,quarter) := by
  rintro ⟨_,_,_,h⟩
  exact (by decide : ¬ Fraction.le quarter (valley ((dyadic 1).nodes 1))) h
example : RectangleContent.strips (dyadic 2) (fun i => valley ((dyadic 2).nodes i))
    (dyadic 2).count ((⟨3,4,by decide⟩ : Fraction),eighth) :=
  staircase_in_strips valley (dyadic 2) (fun i _ => valley_nonnegative _) _
    ⟨2,by decide,Or.inr ⟨by decide,by decide,Or.inl (by decide)⟩⟩

-- A fixed positive height error does not approach even a flat graph.
example : ¬ RationalBoundary.Approaches
    (fun m => RationalBoundary.LowerStaircase (fun _ => one) (dyadic m))
    (RationalBoundary.CurveTrace (fun t => (t,z)) z one) := by
  intro h
  obtain ⟨N,hN⟩ := h half (by decide)
  let s : Point := ((dyadic N).nodes 0,one)
  have hs : RationalBoundary.LowerStaircase (fun _ => one) (dyadic N) s :=
    RationalBoundary.nodes_in_lower_staircase _ _ _
      ⟨0,(dyadic N).positive_count,Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  obtain ⟨y,⟨t,_,_,hy⟩,hsmall⟩ := (hN N (Nat.le_refl _)).1 s hs
  have hyR := (Fraction.equiv_iff_toRat _ _).mp hy.2
  change y.2.toRat=z.toRat at hyR
  rw [z,Fraction.toRat_ofInt,Rat.intCast_zero] at hyR
  change Fraction.lt (Fraction.add (durationDifference y.1 ((dyadic N).nodes 0)).abs
    (durationDifference y.2 one).abs) half at hsmall
  have hb := (Fraction.lt_iff_toRat _ _).mp hsmall
  simp only [Fraction.toRat_add,Fraction.toRat_abs,Fraction.toRat_durationDifference,
    one,Fraction.toRat_ofInt,Rat.intCast_one,hyR] at hb
  have hhalf : half.toRat=(1/2 : Rat) := by decide +kernel
  have hsub : (1 : Rat)-0=1 := by decide +kernel
  rw [hhalf,hsub] at hb
  have hn := Rat.abs_nonneg (x:=((dyadic N).nodes 0).toRat-y.1.toRat)
  have hunit : (1 : Rat).abs=1 := by decide +kernel
  rw [hunit] at hb
  have hbound : (1 : Rat)≤(((dyadic N).nodes 0).toRat-y.1.toRat).abs+1 := by
    grind only
  exact Rat.not_lt.mpr
    (Rat.le_trans (by decide +kernel : (1/2 : Rat)≤1) hbound) hb

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
        if #[foreign,"DeMotu1684."].any (fun rootName => name.startsWith rootName) then
          throwError "{root} uses foreign witness {dependency}"
        if let some idx := env.getModuleIdxFor? dependency then
          if env.header.moduleNames[idx]!.toString.startsWith "ModernLib" then
            throwError "{root} uses modern module through {dependency}"
  logInfo "Checked six nonmonotone exhaustion clients: own-edition chains, finite rectangle areas, sum gap, classical halving and error comparison; no foreign witness or modern module."
  for (edition,foreign) in #[(`Principia1687,"Principia1713."),(`Principia1713,"Principia1687.")] do
    for root in #[edition ++ `LemmaII.uniform_graph_assigned_magnitude_ratios,
        edition ++ `LemmaIII.uniform_graph_assigned_magnitude_ratios] do
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
      let chain := if root.toString.startsWith (edition.toString ++ ".LemmaIII.") then
        #[edition ++ `LemmaII.uniform_graph_assigned_magnitude_ratios] else #[]
      for dependency in chain ++ #[
          `NewtonLimitDynamics.Polygon.UniformRectangles.ratios_exhaustion,
          `NewtonLimitDynamics.Polygon.UniformRectangles.positive_rectangle,
          `NewtonLimitDynamics.Polygon.UniformRectangles.fine_rectangles,
          `NewtonLimitDynamics.Polygon.UniformRectangles.rectangle_enclosure,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.finite_ratios_of_enclosure,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.multiple_monotone,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.multiple_embed,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules.embed_lt,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules.add_le_add_left] do
        unless used.contains dependency do throwError "{root} omits {dependency}"
      for dependency in used do
        let name := ((privateToUserName? dependency).getD dependency).toString
        if #[foreign,"DeMotu1684."].any (fun rootName => name.startsWith rootName) then
          throwError "{root} uses foreign witness {dependency}"
        if let some idx := env.getModuleIdxFor? dependency then
          if env.header.moduleNames[idx]!.toString.startsWith "ModernLib" then
            throwError "{root} uses modern module through {dependency}"
  logInfo "Checked four nonmonotone multiple-ratio clients: constructed positive rectangle, fine rectangle areas, finite comparison and own-edition II-to-III chain; no foreign witness or modern module."
  for (root,foreign) in #[(
      `Principia1687.LemmaIII.corollary1_uniform_graph_staircases,"Principia1713."),
      (`Principia1713.LemmaIII.corollary1_uniform_graph_staircases,"Principia1687.")] do
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
    for dependency in #[
        `NewtonLimitDynamics.Polygon.UniformRectangles.staircase_approaches,
        `NewtonLimitDynamics.Polygon.UniformRectangles.staircase_in_strips,
        `NewtonLimitDynamics.Polygon.RationalBoundary.perturbed_trace_approaches,
        `NewtonLimitDynamics.Polygon.RationalBoundary.nodes_in_lower_staircase,
        `NewtonLimitDynamics.Polygon.RationalBoundary.lower_staircase_in_rectangles,
        `NewtonLimitDynamics.Polygon.SupportingTangents.rectangle_distance_bound] do
      unless used.contains dependency do throwError "{root} omits {dependency}"
    for dependency in used do
      let name := ((privateToUserName? dependency).getD dependency).toString
      if #[foreign,"DeMotu1684."].any (fun libraryPrefix => name.startsWith libraryPrefix) then
        throwError "{root} uses foreign witness {dependency}"
      if let some idx := env.getModuleIdxFor? dependency then
        if env.header.moduleNames[idx]!.toString.startsWith "ModernLib" then
          throwError "{root} uses modern module through {dependency}"
    unless used.toArray.any (fun n => ((privateToUserName? n).getD n) ==
        `NewtonLimitDynamics.Polygon.UniformRectangles.height_distances) do
      throwError "{root} omits the derived height-error bounds"
  logInfo "Checked two nonmonotone free-staircase clients: shrinking node perturbations, actual rectangle membership and no foreign witness/modern module."
