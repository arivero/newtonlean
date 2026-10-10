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
One increasing selection now couples these boundary and area conclusions
with all three unit-ratio comparisons, even when its first lower area is
zero; shrinking but unselected mesh/height pairs can fail graph enclosure.
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

-- The matched theorem derives the coupling rather than asking for it.
example {Q : Type} (area : MagnitudeContent.AreaRules Q) (A : Q)
    (hA : area.HasArea (figure valley z one) A) :
    ∃ indices, MatchedApproximation area valley z one A dyadic errors indices :=
  Principia1687.LemmaIII.corollary1_uniform_graph_matched area valley z one A dyadic errors
    (fun _ => by change (0 : Int)<8; decide) (by decide)
    (fun t _ _ => valley_nonnegative t) valley_uniform hA dyadic_mesh errors_vanish
example {Q : Type} (area : MagnitudeContent.AreaRules Q) (A : Q)
    (hA : area.HasArea (figure valley z one) A) :
    ∃ indices, MatchedApproximation area valley z one A dyadic errors indices :=
  Principia1713.LemmaIII.corollary1_uniform_graph_matched area valley z one A dyadic errors
    (fun _ => by change (0 : Int)<8; decide) (by decide)
    (fun t _ _ => valley_nonnegative t) valley_uniform hA dyadic_mesh errors_vanish

-- Area and edge tails hold at the SAME selected index after a common cutoff.
example {Q : Type} (area : MagnitudeContent.AreaRules Q) (A d : Q)
    (hA : area.HasArea (figure valley z one) A) (hd : area.magnitudes.order.positive d)
    (q : Fraction) (hq : 0<q.num) :
    ∃ indices : Nat → Nat, (∀ m, indices m<indices (m+1)) ∧
      ∃ N, ∀ m, N≤m →
        Encloses area valley z one A (dyadic (indices m))
          (lowerHeights valley (dyadic (indices m)) (errors m))
          (upperHeights valley (dyadic (indices m)) (errors m)) ∧
        area.magnitudes.order.lt A (area.magnitudes.add
          (area.magnitudes.embed (value (dyadic (indices m))
            (lowerHeights valley (dyadic (indices m)) (errors m)))) d) ∧
        (∀ x, RationalBoundary.LowerStaircase (fun t => lower (valley t) (errors m))
          (dyadic (indices m)) x → ∃ y,
            RationalBoundary.CurveTrace (fun t => (t,valley t)) z one y ∧
            Fraction.lt (FiniteEstimates.pointDistance x y) q) := by
  obtain ⟨indices,_,hincrease,_,henclose,_,herrors,hboundary⟩ :=
    Principia1713.LemmaIII.corollary1_uniform_graph_matched area valley z one A dyadic errors
      (fun _ => by change (0 : Int)<8; decide) (by decide)
      (fun t _ _ => valley_nonnegative t) valley_uniform hA dyadic_mesh errors_vanish
  obtain ⟨N,hN⟩ := herrors d hd
  obtain ⟨M,hM⟩ := hboundary.1 q hq
  exact ⟨indices,hincrease,N+M,fun m hm =>
    ⟨henclose m,(hN m (by omega)).1,(hM m (by omega)).1⟩⟩

-- Both ratio conclusions retain the matched family's exact same indices.
example {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes) (A : Q)
    (hA : area.HasArea (figure valley z one) A) :
    ∃ indices, MatchedApproximation area valley z one A dyadic errors indices ∧
      let selected := fun k => dyadic (indices k)
      MagnitudeContent.AreaRatiosOne area.magnitudes
        (fun k => value (selected k) (lowerHeights valley (selected k) (errors k)))
        (fun k => value (selected k) (upperHeights valley (selected k) (errors k))) A :=
  Principia1687.LemmaIII.corollary1_uniform_graph_matched_ratios
    area multiples valley z one quarter A dyadic errors
    (fun _ => by change (0 : Int)<8; decide) (by decide) (by decide) (by decide)
    (fun t _ _ => valley_nonnegative t) valley_uniform hA dyadic_mesh errors_vanish
example {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes) (A : Q)
    (hA : area.HasArea (figure valley z one) A) :
    ∃ indices, MatchedApproximation area valley z one A dyadic errors indices ∧
      let selected := fun k => dyadic (indices k)
      MagnitudeContent.AreaRatiosOne area.magnitudes
        (fun k => value (selected k) (lowerHeights valley (selected k) (errors k)))
        (fun k => value (selected k) (upperHeights valley (selected k) (errors k))) A :=
  Principia1713.LemmaIII.corollary1_uniform_graph_matched_ratios
    area multiples valley z one quarter A dyadic errors
    (fun _ => by change (0 : Int)<8; decide) (by decide) (by decide) (by decide)
    (fun t _ _ => valley_nonnegative t) valley_uniform hA dyadic_mesh errors_vanish

-- All six directed 2:3 comparisons hold after ONE common returned cutoff.
example {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes) (A : Q)
    (hA : area.HasArea (figure valley z one) A) :
    ∃ indices, MatchedApproximation area valley z one A dyadic errors indices ∧
      let M := area.magnitudes
      let L := fun k => M.embed (value (dyadic (indices k))
        (lowerHeights valley (dyadic (indices k)) (errors k)))
      let U := fun k => M.embed (value (dyadic (indices k))
        (upperHeights valley (dyadic (indices k)) (errors k)))
      let compare := fun X Y =>
        M.order.lt (MagnitudeContent.multiple M 2 X) (MagnitudeContent.multiple M 3 Y) ∧
        M.order.lt (MagnitudeContent.multiple M 2 Y) (MagnitudeContent.multiple M 3 X)
      ∃ N, ∀ k, N≤k → compare (L k) (U k) ∧ compare (L k) A ∧ compare (U k) A := by
  obtain ⟨indices,hmatched,hLU,hLA,hUA⟩ :=
    Principia1713.LemmaIII.corollary1_uniform_graph_matched_ratios
      area multiples valley z one quarter A dyadic errors
      (fun _ => by change (0 : Int)<8; decide) (by decide) (by decide) (by decide)
      (fun t _ _ => valley_nonnegative t) valley_uniform hA dyadic_mesh errors_vanish
  obtain ⟨N,hN⟩ := hLU 2 3 (by decide) (by decide)
  obtain ⟨M,hM⟩ := hLA 2 3 (by decide) (by decide)
  obtain ⟨K,hK⟩ := hUA 2 3 (by decide) (by decide)
  exact ⟨indices,hmatched,N+M+K,fun k hk =>
    ⟨hN k (by omega),hM k (by omega),hK k (by omega)⟩⟩

-- Initial lower areas can be zero for ANY selected partition: eps(0)=8.
example (p : Partition z one) :
    Fraction.equiv (value p (lowerHeights valley p (errors 0))) z := by
  classical
  have hheight (i : Nat) (hi : i<p.count) :
      lowerHeights valley p (errors 0) i=z := by
    have hnode := node_bounds p i (by omega)
    have ha := (Fraction.le_iff_toRat _ _).mp hnode.1
    have hb := (Fraction.le_iff_toRat _ _).mp hnode.2
    simp only [z,one,Fraction.toRat_ofInt,Rat.intCast_zero,Rat.intCast_one] at ha hb
    have hnot : ¬ Fraction.le (errors 0) (valley (p.nodes i)) := by
      intro h
      have hR := (Fraction.le_iff_toRat _ _).mp h
      have he : (errors 0).toRat=8 := by decide +kernel
      have hhalf : half.toRat=(1/2 : Rat) := by decide +kernel
      simp only [valley,Fraction.toRat_abs,Fraction.toRat_durationDifference,he,hhalf] at hR
      have hbound : ∀ x : Rat, 0≤x → x≤1 → (x-(1/2 : Rat)).abs<8 := by
        intro x hx0 hx1
        rw [Rat.abs]
        split <;> grind
      exact Rat.not_lt.mpr hR (hbound _ ha hb)
    simp only [lowerHeights,lower,hnot,ite_false]
    rfl
  let f := fun i => Fraction.mul (width p i) (lowerHeights valley p (errors 0) i)
  have hsum (n : Nat) (hn : n≤p.count) : (sum f n).num=0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hterm : (f n).num=0 := by
        dsimp only [f]
        rw [hheight n (by omega)]
        exact Int.mul_zero _
      change (sum f n).num*(f n).den+(f n).num*(sum f n).den=0
      rw [ih (by omega),hterm]
      simp only [Int.zero_mul,Int.add_zero]
  change (sum f p.count).num*1=0*(sum f p.count).den
  rw [hsum p.count (Nat.le_refl _)]
  simp only [Int.zero_mul]

private def tooSmall (m : Nat) : Fraction := duration quarter m
example : Exhaustion.VanishingDifference Fraction.magnitudes tooSmall := by
  intro q hq
  exact duration_eventually_small quarter q (by decide) hq
example : ¬ Exhaustion.VanishingDifference Fraction.magnitudes (fun _ => quarter) := by
  intro h
  obtain ⟨N,hN⟩ := h quarter (by change (0 : Int)<1; decide)
  exact Fraction.magnitudes.lt_irrefl quarter (hN N (Nat.le_refl _))

-- Mesh and height errors both vanish, yet their unselected pairing fails
-- upper enclosure at EVERY level, on the positive identity graph.
example (m : Nat) : ∃ x, figure id z one x ∧
    ¬ RectangleContent.strips (dyadic m)
      (upperHeights id (dyadic m) (tooSmall m)) (dyadic m).count x := by
  let t := duration one (m+1)
  have hp : 0<(2 : Int)^m := Int.pow_pos (by decide)
  have ht : Fraction.le t one := by
    simp only [Fraction.le,t,one,Fraction.ofInt,duration,Int.one_mul]
    have := two_pow_ge_succ (m+1)
    omega
  refine ⟨(t,t),⟨?_,ht,?_,Fraction.magnitudes.le_refl _⟩,?_⟩
  · simp only [Fraction.le,z,t,one,Fraction.ofInt,duration,Int.zero_mul,Int.mul_one]
    decide
  · change (0 : Int)≤1
    decide
  · rintro ⟨i,_,hl,_,_,hy⟩
    have hleft : (i : Int)*2≤1 := by
      have h := hl
      dsimp only [Fraction.le,dyadic,countTime,Fraction.mul,Fraction.ofInt,one,duration,t] at h
      simp only [Int.one_mul,Int.mul_one] at h
      rw [Int.pow_succ] at h
      have h' : ((i : Int)*2)*2^m≤1*2^m := by
        calc
          ((i : Int)*2)*2^m = (i : Int)*(2^m*2) := by ac_rfl
          _ ≤ 1*2^m := by simpa only [Int.one_mul] using h
      exact Int.le_of_mul_le_mul_right h' hp
    have hi : i=0 := by omega
    subst i
    dsimp only [Fraction.le,upperHeights,upper,id,dyadic,countTime,Fraction.mul,
      Fraction.add,Fraction.ofInt,one,duration,tooSmall,quarter,t] at hy
    simp only [Int.natCast_zero,Int.zero_mul,Int.zero_add,Int.one_mul,Int.pow_succ] at hy
    have h' : ((4 : Int)*2^m)*2^m≤(2*2^m)*2^m := by
      calc
        ((4 : Int)*2^m)*2^m = 2^m*(4*2^m) := by ac_rfl
        _ ≤ 2^m*(2^m*2) := hy
        _ = (2*2^m)*2^m := by ac_rfl
    have hcancel := Int.le_of_mul_le_mul_right (Int.le_of_mul_le_mul_right h' hp) hp
    omega

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
      (`Principia1713.LemmaIII.corollary1_uniform_graph_staircases,"Principia1687."),
      (`Principia1687.LemmaIII.corollary1_uniform_graph_matched,"Principia1713."),
      (`Principia1713.LemmaIII.corollary1_uniform_graph_matched,"Principia1687.")] do
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
    if root.getString! == "corollary1_uniform_graph_matched" then
      for dependency in #[
          `NewtonLimitDynamics.Polygon.UniformRectangles.matched_approximation,
          `NewtonLimitDynamics.Polygon.UniformRectangles.fine_rectangles,
          `NewtonLimitDynamics.Polygon.UniformRectangles.rectangle_enclosure,
          `NewtonLimitDynamics.Polygon.RectangleContent.strips_area,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.errors_vanish,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.rational_exhaustion,
          `NewtonLimitDynamics.Polygon.HarmonicTimeRealization.factor_delta_weak] do
        unless used.contains dependency do throwError "{root} omits matched-family step {dependency}"
  logInfo "Checked two free-staircase and two matched-family clients: shrinking perturbations, actual rectangle membership and simultaneous derived area/error/boundary limits; no foreign witness/modern module."
  for (edition,foreign) in #[(`Principia1687,"Principia1713."),(`Principia1713,"Principia1687.")] do
    for root in #[edition ++ `LemmaII.uniform_graph_matched_area_ratios,
        edition ++ `LemmaIII.uniform_graph_matched_area_ratios,
        edition ++ `LemmaIII.corollary1_uniform_graph_matched_ratios] do
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
          `NewtonLimitDynamics.Polygon.UniformRectangles.rectangle_sequence_ratios,
          `NewtonLimitDynamics.Polygon.UniformRectangles.positive_rectangle,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.AreaRules.monotone,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.ratios_one_of_enclosure,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.finite_ratios_of_enclosure,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.multiple_monotone,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules.embed_lt] do
        unless used.contains dependency do throwError "{root} omits {dependency}"
      if root.toString.startsWith (edition.toString ++ ".LemmaIII.") then
        unless used.contains (edition ++ `LemmaII.uniform_graph_matched_area_ratios) do
          throwError "{root} omits its own Lemma II"
      if root.getString! == "corollary1_uniform_graph_matched_ratios" then
        for dependency in #[edition ++ `LemmaIII.uniform_graph_matched_area_ratios,
            edition ++ `LemmaIII.corollary1_uniform_graph_matched,
            `NewtonLimitDynamics.Polygon.UniformRectangles.matched_approximation,
            `NewtonLimitDynamics.Polygon.UniformRectangles.fine_rectangles,
            `NewtonLimitDynamics.Polygon.RectangleContent.strips_area,
            `NewtonLimitDynamics.Polygon.UniformRectangles.staircase_approaches,
            `NewtonLimitDynamics.Polygon.MagnitudeContent.errors_vanish] do
          unless used.contains dependency do throwError "{root} omits matched-family step {dependency}"
      for dependency in used do
        let name := ((privateToUserName? dependency).getD dependency).toString
        if #[foreign,"DeMotu1684."].any (fun libraryPrefix => name.startsWith libraryPrefix) then
          throwError "{root} uses foreign witness {dependency}"
        if let some idx := env.getModuleIdxFor? dependency then
          if env.header.moduleNames[idx]!.toString.startsWith "ModernLib" then
            throwError "{root} uses modern module through {dependency}"
  logInfo "Checked six matched-family ratio clients: contained positive rectangle, eventual lower bracket, finite multiple comparisons and own-edition II-to-III-to-Corollary-I chains; no foreign witness or modern module."
