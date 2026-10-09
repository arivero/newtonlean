import NewtonLimitDynamics.Historical.LemmaIII.CorollaryI
import Lean

/-! Magnitude-area controls. Actual nonzero dyadic identity-graph partitions
realize geometry/mesh premises; the curved area and partial convention remain
explicit. A zero-height patch needs no curved-area assignment beyond the
rectangle rule. Constant-gap and lexicographic infinitesimal controls reject
false convergence and the omission of the classical halving condition.
These checks share the rational definitions and kernel; they construct neither
a nonrational area model nor an area convention for arbitrary curved figures. -/

namespace NewtonLimitDynamics.Polygon.MagnitudeControls
open NewtonLimitDynamics TimeSubdivision MonotoneRectangles MagnitudeContent
open HarmonicTimeComparison HarmonicTimeRealization HarmonicDyadic

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den≤b.num*a.den))
local instance (a b : Fraction) : Decidable (Fraction.lt a b) :=
  inferInstanceAs (Decidable (a.num*b.den<b.num*a.den))

private def z : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1
private def half : Fraction := ⟨1,2,by decide⟩
private def quarter : Fraction := ⟨1,4,by decide⟩

-- The supplied magnitude interface is inhabited; the area relation is separate.
example : Nonempty (Rules Fraction) := ⟨rational⟩
example (area : RectangleContent.AreaRules) (U : Point → Prop) (A : Fraction) :
    (rationalAreas (ofRationalAreas area)).HasArea U A ↔ area.HasArea U A := Iff.rfl

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

private theorem unit_mesh : Exhaustion.VanishingDifference Fraction.magnitudes
    (duration one) := by
  intro eps heps
  exact duration_eventually_small one eps (by decide) heps

private theorem dyadic_mesh : Exhaustion.VanishingDifference Fraction.magnitudes
    (fun m => maxWidth (dyadic m)) := by
  intro eps heps
  obtain ⟨N,hN⟩ := unit_mesh eps heps
  exact ⟨N,fun m hm => Fraction.magnitudes.lt_of_le_lt
    ((maxWidth_bounds (dyadic m)).2 _ (fun i _ => Fraction.le_of_equiv (grid_width m i)))
    (hN m hm)⟩

-- No rational-image hypothesis on A: the geometry and mesh are constructed.
example {Q : Type} (area : AreaRules Q) (A : Q)
    (hA : area.HasArea (figure id z one) A) :
    Approximates area id z one A dyadic ∧
      ∀ D : Q, Exhaustion.TerminalLower area.magnitudes.order
        (fun m => area.magnitudes.embed (gap id (dyadic m))) D →
        ¬ area.magnitudes.order.positive D :=
  Principia1687.LemmaII.equal_width_magnitude_approximation area id z one A dyadic
    (fun _ _ _ h _ => h) (by decide) hA (duration one) (fun m i _ => grid_width m i) unit_mesh
example {Q : Type} (area : AreaRules Q) (A : Q)
    (hA : area.HasArea (figure id z one) A) :
    Approximates area id z one A dyadic :=
  (Principia1713.LemmaII.equal_width_magnitude_approximation area id z one A dyadic
    (fun _ _ _ h _ => h) (by decide) hA (duration one) (fun m i _ => grid_width m i) unit_mesh).1
example {Q : Type} (area : AreaRules Q) (A : Q)
    (hA : area.HasArea (figure id z one) A) :
    Approximates area id z one A dyadic :=
  Principia1687.LemmaIII.corollary1_magnitude_area_approximation area id z one A dyadic
    (fun _ _ _ h _ => h) (by decide) hA dyadic_mesh
example {Q : Type} (area : AreaRules Q) (A : Q)
    (hA : area.HasArea (figure id z one) A) :
    Approximates area id z one A dyadic :=
  Principia1713.LemmaIII.corollary1_magnitude_area_approximation area id z one A dyadic
    (fun _ _ _ h _ => h) (by decide) hA dyadic_mesh

-- The legacy rational-area specialization still accepts unreduced displays.
example (area : RectangleContent.AreaRules)
    (hA : area.HasArea (figure id z one) (⟨2,4,by decide⟩ : Fraction)) :
    Approximates (ofRationalAreas area) id z one (⟨2,4,by decide⟩ : Fraction) dyadic :=
  Principia1713.LemmaIII.corollary1_magnitude_area_approximation
    (ofRationalAreas area) id z one _ dyadic (fun _ _ _ h _ => h) (by decide) hA dyadic_mesh

-- Zero assigned area is permitted by absolute approximation, with no division.
example (area : RectangleContent.AreaRules) :
    Approximates (ofRationalAreas area) (fun _ => z) z one z dyadic := by
  have hA : area.HasArea (figure (fun _ => z) z one) z :=
    area.congr_value _ _ _ (by decide) (area.rectangle z one z (by decide) (by decide))
  exact Principia1687.LemmaIII.corollary1_magnitude_area_approximation
    (ofRationalAreas area) (fun _ => z) z one z dyadic
    (fun _ _ _ _ _ => Fraction.magnitudes.le_refl _) (by decide) hA dyadic_mesh

-- An enclosure with a nonshrinking gap does not imply approximation.
example : ¬ ErrorsVanish rational (fun _ => z) (fun _ => one) half := by
  intro h
  obtain ⟨N,hN⟩ := h quarter (by change 0<quarter.num; decide)
  exact (by decide : ¬ Fraction.lt half (Fraction.add z quarter)) (hN N (Nat.le_refl _)).1
example : ¬ rational.order.lt z (rational.add z z) := by
  change ¬ Fraction.lt z (Fraction.add z z)
  decide

-- A lexicographic infinitesimal is positive yet below every rational unit half.
-- This comparison counterexample is not claimed to realize all of AreaRules.
private def lexLt (x y : Fraction × Fraction) : Prop :=
  Fraction.lt x.1 y.1 ∨ (Fraction.equiv x.1 y.1 ∧ Fraction.lt x.2 y.2)
example : lexLt (z,z) (z,one) := Or.inr ⟨by decide,by decide⟩
example (n : Nat) : ¬ lexLt (duration one n,z) (z,one) := by
  rintro (h | ⟨h,_⟩)
  · change 1*1 < 0*(1*(2:Int)^n) at h
    simp at h
  · change 1*1 = 0*(1*(2:Int)^n) at h
    simp at h

-- General assigned-area ratios use actual integer multiples and an interior
-- rectangle. The identity patch has zero first lower sum, which is permitted.
example : Fraction.equiv (lowerSum id (dyadic 0)) z := by decide
example : Nonempty (MultipleRules rational) := ⟨rationalMultiples⟩
example {Q : Type} (area : AreaRules Q) (R : MultipleRules area.magnitudes)
    (A : Q) (hA : area.HasArea (figure id z one) A) :
    AreaRatiosOne area.magnitudes (fun k => lowerSum id (dyadic k))
      (fun k => upperSum id (dyadic k)) A :=
  Principia1687.LemmaII.equal_width_assigned_magnitude_ratios
    area R id z one half A dyadic (fun _ _ _ h _ => h) (by decide)
    (by decide) (by decide) (by decide) hA (duration one)
    (fun k i _ => grid_width k i) unit_mesh
example {Q : Type} (area : AreaRules Q) (R : MultipleRules area.magnitudes)
    (A : Q) (hA : area.HasArea (figure id z one) A) :
    AreaRatiosOne area.magnitudes (fun k => lowerSum id (dyadic k))
      (fun k => upperSum id (dyadic k)) A :=
  Principia1687.LemmaIII.unequal_width_assigned_magnitude_ratios
    area R id z one half A dyadic (fun _ _ _ h _ => h) (by decide)
    (by decide) (by decide) (by decide) hA dyadic_mesh
example {Q : Type} (area : AreaRules Q) (R : MultipleRules area.magnitudes)
    (A : Q) (hA : area.HasArea (figure id z one) A) :
    AreaRatiosOne area.magnitudes (fun k => lowerSum id (dyadic k))
      (fun k => upperSum id (dyadic k)) A :=
  Principia1713.LemmaII.equal_width_assigned_magnitude_ratios
    area R id z one half A dyadic (fun _ _ _ h _ => h) (by decide)
    (by decide) (by decide) (by decide) hA (duration one)
    (fun k i _ => grid_width k i) unit_mesh
example {Q : Type} (area : AreaRules Q) (R : MultipleRules area.magnitudes)
    (A : Q) (hA : area.HasArea (figure id z one) A) :
    AreaRatiosOne area.magnitudes (fun k => lowerSum id (dyadic k))
      (fun k => upperSum id (dyadic k)) A :=
  Principia1713.LemmaIII.unequal_width_assigned_magnitude_ratios
    area R id z one half A dyadic (fun _ _ _ h _ => h) (by decide)
    (by decide) (by decide) (by decide) hA dyadic_mesh

-- A returned tail supplies an actual comparison, rather than an unusable index.
example {Q : Type} (area : AreaRules Q) (R : MultipleRules area.magnitudes)
    (A : Q) (hA : area.HasArea (figure id z one) A) :
    ∃ k, area.magnitudes.order.lt
      (multiple area.magnitudes 2 (area.magnitudes.embed (lowerSum id (dyadic k))))
      (multiple area.magnitudes 3 A) ∧
      area.magnitudes.order.lt (multiple area.magnitudes 2 A)
      (multiple area.magnitudes 3 (area.magnitudes.embed (lowerSum id (dyadic k)))) := by
  have h := Principia1713.LemmaIII.unequal_width_assigned_magnitude_ratios
    area R id z one half A dyadic (fun _ _ _ h _ => h) (by decide)
    (by decide) (by decide) (by decide) hA dyadic_mesh
  obtain ⟨N,hN⟩ := h.2.1 2 3 (by decide) (by decide)
  exact ⟨N,hN N (Nat.le_refl _)⟩

-- Unit-ratio comparisons cannot be inferred for zero figures or fixed ratio 1:2.
example : ¬ RatiosOne rational (fun _ => z) (fun _ => z) := by
  intro h
  obtain ⟨N,hN⟩ := h 1 2 (by decide) (by decide)
  exact (by change ¬ Fraction.lt _ _; decide : ¬ rational.order.lt (multiple rational 1 z)
    (multiple rational 2 z)) (hN N (Nat.le_refl _)).1
example : ¬ RatiosOne rational (fun _ => one) (fun _ => Fraction.ofInt 2) := by
  intro h
  obtain ⟨N,hN⟩ := h 2 3 (by decide) (by decide)
  exact (by change ¬ Fraction.lt _ _; decide : ¬ rational.order.lt (multiple rational 2 (Fraction.ofInt 2))
    (multiple rational 3 one)) (hN N (Nat.le_refl _)).2

-- Both areas and their gap can vanish while their ratio stays 1:2.
example : Exhaustion.VanishingDifference Fraction.magnitudes
    (fun k => durationDifference (duration one k) (duration (Fraction.ofInt 2) k)) := by
  intro eps heps
  obtain ⟨N,hN⟩ := unit_mesh eps heps
  refine ⟨N,fun k hk => Fraction.magnitudes.lt_of_le_lt ?_ (hN k hk)⟩
  apply Fraction.le_of_equiv
  simp only [durationDifference, HarmonicStability.negF, duration, one,
    Fraction.equiv, Fraction.add, Fraction.ofInt, Int.neg_mul,
    Int.one_mul, Int.mul_one, Int.add_mul, Int.mul_add]
  ac_nf
  omega
example : ¬ RatiosOne rational (duration one) (duration (Fraction.ofInt 2)) := by
  intro h
  obtain ⟨N,hN⟩ := h 2 3 (by decide) (by decide)
  have hbad := (hN N (Nat.le_refl _)).2
  change Fraction.lt _ _ at hbad
  simp only [multiple, rational, duration, Fraction.lt, Fraction.add, Fraction.ofInt,
    one, id_eq, Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one] at hbad
  have hp : 0 < (2 : Int)^N := Int.pow_pos (by decide)
  have hp4 := Int.mul_pos (Int.mul_pos (Int.mul_pos hp hp) hp) hp
  simp only [show (2 : Int) = 1+1 by rfl, Int.add_mul, Int.mul_add] at hbad
  ac_nf at hbad hp4
  simp only [show (1+1 : Int) = 2 by rfl] at hbad
  omega

-- A nonzero equal pair does meet every comparison with unity.
example : RatiosOne rational (fun _ => one) (fun _ => one) := by
  apply ratios_one_of_enclosure rational rationalMultiples
    (fun _ => one) (fun _ => one) _ _
    (fun _ => ⟨Fraction.magnitudes.le_refl _,Fraction.magnitudes.le_refl _⟩)
    (fun _ => ⟨Fraction.magnitudes.le_refl _,Fraction.magnitudes.le_refl _⟩)
    one (by decide) 0 (fun _ _ => Fraction.magnitudes.le_refl _)
  intro eps heps
  refine ⟨0,fun _ _ => ?_⟩
  change Fraction.lt (durationDifference one one) eps
  simpa only [durationDifference, HarmonicStability.negF, one, Fraction.lt,
    Fraction.add, Fraction.ofInt, Int.one_mul, Int.mul_one, Int.neg_mul,
    Int.zero_mul, Int.reduceNeg, Int.reduceAdd] using heps

end NewtonLimitDynamics.Polygon.MagnitudeControls

open Lean in
run_elab do
  let env ← getEnv
  for (edition,foreign) in #[(`Principia1687,"Principia1713."),(`Principia1713,"Principia1687.")] do
    for (root,required) in #[
        (edition ++ `LemmaII.equal_width_magnitude_approximation,
          #[edition ++ `LemmaII.rectangle_magnitude_enclosure, edition ++ `LemmaII.equal_width_gap_vanishes]),
        (edition ++ `LemmaIII.unequal_width_magnitude_approximation,
          #[edition ++ `LemmaII.rectangle_magnitude_enclosure, edition ++ `LemmaIII.unequal_width_gap_vanishes]),
        (edition ++ `LemmaIII.corollary1_magnitude_area_approximation,
          #[edition ++ `LemmaIII.unequal_width_magnitude_approximation,
            edition ++ `LemmaII.rectangle_magnitude_enclosure, edition ++ `LemmaIII.unequal_width_gap_vanishes]),
        (edition ++ `LemmaII.equal_width_assigned_magnitude_ratios,
          #[edition ++ `LemmaII.rectangle_magnitude_enclosure, edition ++ `LemmaII.equal_width_gap_vanishes]),
        (edition ++ `LemmaIII.unequal_width_assigned_magnitude_ratios,
          #[edition ++ `LemmaII.rectangle_magnitude_enclosure, edition ++ `LemmaIII.unequal_width_gap_vanishes])
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
      let shared := if root.toString.endsWith "_assigned_magnitude_ratios" then
        #[`NewtonLimitDynamics.Polygon.MagnitudeContent.rectangle_magnitude_ratios,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.ratios_one_of_enclosure,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.multiple_monotone,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.multiple_embed,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules.embed_lt,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.MultipleRules.add_le_add_left,
          `NewtonLimitDynamics.Polygon.RectangleContent.rectangle_interior_denominator_bound]
        else #[edition ++ `LemmaI.no_positive_ultimate_difference,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.rational_exhaustion,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.errors_vanish,
          `NewtonLimitDynamics.Polygon.MagnitudeContent.Rules.unit_halves_exhaust,
          `NewtonLimitDynamics.Polygon.RectangleContent.lower_upper_areas]
      for dependency in required ++ shared do
        unless used.contains dependency do throwError "{root} omits {dependency}"
      for dependency in used do
        let name := ((privateToUserName? dependency).getD dependency).toString
        if #[foreign,"DeMotu1684."].any name.startsWith then
          throwError "{root} uses foreign witness {dependency}"
        if let some idx := env.getModuleIdxFor? dependency then
          if env.header.moduleNames[idx]!.toString.startsWith "ModernLib" then
            throwError "{root} uses modern module through {dependency}"
  logInfo "Checked six magnitude-approximation and four multiple-ratio clients: own-edition enclosure/exhaustion, actual shared derivations and visible compatibility laws; no foreign witness or modern module."
