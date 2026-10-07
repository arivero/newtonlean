import NewtonLimitDynamics

/-! Constructed shrinking slope-parameter partitions of a nonconstant radial graph.
The geometric area convention and any assigned curved/between areas remain
explicit; no enclosure, discrepancy bound or vanishing area is supplied. -/
namespace NewtonLimitDynamics.Polygon.HistoricalRadialSectorControls
open NewtonLimitDynamics TimeSubdivision MonotoneRectangles RadialSector
open HarmonicTimeComparison HarmonicTimeRealization HarmonicDyadic

private def z := Fraction.ofInt 0
private def o := Fraction.ofInt 1
private def g (t : Fraction) := Fraction.add o t
private theorem hg : MonotoneOn g z o := by
  intro s t _ hst _
  exact Fraction.add_le_add_left hst o
private theorem grid_width (m i : Nat) : Fraction.equiv
    (durationDifference (countTime o m i) (countTime o m (i+1))) (duration o m) :=
  Fraction.equiv_trans (countTime_difference o m i 1)
    (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one,Int.natCast_one])
private def dyadic (m : Nat) : Partition z o where
  count := blocks m
  positive_count := by unfold blocks; exact Nat.pow_pos (by decide)
  nodes := countTime o m
  first := by simp only [countTime,z,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_zero,
    Int.zero_mul,Int.mul_zero]
  last := blocks_duration o m
  ordered := by
    intro i _
    exact (difference_nonnegative_iff _ _).mp
      (Fraction.nonnegative_equiv (grid_width m i) (by change (0 : Int) ≤ 1; decide))
private theorem mesh : Exhaustion.VanishingDifference Fraction.magnitudes
    (fun m => maxWidth (dyadic m)) := by
  intro delta hd
  obtain ⟨N,hN⟩ := duration_eventually_small o delta (by decide) hd
  refine ⟨N,fun m hm => Fraction.magnitudes.lt_of_le_lt ?_ (hN m hm)⟩
  exact (maxWidth_bounds (dyadic m)).2 _ (fun i _ => Fraction.le_of_equiv (grid_width m i))

example : Fraction.equiv (gap (density g) (dyadic 0)) (Fraction.ofInt 3).half := by decide
example (area : DifferenceAreaRules) (A : Fraction) (hA : area.HasArea (sector g z o) A) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (durationDifference A (chordArea g (dyadic m))).abs) :=
  (Principia1687.PropositionI.radial_sector_approximation area g z o A dyadic hg (by decide) hA mesh).2.1
example (area : DifferenceAreaRules) (A : Fraction) (hA : area.HasArea (sector g z o) A) :
    (∀ m, area.HasArea (collar g (dyadic m)) (gap (density g) (dyadic m))) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes (fun m => gap (density g) (dyadic m)) :=
  (Principia1713.PropositionI.radial_sector_approximation area g z o A dyadic hg (by decide) hA mesh).2.2.2
example (area : DifferenceAreaRules) (B : Nat → Fraction)
    (hB : ∀ m, area.HasArea (between g (dyadic m)) (B m)) :
    (∀ m, 0 ≤ (B m).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes B :=
  Principia1687.PropositionI.radial_between_area_approximation area g z o dyadic hg (by decide) B hB mesh
example (area : DifferenceAreaRules) (B : Nat → Fraction)
    (hB : ∀ m, area.HasArea (between g (dyadic m)) (B m)) :
    (∀ m, 0 ≤ (B m).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes B :=
  Principia1713.PropositionI.radial_between_area_approximation area g z o dyadic hg (by decide) B hB mesh

#print axioms Principia1687.PropositionI.radial_sector_approximation
#print axioms Principia1713.PropositionI.radial_sector_approximation
#print axioms Principia1687.PropositionI.radial_ultimate_chord_difference_zero
#print axioms Principia1713.PropositionI.radial_ultimate_chord_difference_zero
end NewtonLimitDynamics.Polygon.HistoricalRadialSectorControls
