import ModernLib.Foundation.Polygon.MonotoneRectangles

/-! Cross-result monotone rectangle reconstruction; the two witness models remain distinct. -/

namespace ModernLib.Reconstruction.Principia1687.LemmaIIIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

-- Modern dependency score: 22/97 (M=22, H=75; transitive project theorems/axioms).
theorem lemmas2_3_monotone_rectangle_reconstruction (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hmesh : ∀ delta : Fraction, 0<delta.num → ∃ N : Nat, ∀ m, N≤m →
      Fraction.lt (MonotoneRectangles.maxWidth (parts m)) delta) :
    (∀ m, (∀ x, MonotoneRectangles.completed (MonotoneRectangles.lowerFigure g (parts m)) x →
        MonotoneRectangles.completed (MonotoneRectangles.figure g a b) x) ∧
      (∀ x, MonotoneRectangles.completed (MonotoneRectangles.figure g a b) x →
        MonotoneRectangles.completed (MonotoneRectangles.upperFigure g (parts m)) x)) ∧
    (∀ m, (0≤(MonotoneRectangles.lowerSum g (parts m)).num ∧
        0≤(MonotoneRectangles.upperSum g (parts m)).num) ∧
      (0≤(MonotoneRectangles.gap g (parts m)).num ∧
        Fraction.le (MonotoneRectangles.gap g (parts m))
          (Fraction.mul (MonotoneRectangles.maxWidth (parts m))
            (HarmonicTimeComparison.durationDifference (g a) (g b))))) ∧
    (∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
      Fraction.lt (MonotoneRectangles.gap g (parts m)) eps) :=
  ⟨fun m => MonotoneRectangles.completed_enclosure g (parts m) hg,
    fun m => ⟨MonotoneRectangles.sums_nonnegative g (parts m) hg hbase,
      MonotoneRectangles.gap_bound g (parts m) hg (MonotoneRectangles.maxWidth (parts m))
        (MonotoneRectangles.maxWidth_bounds (parts m)).1⟩,
    MonotoneRectangles.gaps_vanish g parts hg hmesh⟩

end ModernLib.Reconstruction.Principia1687.LemmaIIIII

namespace ModernLib.Reconstruction.Principia1713.LemmaIIIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

-- Modern dependency score: 22/97 (M=22, H=75; transitive project theorems/axioms).
theorem lemmas2_3_monotone_rectangle_reconstruction (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hmesh : ∀ delta : Fraction, 0<delta.num → ∃ N : Nat, ∀ m, N≤m →
      Fraction.lt (MonotoneRectangles.maxWidth (parts m)) delta) :
    (∀ m, (∀ x, MonotoneRectangles.completed (MonotoneRectangles.lowerFigure g (parts m)) x →
        MonotoneRectangles.completed (MonotoneRectangles.figure g a b) x) ∧
      (∀ x, MonotoneRectangles.completed (MonotoneRectangles.figure g a b) x →
        MonotoneRectangles.completed (MonotoneRectangles.upperFigure g (parts m)) x)) ∧
    (∀ m, (0≤(MonotoneRectangles.lowerSum g (parts m)).num ∧
        0≤(MonotoneRectangles.upperSum g (parts m)).num) ∧
      (0≤(MonotoneRectangles.gap g (parts m)).num ∧
        Fraction.le (MonotoneRectangles.gap g (parts m))
          (Fraction.mul (MonotoneRectangles.maxWidth (parts m))
            (HarmonicTimeComparison.durationDifference (g a) (g b))))) ∧
    (∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
      Fraction.lt (MonotoneRectangles.gap g (parts m)) eps) :=
  ⟨fun m => MonotoneRectangles.completed_enclosure g (parts m) hg,
    fun m => ⟨MonotoneRectangles.sums_nonnegative g (parts m) hg hbase,
      MonotoneRectangles.gap_bound g (parts m) hg (MonotoneRectangles.maxWidth (parts m))
        (MonotoneRectangles.maxWidth_bounds (parts m)).1⟩,
    MonotoneRectangles.gaps_vanish g parts hg hmesh⟩

end ModernLib.Reconstruction.Principia1713.LemmaIIIII
