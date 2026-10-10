import ClassicsLib.Euclid.FiniteLattice
import BarrowLib.Common.RationalMagnitudes
import ModernLib.Foundation.Polygon.RationalEnclosure

namespace NewtonLimitDynamics.Polygon

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem isum_mono (f g : Nat → Int) (n : Nat) (h : ∀ i, i < n → f i ≤ g i) :
    isum f n ≤ isum g n := by
  induction n with
  | zero => exact Int.le_refl _
  | succ n ih =>
    simp only [isum]
    exact Int.add_le_add (ih (fun i hi => h i (by omega))) (h n (by omega))

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem isum_mul (f : Nat → Int) (c : Int) (n : Nat) :
    isum (fun i => c * f i) n = c * isum f n := by
  induction n with
  | zero => simp [isum]
  | succ n ih => simp [isum, ih, Int.mul_add]

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem telescoping (height : Nat → Int) (n : Nat) :
    isum (fun i => height (i+1) - height i) n = height n - height 0 := by
  induction n with
  | zero => simp [isum]
  | succ n ih => simp only [isum, ih]; omega

/-- Lemmas II/III's finite rectangle estimate, for a monotone patch. Widths
    may be unequal; every width must obey the SAME maximum. Multiplication
    measures rectangle area. A curve enclosed by these rectangles is an
    additional geometric hypothesis, not supplied by this arithmetic result. -/
-- Modern dependency score: 3/3 (M=3, H=0; transitive project theorems/axioms).
theorem rectangle_gap_bound (width height : Nat → Int) (maxWidth : Int) (n : Nat)
    (hw : ∀ i, i < n → width i ≤ maxWidth)
    (hh : ∀ i, i < n → height i ≤ height (i+1)) :
    isum (fun i => width i * (height (i+1)-height i)) n ≤
      maxWidth * (height n - height 0) := by
  have h := isum_mono (fun i => width i * (height (i+1)-height i))
    (fun i => maxWidth * (height (i+1)-height i)) n (by
      intro i hi
      exact Int.mul_le_mul_of_nonneg_right (hw i hi) (by have := hh i hi; omega))
  rw [isum_mul, telescoping] at h
  exact h

/-- Refinement indexed by positive rational mesh. The budget represents the
    maximum-width times total-height estimate. Making that budget small must
    be justified for the selected curve; it does not assert a trajectory. -/
def Vanishes {A : Type} [RationalEnclosure.Magnitude A] (gap : Fraction → A) : Prop :=
  ∀ epsilon, Fraction.positive epsilon →
    Near Fraction.magnitudes (fun mesh => RationalEnclosure.Magnitude.small (gap mesh) epsilon)

-- Modern dependency score: 0/5 (M=0, H=5; transitive project theorems/axioms).
theorem enclosed_gap_vanishes {A : Type} [RationalEnclosure.Magnitude A]
    (gap : Fraction → A) (budget : Fraction → Fraction)
    (hbudget : Vanishes budget)
    (henclose : Near Fraction.magnitudes (fun mesh =>
      RationalEnclosure.Magnitude.bounded (gap mesh) (budget mesh))) :
    Vanishes gap := by
  intro epsilon hepsilon
  obtain ⟨d, hd, h⟩ := near_and Fraction.magnitudes _ _ henclose (hbudget epsilon hepsilon)
  exact ⟨d, hd, fun mesh hm hmd =>
    RationalEnclosure.Magnitude.small_of_bound _ _ _ (h mesh hm hmd).1 (h mesh hm hmd).2⟩

/-- An explicit unconditional rational budget instance, including zero
coefficient. This is the squeeze used by constructed geometric content. -/
-- Modern dependency score: 0/11 (M=0, H=11; transitive project theorems/axioms).
theorem linear_budget_vanishes (A : Fraction) (hA : 0 ≤ A.num) :
    Vanishes (fun mesh => Fraction.mul mesh A) := by
  intro eps heps
  refine ⟨Fraction.ofRat (Polygon.HarmonicTimeRealization.factorDelta (A).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat A).mp hA)),
    (by
        apply (Fraction.positive_iff_toRat _).mpr
        change 0 < (Fraction.ofRat _).toRat
        rw [Fraction.toRat_ofRat]
        have hcoef := ((Fraction.nonnegative_iff_toRat A).mp hA)
        have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
        (try dsimp only at hcoef hepsRat ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]),?_⟩
  intro mesh hm hmd
  exact (show Fraction.lt (Fraction.mul (mesh) (A)) (eps) from by
      apply (Fraction.lt_iff_toRat _ _).mpr
      rw [Fraction.toRat_mul]
      have hcoef := ((Fraction.nonnegative_iff_toRat A).mp hA)
      have hdist := ((Fraction.nonnegative_iff_toRat mesh).mp (Int.le_of_lt hm))
      have hstrict := (Fraction.lt_iff_toRat _ _).mp hmd
      change Fraction.toRat _ < (Fraction.ofRat _).toRat at hstrict
      rw [Fraction.toRat_ofRat] at hstrict
      (try dsimp only at hcoef hdist hstrict ⊢)
      grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff])

/-- Conditional transfer of polygon area ratios to enclosed sector area ratios.
    Lower and upper limits are geometric premises. No trajectory existence or
    identification with continuous force follows from this type. -/
-- Modern dependency score: 0/6 (M=0, H=6; transitive project theorems/axioms).
theorem sector_ratio_reconstruction (sector inner outer : Fraction → Fraction)
    (c : Fraction) (hin : Ultimate Fraction.magnitudes inner c)
    (hout : Ultimate Fraction.magnitudes outer c)
    (henclose : Near Fraction.magnitudes (fun mesh =>
      Fraction.le (inner mesh) (sector mesh) ∧ Fraction.le (sector mesh) (outer mesh))) :
    Ultimate Fraction.magnitudes sector c :=
  enclosure_reconstruction Fraction.magnitudes sector inner outer c hin hout henclose

end NewtonLimitDynamics.Polygon
