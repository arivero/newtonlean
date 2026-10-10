import ModernLib.Foundation.Polygon.CauchyValues
import BarrowLib.Common.RationalTolerance

/-! Elementary rational tolerances for scaling and monotonicity of generic
closed quotient bounds. The retained namespace is an import-compatible name;
no harmonic parameter or mechanical result is a premise. -/

namespace NewtonLimitDynamics.Polygon.HarmonicTimeRealization
open NewtonLimitDynamics
open HarmonicDyadic CauchyValues

-- Modern dependency score: 0/5 (M=0, H=5; transitive project theorems/axioms).
theorem nameBound_mono (a b : EndpointCauchyName) (R S : Fraction)
    (hRS : Fraction.le R S) (h : NameBound a b R) :
    NameBound a b S := by
  intro eps heps
  obtain ⟨N, hN⟩ := h eps heps
  refine ⟨N, ?_⟩
  intro n hn
  exact Fraction.magnitudes.lt_of_lt_le (hN n hn)
    (Fraction.add_le_add_right hRS eps)

-- Modern dependency score: 16/53 (M=16, H=37; transitive project theorems/axioms).
theorem within_mono (x y : Value) (R S : Fraction)
    (hRS : Fraction.le R S) (h : Within x y R) : Within x y S := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => exact nameBound_mono a b R S hRS h

-- Modern dependency score: 1/23 (M=1, H=22; transitive project theorems/axioms).
theorem nameBound_scale (a b ta tb : EndpointCauchyName)
    (C R : Fraction) (hC : 0 ≤ C.num)
    (hlevel : ∀ n : Nat,
      Fraction.le (distance (a.approx n) (b.approx n))
        (Fraction.mul (distance (ta.approx n) (tb.approx n)) C))
    (hnear : NameBound ta tb R) :
    NameBound a b (Fraction.mul R C) := by
  intro eps heps
  let q := eps.half
  let delta := Fraction.ofRat (factorDelta (C).toRat (q).toRat ((Fraction.nonnegative_iff_toRat C).mp hC))
  obtain ⟨N, hN⟩ := hnear delta
    ((by
        apply (Fraction.positive_iff_toRat _).mpr
        change 0 < (Fraction.ofRat _).toRat
        rw [Fraction.toRat_ofRat]
        have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
        have hepsRat : 0 < (q).toRat := (Fraction.positive_iff_toRat (q)).mp heps
        (try dsimp only at hcoef hepsRat ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
  refine ⟨N, ?_⟩
  intro n hn
  have hmul := Fraction.mul_le_mul_nonnegative
    (Fraction.magnitudes.lt_implies_le (hN n hn)) C hC
  have hsum := Fraction.le_equiv_right hmul (Fraction.add_mul R delta C)
  have hdelta : Fraction.le (Fraction.mul delta C) q := (by
      apply (Fraction.le_iff_toRat _ _).mpr
      change (Fraction.mul (Fraction.ofRat _) _).toRat ≤ Fraction.toRat _
      rw [Fraction.toRat_mul, Fraction.toRat_ofRat]
      exact HarmonicTimeRealization.factor_delta_weak _ _ ((Fraction.nonnegative_iff_toRat C).mp hC) ((Fraction.nonnegative_iff_toRat q).mp (by simpa only [q, Fraction.half] using Int.le_of_lt heps)))
  have htotal := Fraction.add_le_add_left hdelta (Fraction.mul R C)
  have hsmall : Fraction.lt
      (Fraction.add (Fraction.mul R C) q)
      (Fraction.add (Fraction.mul R C) eps) :=
    CauchyValues.add_lt_add_left (Fraction.half_lt eps heps) _
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.magnitudes.le_trans (hlevel n)
      (Fraction.magnitudes.le_trans hsum htotal)) hsmall

end NewtonLimitDynamics.Polygon.HarmonicTimeRealization
