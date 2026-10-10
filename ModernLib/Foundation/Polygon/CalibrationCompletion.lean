import BarrowLib.Polygon.TimeCalibration
import ModernLib.Foundation.Polygon.ScaledTolerance

namespace NewtonLimitDynamics.Polygon.TimeCalibration
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates

def CalibratedCauchy (tau : Fraction) (a : Nat → Point × Point) : Prop :=
  ∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ m n : Nat,
    N ≤ m → N ≤ n → Fraction.lt (distance tau (a m) (a n)) eps


-- Modern dependency score: 0/34 (M=0, H=34; transitive project theorems/axioms).
theorem cauchy_calibration_iff (tau : Fraction) (ht : 0 < tau.num)
    (a : Nat → Point × Point) :
    CalibratedCauchy tau a ↔ CalibratedCauchy (Fraction.ofInt 1) a := by
  constructor
  · intro ha eps heps
    let C := Fraction.add (Fraction.ofInt 1) (inverse tau ht)
    have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide)
      (Int.le_of_lt tau.den_pos)
    obtain ⟨N,hN⟩ := ha (Fraction.ofRat (HarmonicTimeRealization.factorDelta (C).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat C).mp hC)))
      ((by
          apply (Fraction.positive_iff_toRat _).mpr
          change 0 < (Fraction.ofRat _).toRat
          rw [Fraction.toRat_ofRat]
          have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
          have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
          (try dsimp only at hcoef hepsRat ⊢)
          grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
    exact ⟨N,fun m n hm hn => Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (distance_unit_calibration (a m) (a n)))
      (unit_tolerance tau eps ht (a m) (a n) (hN m n hm hn))⟩
  · intro ha eps heps
    let C := Fraction.add (Fraction.ofInt 1) tau
    have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt ht)
    obtain ⟨N,hN⟩ := ha (Fraction.ofRat (HarmonicTimeRealization.factorDelta (C).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat C).mp hC)))
      ((by
          apply (Fraction.positive_iff_toRat _).mpr
          change 0 < (Fraction.ofRat _).toRat
          rw [Fraction.toRat_ofRat]
          have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
          have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
          (try dsimp only at hcoef hepsRat ⊢)
          grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
    exact ⟨N,fun m n hm hn => calibrated_tolerance tau eps ht (a m) (a n)
      (Fraction.magnitudes.lt_of_le_lt
        (Fraction.le_of_equiv (Fraction.equiv_symm (distance_unit_calibration (a m) (a n))))
        (hN m n hm hn))⟩

def CalibratedEquivalent (tau : Fraction) (a b : Nat → Point × Point) : Prop :=
  ∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ n : Nat,
    N ≤ n → Fraction.lt (distance tau (a n) (b n)) eps

/-- The actual completed value relation is unchanged by a fixed calibration. -/
-- Modern dependency score: 0/33 (M=0, H=33; transitive project theorems/axioms).
theorem nameEquiv_calibration_iff (tau : Fraction) (ht : 0 < tau.num)
    (a b : HarmonicDyadic.EndpointCauchyName) :
    CalibratedEquivalent tau a.approx b.approx ↔ CauchyValues.NameEquiv a b := by
  constructor
  · intro ha eps heps
    let C := Fraction.add (Fraction.ofInt 1) (inverse tau ht)
    have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide)
      (Int.le_of_lt tau.den_pos)
    obtain ⟨N,hN⟩ := ha (Fraction.ofRat (HarmonicTimeRealization.factorDelta (C).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat C).mp hC)))
      ((by
          apply (Fraction.positive_iff_toRat _).mpr
          change 0 < (Fraction.ofRat _).toRat
          rw [Fraction.toRat_ofRat]
          have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
          have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
          (try dsimp only at hcoef hepsRat ⊢)
          grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
    exact ⟨N,fun n hn => unit_tolerance tau eps ht (a.approx n) (b.approx n) (hN n hn)⟩
  · intro ha eps heps
    let C := Fraction.add (Fraction.ofInt 1) tau
    have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt ht)
    obtain ⟨N,hN⟩ := ha (Fraction.ofRat (HarmonicTimeRealization.factorDelta (C).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat C).mp hC)))
      ((by
          apply (Fraction.positive_iff_toRat _).mpr
          change 0 < (Fraction.ofRat _).toRat
          rw [Fraction.toRat_ofRat]
          have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
          have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
          (try dsimp only at hcoef hepsRat ⊢)
          grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
    exact ⟨N,fun n hn => calibrated_tolerance tau eps ht
      (a.approx n) (b.approx n) (hN n hn)⟩


/-- Time-unit rescaling preserves the actual-family Cauchy condition. -/
-- Modern dependency score: 0/23 (M=0, H=23; transitive project theorems/axioms).
theorem cauchy_rescale (c tau : Fraction) (hc : 0 < c.num)
    (a : Nat → Point × Point) :
    CalibratedCauchy (Fraction.mul c tau) (fun n => rescaleState c hc (a n)) ↔
      CalibratedCauchy tau a := by
  constructor
  · intro ha eps heps
    obtain ⟨N,hN⟩ := ha eps heps
    refine ⟨N,fun m n hm hn => ?_⟩
    exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (Fraction.equiv_symm (distance_rescale c tau (a m) (a n) hc)))
      (hN m n hm hn)
  · intro ha eps heps
    obtain ⟨N,hN⟩ := ha eps heps
    refine ⟨N,fun m n hm hn => ?_⟩
    exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (distance_rescale c tau (a m) (a n) hc))
      (hN m n hm hn)


end NewtonLimitDynamics.Polygon.TimeCalibration
