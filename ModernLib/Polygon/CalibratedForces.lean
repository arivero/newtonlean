import ModernLib.Polygon.ForceClasses
import BarrowLib.Polygon.TimeCalibration
import BarrowLib.Polygon.EquivalentDuration

/-! Modern calibrated instances of the general finite force estimates.
The free calibration fixes no physical action constant and adds no historical
premise. General convergence, confinement and restart remain separate. -/

namespace NewtonLimitDynamics.Polygon.CalibratedForces
open NewtonLimitDynamics
open TimeSubdivision PointBounds CentralSchedule HarmonicStability ForceClasses

/-- Actual two-precision sampled polygons retain the weighted sampling budget. -/
theorem sampled_calibrated_discrepancy (o : Oracle) (tau h L : Fraction)
    (ht : 0 < tau.num) (hL : LipschitzOn o L)
    (i j : Nat) (hij : i ≤ j) (s : Point × Point) (n : Nat)
    (hR : ∀ k, k < n →
      o.region (BoundedIteration.run (o.sample i) h s (k+1)).1 ∧
      o.region (BoundedIteration.run (o.sample j) h s (k+1)).1)
    (hs : TimeCalibration.Window tau h L ht n) :
    Fraction.le
      (TimeCalibration.distance tau
        (schedule (o.sample i) (List.replicate n h) s)
        (schedule (o.sample j) (List.replicate n h) s))
      (Fraction.mul (Fraction.ofInt (2 * (n : Int)))
        (Fraction.mul (Fraction.mul tau h.abs)
          (Fraction.add (Fraction.add (o.error i) (o.error i)) (o.error i)))) := by
  rw [← run_eq_schedule, ← run_eq_schedule]
  apply EquivalentDuration.run_uniform_error_at tau ht (o.sample i) (o.sample j)
    h h L _ s (Fraction.equiv_refl _) hL.1
    (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_add _ _ (o.error_nonnegative i) (o.error_nonnegative i))
      (o.error_nonnegative i))
    n hs
  intro k hk
  exact samples_comparison_contract o L hL i j hij _ _ (hR k hk).1 (hR k hk).2

/-- Harmonic motion is an instance of the calibrated general estimate. -/
theorem harmonic_calibrated_cell (tau w h : Fraction) (ht : 0 < tau.num)
    (s t : Point × Point) :
    Fraction.le
      (TimeCalibration.distance tau (cell (linearField w) h s) (cell (linearField w) h t))
      (Fraction.add
        (Fraction.mul (TimeCalibration.amplification tau h w.abs ht)
          (TimeCalibration.distance tau s t))
        (Fraction.mul (Fraction.mul tau h.abs) (Fraction.ofInt 0))) :=
  TimeCalibration.cell_amplification tau ht _ _ _ _ _ _ _
    (Fraction.abs_num_nonnegative w) (harmonic_comparison_contract w)

/-- The centre-at-infinity instance uses L=0. -/
theorem parallel_calibrated_cell (tau h : Fraction) (ht : 0 < tau.num)
    (a : Point) (s t : Point × Point) :
    Fraction.le
      (TimeCalibration.distance tau (cell (fun _ => a) h s) (cell (fun _ => a) h t))
      (Fraction.add
        (Fraction.mul (TimeCalibration.amplification tau h (Fraction.ofInt 0) ht)
          (TimeCalibration.distance tau s t))
        (Fraction.mul (Fraction.mul tau h.abs) (Fraction.ofInt 0))) := by
  have hcontract : FiniteEstimates.comparisonContract (fun _ => a) (fun _ => a)
      (Fraction.ofInt 0) (Fraction.ofInt 0) := by
    intro p q
    exact Fraction.le_equiv_right
      (Fraction.le_of_equiv (FiniteEstimates.pointDistance_self_zero a))
      (by simp [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt])
  exact TimeCalibration.cell_amplification tau ht (fun _ => a) (fun _ => a) h
    (Fraction.ofInt 0) (Fraction.ofInt 0) s t (by decide) hcontract

set_option maxHeartbeats 500000 in
/-- Exact finite harmonic mechanics commute with a positive change of time unit. -/
theorem harmonic_cell_rescale (c w h : Fraction) (hc : 0 < c.num)
    (s : Point × Point) :
    stateEquiv
      (TimeCalibration.rescaleState c hc (cell (linearField w) h s))
      (cell (linearField (TimeCalibration.rescaleConstant c w hc))
        (Fraction.mul c h) (TimeCalibration.rescaleState c hc s)) := by
  constructor <;> constructor <;>
    simp only [stateEquiv,pointEquiv,cell,linearField,negF,pointAdd,pointScale,
      TimeCalibration.rescaleState,TimeCalibration.rescaleConstant,TimeCalibration.inverse,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,
      Int.neg_mul,Int.mul_neg] <;> ac_nf

end NewtonLimitDynamics.Polygon.CalibratedForces
