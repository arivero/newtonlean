import NewtonLimitDynamics.Polygon.GeneralForcePrefix
import BarrowLib.Polygon.CalibratedGrowth

/-! Derive all motion-sample bounds required by the general construction from
globally compared inward central samples and the calibrated short window.
The bound is computed from force data, initial state and sampling scale.
No globally bounded force or supplied bound along a desired curve is used.
Region-local singular laws still require their own confinement argument. -/

namespace NewtonLimitDynamics.Polygon.GeneralForceGrowth
open NewtonLimitDynamics TimeSubdivision PointBounds HarmonicDyadic ForceClasses
open FiniteEstimates
open GeneralForceEndpoint GeneralForcePrecision

structure Data (o : CentralOracle) (T tau L : Fraction) where
  time_nonnegative : 0 ≤ T.num
  calibration_positive : 0 < tau.num
  lipschitz : LipschitzOn o.toOracle L
  global_region : ∀ p, o.region p
  window : Fraction.le
    (Fraction.mul T (TimeCalibration.rate tau L calibration_positive)) ⟨1,2,by decide⟩

def shadowCap (E0 T tau : Fraction) (s : Point × Point) (ht : 0 < tau.num) : Fraction :=
  let M := CalibratedGrowth.cap tau T (Fraction.mul (Fraction.ofInt 2) E0) s
  Fraction.add M (Fraction.mul T (Fraction.mul M (TimeCalibration.inverse tau ht)))

def forceCap (E0 T tau L : Fraction) (s : Point × Point) (ht : 0 < tau.num) : Fraction :=
  Fraction.add (Fraction.mul L (shadowCap E0 T tau s ht)) (Fraction.mul (Fraction.ofInt 2) E0)

/-- Chosen force precision yields one growth contract for every mesh level. -/
theorem field_growth (o : CentralOracle) (E0 T tau L : Fraction)
    (hE : 0 < E0.num) (d : Data o T tau L) (j : Nat) :
    CalibratedGrowth.Growth (field o E0 hE j) L (Fraction.mul (Fraction.ofInt 2) E0) := by
  intro p
  have he := Fraction.magnitudes.lt_implies_le (precision_error o.toOracle E0 hE j)
  have ht : Fraction.le (GeometricTail.tailCap E0 j) E0 := by
    exact duration_le_window E0 (Int.le_of_lt hE) j
  have herr := Fraction.add_le_add (Fraction.magnitudes.le_trans he ht)
    (Fraction.magnitudes.le_trans he ht)
  have htwo : Fraction.equiv (Fraction.add E0 E0) (Fraction.mul (Fraction.ofInt 2) E0) := by
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt]
    simp only [show (2:Int)=1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  exact Fraction.magnitudes.le_trans
    (sample_linear_growth o L d.lipschitz (d.global_region _) _ p (d.global_region p))
    (Fraction.add_le_add_left (Fraction.le_equiv_right herr htwo) _)

theorem shadowCap_nonnegative (E0 T tau : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (ht : 0 < tau.num) :
    0 ≤ (shadowCap E0 T tau s ht).num := by
  have hM := CalibratedGrowth.cap_nonnegative tau T (Fraction.mul (Fraction.ofInt 2) E0) s
    (Int.le_of_lt ht) hT (Fraction.nonnegative_mul _ _ (by decide) (Int.le_of_lt hE))
  exact Fraction.nonnegative_add _ _ hM
    (Fraction.nonnegative_mul _ _ hT
      (Fraction.nonnegative_mul _ _ hM (Int.le_of_lt tau.den_pos)))

theorem forceCap_nonnegative (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o T tau L) :
    0 ≤ (forceCap E0 T tau L s d.calibration_positive).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ d.lipschitz.1
      (shadowCap_nonnegative E0 T tau s hE d.time_nonnegative d.calibration_positive))
    (Fraction.nonnegative_mul _ _ (by decide) (Int.le_of_lt hE))

/-- Actual iterates are bounded independently of mesh or level precision. -/
theorem run_state_bound (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o T tau L)
    (j : Nat) (h : Fraction) (hh : 0 ≤ h.num) (n : Nat)
    (hn : Fraction.le (BoundedIteration.time h n) T) :
    Fraction.le (TimeCalibration.norm tau (BoundedIteration.run (field o E0 hE j) h s n))
      (CalibratedGrowth.cap tau T (Fraction.mul (Fraction.ofInt 2) E0) s) := by
  have he := Fraction.le_equiv_left
    (Fraction.mul_equiv (Fraction.equiv_refl (Fraction.ofInt (n:Int)))
      (Fraction.abs_of_nonnegative h hh)) hn
  exact CalibratedGrowth.run_norm_le_cap tau d.calibration_positive _ h T L _ s
    d.lipschitz.1 (Fraction.nonnegative_mul _ _ (by decide) (Int.le_of_lt hE))
    (field_growth o E0 T tau L hE d j) n he d.window

/-- One finite argument covers the actual mesh and the doubled half mesh. -/
theorem bounded_samples (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o T tau L)
    (j : Nat) (h : Fraction) (hh : 0 ≤ h.num) (n : Nat)
    (hn : Fraction.le (BoundedIteration.time h n) T) :
    BoundedIteration.BoundedSamples (field o E0 hE j) h s
      (forceCap E0 T tau L s d.calibration_positive) n := by
  intro i hi
  have hstate := run_state_bound o E0 T tau L s hE d j h hh (i+1)
    (Fraction.magnitudes.le_trans (BoundedIteration.time_monotone h hh (i+1) n (by omega)) hn)
  have hp := Fraction.magnitudes.le_trans
    (TimeCalibration.position_le_norm tau _ (Int.le_of_lt d.calibration_positive)) hstate
  have hM := CalibratedGrowth.cap_nonnegative tau T (Fraction.mul (Fraction.ofInt 2) E0) s
    (Int.le_of_lt d.calibration_positive) d.time_nonnegative
    (Fraction.nonnegative_mul _ _ (by decide) (Int.le_of_lt hE))
  have hshadow : Fraction.le
      (CalibratedGrowth.cap tau T (Fraction.mul (Fraction.ofInt 2) E0) s)
      (shadowCap E0 T tau s d.calibration_positive) := Fraction.le_add_nonnegative _ _
    (Fraction.nonnegative_mul _ _ d.time_nonnegative
      (Fraction.nonnegative_mul _ _ hM (Int.le_of_lt tau.den_pos)))
  exact Fraction.magnitudes.le_trans (field_growth o E0 T tau L hE d j _)
    (Fraction.add_le_add_right
      (Fraction.mul_le_mul_nonnegative_left (Fraction.magnitudes.le_trans hp hshadow)
        L d.lipschitz.1) _)

/-- All three previously explicit motion bounds now follow from force data.
The existing construction and all of its conditional APIs are retained. -/
def conditions (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o T tau L) :
    GeneralForcePrefix.Conditions o E0 T tau L
      (forceCap E0 T tau L s d.calibration_positive) s hE where
  time_nonnegative := d.time_nonnegative
  calibration_positive := d.calibration_positive
  lipschitz := d.lipschitz
  global_region := d.global_region
  window := d.window
  bound_nonnegative := forceCap_nonnegative o E0 T tau L s hE d
  actual_samples := fun j => bounded_samples o E0 T tau L s hE d j (duration T j)
    d.time_nonnegative (blocks j) (Fraction.le_of_equiv (blocks_duration T j))
  coarse_samples := fun j => bounded_samples o E0 T tau L s hE d j
    (Fraction.add (duration T (j+1)) (duration T (j+1)))
    (Fraction.nonnegative_add _ _ d.time_nonnegative d.time_nonnegative)
    (blocks j) (Fraction.le_of_equiv (coarse_time T j))
  shadow_samples := by
    intro j k hk
    let h := duration T (j+1)
    let a := field o E0 hE j
    let q := FiniteAccumulation.coarseAt a h s k
    let M := CalibratedGrowth.cap tau T (Fraction.mul (Fraction.ofInt 2) E0) s
    have hfull : 0 ≤ (Fraction.add h h).num :=
      Fraction.nonnegative_add _ _ d.time_nonnegative d.time_nonnegative
    have htime := Fraction.magnitudes.le_trans
      (BoundedIteration.time_monotone (Fraction.add h h) hfull k (blocks j) (Nat.le_of_lt hk))
      (Fraction.le_of_equiv (coarse_time T j))
    have hstate : Fraction.le (TimeCalibration.norm tau q) M := by
      dsimp only [q]
      rw [CalibratedRefinement.coarseAt_eq_run]
      exact run_state_bound o E0 T tau L s hE d j (Fraction.add h h) hfull k htime
    have hp := Fraction.magnitudes.le_trans
      (TimeCalibration.position_le_norm tau q (Int.le_of_lt d.calibration_positive)) hstate
    have hv := Fraction.magnitudes.le_trans
      (TimeCalibration.velocity_le_norm_inverse tau q d.calibration_positive)
      (Fraction.mul_le_mul_nonnegative hstate (TimeCalibration.inverse tau d.calibration_positive)
        (Int.le_of_lt tau.den_pos))
    have hM := CalibratedGrowth.cap_nonnegative tau T (Fraction.mul (Fraction.ofInt 2) E0) s
      (Int.le_of_lt d.calibration_positive) d.time_nonnegative
      (Fraction.nonnegative_mul _ _ (by decide) (Int.le_of_lt hE))
    have hh := Fraction.abs_of_nonnegative h d.time_nonnegative
    have hdrift := Fraction.le_equiv_right (cell_position_growth a h q)
      (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.mul_equiv hh (Fraction.equiv_refl _)))
    have hvelocity := Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative_left hv h d.time_nonnegative)
      (Fraction.mul_le_mul_nonnegative (duration_le_window T d.time_nonnegative (j+1))
        (Fraction.mul M (TimeCalibration.inverse tau d.calibration_positive))
        (Fraction.nonnegative_mul _ _ hM (Int.le_of_lt tau.den_pos)))
    have hposition : Fraction.le (pointNorm (cell a h q).1)
        (shadowCap E0 T tau s d.calibration_positive) :=
      Fraction.magnitudes.le_trans hdrift (Fraction.add_le_add hp hvelocity)
    exact Fraction.magnitudes.le_trans (field_growth o E0 T tau L hE d j _)
      (Fraction.add_le_add_right (Fraction.mul_le_mul_nonnegative_left hposition L d.lipschitz.1) _)

end NewtonLimitDynamics.Polygon.GeneralForceGrowth
