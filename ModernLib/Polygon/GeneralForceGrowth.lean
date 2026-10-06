import ModernLib.Polygon.GeneralForcePrefix
import BarrowLib.Polygon.CalibratedGrowth

/-! Derive the motion-sample bounds on a finite ball from regional linear
force growth and the calibrated window. The ball budget is closed before
sampling, using only initial-state magnitudes and force data. Actual and
shadow confinement then follow from the shared partial-time invariant.
Singular laws use the annular constructor rather than growth at the origin. -/

namespace NewtonLimitDynamics.Polygon.GeneralForceGrowth
open NewtonLimitDynamics TimeSubdivision PointBounds HarmonicDyadic ForceClasses
open FiniteEstimates
open GeneralForceEndpoint GeneralForcePrecision

def shadowCap (E0 T tau : Fraction) (s : Point × Point) (ht : 0 < tau.num) : Fraction :=
  CalibratedGrowth.driftCap tau T (Fraction.mul (Fraction.ofInt 2) E0) s ht

def forceCap (E0 T tau L : Fraction) (s : Point × Point) (ht : 0 < tau.num) : Fraction :=
  Fraction.add (Fraction.mul L (shadowCap E0 T tau s ht)) (Fraction.mul (Fraction.ofInt 2) E0)

structure Data (o : CentralOracle) (E0 T tau L : Fraction) (s : Point × Point) where
  time_nonnegative : 0 ≤ T.num
  calibration_positive : 0 < tau.num
  lipschitz : LipschitzOn o.toOracle L
  window : Fraction.le
    (Fraction.mul T (TimeCalibration.rate tau L calibration_positive)) ⟨1,2,by decide⟩
  ball_contained : ∀ p, Fraction.le (pointNorm p) (shadowCap E0 T tau s calibration_positive) →
    o.region p

theorem shadowCap_nonnegative (E0 T tau : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (ht : 0 < tau.num) :
    0 ≤ (shadowCap E0 T tau s ht).num := by
  have hM := CalibratedGrowth.cap_nonnegative tau T (Fraction.mul (Fraction.ofInt 2) E0) s
    (Int.le_of_lt ht) hT (Fraction.nonnegative_mul _ _ (by decide) (Int.le_of_lt hE))
  exact Fraction.nonnegative_add _ _ hM
    (Fraction.nonnegative_mul _ _ hT
      (Fraction.nonnegative_mul _ _ hM (Int.le_of_lt tau.den_pos)))

/-- Chosen force precision gives a growth estimate only at regional points. -/
theorem field_growth (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o E0 T tau L s)
    (j : Nat) (p : Point) (hp : o.region p) :
    Fraction.le (pointNorm (field o E0 hE j p))
      (Fraction.add (Fraction.mul L (pointNorm p)) (Fraction.mul (Fraction.ofInt 2) E0)) := by
  have hzero : o.region (Fraction.ofInt 0,Fraction.ofInt 0) := d.ball_contained _ (by
    simpa [Fraction.le,pointNorm,Fraction.add,Fraction.abs,Fraction.ofInt] using
      (shadowCap_nonnegative E0 T tau s hE d.time_nonnegative d.calibration_positive))
  have he := Fraction.magnitudes.lt_implies_le (precision_error o.toOracle E0 hE j)
  have ht : Fraction.le (GeometricTail.tailCap E0 j) E0 :=
    duration_le_window E0 (Int.le_of_lt hE) j
  have herr := Fraction.add_le_add (Fraction.magnitudes.le_trans he ht)
    (Fraction.magnitudes.le_trans he ht)
  have htwo : Fraction.equiv (Fraction.add E0 E0) (Fraction.mul (Fraction.ofInt 2) E0) := by
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt]
    simp only [show (2:Int)=1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  exact Fraction.magnitudes.le_trans
    (sample_linear_growth o L d.lipschitz hzero _ p hp)
    (Fraction.add_le_add_left (Fraction.le_equiv_right herr htwo) _)

theorem forceCap_nonnegative (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o E0 T tau L s) :
    0 ≤ (forceCap E0 T tau L s d.calibration_positive).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ d.lipschitz.1
      (shadowCap_nonnegative E0 T tau s hE d.time_nonnegative d.calibration_positive))
    (Fraction.nonnegative_mul _ _ (by decide) (Int.le_of_lt hE))

/-- The outer budget follows from the existing calibrated window. No
membership of an iterate or shadow is included in Data. -/
def region_frame (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o E0 T tau L s) :
    RegionConfinement.Frame o.region T (forceCap E0 T tau L s d.calibration_positive)
      (Fraction.ofInt 0) (shadowCap E0 T tau s d.calibration_positive) s :=
  RegionConfinement.ball_frame o.region T _ _ s d.time_nonnegative
    (forceCap_nonnegative o E0 T tau L s hE d)
    (CalibratedGrowth.driftCap_budget tau T L (Fraction.mul (Fraction.ofInt 2) E0) s
      d.calibration_positive d.time_nonnegative d.lipschitz.1
      (Fraction.nonnegative_mul _ _ (by decide) (Int.le_of_lt hE)) d.window)
    d.ball_contained

theorem field_bound_on_ball (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o E0 T tau L s)
    (j : Nat) (p : Point)
    (hp : RegionConfinement.Band (Fraction.ofInt 0)
      (shadowCap E0 T tau s d.calibration_positive) p) :
    Fraction.le (pointNorm (field o E0 hE j p)) (forceCap E0 T tau L s d.calibration_positive) :=
  Fraction.magnitudes.le_trans
    (field_growth o E0 T tau L s hE d j p (d.ball_contained p hp.2))
    (Fraction.add_le_add_right (Fraction.mul_le_mul_nonnegative_left hp.2 L d.lipschitz.1) _)

/-- Actual iterates are bounded independently of mesh or level precision. -/
theorem run_state_bound (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o E0 T tau L s)
    (j : Nat) (h : Fraction) (hh : 0 ≤ h.num) (n : Nat)
    (hn : Fraction.le (BoundedIteration.time h n) T) :
    Fraction.le (TimeCalibration.norm tau (BoundedIteration.run (field o E0 hE j) h s n))
      (CalibratedGrowth.cap tau T (Fraction.mul (Fraction.ofInt 2) E0) s) := by
  have he := Fraction.le_equiv_left
    (Fraction.mul_equiv (Fraction.equiv_refl (Fraction.ofInt (n:Int)))
      (Fraction.abs_of_nonnegative h hh)) hn
  apply CalibratedGrowth.run_norm_le_cap_at tau d.calibration_positive _ h T L _ s
    d.lipschitz.1 (Fraction.nonnegative_mul _ _ (by decide) (Int.le_of_lt hE)) n _ he d.window
  intro k hk
  have hb := RegionConfinement.run_band o.region T _ _ _ s
    (region_frame o E0 T tau L s hE d) _ (sample_central o _)
    (field_bound_on_ball o E0 T tau L s hE d j) h hh (k+1)
    (Fraction.magnitudes.le_trans (BoundedIteration.time_monotone h hh (k+1) n (by omega)) hn)
  exact field_growth o E0 T tau L s hE d j _ (d.ball_contained _ hb.2)

/-- One finite argument covers actual and doubled-half meshes. -/
theorem bounded_samples (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o E0 T tau L s)
    (j : Nat) (h : Fraction) (hh : 0 ≤ h.num) (n : Nat)
    (hn : Fraction.le (BoundedIteration.time h n) T) :
    BoundedIteration.BoundedSamples (field o E0 hE j) h s
      (forceCap E0 T tau L s d.calibration_positive) n :=
  RegionConfinement.run_bounded_samples o.region T _ _ _ s
    (region_frame o E0 T tau L s hE d) _ (sample_central o _)
    (field_bound_on_ball o E0 T tau L s hE d j) h hh n hn

/-- The existing regional construction needs only the ball force contract;
all actual, coarse and both shadow certificates are derived internally. -/
def conditions (o : CentralOracle) (E0 T tau L : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Data o E0 T tau L s) :
    GeneralForcePrefix.Conditions o E0 T tau L
      (forceCap E0 T tau L s d.calibration_positive) s hE where
  calibration_positive := d.calibration_positive
  lipschitz := d.lipschitz
  window := d.window
  inner_radius := Fraction.ofInt 0
  outer_radius := shadowCap E0 T tau s d.calibration_positive
  frame := region_frame o E0 T tau L s hE d
  samples_on_band := field_bound_on_ball o E0 T tau L s hE d

end NewtonLimitDynamics.Polygon.GeneralForceGrowth
