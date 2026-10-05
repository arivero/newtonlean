import NewtonLimitDynamics.Polygon.GeneralForceGrowth
import NewtonLimitDynamics.Polygon.GeneralForceAccelerationSecants
import NewtonLimitDynamics.Polygon.GeneralForceQuadraticSecants
import NewtonLimitDynamics.Polygon.HarmonicGeneralEndpoint

/-! Regional construction controls. The proper annulus excludes the origin;
its curve and completed force use derived certificates at every mesh. The
regular-ball control supplies regularity only on the computed finite ball.
These harmonic controls exercise the interface, not the pending Kepler law. -/
namespace RegionalConstructionControls
open NewtonLimitDynamics Polygon
open TimeSubdivision PointBounds HarmonicStability RegionConfinement ForceClasses
open CauchyValues BinaryTime PositionValues GeneralForceEndpoint GeneralForceTime
private def z : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1
private def two : Fraction := Fraction.ofInt 2
private def quarter : Fraction := ⟨1,4,by decide⟩
private def eighth : Fraction := ⟨1,8,by decide⟩
private def initial : Point × Point := ((⟨1,2,by decide⟩,z),(z,one))

private def oracle : CentralOracle where
  toOracle := { exactOracle (linearField one) with
    region := Band quarter two
    coherent := by
      intro _ _ _ _ _
      exact Fraction.le_of_equiv (HarmonicAccumulation.stateSub_self_norm_zero _) }
  inward := fun _ _ => ⟨one,by decide,⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

private def frame : Frame oracle.region eighth two quarter two initial where
  time_nonnegative := by decide
  bound_nonnegative := by decide
  inner_zero_or_speed_positive := Or.inr (by decide)
  areal_bound := by unfold Fraction.le; decide
  outer_bound := by unfold Fraction.le; decide
  contains_band := fun _ hp => hp

private theorem lipschitz : LipschitzOn oracle.toOracle one.abs := by
  refine ⟨Fraction.abs_num_nonnegative _, ?_⟩
  intro n p q _ _
  exact (harmonic_lipschitz_on one (by decide)).2 n p q True.intro True.intro

private theorem bounded (j : Nat) (p : Point) (hp : Band quarter two p) :
    Fraction.le (pointNorm (oracle.sample j p)) two :=
  Fraction.le_equiv_left (HarmonicGeneralEndpoint.linear_sample_norm one p)
    (Fraction.le_equiv_left (by simp [one,Fraction.equiv,Fraction.mul,Fraction.ofInt,
      Fraction.abs]) hp.2)

private theorem window (h : Fraction) (hh : 0 ≤ h.num) (n : Nat)
    (ht : Fraction.le (BoundedIteration.time h n) eighth) :
    TimeCalibration.Window one h one.abs (by decide) n := by
  apply TimeCalibration.window_of_elapsed one h eighth one.abs (by decide)
    (Fraction.abs_num_nonnegative one) n _ (by unfold Fraction.le; decide)
  exact Fraction.le_equiv_left
    (Fraction.mul_equiv (Fraction.equiv_refl _) (Fraction.abs_of_nonnegative h hh)) ht

private def E0 : Fraction := ⟨1,16,by decide⟩
private def conditions : GeneralForcePrefix.Conditions oracle E0 eighth one one.abs two initial (by decide) where
  calibration_positive := by decide
  lipschitz := lipschitz
  window := by unfold Fraction.le; decide
  inner_radius := quarter
  outer_radius := two
  frame := frame
  samples_on_band := fun j p hp => bounded _ p hp

example : ¬ oracle.region zeroPoint := by
  change ¬ Band quarter two zeroPoint
  intro hp
  have h := hp.1
  unfold Fraction.le pointNorm zeroPoint at h
  contradiction

example (j : Nat) :
    Band quarter two (endpoint oracle E0 eighth (by decide) initial j).1 :=
  conditions.toConditions.run_band j (HarmonicDyadic.duration eighth j)
    conditions.time_nonnegative (HarmonicDyadic.blocks j) (Fraction.le_of_equiv (HarmonicDyadic.blocks_duration eighth j))

example (j k : Nat) (hk : k < HarmonicDyadic.blocks j) :
    Band quarter two (FiniteEstimates.twoHalf (field oracle E0 (by decide) j)
      (HarmonicDyadic.duration eighth (j+1))
      (FiniteAccumulation.coarseAt (field oracle E0 (by decide) j)
        (HarmonicDyadic.duration eighth (j+1)) initial k)).1 :=
  (shadow_bands oracle.region eighth two quarter two initial frame _
    (sample_central oracle _) (conditions.samples_on_band j) j k hk).2

example (x : BinaryTime eighth (by decide)) :
    Within (positionValue (gammaValue oracle E0 eighth one one.abs two initial (by decide) conditions x))
      (embed (zeroPoint,zeroPoint)) two ∧
      ∀ D, Within (positionValue (gammaValue oracle E0 eighth one one.abs two initial (by decide) conditions x))
        (embed (zeroPoint,zeroPoint)) D → Fraction.le quarter D :=
  gamma_band oracle E0 eighth one one.abs two initial (by decide) conditions x

example (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m → ∀ b : Nat → Bool,
      Within (GeneralForceAccelerationSecants.cellAccelerationSecant oracle E0 eighth one one.abs two
          initial (by decide) conditions (by decide) m (HarmonicBinaryPrefix.ticks b m))
        (CompletedForce.forceValue oracle E0 one.abs (by decide) lipschitz
          (gammaValue oracle E0 eighth one one.abs two initial (by decide) conditions (Quotient.mk _ b))
          (gamma_admissible oracle E0 eighth one one.abs two initial (by decide) conditions (Quotient.mk _ b))) eps :=
  GeneralForceAccelerationSecants.dyadic_acceleration_uniform_identification oracle E0 eighth one one.abs two
    initial (by decide) conditions (by decide) eps heps

private def ballOracle : CentralOracle where
  toOracle := { exactOracle (linearField one) with
    region := fun p => Fraction.le (pointNorm p) (GeneralForceGrowth.shadowCap E0 eighth one initial (by decide))
    coherent := by
      intro _ _ _ _ _
      exact Fraction.le_of_equiv (HarmonicAccumulation.stateSub_self_norm_zero _) }
  inward := fun _ _ => ⟨one,by decide,⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

private def ballData : GeneralForceGrowth.Data ballOracle E0 eighth one one.abs initial where
  time_nonnegative := by decide
  calibration_positive := by decide
  lipschitz := by
    refine ⟨Fraction.abs_num_nonnegative _,?_⟩
    intro n p q _ _
    exact (harmonic_lipschitz_on one (by decide)).2 n p q True.intro True.intro
  window := by unfold Fraction.le; decide
  ball_contained := fun _ hp => hp

example : ¬ ballOracle.region (Fraction.ofInt 100,z) := by
  unfold ballOracle Fraction.le GeneralForceGrowth.shadowCap CalibratedGrowth.driftCap
    CalibratedGrowth.cap TimeCalibration.norm pointNorm TimeCalibration.inverse initial E0 eighth one z
    Fraction.add Fraction.mul Fraction.ofInt Fraction.abs
  decide

example (j : Nat) :
    BoundedIteration.BoundedSamples (field ballOracle E0 (by decide) j)
      (HarmonicDyadic.duration eighth j) initial
      (GeneralForceGrowth.forceCap E0 eighth one one.abs initial (by decide)) (HarmonicDyadic.blocks j) :=
  (GeneralForceGrowth.conditions ballOracle E0 eighth one one.abs initial (by decide) ballData).toConditions.actual_samples j

end RegionalConstructionControls
