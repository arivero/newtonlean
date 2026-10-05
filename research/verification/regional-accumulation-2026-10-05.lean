import NewtonLimitDynamics.Polygon.RegionConfinement
import NewtonLimitDynamics.Polygon.HarmonicGeneralEndpoint

/-! Proper-annulus controls for actual paired accumulation and distinct
represented durations. No regional trace or whole-plane premise is supplied.
The harmonic samples remain a control, not the pending Kepler law. -/

namespace RegionalAccumulationControls
open NewtonLimitDynamics Polygon
open TimeSubdivision PointBounds HarmonicStability RegionConfinement ForceClasses

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

example (i j : Nat) (hij : i ≤ j) (m n : Nat) (hn : n ≤ HarmonicDyadic.blocks m) :
    Fraction.le (TimeCalibration.distance one
      (FiniteAccumulation.fineAt (oracle.sample j) (HarmonicDyadic.duration eighth (m+1)) initial n)
      (FiniteAccumulation.coarseAt (oracle.sample i) (HarmonicDyadic.duration eighth (m+1)) initial n))
      (Fraction.mul (Fraction.ofInt (2*(n : Int)))
        (CalibratedRefinement.blockSource one (HarmonicDyadic.duration eighth (m+1)) one.abs
          (Fraction.add (Fraction.add (oracle.error i) (oracle.error i)) (oracle.error i))
          two (GeneralForceEndpoint.velocityCap eighth two initial) (by decide))) := by
  apply sampled_refinement_bound oracle eighth two quarter two initial frame one.abs one
    lipschitz (by decide) i j hij (bounded i) (bounded j) m n hn
  apply window (HarmonicDyadic.duration eighth (m+1)) frame.time_nonnegative
  exact Fraction.magnitudes.le_trans
    (BoundedIteration.time_monotone (HarmonicDyadic.duration eighth (m+1))
      frame.time_nonnegative (2*n) (2*HarmonicDyadic.blocks m) (by omega))
    (Fraction.le_of_equiv (GeneralForceEndpoint.fine_time eighth m))

example (i j : Nat) (hij : i ≤ j) :
    Fraction.le (TimeCalibration.distance one
      (BoundedIteration.run (oracle.sample i) eighth initial 1)
      (BoundedIteration.run (oracle.sample j) (⟨2,16,by decide⟩ : Fraction) initial 1))
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (Fraction.mul one eighth.abs)
          (Fraction.add (Fraction.add (oracle.error i) (oracle.error i)) (oracle.error i)))) :=
  sampled_equivalent_duration_bound oracle eighth two quarter two initial frame one.abs one
    lipschitz (by decide) i j hij (bounded i) (bounded j) eighth ⟨2,16,by decide⟩ (by decide)
    (by decide) (by decide) 1 (by unfold Fraction.le; decide) (by unfold Fraction.le; decide)
    (window eighth (by decide) 1 (by unfold Fraction.le; decide))

end RegionalAccumulationControls
