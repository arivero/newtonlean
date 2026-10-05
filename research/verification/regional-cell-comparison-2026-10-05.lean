import NewtonLimitDynamics.Polygon.RegionConfinement
import NewtonLimitDynamics.Polygon.HarmonicGeneralEndpoint

/-! A proper annular oracle tests the A.6 comparison interface: the origin
is excluded, and finite cell comparison uses only derived arrival membership.
This is a regional harmonic control, not the pending Kepler instance. -/

namespace RegionalCellComparisonControls
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

example : ¬ oracle.region (z,z) := by
  intro h
  have hn : ¬ Fraction.le quarter (pointNorm (z,z)) := by unfold Fraction.le; decide
  exact hn h.1

example (i j : Nat) (hij : i ≤ j) (h : Fraction) (hh : 0 ≤ h.num)
    (hT : Fraction.le (Fraction.add z h) eighth) :
    Fraction.le (TimeCalibration.distance one
      (FiniteEstimates.cell (oracle.sample i) h initial)
      (FiniteEstimates.cell (oracle.sample j) h initial))
      (Fraction.add
        (Fraction.mul (TimeCalibration.amplification one h one.abs (by decide))
          (TimeCalibration.distance one initial initial))
        (Fraction.mul (Fraction.mul one h.abs)
          (Fraction.add (Fraction.add (oracle.error i) (oracle.error i)) (oracle.error i)))) :=
  sampled_cell_comparison oracle eighth two quarter two initial frame one.abs one
    lipschitz (by decide) i j hij z z h initial initial hh hT hT
    (initial_invariant _ _ _) (initial_invariant _ _ _)

end RegionalCellComparisonControls
