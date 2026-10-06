import ModernLib.Polygon.RegionConfinement
import ModernLib.Polygon.HarmonicGeneralEndpoint

/-! Scope controls for the finite A.6 invariant. These are kernel-checked
instances and a degenerate countermodel, not an independent numerical orbit
or a Kepler force implementation. No global force bound is supplied. -/

namespace RegionConfinementControls
open NewtonLimitDynamics Polygon
open TimeSubdivision PointBounds HarmonicStability RegionConfinement

private def z : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1
private def two : Fraction := Fraction.ofInt 2
private def quarter : Fraction := ⟨1,4,by decide⟩
private def eighth : Fraction := ⟨1,8,by decide⟩
private def initial : Point × Point := ((⟨1,2,by decide⟩,z),(z,one))

private def frame : Frame (fun _ => True) eighth two quarter two initial where
  time_nonnegative := by decide
  bound_nonnegative := by decide
  inner_zero_or_speed_positive := Or.inr (by decide)
  areal_bound := by unfold Fraction.le; decide
  outer_bound := by unfold Fraction.le; decide
  contains_band := fun _ _ => True.intro

private theorem bounded_in_band (p : Point) (hp : Band quarter two p) :
    Fraction.le (pointNorm (linearField one p)) two :=
  Fraction.le_equiv_left (HarmonicGeneralEndpoint.linear_sample_norm one p)
    (Fraction.le_equiv_left (by simp [one,Fraction.equiv,Fraction.mul,Fraction.ofInt,
      Fraction.abs]) hp.2)

example : Frame (fun _ => True) z z z one ((z,z),(z,z)) :=
  ball_frame _ z z one _ (by decide) (by decide)
    (by unfold Fraction.le; decide) (fun _ _ => True.intro)

example (h : Fraction) (hh : 0 ≤ h.num) (n : Nat)
    (hn : Fraction.le (BoundedIteration.time h n) eighth) :
    Band quarter two (BoundedIteration.run (linearField one) h initial n).1 :=
  run_band _ eighth two quarter two initial frame _ (linearField_central one)
    bounded_in_band h hh n hn

example (m k : Nat) (hk : k < HarmonicDyadic.blocks m) :
    Band quarter two (FiniteEstimates.cell (linearField one) (HarmonicDyadic.duration eighth (m+1))
      (FiniteAccumulation.coarseAt (linearField one) (HarmonicDyadic.duration eighth (m+1)) initial k)).1 ∧
    Band quarter two (FiniteEstimates.twoHalf (linearField one) (HarmonicDyadic.duration eighth (m+1))
      (FiniteAccumulation.coarseAt (linearField one) (HarmonicDyadic.duration eighth (m+1)) initial k)).1 :=
  shadow_bands _ eighth two quarter two initial frame _ (linearField_central one)
    bounded_in_band m k hk

/-- A zero speed invalidates cancellation for a positive inner radius. -/
example :
    Fraction.le (Fraction.mul one z) (det (z,z) (z,z)).abs ∧
    Fraction.le (pointNorm (z,z)) z ∧ ¬ Fraction.le one (pointNorm (z,z)) := by
  unfold Fraction.le
  decide

end RegionConfinementControls
