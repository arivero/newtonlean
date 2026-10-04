import NewtonLimitDynamics

/-!
Production-side scope control for HarmonicTimeComparison. This uses project
definitions and the disclosed model, so it is not an independent oracle.
Removing the named short-time premise makes the displayed coefficient false.
Run: lake env lean research/verification/harmonic-time-scope-2026-10-04.lean
-/

namespace NewtonLimitDynamics.Verification.HarmonicTimeScope

open NewtonLimitDynamics.Polygon
open TimeSubdivision PointBounds HarmonicComparison HarmonicDyadic
open HarmonicTimeComparison

private def z : Fraction := ⟨0, 1, by decide⟩
private def o : Fraction := ⟨1, 1, by decide⟩
private def hundred : Fraction := ⟨100, 1, by decide⟩
private def s : Point × Point := ((o, z), (z, o))

theorem actual_large_time_error : Fraction.equiv
    (stateNorm (stateSub (endpoint o hundred s 0) (endpoint o z s 0)))
    (Fraction.ofInt 10200) := by decide

theorem proposed_large_time_budget : Fraction.equiv
    (Fraction.mul (timeLipschitz o s) (durationDifference z hundred).abs)
    (Fraction.ofInt 2400) := by decide

theorem unrestricted_time_bound_false : ¬ Fraction.le
    (stateNorm (stateSub (endpoint o hundred s 0) (endpoint o z s 0)))
    (Fraction.mul (timeLipschitz o s) (durationDifference z hundred).abs) := by
  unfold Fraction.le
  decide

theorem large_time_violates_premise : ¬ DyadicSmallTime o hundred := by
  unfold DyadicSmallTime Fraction.le
  decide

#print axioms unrestricted_time_bound_false
#print axioms large_time_violates_premise

end NewtonLimitDynamics.Verification.HarmonicTimeScope
