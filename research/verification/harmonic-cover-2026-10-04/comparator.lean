import NewtonLimitDynamics.Polygon.HarmonicCover

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open NewtonLimitDynamics
open NewtonLimitDynamics.Polygon
open NewtonLimitDynamics.Polygon.PointBounds
open NewtonLimitDynamics.Polygon.TimeSubdivision
open NewtonLimitDynamics.Polygon.HarmonicAccumulation
open NewtonLimitDynamics.Polygon.HarmonicComparison
open NewtonLimitDynamics.Polygon.HarmonicCover

private def f (num den : Int) (hden : 0 < den) : Fraction := ⟨num, den, hden⟩
def holdW : Fraction := f (-2) 3 (by decide)
def holdH : Fraction := f 1 24 (by decide)
def holdInitial : Point × Point :=
  ((f (-1008) 2520 (by decide), f 1080 2520 (by decide)),
   (f 1120 2520 (by decide), f (-1575) 2520 (by decide)))
def referencePoint (x y den : Int) (hden : 0 < den) : Point :=
  (f x den hden, f y den hden)
def referenceState (x y vx vy den : Int) (hden : 0 < den) : Point × Point :=
  (referencePoint x y den hden, referencePoint vx vy den hden)

theorem coarse_block_coordinates_match :
    stateEquiv (coarseAt holdW holdH holdInitial 0)
        (referenceState (-1008) 1080 1120 (-1575) 2520 (by decide)) ∧
    stateEquiv (coarseAt holdW holdH holdInitial 1)
        (referenceState (-395136) 409860 461888 (-657630) 1088640 (by decide)) ∧
    stateEquiv (coarseAt holdW holdH holdInitial 2)
        (referenceState (-154070784) 153384840 190976128 (-275574780)
          470292480 (by decide)) := by
  decide

theorem fine_block_coordinates_match :
    stateEquiv (fineAt holdW holdH holdInitial 0)
        (referenceState (-1008) 1080 1120 (-1575) 2520 (by decide)) ∧
    stateEquiv (fineAt holdW holdH holdInitial 1)
        (referenceState (-2734502400) 2836458000 3188606848 (-4539997980)
          7524679680 (by decide)) ∧
    stateEquiv (fineAt holdW holdH holdInitial 2)
        (referenceState (-7380744276068352) 7349070466451520
          9100317614284288 (-13132643542688880)
          22468573129605120 (by decide)) := by
  decide

theorem final_state_error_matches :
    Fraction.equiv
      (stateNorm (stateSub (fineAt holdW holdH holdInitial 2)
        (coarseAt holdW holdH holdInitial 2)))
      (f 45970688072946954240000
        10566800979183353305497600 (by decide)) := by
  decide

theorem cover_radius_matches :
    Fraction.equiv (radius holdW holdH holdInitial 2)
      (f 1492296 4354560 (by decide)) := by
  decide

theorem cover_budget_matches :
    Fraction.equiv (coverBudget holdW holdH holdInitial 2)
      (f 17815578812928 18962192793600 (by decide)) := by
  decide

#print axioms coarse_block_coordinates_match
#print axioms fine_block_coordinates_match
#print axioms final_state_error_matches
#print axioms cover_radius_matches
#print axioms cover_budget_matches
