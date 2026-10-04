import NewtonLimitDynamics.Polygon.HarmonicCover

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open NewtonLimitDynamics
open NewtonLimitDynamics.Polygon
open NewtonLimitDynamics.Polygon.HarmonicAccumulation
open NewtonLimitDynamics.Polygon.TimeSubdivision
open NewtonLimitDynamics.Polygon.HarmonicCover

private def f (num den : Int) (hden : 0 < den) : Fraction := ⟨num, den, hden⟩
def holdW : Fraction := f (-2) 3 (by decide)
def holdH : Fraction := f 1 24 (by decide)
def holdInitial : Point × Point :=
  ((f (-1008) 2520 (by decide), f 1080 2520 (by decide)),
   (f 1120 2520 (by decide), f (-1575) 2520 (by decide)))

-- Deliberately corrupt the reference radius numerator by +1.
theorem corrupted_radius_comparator_should_fail :
    Fraction.equiv (radius holdW holdH holdInitial 2)
      (f 1492297 4354560 (by decide)) := by
  decide
