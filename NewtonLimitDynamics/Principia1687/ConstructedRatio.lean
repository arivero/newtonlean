import NewtonLimitDynamics.Principia1687.LemmaX
import NewtonLimitDynamics.Common.RationalMagnitudes

namespace Principia1687
open NewtonLimitDynamics NewtonLimitDynamics.Fraction

/-- Explicit contact and area-enclosure obligations for the constructed ratio.
    Slopes refer to DOUBLED triangle areas, incorporating the half-area factor.
    Establishing these data from an actual curved diagram remains open. -/
structure ContactEnclosure (s : Fraction → Fraction) (c : Fraction) where
  lowerSlope : Fraction → Fraction
  upperSlope : Fraction → Fraction
  lower_contact : Ultimate magnitudes lowerSlope c
  upper_contact : Ultimate magnitudes upperSlope c
  mechanical_enclosure : Near magnitudes (fun t =>
    le (ratio (fun u => mul (lowerSlope u) (mul u u)) t) (ratio s t) ∧
    le (ratio s t) (ratio (fun u => mul (upperSlope u) (mul u u)) t))

theorem constructed_quadratic_bridge (s : Fraction → Fraction) (c : Fraction)
    (hc : positive c) (p : ContactEnclosure s c) :
    DeMotu1684.QuadraticInitialDeflection magnitudes (ratio s) c := by
  refine ⟨hc, enclosure_reconstruction magnitudes _ _ _ c ?_ ?_ p.mechanical_enclosure⟩
  · exact triangle_normalized_limit p.lowerSlope c p.lower_contact
  · exact triangle_normalized_limit p.upperSlope c p.upper_contact
end Principia1687
