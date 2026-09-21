import NewtonLimitDynamics.Principia1687.LemmaX
import NewtonLimitDynamics.Common.RationalMagnitudes

namespace Principia1687
open NewtonLimitDynamics NewtonLimitDynamics.Fraction

/-- Explicit contact and area-enclosure obligations for the constructed ratio.
    Areas use half base times height; half the secant slope has limit c.
    Establishing these data from an actual curved diagram remains open. -/
structure ContactEnclosure (s : Fraction → Fraction) (c : Fraction) where
  lowerSlope : Fraction → Fraction
  upperSlope : Fraction → Fraction
  lower_contact : Ultimate magnitudes (fun t => half (lowerSlope t)) c
  upper_contact : Ultimate magnitudes (fun t => half (upperSlope t)) c
  mechanical_enclosure : Near magnitudes (fun t =>
    le (ratio (fun u => triangleArea u (mul (lowerSlope u) u)) t) (ratio s t) ∧
    le (ratio s t) (ratio (fun u => triangleArea u (mul (upperSlope u) u)) t))

theorem constructed_quadratic_bridge (s : Fraction → Fraction) (c : Fraction)
    (hc : positive c) (p : ContactEnclosure s c) :
    DeMotu1684.QuadraticInitialDeflection magnitudes (ratio s) c := by
  refine ⟨hc, enclosure_reconstruction magnitudes _ _ _ c ?_ ?_ p.mechanical_enclosure⟩
  · exact constructed_triangle_limit p.lowerSlope c p.lower_contact
  · exact constructed_triangle_limit p.upperSlope c p.upper_contact
end Principia1687
