import NewtonLimitDynamics.DeMotu1684.QuadraticDeflection

namespace Principia1687
open NewtonLimitDynamics

/-- Explicit obligations for Newton's area-diagram route (NATP00077 par28).
    Lemma IX geometry and the velocity-area representation remain premises. -/
structure LemmaXPremises {Q : Type} (g : Magnitudes Q)
    (deflectionRatio : Q → Q) (c : Q) where
  areaRatio : Q → Q
  lowerTriangle : Q → Q
  upperTriangle : Q → Q
  velocity_area : ∀ h, deflectionRatio h = areaRatio h
  lower_limit : Ultimate g lowerTriangle c
  upper_limit : Ultimate g upperTriangle c
  enclosure : Near g (fun h => g.le (lowerTriangle h) (areaRatio h) ∧
    g.le (areaRatio h) (upperTriangle h))

theorem lemmaX_reconstruction {Q : Type} (g : Magnitudes Q)
    (ratio : Q → Q) (c : Q) (p : LemmaXPremises g ratio c) :
    Ultimate g ratio c := by
  have heq : ratio = p.areaRatio := funext p.velocity_area
  rw [heq]
  exact enclosure_reconstruction g _ _ _ c p.lower_limit p.upper_limit p.enclosure

/-- Conditional bridge; not a completed historical discharge of Hypothesis 4. -/
theorem discharges_quadraticPremise_reconstruction {Q : Type}
    (g : Magnitudes Q) (ratio : Q → Q) (c : Q)
    (hc : g.positive c) (p : LemmaXPremises g ratio c) :
    DeMotu1684.QuadraticInitialDeflection g ratio c :=
  ⟨hc, lemmaX_reconstruction g ratio c p⟩

end Principia1687
