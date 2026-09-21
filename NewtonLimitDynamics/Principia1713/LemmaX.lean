import NewtonLimitDynamics.Principia1687.LemmaX

namespace Principia1713
open NewtonLimitDynamics

/-- Shared geometry of the proof, not an assertion that the editions state
    identical mechanical hypotheses. See NATP00082 par28-34. -/
structure LemmaXPremises {Q : Type} (g : Magnitudes Q)
    (ratio : Q → Q) (c : Q) where
  geometry : Principia1687.LemmaXPremises g ratio c

theorem lemmaX_reconstruction {Q : Type} (g : Magnitudes Q)
    (ratio : Q → Q) (c : Q) (p : LemmaXPremises g ratio c) :
    Ultimate g ratio c :=
  Principia1687.lemmaX_reconstruction g ratio c p.geometry

end Principia1713
