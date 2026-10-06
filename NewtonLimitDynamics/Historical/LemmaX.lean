import BarrowLib.Common.RationalMagnitudes
import BarrowLib.Common.Quadratic

/-! Historical result: lemma_x.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Conditional area-diagram reconstruction; velocity-area and enclosures explicit. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par27
Anchor URLs: NATP00077.par27 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par27; NATP00077.par28 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par28
Proof-step correspondence: The checked finite displacement expression below addresses the initial geometric step; the vanishing-time force identification remains open.
Historical dependency ledger for this exact witness:
- P1687.L9 → P1687.L10; passage NATP00077.par28; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par28; status explicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00077.par27
Spatia, quæ corpus urgente quacunq; vi regulari describit, sunt ipso motus initio in duplicata ratione temporum.
LATIN END NATP00077.par27 -/
/- LATIN BEGIN NATP00077.par28
Exponantur tempora per lineas AD, AE, & velocitates genitæ per ordinatas DB, EC, & spatia his velocitatibus descripta erunt ut areæ ABD, ACE his ordinatis descriptæ, hoc est ipso motus initio (per Lemma IX) in duplicata ratione temporum AD, AE. Q.E.D.
LATIN END NATP00077.par28 -/

namespace Principia1687
open NewtonLimitDynamics NewtonLimitDynamics.Fraction

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

theorem discharges_quadraticPremise_reconstruction {Q : Type}
    (g : Magnitudes Q) (ratio : Q → Q) (c : Q)
    (hc : g.positive c) (p : LemmaXPremises g ratio c) :
    NewtonLimitDynamics.QuadraticInitialDeflection g ratio c :=
  ⟨hc, lemmaX_reconstruction g ratio c p⟩

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
    NewtonLimitDynamics.QuadraticInitialDeflection magnitudes (ratio s) c := by
  refine ⟨hc, enclosure_reconstruction magnitudes _ _ _ c ?_ ?_ p.mechanical_enclosure⟩
  · exact constructed_triangle_limit p.lowerSlope c p.lower_contact
  · exact constructed_triangle_limit p.upperSlope c p.upper_contact

end Principia1687

/-! 1713. Distinct edition structure; its geometry references the 1687 formal structure as a mathematical interface, not a historical premise. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par28
Anchor URLs: NATP00082.par28 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par28; NATP00082.par29 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par29
Proof-step correspondence: The checked finite displacement expression below addresses the initial geometric step; the vanishing-time force identification remains open.
Historical dependency ledger for this exact witness:
- P1713.L9 → P1713.L10; passage NATP00082.par29; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par29; status explicit_dependency; confidence high.
- P1687.L10 → P1713.L10; passage NATP00082.par28; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par28; status editorial_interpretation; confidence high.
-/
/- LATIN BEGIN NATP00082.par28
Spatia, quæ corpus urgente quacunque Vi finita describit, sive Vis illa determinata & immutabilis sit, sive eadem continuo augetur vel continuo diminuatur, sunt ipso motus initio in duplicata ratione Temporum.
LATIN END NATP00082.par28 -/
/- LATIN BEGIN NATP00082.par29
Exponantur tempora per lineas AD, AE, & velocitates genitæ per ordinatas DB, EC, & spatia his velocitatibus descripta, erunt ut areæ ABD, ACE his ordinatis descriptæ, hoc est, ipso motus initio (per Lemma IX) in duplicata ratione temporum AD, AE. Q.E.D.
LATIN END NATP00082.par29 -/

namespace Principia1713
open NewtonLimitDynamics

structure LemmaXPremises {Q : Type} (g : Magnitudes Q)
    (ratio : Q → Q) (c : Q) where
  geometry : Principia1687.LemmaXPremises g ratio c

theorem lemmaX_reconstruction {Q : Type} (g : Magnitudes Q)
    (ratio : Q → Q) (c : Q) (p : LemmaXPremises g ratio c) :
    Ultimate g ratio c :=
  Principia1687.lemmaX_reconstruction g ratio c p.geometry

end Principia1713
