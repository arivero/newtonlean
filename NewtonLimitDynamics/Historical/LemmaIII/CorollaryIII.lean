import BarrowLib.Polygon.RationalBoundary
import NewtonLimitDynamics.Historical.LemmaIII.CorollaryI
/-! Historical result: lemma_iii_corollary_iii.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Primary rational approximation with explicit geometric and regularity premises. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par9
Anchor URLs: NATP00077.par9 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par9
Proof-step correspondence: Joined supporting segments lie between sampled nodes and endpoint rectangles; the edition's Corollary I and elementary node approximation derive two-sided approach. Supporting-cell geometry, uniform continuity and shrinking mesh are supplied. Identification with actual tangents, circumscribed-figure area and arclength remain open.
Historical dependency ledger for this exact witness:
- P1687.L3 → P1687.L3C3; passage NATP00077.par9; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par9; status implicit_dependency; confidence medium.
-/
/- LATIN BEGIN NATP00077.par9
Corol. 3. Ut & figura rectilinea quæ tangentibus eorundem arcuum circumscribitur.
LATIN END NATP00077.par9 -/

namespace Principia1687.LemmaIII

open NewtonLimitDynamics NewtonLimitDynamics.Polygon

/-- Constructed meetings and their joined finite segments inherit rectangle
enclosure. Tangent identification is separate: the supplied supporting
lines are not asserted to be derivatives of the given curve. This proves
a rational boundary approximation, not a curved area or arclength claim. -/
theorem corollary3_supporting_boundary (f : Fraction → TimeSubdivision.Point) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b) (hf : RationalBoundary.UniformOn f a b)
    (cells : ∀ m i, SupportingTangents.Cell (f ((parts m).nodes i)) (f ((parts m).nodes (i+1))))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => RationalBoundary.SupportingTrace f (parts m) (cells m))
      (RationalBoundary.CurveTrace f a b) :=
  RationalBoundary.trace_sandwich _ _ _ _ (RationalBoundary.nodes_approach f a b parts hf hmesh)
    (corollary1_rectangle_boundary f a b parts hf hmesh)
    (fun m x hx => RationalBoundary.nodes_in_supporting f (parts m) (cells m) x hx)
    (fun m x hx => RationalBoundary.supporting_in_rectangles f (parts m) (cells m) x hx)

end Principia1687.LemmaIII

/-! 1713. Its own primary rational approximation with explicit premises. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par10
Anchor URLs: NATP00082.par10 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par10
Proof-step correspondence: Joined supporting segments lie between sampled nodes and endpoint rectangles; the edition's Corollary I and elementary node approximation derive two-sided approach. Supporting-cell geometry, uniform continuity and shrinking mesh are supplied. Identification with actual tangents, circumscribed-figure area and arclength remain open.
Historical dependency ledger for this exact witness:
- P1713.L3 → P1713.L3C3; passage NATP00082.par10; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par10; status implicit_dependency; confidence medium.
-/
/- LATIN BEGIN NATP00082.par10
Corol. 3. Ut & Figura rectilinea circumscripta quæ tangentibus eorundem arcuum comprehenditur.
LATIN END NATP00082.par10 -/

namespace Principia1713.LemmaIII

open NewtonLimitDynamics NewtonLimitDynamics.Polygon

/-- Constructed meetings and their joined finite segments inherit rectangle
enclosure. Tangent identification is separate: the supplied supporting
lines are not asserted to be derivatives of the given curve. This proves
a rational boundary approximation, not a curved area or arclength claim. -/
theorem corollary3_supporting_boundary (f : Fraction → TimeSubdivision.Point) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b) (hf : RationalBoundary.UniformOn f a b)
    (cells : ∀ m i, SupportingTangents.Cell (f ((parts m).nodes i)) (f ((parts m).nodes (i+1))))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => RationalBoundary.SupportingTrace f (parts m) (cells m))
      (RationalBoundary.CurveTrace f a b) :=
  RationalBoundary.trace_sandwich _ _ _ _ (RationalBoundary.nodes_approach f a b parts hf hmesh)
    (corollary1_rectangle_boundary f a b parts hf hmesh)
    (fun m x hx => RationalBoundary.nodes_in_supporting f (parts m) (cells m) x hx)
    (fun m x hx => RationalBoundary.supporting_in_rectangles f (parts m) (cells m) x hx)

end Principia1713.LemmaIII
