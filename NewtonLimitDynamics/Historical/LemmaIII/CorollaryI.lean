import BarrowLib.Polygon.RationalBoundary
import NewtonLimitDynamics.Historical.LemmaIII
/-! Historical result: lemma_iii_corollary_i.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Primary rational approximation with explicit geometric and regularity premises. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par7
Anchor URLs: NATP00077.par7 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par7
Proof-step correspondence: The edition's Lemma III derives lower/upper area errors for a separately assigned rational curved area under explicit area rules. A separate rectangle-endpoint-cover approximation follows from supplied uniform continuity and shrinking mesh. This cover is not the whole staircase perimeter; general curved-area existence and ultimate geometric identification remain open.
Historical dependency ledger for this exact witness:
- P1687.L3 → P1687.L3C1; passage NATP00077.par7; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par7; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00077.par7
Corol. 1. Hinc summa ultima parallelogrammorum evanescentium coincidit omni ex parte cum figura curvilinea.
LATIN END NATP00077.par7 -/

namespace Principia1687.LemmaIII

open NewtonLimitDynamics NewtonLimitDynamics.Polygon

/-- Conditional rational-area approximation through the separately proved
Lemma III. Existence or rationality of curvilinear area is not asserted. -/
theorem corollary1_area_approximation (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (MonotoneRectangles.lowerSum g (parts m)) A).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (MonotoneRectangles.upperSum g (parts m))).abs) :=
  (unequal_width_curved_area_approximation area g a b A parts hg hbase hA hmesh).2

/-- Rectangle endpoint covers approach the given rational curve in both
directions under the explicit continuity and mesh premises. This is a
boundary reconstruction separate from the preceding area assertion. -/
theorem corollary1_rectangle_boundary (f : Fraction → TimeSubdivision.Point) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b) (hf : RationalBoundary.UniformOn f a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => RationalBoundary.RectangleTrace f (parts m))
      (RationalBoundary.CurveTrace f a b) :=
  RationalBoundary.rectangle_approaches f a b parts hf hmesh

end Principia1687.LemmaIII

/-! 1713. Its own primary rational approximation with explicit premises. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par8
Anchor URLs: NATP00082.par8 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par8
Proof-step correspondence: The edition's Lemma III derives lower/upper area errors for a separately assigned rational curved area under explicit area rules. A separate rectangle-endpoint-cover approximation follows from supplied uniform continuity and shrinking mesh. This cover is not the whole staircase perimeter; general curved-area existence and ultimate geometric identification remain open.
Historical dependency ledger for this exact witness:
- P1713.L3 → P1713.L3C1; passage NATP00082.par8; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par8; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00082.par8
Corol. 1. Hinc summa ultima parallelogrammorum evanescentium coincidit omni ex parte cum Figura curvilinea.
LATIN END NATP00082.par8 -/

namespace Principia1713.LemmaIII

open NewtonLimitDynamics NewtonLimitDynamics.Polygon

/-- Conditional rational-area approximation through the separately proved
Lemma III. Existence or rationality of curvilinear area is not asserted. -/
theorem corollary1_area_approximation (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (MonotoneRectangles.lowerSum g (parts m)) A).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (MonotoneRectangles.upperSum g (parts m))).abs) :=
  (unequal_width_curved_area_approximation area g a b A parts hg hbase hA hmesh).2

/-- Rectangle endpoint covers approach the given rational curve in both
directions under the explicit continuity and mesh premises. This is a
boundary reconstruction separate from the preceding area assertion. -/
theorem corollary1_rectangle_boundary (f : Fraction → TimeSubdivision.Point) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b) (hf : RationalBoundary.UniformOn f a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => RationalBoundary.RectangleTrace f (parts m))
      (RationalBoundary.CurveTrace f a b) :=
  RationalBoundary.rectangle_approaches f a b parts hf hmesh

end Principia1713.LemmaIII
