import ModernLib.Polygon.GeneralForcePolygonCurve

/-! Historical result: lemma_iii_corollary_iv.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Modern boundary reconstructions only; supporting result also relates to Corollary III but does not prove its area claim. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10
Anchor URLs: NATP00077.par10 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10
Proof-step correspondence: The Corollary IV-specific boundary and chord lemmas below address the cited enclosure step; the combined III-IV support model is in ModernLib.Reconstruction.SupportingBoundary. Identification of the ultimate perimeter with the curve remains open.
Historical dependency ledger for this exact witness:
- P1687.L3 → P1687.L3C4; passage NATP00077.par10; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10; status implicit_dependency; confidence high.
- P1687.L3C1 → P1687.L3C4; passage NATP00077.par10; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10; status implicit_dependency; confidence high.
- P1687.L3C2 → P1687.L3C4; passage NATP00077.par10; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10; status implicit_dependency; confidence high.
- P1687.L3C3 → P1687.L3C4; passage NATP00077.par10; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00077.par10
Corol. 4. Et propterea hæ figuræ ultimæ (quoad perimetros acE,) non sunt rectilineæ, sed rectilinearum limites curvilinci.
LATIN END NATP00077.par10 -/

-- The combined Corollaries III-IV support model is in ModernLib.Reconstruction.SupportingBoundary.
/-
===============================================================================
===============================================================================
===============================================================================
===============================================================================
===============================================================================
ANACHRONICAL PROOFS
-/

namespace Principia1687.LemmaIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon
open TimeSubdivision PositionValues BinaryTime HarmonicDyadic DyadicNodes CurveTrace

theorem corollary4_chord_reconstruction (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f) :
    BoundaryLimit (fun m => chordTrace f (nodeTime T hT m) (blocks m)) (ImageTrace f) :=
  dyadic_chordTrace_limit T hT f hf

theorem corollary4_constructed_polygon_boundary (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0<E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    BoundaryLimit (fun m => ImageTrace
      (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
      (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  GeneralForcePolygonCurve.constructed_polygon_boundary_limit o E0 T tau L B s hE d

end Principia1687.LemmaIII

/-! 1713. Modern boundary reconstructions only; Corollary III remains text-only open. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11
Anchor URLs: NATP00082.par11 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11
Proof-step correspondence: The Corollary IV-specific boundary and chord lemmas below address the cited enclosure step; the combined III-IV support model is in ModernLib.Reconstruction.SupportingBoundary. Identification of the ultimate perimeter with the curve remains open.
Historical dependency ledger for this exact witness:
- P1713.L3 → P1713.L3C4; passage NATP00082.par11; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11; status implicit_dependency; confidence high.
- P1713.L3C1 → P1713.L3C4; passage NATP00082.par11; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11; status implicit_dependency; confidence high.
- P1713.L3C2 → P1713.L3C4; passage NATP00082.par11; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11; status implicit_dependency; confidence high.
- P1713.L3C3 → P1713.L3C4; passage NATP00082.par11; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00082.par11
Corol. 4. Et propterea hæ Figuræ ultimæ (quoad perimetros acE,) non sunt rectilineæ, sed rectilinearum limites curvilinei.
LATIN END NATP00082.par11 -/

namespace Principia1713.LemmaIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon
open TimeSubdivision PositionValues BinaryTime HarmonicDyadic DyadicNodes CurveTrace

theorem corollary4_chord_reconstruction (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f) :
    BoundaryLimit (fun m => chordTrace f (nodeTime T hT m) (blocks m)) (ImageTrace f) :=
  dyadic_chordTrace_limit T hT f hf

theorem corollary4_constructed_polygon_boundary (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0<E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    BoundaryLimit (fun m => ImageTrace
      (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
      (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  GeneralForcePolygonCurve.constructed_polygon_boundary_limit o E0 T tau L B s hE d

end Principia1713.LemmaIII
