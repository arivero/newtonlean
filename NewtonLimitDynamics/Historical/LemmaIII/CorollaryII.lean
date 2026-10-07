import BarrowLib.Polygon.RationalBoundary
import NewtonLimitDynamics.Historical.LemmaIII.CorollaryI
/-! Historical result: lemma_iii_corollary_ii.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Primary rational approximation with explicit geometric and regularity premises. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par8
Anchor URLs: NATP00077.par8 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par8
Proof-step correspondence: Chord traces lie between sampled nodes and endpoint rectangles; the edition's Corollary I and elementary node approximation derive two-sided approach to the given rational curve. Uniform continuity and shrinking mesh are supplied. The theorem does not infer area or arclength convergence.
Historical dependency ledger for this exact witness:
- P1687.L3C1 → P1687.L3C2; passage NATP00077.par8; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par8; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00077.par8
Corol. 2. Et multo magis figura rectilinea, quæ chordis evanescentium arcuum ab, bc, cd, &c. comprehenditur, coincidit ultimo cum figura curvilinea.
LATIN END NATP00077.par8 -/

namespace Principia1687.LemmaIII

open NewtonLimitDynamics NewtonLimitDynamics.Polygon

/-- Chord points lie in the endpoint rectangles and all sampled nodes lie
on chords. The two-sided rational boundary conclusion uses Corollary I,
not a supplied chord-convergence premise. No arclength or curved area
conclusion follows from this theorem. -/
theorem corollary2_chord_boundary (f : Fraction → TimeSubdivision.Point) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b) (hf : RationalBoundary.UniformOn f a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => RationalBoundary.ChordTrace f (parts m))
      (RationalBoundary.CurveTrace f a b) :=
  RationalBoundary.trace_sandwich _ _ _ _ (RationalBoundary.nodes_approach f a b parts hf hmesh)
    (corollary1_rectangle_boundary f a b parts hf hmesh)
    (fun m x hx => RationalBoundary.nodes_in_chords f (parts m) x hx)
    (fun m x hx => RationalBoundary.chords_in_rectangles f (parts m) x hx)

end Principia1687.LemmaIII

/-! 1713. Its own primary rational approximation with explicit premises. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par9
Anchor URLs: NATP00082.par9 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par9
Proof-step correspondence: Chord traces lie between sampled nodes and endpoint rectangles; the edition's Corollary I and elementary node approximation derive two-sided approach to the given rational curve. Uniform continuity and shrinking mesh are supplied. The theorem does not infer area or arclength convergence.
Historical dependency ledger for this exact witness:
- P1713.L3C1 → P1713.L3C2; passage NATP00082.par9; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par9; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00082.par9
Corol. 2. Et multo magis Figura rectilinea, quæ chordis evanescentium arcuum ab, bc, cd, &c. comprehenditur, coincidit ultimo cum Figura curvilinea.
LATIN END NATP00082.par9 -/

namespace Principia1713.LemmaIII

open NewtonLimitDynamics NewtonLimitDynamics.Polygon

/-- Chord points lie in the endpoint rectangles and all sampled nodes lie
on chords. The two-sided rational boundary conclusion uses Corollary I,
not a supplied chord-convergence premise. No arclength or curved area
conclusion follows from this theorem. -/
theorem corollary2_chord_boundary (f : Fraction → TimeSubdivision.Point) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b) (hf : RationalBoundary.UniformOn f a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => RationalBoundary.ChordTrace f (parts m))
      (RationalBoundary.CurveTrace f a b) :=
  RationalBoundary.trace_sandwich _ _ _ _ (RationalBoundary.nodes_approach f a b parts hf hmesh)
    (corollary1_rectangle_boundary f a b parts hf hmesh)
    (fun m x hx => RationalBoundary.nodes_in_chords f (parts m) x hx)
    (fun m x hx => RationalBoundary.chords_in_rectangles f (parts m) x hx)

end Principia1713.LemmaIII
