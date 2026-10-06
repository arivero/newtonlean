import ModernLib.Reconstruction.MonotoneRectangles

/-! Historical result: lemma_iii.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Unequal-width estimate uses maximum width; no union-area theorem. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par5
Anchor URLs: NATP00077.par5 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par5; NATP00077.par6 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par6
Proof-step correspondence: The cross-result finite monotone rectangle model is in ModernLib.Reconstruction.MonotoneRectangles; the final curved-area comparison remains open.
Historical dependency ledger for this exact witness:
- P1687.L2 → P1687.L3; passage NATP00077.par5; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par5; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00077.par5
Eædem rationes ultimæ sunt etiam æqualitatis, ubi parallelogramomrum latitudines AB, BC, CD, &c. sunt inæquales, & omnes minuuntur in infinitum.
LATIN END NATP00077.par5 -/
/- LATIN BEGIN NATP00077.par6
Sit enim AF æqualis latitudini maximæ, & compleatur parallelogrammum FAaf. Hoc erit majus quam differentia figuræ inscriptæ & figuræ circumscriptæ, at latitudine sua AF in infinitum diminuta, minus fiet quam datum quodvis rectangulum.
LATIN END NATP00077.par6 -/


/-! 1713. Unequal-width estimate uses maximum width; no union-area theorem. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par6
Anchor URLs: NATP00082.par6 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par6; NATP00082.par7 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par7
Proof-step correspondence: The cross-result finite monotone rectangle model is in ModernLib.Reconstruction.MonotoneRectangles; the final curved-area comparison remains open.
Historical dependency ledger for this exact witness:
- P1713.L2 → P1713.L3; passage NATP00082.par6; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par6; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00082.par6
Eædem rationes ultimæ sunt etiam æqualitatis, ubi parallelogramomrum latitudines AB, BC, CD &c. sunt inæquales, & omnes minuuntur in infinitum.
LATIN END NATP00082.par6 -/
/- LATIN BEGIN NATP00082.par7
Sit enim AF æqualis latitudini maximæ, & compleatur parallelogrammum FAaf. Hoc erit majus quam differentia Figuræ inscriptæ & Figuræ circumscriptæ; at latitudine sua AF in infinitum diminuta, minus fiet quam datum quodvis rectangulum. Q.E.D.
LATIN END NATP00082.par7 -/

/-
===============================================================================
===============================================================================
===============================================================================
===============================================================================
===============================================================================
ANACHRONICAL PROOFS
-/

/-! The completed-figure and gap estimates below use modern metric closure.
They do not identify the numerical sums with ordinary curvilinear area. -/
namespace Principia1687.LemmaIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

theorem unequal_width_completed_enclosure_and_gap
    (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hmesh : ∀ delta : Fraction, 0 < delta.num → ∃ N : Nat, ∀ m, N ≤ m →
      Fraction.lt (MonotoneRectangles.maxWidth (parts m)) delta) :
    (∀ m, (∀ x, MonotoneRectangles.completed (MonotoneRectangles.lowerFigure g (parts m)) x →
        MonotoneRectangles.completed (MonotoneRectangles.figure g a b) x) ∧
      (∀ x, MonotoneRectangles.completed (MonotoneRectangles.figure g a b) x →
        MonotoneRectangles.completed (MonotoneRectangles.upperFigure g (parts m)) x)) ∧
    (∀ m, (0 ≤ (MonotoneRectangles.lowerSum g (parts m)).num ∧
        0 ≤ (MonotoneRectangles.upperSum g (parts m)).num) ∧
      (0 ≤ (MonotoneRectangles.gap g (parts m)).num ∧
        Fraction.le (MonotoneRectangles.gap g (parts m))
          (Fraction.mul (MonotoneRectangles.maxWidth (parts m))
            (HarmonicTimeComparison.durationDifference (g a) (g b))))) ∧
    (∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ m, N ≤ m →
      Fraction.lt (MonotoneRectangles.gap g (parts m)) eps) :=
  ModernLib.Reconstruction.Principia1687.LemmaIIIII.lemmas2_3_monotone_rectangle_reconstruction
    g a b parts hg hbase hmesh

end Principia1687.LemmaIII

namespace Principia1713.LemmaIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

theorem unequal_width_completed_enclosure_and_gap
    (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hmesh : ∀ delta : Fraction, 0 < delta.num → ∃ N : Nat, ∀ m, N ≤ m →
      Fraction.lt (MonotoneRectangles.maxWidth (parts m)) delta) :
    (∀ m, (∀ x, MonotoneRectangles.completed (MonotoneRectangles.lowerFigure g (parts m)) x →
        MonotoneRectangles.completed (MonotoneRectangles.figure g a b) x) ∧
      (∀ x, MonotoneRectangles.completed (MonotoneRectangles.figure g a b) x →
        MonotoneRectangles.completed (MonotoneRectangles.upperFigure g (parts m)) x)) ∧
    (∀ m, (0 ≤ (MonotoneRectangles.lowerSum g (parts m)).num ∧
        0 ≤ (MonotoneRectangles.upperSum g (parts m)).num) ∧
      (0 ≤ (MonotoneRectangles.gap g (parts m)).num ∧
        Fraction.le (MonotoneRectangles.gap g (parts m))
          (Fraction.mul (MonotoneRectangles.maxWidth (parts m))
            (HarmonicTimeComparison.durationDifference (g a) (g b))))) ∧
    (∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ m, N ≤ m →
      Fraction.lt (MonotoneRectangles.gap g (parts m)) eps) :=
  ModernLib.Reconstruction.Principia1713.LemmaIIIII.lemmas2_3_monotone_rectangle_reconstruction
    g a b parts hg hbase hmesh

end Principia1713.LemmaIII
