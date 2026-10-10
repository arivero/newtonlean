import ModernLib.Reconstruction.MonotoneRectangles
import NewtonLimitDynamics.Historical.LemmaII

/-! Historical result: lemma_iii.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Primary unequal-width exhaustion and conditional geometric area approximation. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par5
Anchor URLs: NATP00077.par5 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par5; NATP00077.par6 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par6
Proof-step correspondence: Maximum width bounds the unequal-width gap and derives its exhaustion. The edition's Lemma I excludes a positive supplied terminal gap; its Lemma II supplies geometric area enclosure and the mutual-ratio reduction. On a nonzero interval with positive starting ordinate, that reduction gives both varying finite-area ratio errors tending to zero without assigning a curved area. Actual finite rectangle unions also approximate a separately assigned rational curved area under explicit area rules. An interior positive ordinate now also derives a fixed positive denominator bound and mutual-ratio convergence on an actual tail, allowing an initially zero lower sum. The positive-patch restriction and interior-rectangle extension are editorial coordinate interpretations (confidence high); general area existence and non-rational coordinate geometry remain open. The assigned-area unit ratios are now derived below by integer-multiple comparisons; full ratio calculus remains outside this scope. A separately labeled project extension below permits an arbitrary assigned area magnitude through explicit X.1 halving and geometric area rules, retaining this edition’s enclosure, gap exhaustion and Lemma I.
Historical dependency ledger for this exact witness:
- P1687.L2 → P1687.L3; passage NATP00077.par5; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par5; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00077.par5
Eædem rationes ultimæ sunt etiam æqualitatis, ubi parallelogramomrum latitudines AB, BC, CD, &c. sunt inæquales, & omnes minuuntur in infinitum.
LATIN END NATP00077.par5 -/
/- LATIN BEGIN NATP00077.par6
Sit enim AF æqualis latitudini maximæ, & compleatur parallelogrammum FAaf. Hoc erit majus quam differentia figuræ inscriptæ & figuræ circumscriptæ, at latitudine sua AF in infinitum diminuta, minus fiet quam datum quodvis rectangulum.
LATIN END NATP00077.par6 -/


/-! Primary unequal-width area reconstruction. The geometric area convention
and any assigned rational curvilinear area remain explicit premises. -/
namespace Principia1687.LemmaIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

theorem unequal_width_gap_vanishes (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun m => MonotoneRectangles.gap g (parts m)) :=
  MonotoneRectangles.gaps_vanish g parts hg hmesh

theorem unequal_width_ultimate_gap_zero (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m)))
    (D : Fraction) (hD : 0 ≤ D.num)
    (hterminal : Exhaustion.TerminalLower Fraction.magnitudes
      (fun m => MonotoneRectangles.gap g (parts m)) D) :
    Fraction.equiv D (Fraction.ofInt 0) :=
  Principia1687.LemmaI.ultimate_difference_zero _ D hD
    (unequal_width_gap_vanishes g a b parts hg hmesh) hterminal

theorem unequal_width_curved_area_approximation (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, area.HasArea (MonotoneRectangles.lowerFigure g (parts m)) (MonotoneRectangles.lowerSum g (parts m)) ∧
      area.HasArea (MonotoneRectangles.upperFigure g (parts m)) (MonotoneRectangles.upperSum g (parts m))) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (MonotoneRectangles.lowerSum g (parts m)) A).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (MonotoneRectangles.upperSum g (parts m))).abs) :=
  ⟨fun m => RectangleContent.lower_upper_areas area g a b (parts m) hg hbase,
    RectangleContent.area_errors_vanish g a b A parts hg
      (fun m => Principia1687.LemmaII.rectangle_area_enclosure area g a b A (parts m) hg hbase hA)
      (unequal_width_gap_vanishes g a b parts hg hmesh)⟩


/-- Unit ratios to a fixed positive assigned rational curved area. The
positive-area premise is required for division; general curved-area
existence and ratios with vanishing denominators are not asserted. -/
theorem unequal_width_area_ratios (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction) (hpositive : 0 < A.num)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference
        (RectangleContent.ratioTo A hpositive (MonotoneRectangles.lowerSum g (parts m)))
        (Fraction.ofInt 1)).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference
        (RectangleContent.ratioTo A hpositive (MonotoneRectangles.upperSum g (parts m)))
        (Fraction.ofInt 1)).abs) := by
  have h := (unequal_width_curved_area_approximation area g a b A parts hg hbase hA hmesh).2
  exact RectangleContent.area_ratios_approach_one A hpositive _ _ h.1 h.2

/-- The same mutual ratios for unequal widths, using this edition's Lemma II
reduction and its own maximum-width exhaustion. Both denominator bounds are
derived from the positive graph patch. No curved-area assignment is needed. -/
theorem unequal_width_mutual_area_ratios (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b)
    (hab : Fraction.lt a b) (hbase : 0 < (g a).num)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, area.HasArea (MonotoneRectangles.lowerFigure g (parts m))
        (MonotoneRectangles.lowerSum g (parts m)) ∧
      area.HasArea (MonotoneRectangles.upperFigure g (parts m))
        (MonotoneRectangles.upperSum g (parts m))) ∧
    RectangleContent.MutualRatiosOne
      (fun m => MonotoneRectangles.lowerSum g (parts m))
      (fun m => MonotoneRectangles.upperSum g (parts m)) :=
  Principia1687.LemmaII.rectangle_mutual_ratios_from_gap area g a b parts hg hab hbase
    (unequal_width_gap_vanishes g a b parts hg hmesh)


/-- The edition's Lemma II interior-rectangle reduction plus its own
maximum-width exhaustion gives both mutual ratios on an actual tail.
The base ordinate may vanish; an interior ordinate must be positive. -/
theorem unequal_width_mutual_area_ratios_interior (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b c : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hac : Fraction.le a c) (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, area.HasArea (MonotoneRectangles.lowerFigure g (parts m))
        (MonotoneRectangles.lowerSum g (parts m)) ∧
      area.HasArea (MonotoneRectangles.upperFigure g (parts m))
        (MonotoneRectangles.upperSum g (parts m))) ∧
    RectangleContent.EventuallyMutualRatiosOne
      (fun m => MonotoneRectangles.lowerSum g (parts m))
      (fun m => MonotoneRectangles.upperSum g (parts m)) :=
  Principia1687.LemmaII.rectangle_mutual_ratios_from_gap_interior area g a b c
    parts hg hbase hac hcb hgc
    (unequal_width_gap_vanishes g a b parts hg hmesh)

/-- Unequal-width approximation of an arbitrary assigned area magnitude.
The own-edition Lemma II enclosure and maximum-width exhaustion give the
addition/comparison error bounds; the own-edition Lemma I excludes a positive
terminal gap. Euclid X.1 remains an explicit supplied magnitude premise.
This precise extension is a project derivation, without an external exact
statement or priority claim; general area existence is not asserted. -/
theorem unequal_width_magnitude_approximation {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    MagnitudeContent.Approximates area g a b A parts ∧
    ∀ D : Q, Exhaustion.TerminalLower area.magnitudes.order
      (fun m => area.magnitudes.embed (MonotoneRectangles.gap g (parts m))) D →
      ¬ area.magnitudes.order.positive D := by
  have hgap := unequal_width_gap_vanishes g a b parts hg hmesh
  exact ⟨⟨fun m => RectangleContent.lower_upper_areas
      (MagnitudeContent.rationalAreas area) g a b (parts m) hg hbase,
    MagnitudeContent.errors_vanish area.magnitudes _ _ A
      (fun m => Principia1687.LemmaII.rectangle_magnitude_enclosure
        area g a b A (parts m) hg hbase hA) hgap⟩,
    fun D hterminal => Principia1687.LemmaI.no_positive_ultimate_difference
      area.magnitudes.order _ D
      (MagnitudeContent.rational_exhaustion area.magnitudes _ hgap) hterminal⟩

/-- All three ultimate unit-ratio comparisons, expressed by integer multiples
of the finite areas and an arbitrary assigned curved-area magnitude. An
interior positive ordinate derives the eventual lower bracket, allowing zero
initial lower sums. Book V comparison language and this exact coordinate
extension are editorial interpretations, not a new Newton quotation.
Area existence, general coordinates and exact finite ratio equality are not
asserted. The exact extended statement and derivation are project provenance. -/
theorem unequal_width_assigned_magnitude_ratios {Q : Type}
    (area : MagnitudeContent.AreaRules Q)
    (R : MagnitudeContent.MultipleRules area.magnitudes)
    (g : Fraction → Fraction) (a b c : Fraction) (A : Q)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hac : Fraction.le a c) (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun k => MonotoneRectangles.maxWidth (parts k))) :
    MagnitudeContent.AreaRatiosOne area.magnitudes
      (fun k => MonotoneRectangles.lowerSum g (parts k))
      (fun k => MonotoneRectangles.upperSum g (parts k)) A :=
  MagnitudeContent.rectangle_magnitude_ratios area R g a b c A parts hg hbase hac hcb hgc
    (fun k => Principia1687.LemmaII.rectangle_magnitude_enclosure area g a b A (parts k) hg hbase hA)
    (unequal_width_gap_vanishes g a b parts hg hmesh)

/-- Uniform-continuity extension to graphs that may rise and fall. This
uses constructed cell bounds, rather than the printed endpoint/telescoping
construction. It is an editorial project derivation: Newton's exact Latin
is retained above; uniform continuity is not quoted as his hypothesis.
All sufficiently fine partitions have actual enclosing rectangle areas and
errors below any given magnitude tolerance. Area existence stays supplied. -/
theorem uniform_graph_rectangle_exhaustion {Q : Type}
    (area : MagnitudeContent.AreaRules Q) (g : Fraction → Fraction)
    (a b : Fraction) (A : Q) (hab : Fraction.le a b)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A) :
    UniformRectangles.Exhausts area g a b A :=
  Principia1687.LemmaII.uniform_graph_rectangle_exhaustion
    area g a b A hab hzero hf hA

/-- Project extension of this witness's mutual-ratio conclusion to graphs
that may rise and fall. A positive ordinate and continuity construct the
fixed positive rectangle; no denominator bound or ratio limit is supplied.
For each unequal positive integer pair, every sufficiently fine partition
gives all three lower/upper/assigned-area comparisons. Exact Latin remains
above; continuity and the coordinate domain are editorial premises. -/
theorem uniform_graph_assigned_magnitude_ratios {Q : Type}
    (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes)
    (g : Fraction → Fraction) (a b c : Fraction) (A : Q)
    (hac : Fraction.le a c) (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A) :
    UniformRectangles.RatiosExhaust area g a b A :=
  Principia1687.LemmaII.uniform_graph_assigned_magnitude_ratios
    area multiples g a b c A hac hcb hgc hzero hf hA

end Principia1687.LemmaIII

/-! 1713. Its own unequal-width exhaustion and conditional geometric area approximation. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par6
Anchor URLs: NATP00082.par6 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par6; NATP00082.par7 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par7
Proof-step correspondence: Maximum width bounds the unequal-width gap and derives its exhaustion. The edition's Lemma I excludes a positive supplied terminal gap; its Lemma II supplies geometric area enclosure and the mutual-ratio reduction. On a nonzero interval with positive starting ordinate, that reduction gives both varying finite-area ratio errors tending to zero without assigning a curved area. Actual finite rectangle unions also approximate a separately assigned rational curved area under explicit area rules. An interior positive ordinate now also derives a fixed positive denominator bound and mutual-ratio convergence on an actual tail, allowing an initially zero lower sum. The positive-patch restriction and interior-rectangle extension are editorial coordinate interpretations (confidence high); general area existence and non-rational coordinate geometry remain open. The assigned-area unit ratios are now derived below by integer-multiple comparisons; full ratio calculus remains outside this scope. A separately labeled project extension below permits an arbitrary assigned area magnitude through explicit X.1 halving and geometric area rules, retaining this edition’s enclosure, gap exhaustion and Lemma I.
Historical dependency ledger for this exact witness:
- P1713.L2 → P1713.L3; passage NATP00082.par6; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par6; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00082.par6
Eædem rationes ultimæ sunt etiam æqualitatis, ubi parallelogramomrum latitudines AB, BC, CD &c. sunt inæquales, & omnes minuuntur in infinitum.
LATIN END NATP00082.par6 -/
/- LATIN BEGIN NATP00082.par7
Sit enim AF æqualis latitudini maximæ, & compleatur parallelogrammum FAaf. Hoc erit majus quam differentia Figuræ inscriptæ & Figuræ circumscriptæ; at latitudine sua AF in infinitum diminuta, minus fiet quam datum quodvis rectangulum. Q.E.D.
LATIN END NATP00082.par7 -/

namespace Principia1713.LemmaIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

theorem unequal_width_gap_vanishes (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun m => MonotoneRectangles.gap g (parts m)) :=
  MonotoneRectangles.gaps_vanish g parts hg hmesh

theorem unequal_width_ultimate_gap_zero (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m)))
    (D : Fraction) (hD : 0 ≤ D.num)
    (hterminal : Exhaustion.TerminalLower Fraction.magnitudes
      (fun m => MonotoneRectangles.gap g (parts m)) D) :
    Fraction.equiv D (Fraction.ofInt 0) :=
  Principia1713.LemmaI.ultimate_difference_zero _ D hD
    (unequal_width_gap_vanishes g a b parts hg hmesh) hterminal

theorem unequal_width_curved_area_approximation (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, area.HasArea (MonotoneRectangles.lowerFigure g (parts m)) (MonotoneRectangles.lowerSum g (parts m)) ∧
      area.HasArea (MonotoneRectangles.upperFigure g (parts m)) (MonotoneRectangles.upperSum g (parts m))) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (MonotoneRectangles.lowerSum g (parts m)) A).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (MonotoneRectangles.upperSum g (parts m))).abs) :=
  ⟨fun m => RectangleContent.lower_upper_areas area g a b (parts m) hg hbase,
    RectangleContent.area_errors_vanish g a b A parts hg
      (fun m => Principia1713.LemmaII.rectangle_area_enclosure area g a b A (parts m) hg hbase hA)
      (unequal_width_gap_vanishes g a b parts hg hmesh)⟩


/-- Unit ratios to a fixed positive assigned rational curved area. The
positive-area premise is required for division; general curved-area
existence and ratios with vanishing denominators are not asserted. -/
theorem unequal_width_area_ratios (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction) (hpositive : 0 < A.num)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference
        (RectangleContent.ratioTo A hpositive (MonotoneRectangles.lowerSum g (parts m)))
        (Fraction.ofInt 1)).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference
        (RectangleContent.ratioTo A hpositive (MonotoneRectangles.upperSum g (parts m)))
        (Fraction.ofInt 1)).abs) := by
  have h := (unequal_width_curved_area_approximation area g a b A parts hg hbase hA hmesh).2
  exact RectangleContent.area_ratios_approach_one A hpositive _ _ h.1 h.2

/-- The same mutual ratios for unequal widths, using this edition's Lemma II
reduction and its own maximum-width exhaustion. Both denominator bounds are
derived from the positive graph patch. No curved-area assignment is needed. -/
theorem unequal_width_mutual_area_ratios (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b)
    (hab : Fraction.lt a b) (hbase : 0 < (g a).num)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, area.HasArea (MonotoneRectangles.lowerFigure g (parts m))
        (MonotoneRectangles.lowerSum g (parts m)) ∧
      area.HasArea (MonotoneRectangles.upperFigure g (parts m))
        (MonotoneRectangles.upperSum g (parts m))) ∧
    RectangleContent.MutualRatiosOne
      (fun m => MonotoneRectangles.lowerSum g (parts m))
      (fun m => MonotoneRectangles.upperSum g (parts m)) :=
  Principia1713.LemmaII.rectangle_mutual_ratios_from_gap area g a b parts hg hab hbase
    (unequal_width_gap_vanishes g a b parts hg hmesh)


/-- The edition's Lemma II interior-rectangle reduction plus its own
maximum-width exhaustion gives both mutual ratios on an actual tail.
The base ordinate may vanish; an interior ordinate must be positive. -/
theorem unequal_width_mutual_area_ratios_interior (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b c : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hac : Fraction.le a c) (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, area.HasArea (MonotoneRectangles.lowerFigure g (parts m))
        (MonotoneRectangles.lowerSum g (parts m)) ∧
      area.HasArea (MonotoneRectangles.upperFigure g (parts m))
        (MonotoneRectangles.upperSum g (parts m))) ∧
    RectangleContent.EventuallyMutualRatiosOne
      (fun m => MonotoneRectangles.lowerSum g (parts m))
      (fun m => MonotoneRectangles.upperSum g (parts m)) :=
  Principia1713.LemmaII.rectangle_mutual_ratios_from_gap_interior area g a b c
    parts hg hbase hac hcb hgc
    (unequal_width_gap_vanishes g a b parts hg hmesh)

/-- Unequal-width approximation of an arbitrary assigned area magnitude.
The own-edition Lemma II enclosure and maximum-width exhaustion give the
addition/comparison error bounds; the own-edition Lemma I excludes a positive
terminal gap. Euclid X.1 remains an explicit supplied magnitude premise.
This precise extension is a project derivation, without an external exact
statement or priority claim; general area existence is not asserted. -/
theorem unequal_width_magnitude_approximation {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    MagnitudeContent.Approximates area g a b A parts ∧
    ∀ D : Q, Exhaustion.TerminalLower area.magnitudes.order
      (fun m => area.magnitudes.embed (MonotoneRectangles.gap g (parts m))) D →
      ¬ area.magnitudes.order.positive D := by
  have hgap := unequal_width_gap_vanishes g a b parts hg hmesh
  exact ⟨⟨fun m => RectangleContent.lower_upper_areas
      (MagnitudeContent.rationalAreas area) g a b (parts m) hg hbase,
    MagnitudeContent.errors_vanish area.magnitudes _ _ A
      (fun m => Principia1713.LemmaII.rectangle_magnitude_enclosure
        area g a b A (parts m) hg hbase hA) hgap⟩,
    fun D hterminal => Principia1713.LemmaI.no_positive_ultimate_difference
      area.magnitudes.order _ D
      (MagnitudeContent.rational_exhaustion area.magnitudes _ hgap) hterminal⟩

/-- All three ultimate unit-ratio comparisons, expressed by integer multiples
of the finite areas and an arbitrary assigned curved-area magnitude. An
interior positive ordinate derives the eventual lower bracket, allowing zero
initial lower sums. Book V comparison language and this exact coordinate
extension are editorial interpretations, not a new Newton quotation.
Area existence, general coordinates and exact finite ratio equality are not
asserted. The exact extended statement and derivation are project provenance. -/
theorem unequal_width_assigned_magnitude_ratios {Q : Type}
    (area : MagnitudeContent.AreaRules Q)
    (R : MagnitudeContent.MultipleRules area.magnitudes)
    (g : Fraction → Fraction) (a b c : Fraction) (A : Q)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hac : Fraction.le a c) (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun k => MonotoneRectangles.maxWidth (parts k))) :
    MagnitudeContent.AreaRatiosOne area.magnitudes
      (fun k => MonotoneRectangles.lowerSum g (parts k))
      (fun k => MonotoneRectangles.upperSum g (parts k)) A :=
  MagnitudeContent.rectangle_magnitude_ratios area R g a b c A parts hg hbase hac hcb hgc
    (fun k => Principia1713.LemmaII.rectangle_magnitude_enclosure area g a b A (parts k) hg hbase hA)
    (unequal_width_gap_vanishes g a b parts hg hmesh)

/-- Uniform-continuity extension to graphs that may rise and fall. This
uses constructed cell bounds, rather than the printed endpoint/telescoping
construction. It is an editorial project derivation: Newton's exact Latin
is retained above; uniform continuity is not quoted as his hypothesis.
All sufficiently fine partitions have actual enclosing rectangle areas and
errors below any given magnitude tolerance. Area existence stays supplied. -/
theorem uniform_graph_rectangle_exhaustion {Q : Type}
    (area : MagnitudeContent.AreaRules Q) (g : Fraction → Fraction)
    (a b : Fraction) (A : Q) (hab : Fraction.le a b)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A) :
    UniformRectangles.Exhausts area g a b A :=
  Principia1713.LemmaII.uniform_graph_rectangle_exhaustion
    area g a b A hab hzero hf hA

/-- Project extension of this witness's mutual-ratio conclusion to graphs
that may rise and fall. A positive ordinate and continuity construct the
fixed positive rectangle; no denominator bound or ratio limit is supplied.
For each unequal positive integer pair, every sufficiently fine partition
gives all three lower/upper/assigned-area comparisons. Exact Latin remains
above; continuity and the coordinate domain are editorial premises. -/
theorem uniform_graph_assigned_magnitude_ratios {Q : Type}
    (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes)
    (g : Fraction → Fraction) (a b c : Fraction) (A : Q)
    (hac : Fraction.le a c) (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A) :
    UniformRectangles.RatiosExhaust area g a b A :=
  Principia1713.LemmaII.uniform_graph_assigned_magnitude_ratios
    area multiples g a b c A hac hcb hgc hzero hf hA

end Principia1713.LemmaIII

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

-- Modern dependency score: 23/102 (M=23, H=79; transitive project theorems/axioms).
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

-- Modern dependency score: 23/102 (M=23, H=79; transitive project theorems/axioms).
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
