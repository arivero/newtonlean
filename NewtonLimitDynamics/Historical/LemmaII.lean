import BarrowLib.Polygon.MonotoneRectangles
import BarrowLib.Polygon.RectangleContent
import NewtonLimitDynamics.Historical.LemmaI

/-! Historical result: lemma_ii.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Equal-width gap identity in an explicit rational monotone graph model. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par3
Anchor URLs: NATP00077.par3 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par3; NATP00077.par4 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par4
Proof-step correspondence: The finite equal-width gap is identified with the difference of actual rectangle-union areas under explicit elementary area rules. Shrinking mesh derives exhaustion; the edition's Lemma I excludes a positive supplied terminal gap. A separately assigned rational curvilinear area is enclosed and approximated. General area existence and unrestricted ultimate ratios remain open.
Historical dependency ledger for this exact witness:
- P1687.L1 → P1687.L2; passage NATP00077.par4; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par4; status explicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00077.par3
Si in figura quavis Aa cE rectis Aa, AE, & curva AcE comprehensa, inscribentur parallelogramma quotcunq; Ab, Bc, Cd, &c. sub basibus AB, BC, CD, &c. æqualibus, & lateribus Bb, Cc, Dd, &c. figuræ lateri Aa parallelis comenta; & compleantur parallelogramma aKbl, bLcm, cMdn, &c, Dein horum parallelogrammorum latitudo minuatur, & numerus augeatur in infinitum: dico quod ultimæ rationes, quas habent ad se invicem figura inscripta AKbLcMdD, circumscripta AalbmcndoE, & curvilinea AabcdE, sunt rationes æqualitatis.
LATIN END NATP00077.par3 -/
/- LATIN BEGIN NATP00077.par4
Nam figuræ inscriptæ & circumscriptæ differentia est summa parallelogrammorum Kl+Lm+Mn+Do, hoc est (ob æquales omnium bases) rectangulum sub unius basi Kb & altitudinum summa Aa, id est rectangulum ABla. Sed hoc rectangulum, eo quod latitudo ejus AB in infinitum minuitur, sit minus quovis dato. Ergo, per Lemma I, figura inscripta & circumscripta & multo magis figura curvilinea intermedia fiunt ultimo æquales. Q.E.D.
LATIN END NATP00077.par4 -/

namespace Principia1687.LemmaII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

theorem lemma2_equal_width_gap (g : Fraction → Fraction) (a b M : Fraction)
    (p : MonotoneRectangles.Partition a b) (hg : MonotoneRectangles.MonotoneOn g a b)
    (hM : ∀ i, i<p.count → Fraction.equiv (MonotoneRectangles.width p i) M) :
    Fraction.equiv (MonotoneRectangles.gap g p)
      (Fraction.mul M (HarmonicTimeComparison.durationDifference (g a) (g b))) :=
  MonotoneRectangles.gap_equal_width g p hg M hM

/-- Geometric enclosure follows from actual finite rectangle unions and the
explicit elementary area convention. A rational area of the given curved
figure is supplied here; existence or rationality is not inferred. -/
theorem rectangle_area_enclosure (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction) (p : MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A) :
    Fraction.le (MonotoneRectangles.lowerSum g p) A ∧
      Fraction.le A (MonotoneRectangles.upperSum g p) :=
  RectangleContent.curved_area_enclosure area g a b A p hg hbase hA

theorem equal_width_gap_vanishes (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (mesh : Nat → Fraction)
    (hwidth : ∀ m i, i < (parts m).count →
      Fraction.equiv (MonotoneRectangles.width (parts m) i) (mesh m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes mesh) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun m => MonotoneRectangles.gap g (parts m)) :=
  RectangleContent.equal_width_exhaustion g a b parts hg mesh hwidth
    (fun m => lemma2_equal_width_gap g a b (mesh m) (parts m) hg (hwidth m)) hmesh

/-- This is the actual cited application of Lemma I. Only the lower
comparisons of the supplied terminal difference remain a limiting premise. -/
theorem equal_width_ultimate_gap_zero (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (mesh : Nat → Fraction)
    (hwidth : ∀ m i, i < (parts m).count →
      Fraction.equiv (MonotoneRectangles.width (parts m) i) (mesh m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes mesh)
    (D : Fraction) (hD : 0 ≤ D.num)
    (hterminal : Exhaustion.TerminalLower Fraction.magnitudes
      (fun m => MonotoneRectangles.gap g (parts m)) D) :
    Fraction.equiv D (Fraction.ofInt 0) :=
  Principia1687.LemmaI.ultimate_difference_zero _ D hD
    (equal_width_gap_vanishes g a b parts hg mesh hwidth hmesh) hterminal

theorem equal_width_curved_area_approximation (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A) (mesh : Nat → Fraction)
    (hwidth : ∀ m i, i < (parts m).count →
      Fraction.equiv (MonotoneRectangles.width (parts m) i) (mesh m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes mesh) :
    (∀ m, area.HasArea (MonotoneRectangles.lowerFigure g (parts m)) (MonotoneRectangles.lowerSum g (parts m)) ∧
      area.HasArea (MonotoneRectangles.upperFigure g (parts m)) (MonotoneRectangles.upperSum g (parts m))) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (MonotoneRectangles.lowerSum g (parts m)) A).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (MonotoneRectangles.upperSum g (parts m))).abs) :=
  ⟨fun m => RectangleContent.lower_upper_areas area g a b (parts m) hg hbase,
    RectangleContent.area_errors_vanish g a b A parts hg
      (fun m => rectangle_area_enclosure area g a b A (parts m) hg hbase hA)
      (equal_width_gap_vanishes g a b parts hg mesh hwidth hmesh)⟩


/-- Unit ratios to a fixed positive assigned rational curved area. The
positive-area premise is required for division; general curved-area
existence and ratios with vanishing denominators are not asserted. -/
theorem equal_width_area_ratios (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction) (hpositive : 0 < A.num)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (mesh : Nat → Fraction)
    (hwidth : ∀ m i, i < (parts m).count →
      Fraction.equiv (MonotoneRectangles.width (parts m) i) (mesh m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes mesh) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference
        (RectangleContent.ratioTo A hpositive (MonotoneRectangles.lowerSum g (parts m)))
        (Fraction.ofInt 1)).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference
        (RectangleContent.ratioTo A hpositive (MonotoneRectangles.upperSum g (parts m)))
        (Fraction.ofInt 1)).abs) := by
  have h := (equal_width_curved_area_approximation area g a b A parts hg hbase hA mesh hwidth hmesh).2
  exact RectangleContent.area_ratios_approach_one A hpositive _ _ h.1 h.2

end Principia1687.LemmaII

/-! 1713. Equal-width gap identity in an explicit rational monotone graph model. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par4
Anchor URLs: NATP00082.par4 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par4; NATP00082.par5 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par5
Proof-step correspondence: The finite equal-width gap is identified with the difference of actual rectangle-union areas under explicit elementary area rules. Shrinking mesh derives exhaustion; the edition's Lemma I excludes a positive supplied terminal gap. A separately assigned rational curvilinear area is enclosed and approximated. General area existence and unrestricted ultimate ratios remain open.
Historical dependency ledger for this exact witness:
- P1713.L1 → P1713.L2; passage NATP00082.par5; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par5; status explicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00082.par4
Si in Figura quavis AacE rectis Aa, AE, & curva AcE comprehensa, inscribentur parallelogramma quotcunque Ab, Bc, Cd, &c. sub basibus AB, BC, CD, &c. æqualibus, & lateribus Bb, Cc, Dd, &c. Figuræ lateri Aa parallelis comenta; & compleantur parallelogramma aKbl, bLcm, cMdn, &c. Dein horum parallelogrammorum latitudo minuatur, & numerus augeatur in infinitum: dico quod ultimæ rationes, quas habent ad se invicem Figura inscripta AKbLcMdD, circumscripta AalbmcndoE, & curvilinea AabcdE, sunt rationes æqualitatis.
LATIN END NATP00082.par4 -/
/- LATIN BEGIN NATP00082.par5
Nam figuræ inscriptæ & circumscriptæ differentia est summa parallelogrammorum Kl, Lm, Mn, Do, hoc est (ob æquales omnium bases) rectangulum sub unius basi Kb & altitudinum summa Aa, id est rectangulum ABla. Sed hoc rectangulum, eo quod latitudo ejus AB in infinitum minuitur, sit minus quovis dato. Ergo (per Lemma I) Figura inscripta & circumscripta & multo magis Figura curvilinea intermedia fiunt ultimo æquales. Q.E.D.
LATIN END NATP00082.par5 -/

namespace Principia1713.LemmaII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

theorem lemma2_equal_width_gap (g : Fraction → Fraction) (a b M : Fraction)
    (p : MonotoneRectangles.Partition a b) (hg : MonotoneRectangles.MonotoneOn g a b)
    (hM : ∀ i, i<p.count → Fraction.equiv (MonotoneRectangles.width p i) M) :
    Fraction.equiv (MonotoneRectangles.gap g p)
      (Fraction.mul M (HarmonicTimeComparison.durationDifference (g a) (g b))) :=
  MonotoneRectangles.gap_equal_width g p hg M hM

/-- Geometric enclosure follows from actual finite rectangle unions and the
explicit elementary area convention. A rational area of the given curved
figure is supplied here; existence or rationality is not inferred. -/
theorem rectangle_area_enclosure (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction) (p : MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A) :
    Fraction.le (MonotoneRectangles.lowerSum g p) A ∧
      Fraction.le A (MonotoneRectangles.upperSum g p) :=
  RectangleContent.curved_area_enclosure area g a b A p hg hbase hA

theorem equal_width_gap_vanishes (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (mesh : Nat → Fraction)
    (hwidth : ∀ m i, i < (parts m).count →
      Fraction.equiv (MonotoneRectangles.width (parts m) i) (mesh m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes mesh) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun m => MonotoneRectangles.gap g (parts m)) :=
  RectangleContent.equal_width_exhaustion g a b parts hg mesh hwidth
    (fun m => lemma2_equal_width_gap g a b (mesh m) (parts m) hg (hwidth m)) hmesh

/-- This is the actual cited application of Lemma I. Only the lower
comparisons of the supplied terminal difference remain a limiting premise. -/
theorem equal_width_ultimate_gap_zero (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (mesh : Nat → Fraction)
    (hwidth : ∀ m i, i < (parts m).count →
      Fraction.equiv (MonotoneRectangles.width (parts m) i) (mesh m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes mesh)
    (D : Fraction) (hD : 0 ≤ D.num)
    (hterminal : Exhaustion.TerminalLower Fraction.magnitudes
      (fun m => MonotoneRectangles.gap g (parts m)) D) :
    Fraction.equiv D (Fraction.ofInt 0) :=
  Principia1713.LemmaI.ultimate_difference_zero _ D hD
    (equal_width_gap_vanishes g a b parts hg mesh hwidth hmesh) hterminal

theorem equal_width_curved_area_approximation (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A) (mesh : Nat → Fraction)
    (hwidth : ∀ m i, i < (parts m).count →
      Fraction.equiv (MonotoneRectangles.width (parts m) i) (mesh m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes mesh) :
    (∀ m, area.HasArea (MonotoneRectangles.lowerFigure g (parts m)) (MonotoneRectangles.lowerSum g (parts m)) ∧
      area.HasArea (MonotoneRectangles.upperFigure g (parts m)) (MonotoneRectangles.upperSum g (parts m))) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (MonotoneRectangles.lowerSum g (parts m)) A).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (MonotoneRectangles.upperSum g (parts m))).abs) :=
  ⟨fun m => RectangleContent.lower_upper_areas area g a b (parts m) hg hbase,
    RectangleContent.area_errors_vanish g a b A parts hg
      (fun m => rectangle_area_enclosure area g a b A (parts m) hg hbase hA)
      (equal_width_gap_vanishes g a b parts hg mesh hwidth hmesh)⟩


/-- Unit ratios to a fixed positive assigned rational curved area. The
positive-area premise is required for division; general curved-area
existence and ratios with vanishing denominators are not asserted. -/
theorem equal_width_area_ratios (area : RectangleContent.AreaRules)
    (g : Fraction → Fraction) (a b A : Fraction) (hpositive : 0 < A.num)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (mesh : Nat → Fraction)
    (hwidth : ∀ m i, i < (parts m).count →
      Fraction.equiv (MonotoneRectangles.width (parts m) i) (mesh m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes mesh) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference
        (RectangleContent.ratioTo A hpositive (MonotoneRectangles.lowerSum g (parts m)))
        (Fraction.ofInt 1)).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference
        (RectangleContent.ratioTo A hpositive (MonotoneRectangles.upperSum g (parts m)))
        (Fraction.ofInt 1)).abs) := by
  have h := (equal_width_curved_area_approximation area g a b A parts hg hbase hA mesh hwidth hmesh).2
  exact RectangleContent.area_ratios_approach_one A hpositive _ _ h.1 h.2

end Principia1713.LemmaII
