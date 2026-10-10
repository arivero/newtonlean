import BarrowLib.Polygon.RationalBoundary
import BarrowLib.Polygon.AffineCoincidence
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
Proof-step correspondence: Legacy rational clients derive assigned-area errors through the edition's Lemma III and approximation of free staircase tops/joins, omitting fixed sides. The whole-figure reconstruction now uses this edition's unequal-width ordinate control over an arbitrary ordered coordinate field. It proves two-sided approximation of whole actual rectangle unions and complete finite edge traces (baseline, actual endpoint sides, rising/falling joins), then separation gives exact ultimate-point membership for the supplied whole figure and its complete boundary. It applies to every admissible original shrinking family; cell heights may contact the curve inside cells. No curved-area assignment is needed for this geometric conclusion. Coordinates, uniform ordinate control and the global graph description remain explicit editorial interpretation (confidence high), not an exact coordinate quotation. The affine reconstruction below now derives transport to actual parallelograms and contact-height correspondence, with a separate two-straight-side specialization ending the curve on the baseline. The precise source figure/regularity/contact-admissibility scope remains open. With repeated nodes the finite edge trace need not equal the finite union's topological boundary; no perimeter-length claim is made.
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

/-- The explicit free staircase edges, rather than filled endpoint boxes,
approach the graph in both directions and lie in the actual rectangle unions.
Continuity and mesh exhaustion remain premises. The source supports the route;
this precise rational coordinate statement and proof are project derivation. -/
theorem corollary1_staircase_boundaries (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => RationalBoundary.LowerStaircase g (parts m))
      (RationalBoundary.CurveTrace (fun t => (t,g t)) a b) ∧
    RationalBoundary.Approaches (fun m => RationalBoundary.UpperStaircase g (parts m))
      (RationalBoundary.CurveTrace (fun t => (t,g t)) a b) ∧
    ∀ m x, (RationalBoundary.LowerStaircase g (parts m) x →
      MonotoneRectangles.lowerFigure g (parts m) x) ∧
      (RationalBoundary.UpperStaircase g (parts m) x →
        MonotoneRectangles.upperFigure g (parts m) x) := by
  have hn := RationalBoundary.nodes_approach (fun t => (t,g t)) a b parts hf hmesh
  have hr := corollary1_rectangle_boundary (fun t => (t,g t)) a b parts hf hmesh
  exact ⟨RationalBoundary.trace_sandwich _ _ _ _ hn hr
    (fun m => RationalBoundary.nodes_in_lower_staircase g (parts m))
    (fun m => RationalBoundary.lower_staircase_in_rectangles g (parts m)),
    RationalBoundary.trace_sandwich _ _ _ _ hn hr
      (fun m => RationalBoundary.nodes_in_upper_staircase g (parts m))
      (fun m => RationalBoundary.upper_staircase_in_rectangles g (parts m)),
    fun m x => ⟨RationalBoundary.lower_staircase_in_figure g (parts m) hg hbase x,
      RationalBoundary.upper_staircase_in_figure g (parts m) hg hbase x⟩⟩

/-- The edition's Lemma III now approximates any supplied area magnitude,
without requiring it to be a rational image. The classical halving and
geometric area premises are visible in the rules. This coordinate extension
is a project derivation; no curved-area existence or general ratio theorem
is asserted. -/
theorem corollary1_magnitude_area_approximation {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    MagnitudeContent.Approximates area g a b A parts :=
  (unequal_width_magnitude_approximation area g a b A parts hg hbase hA hmesh).1

/-- Area exhaustion for a uniformly continuous nonnegative graph without
monotonicity, using this edition's Lemma III extension. The enclosing sets
are actual finite rectangle unions. This project coordinate reconstruction
asserts area-error control; free-boundary approximation and general area
existence are separate obligations. -/
theorem corollary1_uniform_graph_area_exhaustion {Q : Type}
    (area : MagnitudeContent.AreaRules Q) (g : Fraction → Fraction)
    (a b : Fraction) (A : Q) (hab : Fraction.le a b)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A) :
    UniformRectangles.Exhausts area g a b A :=
  uniform_graph_rectangle_exhaustion area g a b A hab hzero hf hA

/-- Project extension of this witness's free-boundary reconstruction to
nonmonotone graphs, using the actual clipped rectangle height formulas.
Both tops/internal joins approach the graph and lie in their rectangle unions.
Area enclosure still needs the separate fine_rectangles mesh condition;
this theorem derives no area, fixed-side or topological-perimeter claim. -/
theorem corollary1_uniform_graph_staircases (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b) (eps : Nat → Fraction)
    (heps : ∀ m, 0≤(eps m).num)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m)))
    (hvanish : Exhaustion.VanishingDifference Fraction.magnitudes eps) :
    UniformRectangles.StaircaseApproximation g a b parts eps :=
  UniformRectangles.staircase_approaches g a b parts eps heps hzero hf hmesh hvanish

/-- Project-derived coupling of the nonmonotone area and free-boundary
constructions: one strictly increasing selection of the supplied subdivisions
gives enclosure, vanishing area gap/errors and two-sided free-edge approach.
The continuity/mesh premises are editorial. This alternative finite-rectangle
construction does not assert a new textual Lemma III dependency. Curved-area
existence, fixed sides and unrestricted coordinate scope remain separate. -/
theorem corollary1_uniform_graph_matched {Q : Type}
    (area : MagnitudeContent.AreaRules Q) (g : Fraction → Fraction)
    (a b : Fraction) (A : Q) (parts : Nat → MonotoneRectangles.Partition a b)
    (eps : Nat → Fraction) (heps : ∀ m, 0<(eps m).num) (hab : Fraction.le a b)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m)))
    (hvanish : Exhaustion.VanishingDifference Fraction.magnitudes eps) :
    ∃ indices, UniformRectangles.MatchedApproximation area g a b A parts eps indices :=
  UniformRectangles.matched_approximation area g a b A parts eps heps hab hzero hf hA hmesh hvanish

/-- One selected family now supplies enclosure, area-error decay, free-edge
approach and all three unit-ratio comparisons. This witness's matched-family
construction and its own Lemma III → II ratio reduction are used together.
Positivity is derived from a contained rectangle, not supplied as an area
bound. Project reconstruction within the stated rational graph domain;
curved-area existence, fixed sides and full ratio calculus remain separate. -/
theorem corollary1_uniform_graph_matched_ratios {Q : Type}
    (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes)
    (g : Fraction → Fraction) (a b c : Fraction) (A : Q)
    (parts : Nat → MonotoneRectangles.Partition a b) (eps : Nat → Fraction)
    (heps : ∀ m, 0<(eps m).num) (hac : Fraction.le a c) (hcb : Fraction.lt c b)
    (hgc : 0<(g c).num)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m)))
    (hvanish : Exhaustion.VanishingDifference Fraction.magnitudes eps) :
    ∃ indices, UniformRectangles.MatchedApproximation area g a b A parts eps indices ∧
      let selected := fun k => parts (indices k)
      MagnitudeContent.AreaRatiosOne area.magnitudes
        (fun k => UniformRectangles.value (selected k) (UniformRectangles.lowerHeights g (selected k) (eps k)))
        (fun k => UniformRectangles.value (selected k) (UniformRectangles.upperHeights g (selected k) (eps k))) A := by
  obtain ⟨indices,hmatched⟩ := corollary1_uniform_graph_matched area g a b A parts eps heps
    (Fraction.magnitudes.le_trans hac (Fraction.magnitudes.lt_implies_le hcb))
    hzero hf hA hmesh hvanish
  exact ⟨indices,hmatched,uniform_graph_matched_area_ratios area multiples g a b c A
    parts eps indices hac hcb hgc hf hmatched⟩

/-- Whole-figure geometric reconstruction of "coincidit omni ex parte":
the ultimate point predicate equals the supplied figure, and the complete
edge trace has the complete boundary as its ultimate point set. Baseline,
endpoint sides and falling joins are included at their actual finite heights.
This uses this edition's Lemma III ordinate control and applies to every
admissible original shrinking family over the whole ordered coordinate field.
No curved-area assignment or ratio/length conclusion is needed. The affine
correspondence is derived below; the source's whole-figure/contact/regularity
interpretation still needs justification for historical completion. -/
theorem corollary1_whole_figure_coincidence {K : Type}
    [Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]
    [Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K]
    (g : K → K) (a b : K) (parts : Nat → CurvilinearCoincidence.Partition a b)
    (heights : Nat → Nat → K) (mesh : Nat → K)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t)
    (hf : CurvilinearCoincidence.UniformOn g a b)
    (hmesh : CurvilinearCoincidence.Shrinks mesh)
    (hwidth : ∀ k i, i<(parts k).count →
      (parts k).nodes (i+1)-(parts k).nodes i≤mesh k)
    (hheight : ∀ k i, i<(parts k).count →
      CurvilinearCoincidence.CellHeight g (parts k) i (heights k i)) :
    CurvilinearCoincidence.WholeCoincidence g a b parts heights := by
  have hcontrol := unequal_width_ordinate_control g a b parts heights mesh hf hmesh hwidth hheight
  have hpositive := fun k i hi => CurvilinearCoincidence.height_nonnegative
    g (parts k) i hi (heights k i) (hheight k i hi) hzero
  have happrox := CurvilinearCoincidence.rectangles_approach_of_ordinate_control
    g a b parts heights hzero hpositive hcontrol
  exact ⟨happrox,
    CurvilinearCoincidence.perimeters_approach g a b parts heights mesh hzero hf hmesh hwidth hheight,
    CurvilinearCoincidence.ultimate_eq_of_approaches _ _ happrox
      (CurvilinearCoincidence.figure_separated g a b hf),
    CurvilinearCoincidence.perimeters_ultimate_eq g a b parts heights mesh hzero hf hmesh hwidth hheight,
    fun k x hx => CurvilinearCoincidence.perimeter_in_rectangles (parts k) (heights k)
      (hpositive k) x hx⟩

/-- Geometric transport to actual oblique parallelogram unions, specialized
to the two straight sides in this edition's Lemma II: "rectis Aa, AE, & curva
AcE comprehensa". The whole supplied curve is identified, and g(b)=0 puts its
terminal point E on the baseline, rather than adding a third straight side.
Finite contact supplies the height condition; inverse/proximity are proved.
The whole-graph, uniform-control and contact-admissibility interpretation is
editorial (confidence high), not a theorem that every curve admits it.
Source: 1687 Lemma II, NATP00077.par3; exact Latin in Historical/LemmaII.lean.
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par3
Status: editorial_interpretation; confidence high. No extrema existence is inferred. -/
theorem corollary1_parallelogram_coincidence {K : Type}
    [Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]
    [Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K]
    (frame : AffineCoincidence.Frame K) (curve : (K × K) → Prop)
    (g : K → K) (a b : K)
    (parts : Nat → CurvilinearCoincidence.Partition a b)
    (heights : Nat → Nat → K) (mesh : Nat → K)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t)
    (hf : CurvilinearCoincidence.UniformOn g a b)
    (hmesh : CurvilinearCoincidence.Shrinks mesh)
    (hwidth : ∀ k i, i<(parts k).count →
      (parts k).nodes (i+1)-(parts k).nodes i≤mesh k)
    (hcontact : ∀ k i, i<(parts k).count →
      AffineCoincidence.Touches g (parts k) i (heights k i))
    (hend : g b=0)
    (hcurve : ∀ x, curve x ↔ AffineCoincidence.Image frame.toAffine
      (CurvilinearCoincidence.Graph g a b) x) :
    AffineCoincidence.WholeCoincidence frame g a b parts heights ∧
      ∀ x, CurvilinearCoincidence.Ultimate
        (fun k => AffineCoincidence.Image frame.toAffine
          (CurvilinearCoincidence.Perimeter (parts k) (heights k))) x ↔
        AffineCoincidence.TwoSideBoundary frame curve g a b x := by
  apply AffineCoincidence.two_side_coincidence frame curve g a b parts heights hend hcurve
  apply AffineCoincidence.whole_coincidence_image
  exact corollary1_whole_figure_coincidence g a b parts heights mesh hzero hf hmesh hwidth
    (fun k i hi => AffineCoincidence.cell_height_of_contact
      g (parts k) i (heights k i) (hcontact k i hi))

end Principia1687.LemmaIII

/-! 1713. Its own primary rational approximation with explicit premises. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par8
Anchor URLs: NATP00082.par8 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par8
Proof-step correspondence: Legacy rational clients derive assigned-area errors through the edition's Lemma III and approximation of free staircase tops/joins, omitting fixed sides. The whole-figure reconstruction now uses this edition's unequal-width ordinate control over an arbitrary ordered coordinate field. It proves two-sided approximation of whole actual rectangle unions and complete finite edge traces (baseline, actual endpoint sides, rising/falling joins), then separation gives exact ultimate-point membership for the supplied whole figure and its complete boundary. It applies to every admissible original shrinking family; cell heights may contact the curve inside cells. No curved-area assignment is needed for this geometric conclusion. Coordinates, uniform ordinate control and the global graph description remain explicit editorial interpretation (confidence high), not an exact coordinate quotation. The affine reconstruction below now derives transport to actual parallelograms and contact-height correspondence, with a separate two-straight-side specialization ending the curve on the baseline. The precise source figure/regularity/contact-admissibility scope remains open. With repeated nodes the finite edge trace need not equal the finite union's topological boundary; no perimeter-length claim is made.
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

/-- This edition uses its own Corollary I rectangle bound for the two
explicit step-edge traces. The supplied geometric/regularity scope is the
same; no area or arclength assertion is inferred from boundary approach. -/
theorem corollary1_staircase_boundaries (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => RationalBoundary.LowerStaircase g (parts m))
      (RationalBoundary.CurveTrace (fun t => (t,g t)) a b) ∧
    RationalBoundary.Approaches (fun m => RationalBoundary.UpperStaircase g (parts m))
      (RationalBoundary.CurveTrace (fun t => (t,g t)) a b) ∧
    ∀ m x, (RationalBoundary.LowerStaircase g (parts m) x →
      MonotoneRectangles.lowerFigure g (parts m) x) ∧
      (RationalBoundary.UpperStaircase g (parts m) x →
        MonotoneRectangles.upperFigure g (parts m) x) := by
  have hn := RationalBoundary.nodes_approach (fun t => (t,g t)) a b parts hf hmesh
  have hr := corollary1_rectangle_boundary (fun t => (t,g t)) a b parts hf hmesh
  exact ⟨RationalBoundary.trace_sandwich _ _ _ _ hn hr
    (fun m => RationalBoundary.nodes_in_lower_staircase g (parts m))
    (fun m => RationalBoundary.lower_staircase_in_rectangles g (parts m)),
    RationalBoundary.trace_sandwich _ _ _ _ hn hr
      (fun m => RationalBoundary.nodes_in_upper_staircase g (parts m))
      (fun m => RationalBoundary.upper_staircase_in_rectangles g (parts m)),
    fun m x => ⟨RationalBoundary.lower_staircase_in_figure g (parts m) hg hbase x,
      RationalBoundary.upper_staircase_in_figure g (parts m) hg hbase x⟩⟩

/-- The edition's Lemma III now approximates any supplied area magnitude,
without requiring it to be a rational image. The classical halving and
geometric area premises are visible in the rules. This coordinate extension
is a project derivation; no curved-area existence or general ratio theorem
is asserted. -/
theorem corollary1_magnitude_area_approximation {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    MagnitudeContent.Approximates area g a b A parts :=
  (unequal_width_magnitude_approximation area g a b A parts hg hbase hA hmesh).1

/-- Area exhaustion for a uniformly continuous nonnegative graph without
monotonicity, using this edition's Lemma III extension. The enclosing sets
are actual finite rectangle unions. This project coordinate reconstruction
asserts area-error control; free-boundary approximation and general area
existence are separate obligations. -/
theorem corollary1_uniform_graph_area_exhaustion {Q : Type}
    (area : MagnitudeContent.AreaRules Q) (g : Fraction → Fraction)
    (a b : Fraction) (A : Q) (hab : Fraction.le a b)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A) :
    UniformRectangles.Exhausts area g a b A :=
  uniform_graph_rectangle_exhaustion area g a b A hab hzero hf hA

/-- Project extension of this witness's free-boundary reconstruction to
nonmonotone graphs, using the actual clipped rectangle height formulas.
Both tops/internal joins approach the graph and lie in their rectangle unions.
Area enclosure still needs the separate fine_rectangles mesh condition;
this theorem derives no area, fixed-side or topological-perimeter claim. -/
theorem corollary1_uniform_graph_staircases (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b) (eps : Nat → Fraction)
    (heps : ∀ m, 0≤(eps m).num)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m)))
    (hvanish : Exhaustion.VanishingDifference Fraction.magnitudes eps) :
    UniformRectangles.StaircaseApproximation g a b parts eps :=
  UniformRectangles.staircase_approaches g a b parts eps heps hzero hf hmesh hvanish

/-- Project-derived coupling of this witness's nonmonotone area and
free-boundary reconstructions. The selected family and its coupling are
conclusions, not new convergence premises. Exact project statement/proof
provenance, without an additional textual dependency or priority claim;
the same area-existence, fixed-side and coordinate limitations remain. -/
theorem corollary1_uniform_graph_matched {Q : Type}
    (area : MagnitudeContent.AreaRules Q) (g : Fraction → Fraction)
    (a b : Fraction) (A : Q) (parts : Nat → MonotoneRectangles.Partition a b)
    (eps : Nat → Fraction) (heps : ∀ m, 0<(eps m).num) (hab : Fraction.le a b)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m)))
    (hvanish : Exhaustion.VanishingDifference Fraction.magnitudes eps) :
    ∃ indices, UniformRectangles.MatchedApproximation area g a b A parts eps indices :=
  UniformRectangles.matched_approximation area g a b A parts eps heps hab hzero hf hA hmesh hvanish

/-- One selected family now supplies enclosure, area-error decay, free-edge
approach and all three unit-ratio comparisons. This witness's matched-family
construction and its own Lemma III → II ratio reduction are used together.
Positivity is derived from a contained rectangle, not supplied as an area
bound. Project reconstruction within the stated rational graph domain;
curved-area existence, fixed sides and full ratio calculus remain separate. -/
theorem corollary1_uniform_graph_matched_ratios {Q : Type}
    (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes)
    (g : Fraction → Fraction) (a b c : Fraction) (A : Q)
    (parts : Nat → MonotoneRectangles.Partition a b) (eps : Nat → Fraction)
    (heps : ∀ m, 0<(eps m).num) (hac : Fraction.le a c) (hcb : Fraction.lt c b)
    (hgc : 0<(g c).num)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m)))
    (hvanish : Exhaustion.VanishingDifference Fraction.magnitudes eps) :
    ∃ indices, UniformRectangles.MatchedApproximation area g a b A parts eps indices ∧
      let selected := fun k => parts (indices k)
      MagnitudeContent.AreaRatiosOne area.magnitudes
        (fun k => UniformRectangles.value (selected k) (UniformRectangles.lowerHeights g (selected k) (eps k)))
        (fun k => UniformRectangles.value (selected k) (UniformRectangles.upperHeights g (selected k) (eps k))) A := by
  obtain ⟨indices,hmatched⟩ := corollary1_uniform_graph_matched area g a b A parts eps heps
    (Fraction.magnitudes.le_trans hac (Fraction.magnitudes.lt_implies_le hcb))
    hzero hf hA hmesh hvanish
  exact ⟨indices,hmatched,uniform_graph_matched_area_ratios area multiples g a b c A
    parts eps indices hac hcb hgc hf hmatched⟩

/-- Whole-figure geometric reconstruction of "coincidit omni ex parte":
the ultimate point predicate equals the supplied figure, and the complete
edge trace has the complete boundary as its ultimate point set. Baseline,
endpoint sides and falling joins are included at their actual finite heights.
This uses this edition's Lemma III ordinate control and applies to every
admissible original shrinking family over the whole ordered coordinate field.
No curved-area assignment or ratio/length conclusion is needed. The affine
correspondence is derived below; the source's whole-figure/contact/regularity
interpretation still needs justification for historical completion. -/
theorem corollary1_whole_figure_coincidence {K : Type}
    [Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]
    [Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K]
    (g : K → K) (a b : K) (parts : Nat → CurvilinearCoincidence.Partition a b)
    (heights : Nat → Nat → K) (mesh : Nat → K)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t)
    (hf : CurvilinearCoincidence.UniformOn g a b)
    (hmesh : CurvilinearCoincidence.Shrinks mesh)
    (hwidth : ∀ k i, i<(parts k).count →
      (parts k).nodes (i+1)-(parts k).nodes i≤mesh k)
    (hheight : ∀ k i, i<(parts k).count →
      CurvilinearCoincidence.CellHeight g (parts k) i (heights k i)) :
    CurvilinearCoincidence.WholeCoincidence g a b parts heights := by
  have hcontrol := unequal_width_ordinate_control g a b parts heights mesh hf hmesh hwidth hheight
  have hpositive := fun k i hi => CurvilinearCoincidence.height_nonnegative
    g (parts k) i hi (heights k i) (hheight k i hi) hzero
  have happrox := CurvilinearCoincidence.rectangles_approach_of_ordinate_control
    g a b parts heights hzero hpositive hcontrol
  exact ⟨happrox,
    CurvilinearCoincidence.perimeters_approach g a b parts heights mesh hzero hf hmesh hwidth hheight,
    CurvilinearCoincidence.ultimate_eq_of_approaches _ _ happrox
      (CurvilinearCoincidence.figure_separated g a b hf),
    CurvilinearCoincidence.perimeters_ultimate_eq g a b parts heights mesh hzero hf hmesh hwidth hheight,
    fun k x hx => CurvilinearCoincidence.perimeter_in_rectangles (parts k) (heights k)
      (hpositive k) x hx⟩

/-- Geometric transport to actual oblique parallelogram unions, specialized
to the two straight sides in this edition's Lemma II: "rectis Aa, AE, & curva
AcE comprehensa". The whole supplied curve is identified, and g(b)=0 puts its
terminal point E on the baseline, rather than adding a third straight side.
Finite contact supplies the height condition; inverse/proximity are proved.
The whole-graph, uniform-control and contact-admissibility interpretation is
editorial (confidence high), not a theorem that every curve admits it.
Source: 1713 Lemma II, NATP00082.par4; exact Latin in Historical/LemmaII.lean.
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par4
Status: editorial_interpretation; confidence high. No extrema existence is inferred. -/
theorem corollary1_parallelogram_coincidence {K : Type}
    [Lean.Grind.Field K] [LE K] [LT K] [Std.IsLinearOrder K]
    [Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K]
    (frame : AffineCoincidence.Frame K) (curve : (K × K) → Prop)
    (g : K → K) (a b : K)
    (parts : Nat → CurvilinearCoincidence.Partition a b)
    (heights : Nat → Nat → K) (mesh : Nat → K)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t)
    (hf : CurvilinearCoincidence.UniformOn g a b)
    (hmesh : CurvilinearCoincidence.Shrinks mesh)
    (hwidth : ∀ k i, i<(parts k).count →
      (parts k).nodes (i+1)-(parts k).nodes i≤mesh k)
    (hcontact : ∀ k i, i<(parts k).count →
      AffineCoincidence.Touches g (parts k) i (heights k i))
    (hend : g b=0)
    (hcurve : ∀ x, curve x ↔ AffineCoincidence.Image frame.toAffine
      (CurvilinearCoincidence.Graph g a b) x) :
    AffineCoincidence.WholeCoincidence frame g a b parts heights ∧
      ∀ x, CurvilinearCoincidence.Ultimate
        (fun k => AffineCoincidence.Image frame.toAffine
          (CurvilinearCoincidence.Perimeter (parts k) (heights k))) x ↔
        AffineCoincidence.TwoSideBoundary frame curve g a b x := by
  apply AffineCoincidence.two_side_coincidence frame curve g a b parts heights hend hcurve
  apply AffineCoincidence.whole_coincidence_image
  exact corollary1_whole_figure_coincidence g a b parts heights mesh hzero hf hmesh hwidth
    (fun k i hi => AffineCoincidence.cell_height_of_contact
      g (parts k) i (heights k i) (hcontact k i hi))

end Principia1713.LemmaIII
