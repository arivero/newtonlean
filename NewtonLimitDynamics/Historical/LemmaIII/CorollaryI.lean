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
Proof-step correspondence: The edition's Lemma III derives lower/upper area errors for a separately assigned rational curved area under explicit area rules. Its rectangle-endpoint-cover approximation now bounds explicit horizontal tops and vertical joins of the left/right-ordinate rectangle constructions. The lower trace excludes the spurious final rise above its last rectangle. Both free step-edge traces belong to their actual rectangle unions and approach the given rational graph in both directions under supplied uniform continuity and shrinking mesh. Fixed baseline and endpoint sides are omitted. This graph-patch and regularity interpretation is editorial (confidence high), not an exact coordinate quotation; general curved-area existence and unrestricted coordinate/ratio scope remain open. A separately labeled project extension below uses this edition’s Lemma III to approximate any supplied area magnitude through addition and comparison under explicit X.1 halving and geometric area rules.
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

end Principia1687.LemmaIII

/-! 1713. Its own primary rational approximation with explicit premises. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par8
Anchor URLs: NATP00082.par8 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par8
Proof-step correspondence: The edition's Lemma III derives lower/upper area errors for a separately assigned rational curved area under explicit area rules. Its rectangle-endpoint-cover approximation now bounds explicit horizontal tops and vertical joins of the left/right-ordinate rectangle constructions. The lower trace excludes the spurious final rise above its last rectangle. Both free step-edge traces belong to their actual rectangle unions and approach the given rational graph in both directions under supplied uniform continuity and shrinking mesh. Fixed baseline and endpoint sides are omitted. This graph-patch and regularity interpretation is editorial (confidence high), not an exact coordinate quotation; general curved-area existence and unrestricted coordinate/ratio scope remain open. A separately labeled project extension below uses this edition’s Lemma III to approximate any supplied area magnitude through addition and comparison under explicit X.1 halving and geometric area rules.
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

end Principia1713.LemmaIII
