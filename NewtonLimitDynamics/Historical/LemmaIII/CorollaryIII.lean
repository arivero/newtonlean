import BarrowLib.Polygon.RationalBoundary
import BarrowLib.Polygon.TangentContact
import BarrowLib.Polygon.TangentBoundary
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
Proof-step correspondence: The general supporting-segment reconstruction retains supplied cells and uniform continuity. The concave increasing rational graph reconstruction derives supporting cells from two-sided secant contact and independent secant concavity, derives uniform continuity from the tangent bound, and proves two-sided approximation of the joined contact-tangent trace. Finite interpolation identifies that trace exactly with the vertical top of the filled tangent polygon, including coincident tangents and repeated nodes. Its region contains the curved figure and lies in the upper rectangle cover; the edition's Corollary I derives area-error decay for separately assigned rational areas. Tangent existence and arbitrary patches, area existence, non-rational magnitudes and arclength remain open. These precise contact/concavity premises are editorial coordinate regularity, not quoted Newton hypotheses.
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


/-- Contact tangents of a concave increasing rational patch give the actual
finite tangent trace. Support cells and uniform continuity are derived;
contact, concavity and shrinking mesh remain explicit regularity premises. -/
theorem corollary3_tangent_boundary {g d : Fraction → Fraction} {a b : Fraction}
    (C : TangentContact.Patch g d a b) (parts : Nat → MonotoneRectangles.Partition a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => TangentContact.Trace C (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) := by
  have hab : Fraction.le a b := Fraction.magnitudes.le_trans
    (MonotoneRectangles.node_bounds (parts 0) 0 (by omega)).1
    (MonotoneRectangles.node_bounds (parts 0) 0 (by omega)).2
  exact corollary3_supporting_boundary (TangentContact.graph g) a b parts
    (TangentContact.graph_uniform C hab) (fun m => TangentContact.partitionCells C (parts m)) hmesh

/-- Assigned areas of the actual circumscribed tangent polygons approach the
assigned curved area, through this edition's Corollary I. The set inclusions
and error bound are derived. The partial area convention and existence of
these assigned rational areas are supplied; no area law is among the premises. -/
theorem corollary3_tangent_area_approximation (area : RectangleContent.AreaRules)
    {g d : Fraction → Fraction} {a b : Fraction} (C : TangentContact.Patch g d a b)
    (parts : Nat → MonotoneRectangles.Partition a b) (A : Fraction) (P : Nat → Fraction)
    (hbase : 0 ≤ (g a).num) (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hP : ∀ m, area.HasArea (TangentContact.figure g d (parts m)) (P m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, Fraction.le A (P m)) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (P m)).abs) := by
  have he (m : Nat) : Fraction.le A (P m) ∧
      Fraction.le (P m) (MonotoneRectangles.upperSum g (parts m)) := by
    have hs := TangentContact.figure_enclosure C (parts m)
    exact ⟨area.monotone _ _ _ _ hs.1 hA (hP m),
      area.monotone _ _ _ _ hs.2 (hP m)
        (RectangleContent.lower_upper_areas area g a b (parts m)
          (TangentContact.monotone C) hbase).2⟩
  refine ⟨fun m => (he m).1, ?_⟩
  have hu := (corollary1_area_approximation area g a b A parts
    (TangentContact.monotone C) hbase hA hmesh).2
  intro eps heps
  obtain ⟨N, hN⟩ := hu eps heps
  refine ⟨N, fun m hm => Fraction.magnitudes.lt_of_le_lt ?_ (hN m hm)⟩
  exact (HarmonicTimeComparison.difference_interval_gaps A (P m)
    (MonotoneRectangles.upperSum g (parts m)) (he m).1 (he m).2).1

/-- The vertical top of the filled circumscribed tangent polygon approaches
the curve. Its identity with the joined contact-tangent trace is proved,
rather than supplied; rational graph regularity and shrinking mesh remain. -/
theorem corollary3_tangent_polygon_boundary {g d : Fraction → Fraction} {a b : Fraction}
    (C : TangentContact.Patch g d a b) (parts : Nat → MonotoneRectangles.Partition a b)
    (hbase : 0 ≤ (g a).num)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => TangentContact.VerticalTop g d (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) := by
  intro eps heps
  obtain ⟨N, hN⟩ := corollary3_tangent_boundary C parts hmesh eps heps
  refine ⟨N, fun m hm => ⟨?_, ?_⟩⟩
  · intro z hz
    exact (hN m hm).1 z ((TangentContact.trace_iff_verticalTop C (parts m) hbase z).mpr hz)
  · intro y hy
    obtain ⟨z, hz, hd⟩ := (hN m hm).2 y hy
    exact ⟨z, (TangentContact.trace_iff_verticalTop C (parts m) hbase z).mp hz, hd⟩

end Principia1687.LemmaIII

/-! 1713. Its own primary rational approximation with explicit premises. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par10
Anchor URLs: NATP00082.par10 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par10
Proof-step correspondence: The general supporting-segment reconstruction retains supplied cells and uniform continuity. The concave increasing rational graph reconstruction derives supporting cells from two-sided secant contact and independent secant concavity, derives uniform continuity from the tangent bound, and proves two-sided approximation of the joined contact-tangent trace. Finite interpolation identifies that trace exactly with the vertical top of the filled tangent polygon, including coincident tangents and repeated nodes. Its region contains the curved figure and lies in the upper rectangle cover; the edition's Corollary I derives area-error decay for separately assigned rational areas. Tangent existence and arbitrary patches, area existence, non-rational magnitudes and arclength remain open. These precise contact/concavity premises are editorial coordinate regularity, not quoted Newton hypotheses.
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


/-- Contact tangents of a concave increasing rational patch give the actual
finite tangent trace. Support cells and uniform continuity are derived;
contact, concavity and shrinking mesh remain explicit regularity premises. -/
theorem corollary3_tangent_boundary {g d : Fraction → Fraction} {a b : Fraction}
    (C : TangentContact.Patch g d a b) (parts : Nat → MonotoneRectangles.Partition a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => TangentContact.Trace C (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) := by
  have hab : Fraction.le a b := Fraction.magnitudes.le_trans
    (MonotoneRectangles.node_bounds (parts 0) 0 (by omega)).1
    (MonotoneRectangles.node_bounds (parts 0) 0 (by omega)).2
  exact corollary3_supporting_boundary (TangentContact.graph g) a b parts
    (TangentContact.graph_uniform C hab) (fun m => TangentContact.partitionCells C (parts m)) hmesh

/-- Assigned areas of the actual circumscribed tangent polygons approach the
assigned curved area, through this edition's Corollary I. The set inclusions
and error bound are derived. The partial area convention and existence of
these assigned rational areas are supplied; no area law is among the premises. -/
theorem corollary3_tangent_area_approximation (area : RectangleContent.AreaRules)
    {g d : Fraction → Fraction} {a b : Fraction} (C : TangentContact.Patch g d a b)
    (parts : Nat → MonotoneRectangles.Partition a b) (A : Fraction) (P : Nat → Fraction)
    (hbase : 0 ≤ (g a).num) (hA : area.HasArea (MonotoneRectangles.figure g a b) A)
    (hP : ∀ m, area.HasArea (TangentContact.figure g d (parts m)) (P m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, Fraction.le A (P m)) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (P m)).abs) := by
  have he (m : Nat) : Fraction.le A (P m) ∧
      Fraction.le (P m) (MonotoneRectangles.upperSum g (parts m)) := by
    have hs := TangentContact.figure_enclosure C (parts m)
    exact ⟨area.monotone _ _ _ _ hs.1 hA (hP m),
      area.monotone _ _ _ _ hs.2 (hP m)
        (RectangleContent.lower_upper_areas area g a b (parts m)
          (TangentContact.monotone C) hbase).2⟩
  refine ⟨fun m => (he m).1, ?_⟩
  have hu := (corollary1_area_approximation area g a b A parts
    (TangentContact.monotone C) hbase hA hmesh).2
  intro eps heps
  obtain ⟨N, hN⟩ := hu eps heps
  refine ⟨N, fun m hm => Fraction.magnitudes.lt_of_le_lt ?_ (hN m hm)⟩
  exact (HarmonicTimeComparison.difference_interval_gaps A (P m)
    (MonotoneRectangles.upperSum g (parts m)) (he m).1 (he m).2).1

/-- The vertical top of the filled circumscribed tangent polygon approaches
the curve. Its identity with the joined contact-tangent trace is proved,
rather than supplied; rational graph regularity and shrinking mesh remain. -/
theorem corollary3_tangent_polygon_boundary {g d : Fraction → Fraction} {a b : Fraction}
    (C : TangentContact.Patch g d a b) (parts : Nat → MonotoneRectangles.Partition a b)
    (hbase : 0 ≤ (g a).num)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => TangentContact.VerticalTop g d (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) := by
  intro eps heps
  obtain ⟨N, hN⟩ := corollary3_tangent_boundary C parts hmesh eps heps
  refine ⟨N, fun m hm => ⟨?_, ?_⟩⟩
  · intro z hz
    exact (hN m hm).1 z ((TangentContact.trace_iff_verticalTop C (parts m) hbase z).mpr hz)
  · intro y hy
    obtain ⟨z, hz, hd⟩ := (hN m hm).2 y hy
    exact ⟨z, (TangentContact.trace_iff_verticalTop C (parts m) hbase z).mp hz, hd⟩

end Principia1713.LemmaIII
