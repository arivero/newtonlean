import ModernLib.Polygon.GeneralForcePolygonCurve
import ModernLib.Reconstruction.SupportingBoundary
import NewtonLimitDynamics.Historical.LemmaIII.CorollaryII
import NewtonLimitDynamics.Historical.LemmaIII.CorollaryIII

/-! Historical result: lemma_iii_corollary_iv.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Primary rational perimeter approximation; modern support remains separate. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10
Anchor URLs: NATP00077.par10 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10
Proof-step correspondence: The edition's Corollaries II and III supply two-sided chord and supporting-segment approximation with explicit continuity, mesh and supporting-cell premises. The concave increasing rational patch reconstruction derives continuity and the cells from two-sided secant contact and independent secant concavity. Finite interpolation identifies the joined contact-tangent trace with the filled polygon's vertical top. The edition's Corollaries II and III then prove approach of the chord and that actual upper perimeter to the curve. Tangent existence for arbitrary curves, non-rational points, force-polygon identification and arclength remain open. Modern completed-curve reconstructions remain below the separator.
Historical dependency ledger for this exact witness:
- P1687.L3 → P1687.L3C4; passage NATP00077.par10; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10; status implicit_dependency; confidence high.
- P1687.L3C1 → P1687.L3C4; passage NATP00077.par10; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10; status implicit_dependency; confidence high.
- P1687.L3C2 → P1687.L3C4; passage NATP00077.par10; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10; status implicit_dependency; confidence high.
- P1687.L3C3 → P1687.L3C4; passage NATP00077.par10; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10; status implicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00077.par10
Corol. 4. Et propterea hæ figuræ ultimæ (quoad perimetros acE,) non sunt rectilineæ, sed rectilinearum limites curvilinci.
LATIN END NATP00077.par10 -/

namespace Principia1687.LemmaIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

/-- The source-local corollary chain supplies the inscribed chord and
supporting-segment perimeter approximations for rational points. Actual
tangents, arbitrary completed points, force-polygon identification and
arclength are separate obligations. -/
theorem corollary4_rational_perimeters (f : Fraction → TimeSubdivision.Point) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b) (hf : RationalBoundary.UniformOn f a b)
    (cells : ∀ m i, SupportingTangents.Cell (f ((parts m).nodes i)) (f ((parts m).nodes (i+1))))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => RationalBoundary.ChordTrace f (parts m))
      (RationalBoundary.CurveTrace f a b) ∧
    RationalBoundary.Approaches (fun m => RationalBoundary.SupportingTrace f (parts m) (cells m))
      (RationalBoundary.CurveTrace f a b) :=
  ⟨corollary2_chord_boundary f a b parts hf hmesh,
    corollary3_supporting_boundary f a b parts hf cells hmesh⟩


/-- Both the chord perimeter and the constructed contact-tangent perimeter
approach the curve. On these concave increasing patches uniform continuity
and the supporting cells are conclusions of contact/concavity, not premises.
This is boundary approximation; it asserts no arclength limit. -/
theorem corollary4_tangent_perimeters {g d : Fraction → Fraction} {a b : Fraction}
    (C : TangentContact.Patch g d a b) (parts : Nat → MonotoneRectangles.Partition a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches
      (fun m => RationalBoundary.ChordTrace (TangentContact.graph g) (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) ∧
    RationalBoundary.Approaches (fun m => TangentContact.Trace C (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) := by
  have hab : Fraction.le a b := Fraction.magnitudes.le_trans
    (MonotoneRectangles.node_bounds (parts 0) 0 (by omega)).1
    (MonotoneRectangles.node_bounds (parts 0) 0 (by omega)).2
  exact ⟨corollary2_chord_boundary (TangentContact.graph g) a b parts
    (TangentContact.graph_uniform C hab) hmesh,
    corollary3_tangent_boundary C parts hmesh⟩

/-- The chord perimeter and the actual vertical top of the filled tangent
polygon approach the curve, using this edition's Corollaries II and III.
The finite trace/region identity is proved; no arclength is asserted. -/
theorem corollary4_tangent_polygon_perimeters {g d : Fraction → Fraction} {a b : Fraction}
    (C : TangentContact.Patch g d a b) (parts : Nat → MonotoneRectangles.Partition a b)
    (hbase : 0 ≤ (g a).num)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches
      (fun m => RationalBoundary.ChordTrace (TangentContact.graph g) (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) ∧
    RationalBoundary.Approaches (fun m => TangentContact.VerticalTop g d (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) :=
  ⟨(corollary4_tangent_perimeters C parts hmesh).1,
    corollary3_tangent_polygon_boundary C parts hbase hmesh⟩

end Principia1687.LemmaIII

/-! 1713. Primary rational perimeter approximation; modern support remains separate. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11
Anchor URLs: NATP00082.par11 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11
Proof-step correspondence: The edition's Corollaries II and III supply two-sided chord and supporting-segment approximation with explicit continuity, mesh and supporting-cell premises. The concave increasing rational patch reconstruction derives continuity and the cells from two-sided secant contact and independent secant concavity. Finite interpolation identifies the joined contact-tangent trace with the filled polygon's vertical top. The edition's Corollaries II and III then prove approach of the chord and that actual upper perimeter to the curve. Tangent existence for arbitrary curves, non-rational points, force-polygon identification and arclength remain open. Modern completed-curve reconstructions remain below the separator.
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

/-- The source-local corollary chain supplies the inscribed chord and
supporting-segment perimeter approximations for rational points. Actual
tangents, arbitrary completed points, force-polygon identification and
arclength are separate obligations. -/
theorem corollary4_rational_perimeters (f : Fraction → TimeSubdivision.Point) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b) (hf : RationalBoundary.UniformOn f a b)
    (cells : ∀ m i, SupportingTangents.Cell (f ((parts m).nodes i)) (f ((parts m).nodes (i+1))))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => RationalBoundary.ChordTrace f (parts m))
      (RationalBoundary.CurveTrace f a b) ∧
    RationalBoundary.Approaches (fun m => RationalBoundary.SupportingTrace f (parts m) (cells m))
      (RationalBoundary.CurveTrace f a b) :=
  ⟨corollary2_chord_boundary f a b parts hf hmesh,
    corollary3_supporting_boundary f a b parts hf cells hmesh⟩


/-- Both the chord perimeter and the constructed contact-tangent perimeter
approach the curve. On these concave increasing patches uniform continuity
and the supporting cells are conclusions of contact/concavity, not premises.
This is boundary approximation; it asserts no arclength limit. -/
theorem corollary4_tangent_perimeters {g d : Fraction → Fraction} {a b : Fraction}
    (C : TangentContact.Patch g d a b) (parts : Nat → MonotoneRectangles.Partition a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches
      (fun m => RationalBoundary.ChordTrace (TangentContact.graph g) (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) ∧
    RationalBoundary.Approaches (fun m => TangentContact.Trace C (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) := by
  have hab : Fraction.le a b := Fraction.magnitudes.le_trans
    (MonotoneRectangles.node_bounds (parts 0) 0 (by omega)).1
    (MonotoneRectangles.node_bounds (parts 0) 0 (by omega)).2
  exact ⟨corollary2_chord_boundary (TangentContact.graph g) a b parts
    (TangentContact.graph_uniform C hab) hmesh,
    corollary3_tangent_boundary C parts hmesh⟩

/-- The chord perimeter and the actual vertical top of the filled tangent
polygon approach the curve, using this edition's Corollaries II and III.
The finite trace/region identity is proved; no arclength is asserted. -/
theorem corollary4_tangent_polygon_perimeters {g d : Fraction → Fraction} {a b : Fraction}
    (C : TangentContact.Patch g d a b) (parts : Nat → MonotoneRectangles.Partition a b)
    (hbase : 0 ≤ (g a).num)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches
      (fun m => RationalBoundary.ChordTrace (TangentContact.graph g) (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) ∧
    RationalBoundary.Approaches (fun m => TangentContact.VerticalTop g d (parts m))
      (RationalBoundary.CurveTrace (TangentContact.graph g) a b) :=
  ⟨(corollary4_tangent_perimeters C parts hmesh).1,
    corollary3_tangent_polygon_boundary C parts hbase hmesh⟩

end Principia1713.LemmaIII

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

/-- Modern supporting-line perimeter limit under explicit supporting cells and
uniform endpoint agreement. The cells are not identified with force polygons. -/
-- Modern dependency score: 80/182 (M=80, H=102; transitive project theorems/axioms).
theorem corollary4_supporting_boundary_reconstruction (T : Fraction) (hT : 0 ≤ T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f)
    (points : Nat → Nat → Point)
    (cells : ∀ m k, SupportingTangents.Cell (points m k) (points m (k+1)))
    (hpoints : ∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ m, N ≤ m →
      ∀ k, k ≤ blocks m → CauchyValues.Within (embedPosition (points m k)).val
        (f (nodeTime T hT m k)).val eps) :
    BoundaryLimit (fun m => SupportingBoundary.supportingTrace (points m) (cells m) (blocks m))
      (ImageTrace f) :=
  ModernLib.Reconstruction.Principia1687.LemmaIIICorollaries.corollary3_4_supporting_boundary_reconstruction
    T hT f hf points cells hpoints

-- Modern dependency score: 78/168 (M=78, H=90; transitive project theorems/axioms).
theorem corollary4_chord_reconstruction (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f) :
    BoundaryLimit (fun m => chordTrace f (nodeTime T hT m) (blocks m)) (ImageTrace f) :=
  dyadic_chordTrace_limit T hT f hf

-- Modern dependency score: 129/315 (M=129, H=186; transitive project theorems/axioms).
theorem corollary4_constructed_polygon_boundary (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0<E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    BoundaryLimit (fun m => ImageTrace
      (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
      (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  GeneralForcePolygonCurve.constructed_polygon_boundary_limit o E0 T tau L B s hE d

end Principia1687.LemmaIII

namespace Principia1713.LemmaIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon
open TimeSubdivision PositionValues BinaryTime HarmonicDyadic DyadicNodes CurveTrace

/-- The 1713 witness has the same conditional supporting-line perimeter
model; its area statement and tangent identification remain open. -/
-- Modern dependency score: 80/182 (M=80, H=102; transitive project theorems/axioms).
theorem corollary4_supporting_boundary_reconstruction (T : Fraction) (hT : 0 ≤ T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f)
    (points : Nat → Nat → Point)
    (cells : ∀ m k, SupportingTangents.Cell (points m k) (points m (k+1)))
    (hpoints : ∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ m, N ≤ m →
      ∀ k, k ≤ blocks m → CauchyValues.Within (embedPosition (points m k)).val
        (f (nodeTime T hT m k)).val eps) :
    BoundaryLimit (fun m => SupportingBoundary.supportingTrace (points m) (cells m) (blocks m))
      (ImageTrace f) :=
  ModernLib.Reconstruction.Principia1713.LemmaIIICorollaries.corollary3_4_supporting_boundary_reconstruction
    T hT f hf points cells hpoints

-- Modern dependency score: 78/168 (M=78, H=90; transitive project theorems/axioms).
theorem corollary4_chord_reconstruction (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f) :
    BoundaryLimit (fun m => chordTrace f (nodeTime T hT m) (blocks m)) (ImageTrace f) :=
  dyadic_chordTrace_limit T hT f hf

-- Modern dependency score: 129/315 (M=129, H=186; transitive project theorems/axioms).
theorem corollary4_constructed_polygon_boundary (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0<E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    BoundaryLimit (fun m => ImageTrace
      (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
      (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  GeneralForcePolygonCurve.constructed_polygon_boundary_limit o E0 T tau L B s hE d

end Principia1713.LemmaIII
