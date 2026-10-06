import NewtonLimitDynamics.Polygon.GeneralForcePolygonCurve
import BarrowLib.Polygon.SupportingBoundary
import BarrowLib.Polygon.MonotoneRectangles

/-! 1713 Lemma III Corollary 4, chord-boundary reconstruction:
NATP00082 par4–11, especially par9 (chords) and par11 (perimeters),
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11.
Its given-curve enclosure route through Lemmas I–III remains distinct from
the 1687 passages. The explicit uniform-modulus premise below supplies boundary
control rather than inferring it from scalar area. The actual force-construction
client derives its own curve and whole-edge comparison. The supporting-line
result below reconstructs par10–11 for rational monotone graph cells with
explicit finite line data and convergent endpoint samples; their enclosure
and whole closed boundary limit are derived. Tangent existence for arbitrary
curves, arclength and unrestricted historical force remain separate. -/

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

/-- NATP00082 par10 (`Ut &`) and par11's collective perimeter conclusion.
The 1713 wording stays local; finite supporting-line data do not certify
that these lines are tangents of every curve or of the constructed motion. -/
theorem corollary3_4_supporting_boundary_reconstruction (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f)
    (points : Nat → Nat → Point)
    (cells : ∀ m k, SupportingTangents.Cell (points m k) (points m (k+1)))
    (hpoints : ∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
      ∀ k, k≤blocks m → CauchyValues.Within (embedPosition (points m k)).val
        (f (nodeTime T hT m k)).val eps) :
    BoundaryLimit (fun m => SupportingBoundary.supportingTrace (points m) (cells m) (blocks m))
      (ImageTrace f) :=
  SupportingBoundary.dyadic_supportingTrace_limit T hT f hf points cells hpoints

/-- NATP00082 par5: the equal-width rectangle-sum identity in a
modern rational monotone graph model. Ordinary union-area identification
and the full curvilinear ratio conclusion are separate. -/
theorem lemma2_equal_width_gap (g : Fraction → Fraction) (a b M : Fraction)
    (p : MonotoneRectangles.Partition a b) (hg : MonotoneRectangles.MonotoneOn g a b)
    (hM : ∀ i, i<p.count → Fraction.equiv (MonotoneRectangles.width p i) M) :
    Fraction.equiv (MonotoneRectangles.gap g p)
      (Fraction.mul M (HarmonicTimeComparison.durationDifference (g a) (g b))) :=
  MonotoneRectangles.gap_equal_width g p hg M hM

/-- NATP00082 par4–par7: actual lower/upper rectangle-set enclosure
and exhaustion of their derived rational side-product sum gap. A fixed given
monotone graph and shrinking actual maximum widths remain explicit. No
curvilinear area or desired enclosure is supplied; no ordinary union-area,
ultimate ratio or unrestricted historical proof is concluded. -/
theorem lemmas2_3_monotone_rectangle_reconstruction (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hmesh : ∀ delta : Fraction, 0<delta.num → ∃ N : Nat, ∀ m, N≤m →
      Fraction.lt (MonotoneRectangles.maxWidth (parts m)) delta) :
    (∀ m, (∀ x, MonotoneRectangles.completed (MonotoneRectangles.lowerFigure g (parts m)) x →
        MonotoneRectangles.completed (MonotoneRectangles.figure g a b) x) ∧
      (∀ x, MonotoneRectangles.completed (MonotoneRectangles.figure g a b) x →
        MonotoneRectangles.completed (MonotoneRectangles.upperFigure g (parts m)) x)) ∧
    (∀ m, (0≤(MonotoneRectangles.lowerSum g (parts m)).num ∧
        0≤(MonotoneRectangles.upperSum g (parts m)).num) ∧
      (0≤(MonotoneRectangles.gap g (parts m)).num ∧
        Fraction.le (MonotoneRectangles.gap g (parts m))
          (Fraction.mul (MonotoneRectangles.maxWidth (parts m))
            (HarmonicTimeComparison.durationDifference (g a) (g b))))) ∧
    (∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
      Fraction.lt (MonotoneRectangles.gap g (parts m)) eps) :=
  ⟨fun m => MonotoneRectangles.completed_enclosure g (parts m) hg,
    fun m => ⟨MonotoneRectangles.sums_nonnegative g (parts m) hg hbase,
      MonotoneRectangles.gap_bound g (parts m) hg (MonotoneRectangles.maxWidth (parts m))
        (MonotoneRectangles.maxWidth_bounds (parts m)).1⟩,
    MonotoneRectangles.gaps_vanish g parts hg hmesh⟩

end Principia1713.LemmaIII
