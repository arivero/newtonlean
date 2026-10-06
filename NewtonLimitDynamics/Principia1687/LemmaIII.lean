import NewtonLimitDynamics.Polygon.GeneralForcePolygonCurve
import BarrowLib.Polygon.SupportingBoundary
import BarrowLib.Polygon.MonotoneRectangles

/-! 1687 Lemma III Corollary 4, chord-boundary reconstruction:
NATP00077 par3–10, especially par8 (chords) and par10 (perimeters),
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10.
Lemma II starts with a given curvilinear figure; its proof bounds the finite
area gap and cites Lemma I. Lemma III permits unequal widths and uses their
maximum. Those scalar estimates alone do not prove boundary convergence.
Here the chord case is proved from an explicit uniform modulus of the given
curve and shrinking time-cell spans. The constructed central-force client
derives its own modulus and whole-edge comparison. This is a modern rational
trace reconstruction, not arclength convergence, a proof for tangent polygons,
or certification of the unrestricted historical continuously acting force.
The supporting-line result below reconstructs par9–10 for rational monotone
graph cells with explicit finite line data and convergent endpoint samples;
it derives their enclosure and whole closed boundary limit. It does not prove
that such line data are tangents to every curve or to the constructed motion. -/

namespace Principia1687.LemmaIII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon
open TimeSubdivision PositionValues BinaryTime HarmonicDyadic DyadicNodes CurveTrace

theorem corollary4_chord_reconstruction (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f) :
    BoundaryLimit (fun m => chordTrace f (nodeTime T hT m) (blocks m)) (ImageTrace f) :=
  dyadic_chordTrace_limit T hT f hf

/-- Application to the actual regional constructed force polygons. Their
boundary convergence is derived, not supplied as an instance of Lemma III. -/
theorem corollary4_constructed_polygon_boundary (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0<E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    BoundaryLimit (fun m => ImageTrace
      (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
      (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  GeneralForcePolygonCurve.constructed_polygon_boundary_limit o E0 T tau L B s hE d

/-- NATP00077 par9 (`Ut &`) and par10's collective perimeter conclusion.
This is the explicit supporting-cell reconstruction of the tangent branch,
not a chord-to-tangent inference or a proof of tangent existence. -/
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

/-- NATP00077 par4: the equal-width rectangle-sum identity in a
modern rational monotone graph model. Ordinary union-area identification
and the full curvilinear ratio conclusion are separate. -/
theorem lemma2_equal_width_gap (g : Fraction → Fraction) (a b M : Fraction)
    (p : MonotoneRectangles.Partition a b) (hg : MonotoneRectangles.MonotoneOn g a b)
    (hM : ∀ i, i<p.count → Fraction.equiv (MonotoneRectangles.width p i) M) :
    Fraction.equiv (MonotoneRectangles.gap g p)
      (Fraction.mul M (HarmonicTimeComparison.durationDifference (g a) (g b))) :=
  MonotoneRectangles.gap_equal_width g p hg M hM

/-- NATP00077 par3–par6: actual lower/upper rectangle-set enclosure
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

end Principia1687.LemmaIII
