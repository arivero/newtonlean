import NewtonLimitDynamics.Polygon.GeneralForcePolygonCurve
import BarrowLib.Polygon.SupportingBoundary

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

end Principia1687.LemmaIII
