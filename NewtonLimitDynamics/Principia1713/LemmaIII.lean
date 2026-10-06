import NewtonLimitDynamics.Polygon.GeneralForcePolygonCurve

/-! 1713 Lemma III Corollary 4, chord-boundary reconstruction:
NATP00082 par4–11, especially par9 (chords) and par11 (perimeters),
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11.
Its given-curve enclosure route through Lemmas I–III remains distinct from
the 1687 passages. The explicit uniform-modulus premise below supplies boundary
control rather than inferring it from scalar area. The actual force-construction
client derives its own curve and whole-edge comparison. No tangent-polygon,
arclength or unrestricted historical force conclusion is asserted. -/

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

end Principia1713.LemmaIII
