import NewtonLimitDynamics

namespace NewtonLimitDynamics.Polygon.ChordBoundaryControls
open NewtonLimitDynamics TimeSubdivision PositionValues ConvexValues ConvexCover
open CauchyValues CompletionGeometry CurveTrace BinaryTime HarmonicTimeRealization HarmonicDyadic

private def p (x y : Int) : Point := (Fraction.ofInt x,Fraction.ofInt y)
private def half : Fraction := ⟨1,2,by decide⟩

-- The bound applies to every completed chord point and any completed centre.
example (x y z : PositionValue) (R : Fraction) (hR : 0≤R.num)
    (hy : Within y.val x.val R) (hz : ClosedChord x y z) : Within z.val x.val R :=
  closedChord_anchor x y z R hR hy hz

-- Degenerate and straight curves are allowed: a limit need not be nonstraight.
example (T : Fraction) (hT : 0≤T.num) (x : PositionValue) :
    BoundaryLimit (fun m => chordTrace (fun _ : BinaryTime T hT => x)
      (DyadicNodes.nodeTime T hT m) (blocks m))
      (ImageTrace (fun _ : BinaryTime T hT => x)) := by
  apply dyadic_chordTrace_limit T hT _
  intro eps heps
  refine ⟨Fraction.ofInt 1,by decide,?_⟩
  intro t u _
  exact within_mono _ _ _ _ (Fraction.magnitudes.lt_implies_le
    ((Fraction.positive_iff_zero_lt eps).mp heps)) ((within_zero_iff _ _).mpr rfl)

-- Every sample, including the last one, lies on the closed chord trace.
example (f : BinaryTime (Fraction.ofInt 0) (by decide) → PositionValue) :
    chordTrace f (DyadicNodes.nodeTime (Fraction.ofInt 0) (by decide) 0) 1
      (f (DyadicNodes.nodeTime (Fraction.ofInt 0) (by decide) 0 1)) :=
  chordTrace_node _ _ 1 (by decide) 1 (by decide)

-- Area alone cannot imply boundary convergence: thin unit-height rectangles
-- have vanishing area but retain the upper corner a unit from the origin.
example (eps : Fraction) (heps : 0<eps.num) :
    ∃ N : Nat, ∀ m, N≤m → Fraction.lt (duration (Fraction.ofInt 1) m) eps :=
  duration_eventually_small _ eps (by decide) heps
example : ¬ Within (embedPosition (p 0 1)).val (embedPosition (p 0 0)).val half := by
  intro h
  have hh := (within_embedded_iff (p 0 1,zeroPoint) (p 0 0,zeroPoint) half).mp h
  change (2 : Int)≤1 at hh
  omega

variable (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
  (s : Point × Point) (hE : 0<E0.num)
  (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)

-- The modulus and both boundary directions are derived for the actual curve.
example : UniformCurve T d.time_nonnegative
    (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) :=
  GeneralForcePolygonCurve.constructed_uniform_curve o E0 T tau L B s hE d
example : BoundaryLimit (fun m => chordTrace
    (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)
    (DyadicNodes.nodeTime T d.time_nonnegative m) (blocks m))
    (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  GeneralForcePolygonCurve.constructed_chord_boundary_limit o E0 T tau L B s hE d
example : BoundaryLimit (fun m => ImageTrace
    (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
    (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  Principia1687.LemmaIII.corollary4_constructed_polygon_boundary o E0 T tau L B s hE d
example : BoundaryLimit (fun m => ImageTrace
    (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
    (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  Principia1713.LemmaIII.corollary4_constructed_polygon_boundary o E0 T tau L B s hE d
example : BoundaryLimit (fun m => ImageTrace
    (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
    (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  DeMotu1684.AreaLaw.natp00089_constructed_boundary_limit o E0 T tau L B s hE d
example : BoundaryLimit (fun m => ImageTrace
    (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
    (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  DeMotu1684.AreaLaw.natp00090_constructed_boundary_limit o E0 T tau L B s hE d

-- Boundary convergence accompanies the existing actual interval swept area.
example (t0 t1 : BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t0 t1
      (GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t0 t1) ∧
    BoundaryLimit (fun m => ImageTrace
      (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
      (ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  ⟨GeneralForceArea.interval_area_is_swept o E0 T tau L B s hE d t0 t1,
    GeneralForcePolygonCurve.constructed_polygon_boundary_limit o E0 T tau L B s hE d⟩

#print axioms CurveTrace.dyadic_chordTrace_limit
#print axioms Principia1687.LemmaIII.corollary4_constructed_polygon_boundary
#print axioms Principia1713.LemmaIII.corollary4_chord_reconstruction
end NewtonLimitDynamics.Polygon.ChordBoundaryControls
