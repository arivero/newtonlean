import NewtonLimitDynamics.Polygon.GeneralForceTime
import BarrowLib.Polygon.PolygonValues
import BarrowLib.Polygon.CurveTrace

/-! An actual coarse polygon quotient for the general sampled central-force
construction. Shared finite-vertex geometry proves all aliases; the actual
velocity cap and prefix tail give a uniform whole-edge curve comparison. -/

namespace NewtonLimitDynamics.Polygon.GeneralForcePolygonCurve
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicBinaryPrefix CauchyValues BinaryTime
open PositionValues HarmonicTimeRealization GeneralForceEndpoint GeneralForcePrefix GeneralForceTime

noncomputable def vertices (o : ForceClasses.CentralOracle) (E0 T : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (m : Nat) : PolygonValues.VertexChain T m where
  state := countState o E0 T s hE m
  join := fun _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

noncomputable def polygonMap (o : ForceClasses.CentralOracle) (E0 T : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (m : Nat) :
    BinaryTime T hT → PositionValue := PolygonValues.polygonMap T hT m (vertices o E0 T s hE m)

noncomputable def edgeCoefficient (E0 T tau L B : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) : Fraction :=
  Fraction.add (Fraction.mul T (velocityCap T B s))
    (GeneralForcePrefix.coefficient E0 T tau L B s ht)

theorem edgeCoefficient_nonnegative (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (ht : 0 < tau.num) (hL : 0 ≤ L.num) (hB : 0 ≤ B.num) :
    0 ≤ (edgeCoefficient E0 T tau L B s ht).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ hT (velocityCap_nonnegative T B s hT hB))
    (GeneralForcePrefix.coefficient_nonnegative E0 T tau L B s hE hT ht hL hB)

theorem edgeRadius_geometric (E0 T tau L B : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) (m : Nat) :
    Fraction.equiv
      (Fraction.add (Fraction.mul (duration T m) (velocityCap T B s))
        (GeometricTail.tailCap (GeneralForcePrefix.coefficient E0 T tau L B s ht) m))
      (duration (edgeCoefficient E0 T tau L B s ht) m) := by
  simp only [edgeCoefficient,GeometricTail.tailCap,duration,Fraction.equiv,Fraction.add,
    Fraction.mul,Int.add_mul,Int.mul_add]
  ac_nf

theorem polygon_vertex_bound (b : Nat → Bool) (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    Within (polygonMap o E0 T s hE d.time_nonnegative m (Quotient.mk _ b)).val
      (positionValue (embed (prefixState b o E0 T s hE m)))
      (Fraction.mul (duration T m) (velocityCap T B s)) :=
  PolygonValues.polygon_vertex_bound b T d.time_nonnegative m (vertices o E0 T s hE m) _
    (count_velocity o E0 T tau L B s hE d m (ticks b m) (ticks_le_blocks b m))

/-- Every point of every coarse edge is controlled against the constructed
curve, with an explicit geometric mesh bound. No area is supplied. -/
theorem whole_edge_bound (b : Nat → Bool) (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    Within (polygonMap o E0 T s hE d.time_nonnegative m (Quotient.mk _ b)).val
      (gammaPosition o E0 T tau L B s hE d (Quotient.mk _ b)).val
      (duration (edgeCoefficient E0 T tau L B s d.calibration_positive) m) := by
  have hp := polygon_vertex_bound b o E0 T tau L B s hE d m
  have hg := positionValue_within _ _ _ (prefix_value_bound b o E0 T tau L B s hE d m)
  have hb := within_triangle _ _ _ _ _ hp hg
  exact within_mono _ _ _ _
    (Fraction.le_of_equiv (edgeRadius_geometric E0 T tau L B s d.calibration_positive m)) hb

theorem polygonMap_whole_edge_bound (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat)
    (t : BinaryTime T d.time_nonnegative) :
    Within (polygonMap o E0 T s hE d.time_nonnegative m t).val
      (gammaPosition o E0 T tau L B s hE d t).val
      (duration (edgeCoefficient E0 T tau L B s d.calibration_positive) m) := by
  induction t using Quotient.inductionOn with
  | _ b => exact whole_edge_bound b o E0 T tau L B s hE d m

theorem polygonMap_uniform_convergence (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m → ∀ t : BinaryTime T d.time_nonnegative,
      Within (polygonMap o E0 T s hE d.time_nonnegative m t).val
        (gammaPosition o E0 T tau L B s hE d t).val eps := by
  obtain ⟨N,hN⟩ := duration_eventually_small
    (edgeCoefficient E0 T tau L B s d.calibration_positive) eps
    (edgeCoefficient_nonnegative E0 T tau L B s hE d.time_nonnegative d.calibration_positive
      d.lipschitz.1 d.bound_nonnegative) heps
  exact ⟨N,fun m hm t => within_mono _ _ _ _ (Fraction.magnitudes.lt_implies_le (hN m hm))
    (polygonMap_whole_edge_bound o E0 T tau L B s hE d m t)⟩

theorem polygonMap_left (o : ForceClasses.CentralOracle) (E0 T : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (m : Nat) :
    polygonMap o E0 T s hE hT m (leftTime T hT) = embedPosition s.1 :=
  PolygonValues.polygonMap_left T hT m (vertices o E0 T s hE m)

theorem shared_initial_endpoint (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    polygonMap o E0 T s hE d.time_nonnegative m (leftTime T d.time_nonnegative) =
      gammaPosition o E0 T tau L B s hE d (leftTime T d.time_nonnegative) := by
  rw [polygonMap_left]
  apply Subtype.ext
  change positionValue (embed (s.1,zeroPoint)) = positionValue
    (gammaValue o E0 T tau L B s hE d (leftTime T d.time_nonnegative))
  rw [GeneralForceTime.left_endpoint_value]
  rfl

/-- The given-curve modulus needed by the chord-boundary argument is derived
for the actual constructed general curve, rather than supplied as a limit. -/
theorem constructed_uniform_curve (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0<E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    CurveTrace.UniformCurve T d.time_nonnegative
      (gammaPosition o E0 T tau L B s hE d) := by
  intro eps heps
  refine ⟨timeTolerance T tau B s d.time_nonnegative d.calibration_positive
    d.bound_nonnegative eps,
    timeTolerance_positive T tau B s d.time_nonnegative d.calibration_positive
      d.bound_nonnegative eps heps,?_⟩
  intro x y hxy
  exact within_mono _ _ _ _ (Fraction.magnitudes.lt_implies_le (Fraction.half_lt eps heps))
    (positionValue_within _ _ _ (gamma_uniform_continuity o E0 T tau L B s hE d eps heps x y hxy))

/-- The closed chords of the actual constructed curve have its entire trace
as their two-sided boundary limit. This is the given-curve chord case of
Lemma III Corollary 4, instantiated without a supplied curve modulus. -/
theorem constructed_chord_boundary_limit (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0<E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    CurveTrace.BoundaryLimit (fun m => CurveTrace.chordTrace
      (gammaPosition o E0 T tau L B s hE d)
      (DyadicNodes.nodeTime T d.time_nonnegative m) (blocks m))
      (CurveTrace.ImageTrace (gammaPosition o E0 T tau L B s hE d)) :=
  CurveTrace.dyadic_chordTrace_limit T d.time_nonnegative _
    (constructed_uniform_curve o E0 T tau L B s hE d)

/-- The actual force polygons have the same boundary limit, independently
of the constructed curve's inscribed chord family. The whole-edge comparison
provides both directions; scalar area convergence is not used as a premise.
No tangent-polygon or arclength assertion is made. -/
theorem constructed_polygon_boundary_limit (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0<E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    CurveTrace.BoundaryLimit (fun m => CurveTrace.ImageTrace
      (polygonMap o E0 T s hE d.time_nonnegative m))
      (CurveTrace.ImageTrace (gammaPosition o E0 T tau L B s hE d)) :=
  CurveTrace.imageTrace_limit _ _
    (fun eps heps => polygonMap_uniform_convergence o E0 T tau L B s hE d eps heps)

end NewtonLimitDynamics.Polygon.GeneralForcePolygonCurve
