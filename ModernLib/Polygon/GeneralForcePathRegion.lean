import ModernLib.Polygon.GeneralForcePolygonCurve
import ModernLib.Foundation.Polygon.MatchedRegion

/-! The actual unsigned region between the sampled central-force polygon and
its constructed curve. The shared matched-region geometry retains all cell
closures and the final connector. Covers are derived from actual vertex and
prefix bounds; no area or enclosure of a supplied curve is a premise. -/

namespace NewtonLimitDynamics.Polygon.GeneralForcePathRegion
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicBinaryPrefix HarmonicTimeRealization BinaryTime
open CauchyValues PositionValues ConvexCover ConvexValues CompletionGeometry SquareOuterContent
open GeneralForceEndpoint GeneralForcePrefix GeneralForceTime GeneralForcePolygonCurve

noncomputable def cellStart (o : ForceClasses.CentralOracle) (E0 T : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (m k : Nat) : Point :=
  (countState o E0 T s hE m k).1

def cellPatch (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m k : Nat)
    (x : PositionValue) : Prop :=
  MatchedRegion.cellPatch T d.time_nonnegative
    (polygonMap o E0 T s hE d.time_nonnegative m)
    (gammaPosition o E0 T tau L B s hE d) m k x

def Region (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat)
    (x : PositionValue) : Prop :=
  MatchedRegion.Region T d.time_nonnegative
    (polygonMap o E0 T s hE d.time_nonnegative m)
    (gammaPosition o E0 T tau L B s hE d) m x

noncomputable def coverRadius (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) : NonnegativeRadius :=
  ⟨duration (edgeCoefficient E0 T tau L B s d.calibration_positive) m,
    edgeCoefficient_nonnegative E0 T tau L B s hE d.time_nonnegative d.calibration_positive
      d.lipschitz.1 d.bound_nonnegative⟩

theorem simultaneous_endpoints_square (b : Nat → Bool) (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    CoordinateSquare (cellStart o E0 T s hE m (ticks b m)) (coverRadius o E0 T tau L B s hE d m)
      (polygonMap o E0 T s hE d.time_nonnegative m (Quotient.mk _ b)) ∧
    CoordinateSquare (cellStart o E0 T s hE m (ticks b m)) (coverRadius o E0 T tau L B s hE d m)
      (gammaPosition o E0 T tau L B s hE d (Quotient.mk _ b)) := by
  have hD : 0 ≤ (Fraction.mul (duration T m) (velocityCap T B s)).num :=
    Fraction.nonnegative_mul _ _ d.time_nonnegative
      (velocityCap_nonnegative T B s d.time_nonnegative d.bound_nonnegative)
  have hE' : 0 ≤ (GeometricTail.tailCap
      (GeneralForcePrefix.coefficient E0 T tau L B s d.calibration_positive) m).num :=
    GeneralForcePrefix.coefficient_nonnegative E0 T tau L B s hE d.time_nonnegative
      d.calibration_positive d.lipschitz.1 d.bound_nonnegative
  have hpoly := polygon_vertex_bound b o E0 T tau L B s hE d m
  have hcurve := within_symm _ _ _ (positionValue_within _ _ _
    (prefix_value_bound b o E0 T tau L B s hE d m))
  have hr := edgeRadius_geometric E0 T tau L B s d.calibration_positive m
  have hp := within_mono _ _ _ _
    (Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ hE') hr) hpoly
  have hg := within_mono _ _ _ _
    (Fraction.le_equiv_right
      (Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ hD) (Fraction.add_comm _ _)) hr) hcurve
  exact ⟨square_of_ball_bound _ _ _ hp,square_of_ball_bound _ _ _ hg⟩

/-- One proved square per actual coarse cell, covering its closure. -/
noncomputable def actualCover (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    Cover (Region o E0 T tau L B s hE d m) :=
  MatchedRegion.actualCover T d.time_nonnegative _ _ m (cellStart o E0 T s hE m)
    (coverRadius o E0 T tau L B s hE d m)
    (fun b => simultaneous_endpoints_square b o E0 T tau L B s hE d m)

theorem connector_in_region (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat)
    (t : BinaryTime T d.time_nonnegative) (a : Fraction) (ha : UnitInterval a) :
    Region o E0 T tau L B s hE d m (convexPosition a ha
      (polygonMap o E0 T s hE d.time_nonnegative m t) (gammaPosition o E0 T tau L B s hE d t)) :=
  MatchedRegion.connector_in_region T d.time_nonnegative _ _ m t a ha

/-- The final endpoint may differ from its coarse vertex, so its connector is
retained explicitly rather than assumed to vanish. -/
theorem final_connector_in_region (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat)
    (a : Fraction) (ha : UnitInterval a) :
    Region o E0 T tau L B s hE d m (convexPosition a ha
      (polygonMap o E0 T s hE d.time_nonnegative m (rightTime T d.time_nonnegative))
      (asPosition (endpointValue o E0 T tau L B s hE d.toConditions))) := by
  have h := connector_in_region o E0 T tau L B s hE d m (rightTime T d.time_nonnegative) a ha
  change Region o E0 T tau L B s hE d m (convexPosition a ha _
    (asPosition (gammaValue o E0 T tau L B s hE d (rightTime T d.time_nonnegative)))) at h
  rwa [GeneralForceTime.right_endpoint_value] at h

noncomputable def budgetCoefficient (E0 T tau L B : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) : Fraction := squareArea (edgeCoefficient E0 T tau L B s ht)

theorem budgetCoefficient_nonnegative (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (ht : 0 < tau.num) (hL : 0 ≤ L.num) (hB : 0 ≤ B.num) :
    0 ≤ (budgetCoefficient E0 T tau L B s ht).num :=
  squareArea_nonnegative _ (edgeCoefficient_nonnegative E0 T tau L B s hE hT ht hL hB)

theorem actual_budget_geometric (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    Fraction.equiv (actualCover o E0 T tau L B s hE d m).budget
      (duration (budgetCoefficient E0 T tau L B s d.calibration_positive) m) :=
  MatchedRegion.uniform_budget_geometric (cellStart o E0 T s hE m)
    (coverRadius o E0 T tau L B s hE d m) m
    (edgeCoefficient E0 T tau L B s d.calibration_positive) (Fraction.equiv_refl _)

def D_mesh (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) : Fraction → Prop :=
  LowerContent (Region o E0 T tau L B s hE d m)

theorem D_mesh_nonnegative (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    D_mesh o E0 T tau L B s hE d m (Fraction.ofInt 0) := content_zero_lower _

theorem D_mesh_bound (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat)
    (q : Fraction) (hq : D_mesh o E0 T tau L B s hE d m q) :
    Fraction.le q (duration (budgetCoefficient E0 T tau L B s d.calibration_positive) m) :=
  Fraction.le_equiv_right (hq (actualCover o E0 T tau L B s hE d m))
    (actual_budget_geometric o E0 T tau L B s hE d m)

theorem D_mesh_tends_zero (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N, ∀ m, N≤m → ∀ q, D_mesh o E0 T tau L B s hE d m q → Fraction.lt q eps := by
  obtain ⟨N,hN⟩ := duration_eventually_small
    (budgetCoefficient E0 T tau L B s d.calibration_positive) eps
    (budgetCoefficient_nonnegative E0 T tau L B s hE d.time_nonnegative d.calibration_positive
      d.lipschitz.1 d.bound_nonnegative) heps
  exact ⟨N,fun m hm q hq => Fraction.magnitudes.lt_of_le_lt
    (D_mesh_bound o E0 T tau L B s hE d m q hq) (hN m hm)⟩

theorem budget_zero_window (E0 T tau L B : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) (m : Nat) (hz : T.num=0) :
    Fraction.equiv (duration (budgetCoefficient E0 T tau L B s ht) m) (Fraction.ofInt 0) := by
  simp [budgetCoefficient,squareArea,edgeCoefficient,GeneralForcePrefix.coefficient,
    GeneralForcePrefix.weightedCoefficient,GeneralForceEndpoint.weightedCoefficient,
    duration,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,hz]

theorem D_mesh_zero_window (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat)
    (hz : T.num=0) (q : Fraction) :
    D_mesh o E0 T tau L B s hE d m q ↔ Fraction.le q (Fraction.ofInt 0) := by
  constructor
  · intro hq
    exact Fraction.le_equiv_right (D_mesh_bound o E0 T tau L B s hE d m q hq)
      (budget_zero_window E0 T tau L B s d.calibration_positive m hz)
  · intro hq
    exact content_downward _ _ _ hq (content_zero_lower _)

end NewtonLimitDynamics.Polygon.GeneralForcePathRegion
