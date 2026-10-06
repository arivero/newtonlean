import ModernLib.Polygon.HarmonicPolygonCurve
import ModernLib.Foundation.Polygon.SquareOuterContent
import ModernLib.Foundation.Polygon.MatchedRegion

/-! The actual nonnegative matched region between the constructed harmonic
curve and the coarse polygon. Each cell uses simultaneous polygon/curve
positions and all rational convex connectors, then closure in the completed
plane. The union counts overlapping and crossing lobes once, without signed
cancellation. The final endpoint connector is included in the last cell. -/
namespace NewtonLimitDynamics.Polygon.HarmonicPathRegion
open NewtonLimitDynamics
open TimeSubdivision PointBounds CentralSchedule HarmonicStability
open HarmonicDyadic HarmonicBinaryPrefix HarmonicTimeRealization
open BinaryTime CauchyValues PositionValues HarmonicPolygonCurve
open ConvexCover ConvexValues CompletionGeometry SquareOuterContent

/-- The actual level-m coarse vertex at the start of cell k. -/
def cellStart (w T : Fraction) (s : Point × Point) (m k : Nat) : Point :=
  (schedule (linearField w) (List.replicate k (duration T m)) s).1

/-- Simultaneous positions, using quotient maps rather than a supplied curve. -/
def cellPatch (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (m k : Nat) (x : PositionValue) : Prop :=
  MatchedRegion.cellPatch T hT (polygonMap w T s hT m)
    (gammaPosition w T s hT hs) m k x

/-- Cell closures give all limit connector points, including their endpoints.
The finite union is an unsigned point set, not a determinant sum. -/
def Region (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (m : Nat) (x : PositionValue) : Prop :=
  MatchedRegion.Region T hT (polygonMap w T s hT m) (gammaPosition w T s hT hs) m x

theorem edgeRadius_nonnegative (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (m : Nat) : 0 ≤ (edgeRadius w T s m).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ hT
      (Fraction.nonnegative_mul _ _ (by decide) (stateNorm_nonnegative s)))
    (HarmonicBinaryPrefix.coefficient_nonnegative w T s hT)

def coverRadius (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num)
    (m : Nat) : NonnegativeRadius :=
  ⟨edgeRadius w T s m,edgeRadius_nonnegative w T s hT m⟩

theorem simultaneous_endpoints_square (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat) :
    CoordinateSquare (cellStart w T s m (ticks b m)) (coverRadius w T s hT m)
      (polygonMap w T s hT m (Quotient.mk _ b)) ∧
    CoordinateSquare (cellStart w T s m (ticks b m)) (coverRadius w T s hT m)
      (gammaPosition w T s hT hs (Quotient.mk _ b)) := by
  have hD : 0 ≤ (Fraction.mul (duration T m)
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s))).num :=
    Fraction.nonnegative_mul _ _ hT
      (Fraction.nonnegative_mul _ _ (by decide) (stateNorm_nonnegative s))
  have hE : 0 ≤ (HarmonicBinaryPrefix.tailCap w T s m).num :=
    HarmonicBinaryPrefix.coefficient_nonnegative w T s hT
  have hpoly := polygon_vertex_bound b w T s hT hs m
  have hcurve := within_symm _ _ _ (positionValue_within _ _ _
    (binaryValue_prefix_bound b w T s hT hs m))
  have hp := within_mono _ _ _ _ (Fraction.le_add_nonnegative _ _ hE) hpoly
  have hg := within_mono _ _ _ _
    (Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ hD)
      (Fraction.add_comm _ _)) hcurve
  exact ⟨square_of_ball_bound _ _ _ hp,square_of_ball_bound _ _ _ hg⟩

theorem cellPatch_square (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m k : Nat)
    (x : PositionValue) (hx : cellPatch w T s hT hs m k x) :
    CoordinateSquare (cellStart w T s m k) (coverRadius w T s hT m) x := by
  exact MatchedRegion.cellPatch_square T hT _ _ m (cellStart w T s m)
    (coverRadius w T s hT m) (fun b => simultaneous_endpoints_square b w T s hT hs m) k x hx

theorem closed_cell_square (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m k : Nat)
    (x : PositionValue) (hx : Closure (cellPatch w T s hT hs m k) x) :
    CoordinateSquare (cellStart w T s m k) (coverRadius w T s hT m) x :=
  MatchedRegion.closed_cell_square T hT _ _ m (cellStart w T s m)
    (coverRadius w T s hT m) (fun b => simultaneous_endpoints_square b w T s hT hs m) k x hx

/-- One derived coordinate square per actual coarse cell. -/
def actualCover (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (m : Nat) : Cover (Region w T s hT hs m) :=
  MatchedRegion.actualCover T hT _ _ m (cellStart w T s m) (coverRadius w T s hT m)
    (fun b => simultaneous_endpoints_square b w T s hT hs m)

theorem connector_in_region (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat)
    (t : BinaryTime T hT) (a : Fraction) (ha : UnitInterval a) :
    Region w T s hT hs m (convexPosition a ha
      (polygonMap w T s hT m t) (gammaPosition w T s hT hs t)) :=
  MatchedRegion.connector_in_region T hT _ _ m t a ha

/-- Reversing a connector changes no unsigned region point. -/
theorem reversed_connector_in_region (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat)
    (t : BinaryTime T hT) (a : Fraction) (ha : UnitInterval a) :
    Region w T s hT hs m (convexPosition a ha
      (gammaPosition w T s hT hs t) (polygonMap w T s hT m t)) :=
  MatchedRegion.reversed_connector_in_region T hT _ _ m t a ha

theorem polygon_in_region (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat)
    (t : BinaryTime T hT) : Region w T s hT hs m (polygonMap w T s hT m t) :=
  MatchedRegion.polygon_in_region T hT _ _ m t

theorem curve_in_region (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat)
    (t : BinaryTime T hT) : Region w T s hT hs m (gammaPosition w T s hT hs t) :=
  MatchedRegion.curve_in_region T hT _ _ m t

theorem shared_initial_endpoint (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat) :
    polygonMap w T s hT m (leftTime T hT) = gammaPosition w T s hT hs (leftTime T hT) :=
  (polygonMap_left w T s hT m).trans (gammaPosition_left w T s hT hs).symm

/-- The last-cell connector is explicitly present even when endpoints differ. -/
theorem final_connector_in_region (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat)
    (a : Fraction) (ha : UnitInterval a) :
    Region w T s hT hs m (convexPosition a ha
      (polygonMap w T s hT m (rightTime T hT))
      (asPosition (endpointValue w T s hT hs))) := by
  have h := connector_in_region w T s hT hs m (rightTime T hT) a ha
  rwa [gammaPosition_right] at h

def budgetCoefficient (w T : Fraction) (s : Point × Point) : Fraction :=
  squareArea (edgeCoefficient w T s)

theorem budgetCoefficient_nonnegative (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) : 0 ≤ (budgetCoefficient w T s).num :=
  squareArea_nonnegative _ (edgeCoefficient_nonnegative w T s hT)

/-- The actual region cover has budget 4*C²/2^m, with C the edge coefficient. -/
theorem actual_budget_geometric (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat) :
    Fraction.equiv (actualCover w T s hT hs m).budget
      (duration (budgetCoefficient w T s) m) := by
  exact MatchedRegion.uniform_budget_geometric (cellStart w T s m)
    (coverRadius w T s hT m) m (edgeCoefficient w T s) (edgeRadius_geometric w T s m)

/-- Polygon/constructed-curve outer content, represented exactly by its lower
cut. The definition quantifies over all finite square covers of the actual set. -/
def D_mesh (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (m : Nat) : Fraction → Prop :=
  LowerContent (Region w T s hT hs m)

theorem D_mesh_nonnegative (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat) :
    D_mesh w T s hT hs m (Fraction.ofInt 0) := content_zero_lower _

theorem D_mesh_bound (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat)
    (q : Fraction) (hq : D_mesh w T s hT hs m q) :
    Fraction.le q (duration (budgetCoefficient w T s) m) :=
  Fraction.le_equiv_right (hq (actualCover w T s hT hs m))
    (actual_budget_geometric w T s hT hs m)

/-- Nonnegative outer contents tend to zero: every positive rational test bound
fails to be a lower bound from one explicit mesh onward. -/
theorem D_mesh_tends_zero (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N, ∀ m, N ≤ m → ∀ q, D_mesh w T s hT hs m q → Fraction.lt q eps := by
  obtain ⟨N,hN⟩ := duration_eventually_small (budgetCoefficient w T s) eps
    (budgetCoefficient_nonnegative w T s hT) heps
  exact ⟨N,fun m hm q hq => Fraction.magnitudes.lt_of_le_lt
    (D_mesh_bound w T s hT hs m q hq) (hN m hm)⟩

theorem D_mesh_zero_window (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat)
    (hz : T.num = 0) (q : Fraction) :
    D_mesh w T s hT hs m q ↔ Fraction.le q (Fraction.ofInt 0) := by
  constructor
  · intro hq
    have hb := D_mesh_bound w T s hT hs m q hq
    apply Fraction.le_equiv_right hb
    simp [budgetCoefficient,SquareOuterContent.squareArea,edgeCoefficient,
      HarmonicBinaryPrefix.coefficient,duration,Fraction.equiv,Fraction.add,
      Fraction.mul,Fraction.ofInt,hz]
  · intro hq
    exact content_downward _ _ _ hq (content_zero_lower _)

end NewtonLimitDynamics.Polygon.HarmonicPathRegion
