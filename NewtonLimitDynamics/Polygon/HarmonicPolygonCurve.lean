import NewtonLimitDynamics.Polygon.PositionValues
import BarrowLib.Polygon.AffineBoundary
import BarrowLib.Polygon.PolygonValues

/-!
Actual within-cell polygon positions and their distance from the constructed
harmonic position value, for every binary address. The affine names use later
times in the same cell. No curve or adjacent-error condition is supplied.
Address independence includes same-cell and shared-boundary aliases.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicPolygonCurve

open NewtonLimitDynamics
open TimeSubdivision PointBounds
open HarmonicDyadic HarmonicBinaryPrefix HarmonicTimeRealization
open BinaryTime CauchyValues PositionValues

def vertices (w T : Fraction) (s : Point × Point) (m : Nat) :
    PolygonValues.VertexChain T m where
  state := countState w T s m
  join := by
    intro k
    change pointEquiv (CentralSchedule.schedule (HarmonicStability.linearField w)
      (List.replicate (k+1) (duration T m)) s).1 _
    rw [schedule_replicate_step]
    exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

def polygonName (b : Nat → Bool) (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (m : Nat) : EndpointCauchyName :=
  AffineValues.edgeName b T hT (prefixState b w T s m).1
    (prefixState b w T s m).2 m

def polygonPosition (b : Nat → Bool) (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (m : Nat) : PositionValue :=
  asPosition (realize (polygonName b w T s hT m))

def edgeRadius (w T : Fraction) (s : Point × Point) (m : Nat) : Fraction :=
  Fraction.add
    (Fraction.mul (duration T m) (Fraction.mul (Fraction.ofInt 2) (stateNorm s)))
    (HarmonicBinaryPrefix.tailCap w T s m)

def edgeCoefficient (w T : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add (Fraction.mul T (Fraction.mul (Fraction.ofInt 2) (stateNorm s)))
    (HarmonicBinaryPrefix.coefficient w T s)

theorem edgeCoefficient_nonnegative (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) : 0 ≤ (edgeCoefficient w T s).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ hT
      (Fraction.nonnegative_mul _ _ (by decide) (stateNorm_nonnegative s)))
    (HarmonicBinaryPrefix.coefficient_nonnegative w T s hT)

theorem edgeRadius_geometric (w T : Fraction) (s : Point × Point) (m : Nat) :
    Fraction.equiv (edgeRadius w T s m) (duration (edgeCoefficient w T s) m) := by
  simp only [edgeRadius, edgeCoefficient, duration, HarmonicBinaryPrefix.tailCap,
    Fraction.equiv, Fraction.add, Fraction.mul, Int.add_mul, Int.mul_add]
  ac_nf

theorem edgeRadius_eventually_small (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N ≤ m → Fraction.lt (edgeRadius w T s m) eps := by
  obtain ⟨N,hN⟩ := duration_eventually_small (edgeCoefficient w T s) eps
    (edgeCoefficient_nonnegative w T s hT) heps
  exact ⟨N, fun m hm => Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (edgeRadius_geometric w T s m)) (hN m hm)⟩

/-- Every approximant lies at a time phase between the cell's boundaries. -/
theorem polygon_phase_interval (b : Nat → Bool) (T : Fraction)
    (hT : 0 ≤ T.num) (m j : Nat) :
    0 ≤ (HarmonicTimeComparison.durationDifference (timeApprox b T m)
      (timeApprox b T (m+j))).num ∧
    Fraction.le (HarmonicTimeComparison.durationDifference (timeApprox b T m)
      (timeApprox b T (m+j))) (duration T m) :=
  AffineValues.phase_interval b T hT m j

theorem polygon_vertex_bound (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (m : Nat) :
    Within (polygonPosition b w T s hT m).val
      (positionValue (embed (prefixState b w T s m)))
      (Fraction.mul (duration T m) (Fraction.mul (Fraction.ofInt 2) (stateNorm s))) := by
  have hv := Fraction.magnitudes.le_trans (velocity_le_state (prefixState b w T s m))
    (prefix_state_le_two b w T s m hT hs)
  exact PolygonValues.polygon_vertex_bound b T hT m (vertices w T s m) _ hv

/-- Whole-cell polygon/curve bound, including every interior binary time.
Its radius is an explicit sum of two geometric mesh terms. -/
theorem whole_edge_bound (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (m : Nat) :
    Within (polygonPosition b w T s hT m).val
      (gammaPosition w T s hT hs (Quotient.mk _ b)).val
      (edgeRadius w T s m) := by
  have hv := polygon_vertex_bound b w T s hT hs m
  have hg := positionValue_within _ _ _
    (binaryValue_prefix_bound b w T s hT hs m)
  exact within_triangle _ _ _ _ _ hv hg

theorem uniform_whole_edge_convergence (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N ≤ m → ∀ b : Nat → Bool,
      Within (polygonPosition b w T s hT m).val
        (gammaPosition w T s hT hs (Quotient.mk _ b)).val eps := by
  obtain ⟨N,hN⟩ := edgeRadius_eventually_small w T s hT eps heps
  exact ⟨N, fun m hm b => within_mono _ _ _ _
    (Fraction.magnitudes.lt_implies_le (hN m hm))
    (whole_edge_bound b w T s hT hs m)⟩

theorem polygon_same_cell_address_independent (b c : Nat → Bool)
    (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num) (m : Nat)
    (hcell : ticks b m = ticks c m)
    (htime : AddressEquiv T hT b c) :
    polygonPosition b w T s hT m = polygonPosition c w T s hT m := by
  exact PolygonValues.polygon_same_cell b c T hT m (vertices w T s m) hcell htime

theorem polygon_adjacent_address_independent (b c : Nat → Bool)
    (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num) (m : Nat)
    (hcell : ticks b m + 1 = ticks c m)
    (htime : AddressEquiv T hT b c) :
    polygonPosition b w T s hT m = polygonPosition c w T s hT m := by
  exact PolygonValues.polygon_adjacent_cells b c T hT m (vertices w T s m) hcell htime

theorem polygon_zero_window (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num) (m : Nat) (hz : T.num = 0) :
    polygonPosition b w T s hT m =
      asPosition (embed (s.1,AffineValues.zeroPoint)) := by
  exact PolygonValues.polygon_zero_window b T hT m (vertices w T s m) hz

theorem polygon_address_independent (b c : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num) (m : Nat)
    (htime : AddressEquiv T hT b c) :
    polygonPosition b w T s hT m = polygonPosition c w T s hT m := by
  exact PolygonValues.polygon_address_independent b c T hT m (vertices w T s m) htime

/-- The actual coarse polygon, lifted to the same constructed time quotient
as the trajectory after proving both kinds of address invariance. -/
def polygonMap (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num)
    (m : Nat) : BinaryTime T hT → PositionValue :=
  Quotient.lift (fun b => polygonPosition b w T s hT m)
    (fun b c h => polygon_address_independent b c w T s hT m h)

theorem polygonMap_whole_edge_bound (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat)
    (t : BinaryTime T hT) :
    Within (polygonMap w T s hT m t).val (gammaPosition w T s hT hs t).val
      (edgeRadius w T s m) := by
  induction t using Quotient.inductionOn with
  | _ b => exact whole_edge_bound b w T s hT hs m

theorem polygonMap_uniform_convergence (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N ≤ m → ∀ t : BinaryTime T hT,
      Within (polygonMap w T s hT m t).val
        (gammaPosition w T s hT hs t).val eps := by
  obtain ⟨N,hN⟩ := uniform_whole_edge_convergence w T s hT hs eps heps
  refine ⟨N, ?_⟩
  intro m hm t
  induction t using Quotient.inductionOn with
  | _ b => exact hN m hm b

/-- The standard terminating/nonterminating half-time addresses occupy
different coarse cells and nevertheless give the same polygon point. -/
theorem half_time_polygon_alias (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (m : Nat) :
    polygonPosition firstAlias w T s hT m =
      polygonPosition secondAlias w T s hT m :=
  polygon_address_independent firstAlias secondAlias w T s hT m
    (alias_address_equiv T hT)

theorem half_time_distinct_coarse_cells :
    ticks firstAlias 1 = 1 ∧ ticks secondAlias 1 = 0 := by decide

theorem polygonMap_left (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (m : Nat) :
    polygonMap w T s hT m (leftTime T hT) = embedPosition s.1 := by
  exact PolygonValues.polygonMap_left T hT m (vertices w T s m)

end NewtonLimitDynamics.Polygon.HarmonicPolygonCurve
