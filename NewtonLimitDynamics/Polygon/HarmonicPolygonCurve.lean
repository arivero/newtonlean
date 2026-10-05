import NewtonLimitDynamics.Polygon.PositionValues
import BarrowLib.Polygon.AffineBoundary

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
  have hr := Fraction.mul_le_mul_nonnegative_left hv (duration T m) hT
  have he := AffineValues.edge_vertex_bound b T hT
    (prefixState b w T s m).1 (prefixState b w T s m).2 m
  apply within_mono _ _ _ _ hr
  exact positionValue_within _ _ _ he

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
  have hp : prefixState b w T s m = prefixState c w T s m := by
    simp only [prefixState, hcell]
  have hb : timeApprox b T m = timeApprox c T m := by
    simp only [timeApprox, hcell]
  unfold polygonPosition polygonName
  rw [hp]
  exact congrArg asPosition (Quotient.sound
    (AffineValues.edgeName_same_start b c T hT
      (prefixState c w T s m).1 (prefixState c w T s m).2 m hb htime))

theorem polygon_adjacent_address_independent (b c : Nat → Bool)
    (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num) (m : Nat)
    (hcell : ticks b m + 1 = ticks c m)
    (htime : AddressEquiv T hT b c) :
    polygonPosition b w T s hT m = polygonPosition c w T s hT m := by
  have hb : Fraction.equiv (timeApprox c T m)
      (Fraction.add (timeApprox b T m) (duration T m)) := by
    have hk := congrArg (fun n : Nat => (n:Int)) hcell
    simp only [Int.natCast_add, Int.natCast_one] at hk
    simpa only [hk, timeApprox] using Fraction.equiv_symm (coarse_upper b T m)
  have hp : prefixState c w T s m =
      CentralSchedule.cell (HarmonicStability.linearField w) (duration T m)
        (prefixState b w T s m) := by
    simp only [prefixState, ← hcell]
    exact schedule_replicate_step w (duration T m) s (ticks b m)
  have hx : pointEquiv (prefixState c w T s m).1
      (pointAdd (prefixState b w T s m).1
        (pointScale (duration T m) (prefixState b w T s m).2)) := by
    rw [hp]
    exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  exact congrArg asPosition (Quotient.sound (AffineValues.edge_boundary_names
    b c T hT (prefixState b w T s m).1 (prefixState b w T s m).2
    (prefixState c w T s m).1 (prefixState c w T s m).2 m hb hx htime))

theorem polygon_zero_window (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num) (m : Nat) (hz : T.num = 0) :
    polygonPosition b w T s hT m =
      asPosition (embed (s.1,AffineValues.zeroPoint)) := by
  apply congrArg asPosition
  apply Quotient.sound
  apply nameEquiv_of_levelwise_stateEquiv
  intro j
  have ht : (HarmonicTimeComparison.durationDifference (timeApprox b T m)
      (timeApprox b T (m+j))).num = 0 := by
    simp only [HarmonicTimeComparison.durationDifference,
      HarmonicStability.negF, timeApprox, duration, Fraction.add,
      Fraction.mul, Fraction.ofInt, hz, Int.mul_zero, Int.zero_mul,
      Int.neg_zero, Int.zero_add]
  have hp := AffineValues.affine_zero_phase (prefixState b w T s m).1
    (prefixState b w T s m).2 _ ht
  have hs := zero_time_prefix b w T s m hz
  exact ⟨pointEquiv_trans hp.1 hs.1,hp.2⟩

theorem polygon_address_independent (b c : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num) (m : Nat)
    (htime : AddressEquiv T hT b c) :
    polygonPosition b w T s hT m = polygonPosition c w T s hT m := by
  by_cases hz : T.num = 0
  · exact (polygon_zero_window b w T s hT m hz).trans
      (polygon_zero_window c w T s hT m hz).symm
  · have hpos : 0 < T.num := by omega
    obtain hcell | hcell | hcell := address_equiv_cell_cases b c T hT hpos m htime
    · exact polygon_same_cell_address_independent b c w T s hT m hcell htime
    · exact polygon_adjacent_address_independent b c w T s hT m hcell htime
    · exact (polygon_adjacent_address_independent c b w T s hT m hcell
        (addressEquiv_symm T hT htime)).symm

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
  apply Subtype.ext
  change positionValue (realize (polygonName leftAddress w T s hT m)) =
    positionValue (embed (s.1,zeroPoint))
  apply congrArg positionValue
  apply Quotient.sound
  apply nameEquiv_of_levelwise_stateEquiv
  intro j
  have hp : prefixState leftAddress w T s m = s := all_zero_prefix w T s m
  have hz : (HarmonicTimeComparison.durationDifference (timeApprox leftAddress T m)
      (timeApprox leftAddress T (m+j))).num = 0 := by
    have h0 : ticks leftAddress m = 0 := all_zero_ticks m
    have h1 : ticks leftAddress (m+j) = 0 := all_zero_ticks (m+j)
    simp [timeApprox,h0,h1,HarmonicTimeComparison.durationDifference,HarmonicStability.negF,
      Fraction.add,Fraction.mul,Fraction.ofInt]
  change stateEquiv (AffineValues.affineState _ _ _) (s.1,zeroPoint)
  rw [hp]
  exact AffineValues.affine_zero_phase s.1 s.2 _ hz

end NewtonLimitDynamics.Polygon.HarmonicPolygonCurve
