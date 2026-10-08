import NewtonLimitDynamics.Historical.AreaLaw
import Lean

/-! A constant acceleration and an independently prescribed quadratic curve
exercise nonzero local remainders. This acceleration is deliberately not
central about the origin, so this control does not assert Proposition I.

Target pin, 7 October: extend the finite motion comparison to whole matched
mechanical-polygon/sample-chord edges and their actual interpolation patches.
May assume MotionSampling.Conditions only. Must derive the edge error
2*C*T*h, square radius (V+3*C*T)*h about the left curve sample, and summed
side-product budget 4*(V+3*C*T)^2*T*h with dyadic exhaustion. No centrality,
full-curve temporal continuity, chart, assigned area, union additivity,
polygon agreement or between-region B may be assumed. This is a finite
coordinate intermediary, not a proof of B for the given curve.

Preregistered controls: for the quadratic curve below at T=1/4 and j=0,
the mechanical endpoint is (0,1/4), its given sample is (1/16,1/4),
and matched midpoint edges differ by 1/32. With C=1 and V=2, the radius
is 11/16 and one-square budget is 121/64; at j=1 the total is 121/128.
Reject a zero edge-discrepancy claim for that midpoint. An inertial positive-
time curve must have zero edge discrepancy for every interpolation parameter.
Include endpoint parameters, zero time and equivalent rational representatives.
Extension, 8 October: enclose the terminal triangle and edge squares in one
finite square union. Its area controls explicitly supply the existing
TriangleContent.AreaRules; the geometric enclosure needs no area premise.
The full budgets below are bounds for assigned cover areas, and no area of
the actual sector difference or the given curve's B is assigned.
The geometric controls and formal proofs share the Lean kernel and elementary
rational definitions; exact controls do not independently certify those layers. -/
namespace NewtonLimitDynamics.Polygon.MotionSamplingControls
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates MotionSampling
open HarmonicDyadic HarmonicTimeComparison HarmonicTimeRealization

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))
private def z := Fraction.ofInt 0
private def o := Fraction.ofInt 1
private def two := Fraction.ofInt 2
private def T : Fraction := ⟨1,4,by decide⟩
private def force : Point → Point := fun _ => (two,z)
private def curve (t : Fraction) : Point × Point :=
  ((Fraction.mul t t,t),(Fraction.mul two t,o))
private def timeAt (j k : Nat) : Fraction := if k=0 then z else countTime T j k

private theorem time_equiv (j k : Nat) : Fraction.equiv (timeAt j k) (countTime T j k) := by
  by_cases h : k=0
  · subst k
    simp only [timeAt,if_pos,z,countTime,Fraction.equiv,Fraction.mul,Fraction.ofInt,
      Int.natCast_zero,Int.zero_mul,Int.mul_zero]
  · simp only [timeAt,if_neg h]; exact Fraction.equiv_refl _
private theorem time_next (j k : Nat) :
    Fraction.equiv (timeAt j (k+1)) (Fraction.add (timeAt j k) (duration T j)) := by
  apply Fraction.equiv_trans (time_equiv j (k+1))
  apply Fraction.equiv_trans (b := Fraction.add (countTime T j k) (duration T j))
  · simp only [countTime,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  · exact Fraction.add_equiv_right _ (Fraction.equiv_symm (time_equiv j k))
private theorem curve_congr {s t : Fraction} (h : Fraction.equiv s t) : stateEquiv (curve s) (curve t) :=
  ⟨⟨Fraction.mul_equiv h h,h⟩,⟨Fraction.mul_equiv_left two h,Fraction.equiv_refl _⟩⟩

private theorem polynomial_residual (t h : Fraction) (hh : 0 ≤ h.num) :
    Fraction.equiv (stateDistance (curve (Fraction.add t h)) (cell force h (curve t))) (Fraction.mul h h) := by
  have he : stateEquiv
      (HarmonicComparison.stateSub (curve (Fraction.add t h)) (cell force h (curve t)))
      ((Fraction.mul h h,z),(z,z)) := by
    constructor <;> constructor <;>
      simp only [HarmonicComparison.stateSub,curve,force,cell,pointSub,pointAdd,pointScale,pointNeg,
        z,o,two,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one,Int.zero_mul,Int.mul_zero] <;>
      ac_nf <;> (try simp only [← Int.mul_assoc]) <;> omega
  apply Fraction.equiv_trans (stateNorm_equiv he)
  apply Fraction.equiv_trans (b := (Fraction.mul h h).abs)
  · simp only [stateNorm,pointNorm,z,Fraction.equiv,Fraction.abs,Fraction.add,Fraction.ofInt,
      Int.zero_mul,Int.mul_zero,Int.add_zero,Int.zero_add,Int.one_mul,Int.mul_one,
      Int.natAbs_zero,Int.natCast_zero]
  · exact Fraction.abs_of_nonnegative _ (Fraction.nonnegative_mul _ _ hh hh)

private theorem times_bounds (j k : Nat) (hk : k ≤ blocks j) :
    0 ≤ (timeAt j k).num ∧ Fraction.le (timeAt j k) T := by
  have ht : Fraction.le (countTime T j k) T :=
    Fraction.le_equiv_right (BoundedIteration.time_monotone (duration T j) (by change (0 : Int) ≤ 1; decide)
      k (blocks j) hk) (blocks_duration T j)
  constructor
  · exact Fraction.nonnegative_equiv (time_equiv j k)
      (Fraction.nonnegative_mul _ _ (Int.ofNat_nonneg _) (by change (0 : Int) ≤ 1; decide))
  · exact Fraction.le_equiv_left (time_equiv j k) ht
private theorem curve_norms (t : Fraction) (ht : 0 ≤ t.num) :
    Fraction.equiv (pointNorm (curve t).1) (Fraction.add (Fraction.mul t t) t) ∧
    Fraction.equiv (pointNorm (curve t).2) (Fraction.add (Fraction.mul two t) o) :=
  ⟨Fraction.add_equiv (Fraction.abs_of_nonnegative _ (Fraction.nonnegative_mul _ _ ht ht))
      (Fraction.abs_of_nonnegative _ ht),
    Fraction.add_equiv (Fraction.abs_of_nonnegative _ (Fraction.nonnegative_mul _ _ (by decide) ht))
      (Fraction.abs_of_nonnegative _ (by change (0 : Int) ≤ 1; decide))⟩

private theorem conditions : Conditions force o T z two o two curve := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,?_,?_,by decide,?_,?_,?_⟩
  · intro p r
    exact Fraction.le_of_equiv (Fraction.equiv_trans (pointDistance_self_zero (force p))
      (Fraction.equiv_symm (Fraction.equiv_trans (Fraction.mul_comm _ _) (Fraction.mul_zero _))))
  · intro j k _
    have hc := curve_congr (time_next j k)
    have he : Fraction.equiv (stateDistance (curve (timeAt j (k+1)))
        (cell force (duration T j) (curve (timeAt j k))))
        (stateDistance (curve (Fraction.add (timeAt j k) (duration T j)))
          (cell force (duration T j) (curve (timeAt j k)))) := Fraction.add_equiv
      (pointDistance_equiv hc.1 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (pointDistance_equiv hc.2 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
    apply Fraction.le_of_equiv (Fraction.equiv_trans he (Fraction.equiv_trans
      (polynomial_residual (timeAt j k) (duration T j) (by change (0 : Int) ≤ 1; decide)) ?_))
    simp only [remainder,o,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]
  · intro j k _
    change (2 : Int) ≤ 2
    decide
  · intro j k hk
    have ht := times_bounds j k (by omega)
    have hs := Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative ht.2 (timeAt j k) ht.1)
      (Fraction.mul_le_mul_nonnegative_left ht.2 T (by decide))
    exact Fraction.le_equiv_left (curve_norms _ ht.1).1
      (Fraction.magnitudes.le_trans (Fraction.add_le_add hs ht.2) (by change Fraction.le (Fraction.add (Fraction.mul T T) T) o; decide))
  · intro j k hk
    have ht := times_bounds j k (by omega)
    exact Fraction.le_equiv_left (curve_norms _ ht.1).2
      (Fraction.magnitudes.le_trans (Fraction.add_le_add_right
        (Fraction.mul_le_mul_nonnegative_left ht.2 two (by decide)) o) (by change Fraction.le (Fraction.add (Fraction.mul two T) o) two; decide))

example : ∀ eps, 0 < eps.num → ∃ N, ∀ j, N ≤ j → ∀ k, k ≤ blocks j →
    Fraction.lt (stateDistance (BoundedIteration.run force (duration T j) (curve z) k)
      (samples curve T j k)) eps :=
  sampled_agreement force o T z two o two curve conditions
example : Fraction.equiv (stateBudget o T 0) ⟨1,8,by decide⟩ := by decide

-- Exact data for the first matched cell. The independent quadratic sample
-- leaves the mechanical endpoint in the x direction by one sixteenth.
private def midpoint : Fraction := ⟨1,2,by decide⟩
private def midpointEquivalent : Fraction := ⟨2,4,by decide⟩
private theorem midpoint_interval : ConvexCover.UnitInterval midpoint := ⟨by decide,by decide⟩
private theorem midpointEquivalent_interval : ConvexCover.UnitInterval midpointEquivalent :=
  ⟨by decide,by decide⟩
private theorem zero_interval : ConvexCover.UnitInterval z := ⟨by decide,by decide⟩
private theorem one_interval : ConvexCover.UnitInterval o := ⟨by decide,by decide⟩
private def mechanical (j k : Nat) : Point :=
  (BoundedIteration.run force (duration T j) (curve z) k).1
private def sampled (j k : Nat) : Point := (samples curve T j k).1

example : pointEquiv (mechanical 0 1) (z,T) := by decide
example : pointEquiv (sampled 0 1) (⟨1,16,by decide⟩,T) := by decide
example : Fraction.equiv (pointDistance
    (ConvexCover.lerp midpoint (mechanical 0 0) (mechanical 0 1))
    (ConvexCover.lerp midpoint (sampled 0 0) (sampled 0 1)))
    ⟨1,32,by decide⟩ := by decide
example : ¬ Fraction.equiv (pointDistance
    (ConvexCover.lerp midpoint (mechanical 0 0) (mechanical 0 1))
    (ConvexCover.lerp midpoint (sampled 0 0) (sampled 0 1))) z := by decide
example : Fraction.equiv (pointDistance
    (ConvexCover.lerp midpointEquivalent (mechanical 0 0) (mechanical 0 1))
    (ConvexCover.lerp midpointEquivalent (sampled 0 0) (sampled 0 1)))
    ⟨1,32,by decide⟩ := by decide
example : Fraction.equiv (pointDistance
    (ConvexCover.lerp z (mechanical 0 0) (mechanical 0 1))
    (ConvexCover.lerp z (sampled 0 0) (sampled 0 1))) z := by decide
example : Fraction.equiv (pointDistance
    (ConvexCover.lerp o (mechanical 0 0) (mechanical 0 1))
    (ConvexCover.lerp o (sampled 0 0) (sampled 0 1)))
    ⟨1,16,by decide⟩ := by decide

-- At zero total time, even the noninitial endpoint is a zero displacement.
example : Fraction.equiv (pointDistance
    (BoundedIteration.run force (duration z 0) (curve z) 1).1
    (samples curve z 0 1).1) z := by decide
example : ConvexCover.SquareContains (samples curve z 0 0).1 z
    (ConvexCover.matchedPatch midpoint midpoint
      (BoundedIteration.run force (duration z 0) (curve z) 0).1
      (BoundedIteration.run force (duration z 0) (curve z) 1).1
      (samples curve z 0 0).1 (samples curve z 0 1).1) := by
  unfold ConvexCover.SquareContains
  constructor <;> decide

-- The proposed square accounts for every matched patch, with one square per
-- dyadic cell. These values exercise the definitions without using their
-- general bounds.
example : Fraction.equiv (chordRadiusCoefficient o T two) ⟨11,4,by decide⟩ := by decide
example : Fraction.equiv (chordRadius o T two 0) ⟨11,16,by decide⟩ := by decide
example : Fraction.equiv (chordRadius o T two 1) ⟨11,32,by decide⟩ := by decide
example : Fraction.equiv (chordSquareBudget o T two 0) ⟨121,64,by decide⟩ := by decide
example : Fraction.equiv (chordSquareBudget o T two 1) ⟨121,256,by decide⟩ := by decide
example : Fraction.equiv (chordCoverBudget o T two 0) ⟨121,64,by decide⟩ := by decide
example : Fraction.equiv (chordCoverBudget o T two 1) ⟨121,128,by decide⟩ := by decide

-- The public bounds apply at both parameter endpoints, at equivalent
-- representatives of the midpoint, and at the final cell of a refinement.
private theorem edge_control (j k : Nat) (hk : k < blocks j)
    (theta : Fraction) (htheta : ConvexCover.UnitInterval theta) :
    Fraction.le (pointDistance
      (ConvexCover.lerp theta (mechanical j k) (mechanical j (k+1)))
      (ConvexCover.lerp theta (sampled j k) (sampled j (k+1))))
      (stateBudget o T j) :=
  sampled_chord_edge_bound force o T z two o two curve conditions j k hk theta htheta

example : Fraction.le (pointDistance
    (ConvexCover.lerp midpoint (mechanical 0 0) (mechanical 0 1))
    (ConvexCover.lerp midpoint (sampled 0 0) (sampled 0 1)))
    (stateBudget o T 0) := edge_control 0 0 (by decide) midpoint midpoint_interval
example : Fraction.le (pointDistance
    (ConvexCover.lerp midpointEquivalent (mechanical 0 0) (mechanical 0 1))
    (ConvexCover.lerp midpointEquivalent (sampled 0 0) (sampled 0 1)))
    (stateBudget o T 0) := edge_control 0 0 (by decide) midpointEquivalent midpointEquivalent_interval
example : Fraction.le (pointDistance
    (ConvexCover.lerp z (mechanical 0 0) (mechanical 0 1))
    (ConvexCover.lerp z (sampled 0 0) (sampled 0 1)))
    (stateBudget o T 0) := edge_control 0 0 (by decide) z zero_interval
example : Fraction.le (pointDistance
    (ConvexCover.lerp o (mechanical 0 0) (mechanical 0 1))
    (ConvexCover.lerp o (sampled 0 0) (sampled 0 1)))
    (stateBudget o T 0) := edge_control 0 0 (by decide) o one_interval
example : Fraction.le (pointDistance
    (ConvexCover.lerp midpoint (mechanical 1 1) (mechanical 1 2))
    (ConvexCover.lerp midpoint (sampled 1 1) (sampled 1 2)))
    (stateBudget o T 1) := edge_control 1 1 (by decide) midpoint midpoint_interval

example : ConvexCover.SquareContains (sampled 0 0) (chordRadius o T two 0)
    (ConvexCover.matchedPatch midpoint midpoint
      (mechanical 0 0) (mechanical 0 1) (sampled 0 0) (sampled 0 1)) :=
  sampled_chord_patch_square force o T z two o two curve conditions 0 0
    (by decide) midpoint midpoint midpoint_interval midpoint_interval
example : ConvexCover.SquareContains (sampled 1 1) (chordRadius o T two 1)
    (ConvexCover.matchedPatch o midpointEquivalent
      (mechanical 1 1) (mechanical 1 2) (sampled 1 1) (sampled 1 2)) :=
  sampled_chord_patch_square force o T z two o two curve conditions 1 1
    (by decide) o midpointEquivalent one_interval midpointEquivalent_interval

example : Exhaustion.VanishingDifference Fraction.magnitudes (chordCoverBudget o T two) :=
  chord_cover_budgets_vanish o T two (by decide) (by decide) (by decide)

example : ConvexCover.SquareCover (sampled 0) (chordRadius o T two 0) (blocks 0)
    (ConvexCover.matchedPatch midpoint midpoint
      (mechanical 0 0) (mechanical 0 1) (sampled 0 0) (sampled 0 1)) := by
  apply sampled_chord_cover force o T z two o two curve conditions 0
  exact ⟨0,by decide,midpoint,midpoint,midpoint_interval,midpoint_interval,
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

-- A positive-time inertial cell agrees at both endpoints, hence at every
-- common interpolation parameter. This uses no new sampling conditions.
private def inertialForce : Point → Point := fun _ => (z,z)
private def inertialCurve (t : Fraction) : Point × Point := ((t,z),(o,z))
private def inertialMechanical (k : Nat) : Point :=
  (BoundedIteration.run inertialForce (duration T 0) (inertialCurve z) k).1
private def inertialSampled (k : Nat) : Point := (samples inertialCurve T 0 k).1

-- A displaced terminal radial edge has actual nonzero unsigned triangle
-- area. Values are direct rational computations, independent of the bounds'
-- proof path, but share the kernel and coordinate definitions with it.
example : Fraction.equiv (terminalConnectorArea force T curve 0) ⟨1,128,by decide⟩ := by decide
example : Fraction.equiv (terminalConnectorArea force T curve 1) ⟨1,256,by decide⟩ := by decide
example : ¬ Fraction.equiv (terminalConnectorArea force T curve 0) z := by decide
example : Fraction.equiv (terminalConnectorArea inertialForce T inertialCurve 0) z := by decide
example : Fraction.equiv (terminalConnectorArea force z curve 0) z := by decide
example (area : SectorFan.AreaRules) :
    area.HasArea (terminalConnector force T curve 0) ⟨1,128,by decide⟩ :=
  area.congr_value _ _ _ (by decide) (terminal_connector_area area force T curve 0)
example : Fraction.le (terminalConnectorArea force T curve 0)
    (Fraction.mul (BoundedIteration.uniformPositionCap T (curve z) two) (stateBudget o T 0)) :=
  terminal_connector_bound force o T z two o two curve conditions 0
example : Exhaustion.VanishingDifference Fraction.magnitudes (terminalConnectorArea force T curve) :=
  terminal_connector_areas_vanish force o T z two o two curve conditions

-- The new full square cover includes the terminal triangle and has an
-- assigned union area bounded by a shrinking budget. The independent curve
-- here remains noncentral, and no sector-difference area is assigned.
example : Fraction.equiv (MotionSectorCover.coefficient o T two two (curve z))
    ⟨19,16,by decide⟩ := by decide
example : Fraction.equiv (MotionSectorCover.radius o T two two (curve z) 1)
    ⟨19,32,by decide⟩ := by decide
example : Fraction.equiv (MotionSectorCover.budget o T two two (curve z) 0)
    ⟨361,32,by decide⟩ := by decide
example : Fraction.equiv (MotionSectorCover.budget o T two two (curve z) 1)
    ⟨361,64,by decide⟩ := by decide
example (j : Nat) (x : Point) (hx : terminalConnector force T curve j x) :
    MotionSectorCover.cover force o T two two curve j x :=
  MotionSectorCover.terminal_cover_inside force o T z two o two curve conditions j x hx
example (j : Nat) (x : Point)
    (hx : ConvexCover.SquareCover (sampled j) (chordRadius o T two j) (blocks j) x) :
    MotionSectorCover.cover force o T two two curve j x :=
  MotionSectorCover.edge_cover_inside force o T two two curve j
    (by decide) (by decide) (by decide) x hx
example (area : TriangleContent.AreaRules) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (MotionSectorCover.cover force o T two two curve j) (A j) ∧
        0 ≤ (A j).num ∧ Fraction.le (A j) (MotionSectorCover.budget o T two two (curve z) j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A :=
  MotionSectorCover.cover_areas area force o T two two curve
    (by decide) (by decide) (by decide) (by decide)

-- Distinct edge parameters and the terminal cell of a refinement.
example : ConvexCover.SquareContains (sampled 1 1) (chordRadius o T two 1)
    (ConvexCover.filledPatch z o midpointEquivalent
      (mechanical 1 1) (mechanical 1 2) (sampled 1 1) (sampled 1 2)) :=
  sampled_filled_patch_square force o T z two o two curve conditions 1 1
    (by decide) z o midpointEquivalent zero_interval one_interval midpointEquivalent_interval
example : ConvexCover.SquareCover (sampled 1) (chordRadius o T two 1) (blocks 1)
    (ConvexCover.filledPatch z o midpointEquivalent
      (mechanical 1 1) (mechanical 1 2) (sampled 1 1) (sampled 1 2)) := by
  apply sampled_filled_cover force o T z two o two curve conditions 1
  exact ⟨1,by decide,z,o,midpointEquivalent,zero_interval,one_interval,midpointEquivalent_interval,
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

private theorem inertial_edge_zero (theta : Fraction) (htheta : ConvexCover.UnitInterval theta) :
    Fraction.equiv (pointDistance
      (ConvexCover.lerp theta (inertialMechanical 0) (inertialMechanical 1))
      (ConvexCover.lerp theta (inertialSampled 0) (inertialSampled 1))) z := by
  have h0 : Fraction.le (pointDistance (inertialMechanical 0) (inertialSampled 0)) z := by decide
  have h1 : Fraction.le (pointDistance (inertialMechanical 1) (inertialSampled 1)) z := by decide
  have hu := ConvexCover.lerp_difference_bound theta htheta
    (inertialMechanical 0) (inertialMechanical 1)
    (inertialSampled 0) (inertialSampled 1) z h0 h1
  apply (Fraction.equiv_iff_mutual_le _ _).mpr
  refine ⟨hu,?_⟩
  simpa only [Fraction.le,z,Fraction.ofInt,Int.zero_mul,Int.mul_one,pointDistance] using
    (pointNorm_nonnegative (pointSub
      (ConvexCover.lerp theta (inertialMechanical 0) (inertialMechanical 1))
      (ConvexCover.lerp theta (inertialSampled 0) (inertialSampled 1))))

-- Exercise each edition's canonical polygon client, retaining its own
-- polygonVertex rather than substituting BoundedIteration.run in the tests.
private def deMotuPolygon (j k : Nat) : Point :=
  DeMotu1684.NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd force
    (duration T j) (curve z) k
private def p1687Polygon (j k : Nat) : Point :=
  Principia1687.PropositionI.polygonVertex ZeroForce.inertialAt pointAdd force
    (duration T j) (curve z) k
private def p1713Polygon (j k : Nat) : Point :=
  Principia1713.PropositionI.polygonVertex ZeroForce.inertialAt pointAdd force
    (duration T j) (curve z) k

private def WitnessControl (polygon : Nat → Nat → Point) : Prop :=
  (∀ j k, k < blocks j → ∀ theta, ConvexCover.UnitInterval theta →
    Fraction.le (pointDistance
      (ConvexCover.lerp theta (polygon j k) (polygon j (k+1)))
      (ConvexCover.lerp theta (sampled j k) (sampled j (k+1))))
      (stateBudget o T j)) ∧
  (∀ j x, ConvexCover.MatchedRegion (polygon j) (sampled j) (blocks j) x →
    ConvexCover.SquareCover (sampled j) (chordRadius o T two j) (blocks j) x)

private theorem deMotu_witness_control : WitnessControl deMotuPolygon := by
  have hc := DeMotu1684.NATP00090.AreaLaw.mechanical_sampled_chord_control
    force o T z two o two curve conditions
  exact ⟨hc.1,hc.2.1⟩
private theorem p1687_witness_control : WitnessControl p1687Polygon := by
  have hc := Principia1687.PropositionI.mechanical_sampled_chord_control
    force o T z two o two curve conditions
  exact ⟨hc.1,hc.2.1⟩
private theorem p1713_witness_control : WitnessControl p1713Polygon := by
  have hc := Principia1713.PropositionI.mechanical_sampled_chord_control
    force o T z two o two curve conditions
  exact ⟨hc.1,hc.2.1⟩

private theorem witness_midpoint_check (polygon : Nat → Nat → Point)
    (hc : WitnessControl polygon) :
    Fraction.le (pointDistance
      (ConvexCover.lerp midpoint (polygon 0 0) (polygon 0 1))
      (ConvexCover.lerp midpoint (sampled 0 0) (sampled 0 1)))
      (stateBudget o T 0) ∧
    ConvexCover.SquareCover (sampled 0) (chordRadius o T two 0) (blocks 0)
      (ConvexCover.matchedPatch midpoint midpoint
        (polygon 0 0) (polygon 0 1) (sampled 0 0) (sampled 0 1)) := by
  constructor
  · exact hc.1 0 0 (by decide) midpoint midpoint_interval
  · apply hc.2 0
    exact ⟨0,by decide,midpoint,midpoint,midpoint_interval,midpoint_interval,
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

example : Fraction.le (pointDistance
    (ConvexCover.lerp midpoint (deMotuPolygon 0 0) (deMotuPolygon 0 1))
    (ConvexCover.lerp midpoint (sampled 0 0) (sampled 0 1))) (stateBudget o T 0) ∧
    ConvexCover.SquareCover (sampled 0) (chordRadius o T two 0) (blocks 0)
      (ConvexCover.matchedPatch midpoint midpoint
        (deMotuPolygon 0 0) (deMotuPolygon 0 1) (sampled 0 0) (sampled 0 1)) :=
  witness_midpoint_check deMotuPolygon deMotu_witness_control
example : Fraction.le (pointDistance
    (ConvexCover.lerp midpoint (p1687Polygon 0 0) (p1687Polygon 0 1))
    (ConvexCover.lerp midpoint (sampled 0 0) (sampled 0 1))) (stateBudget o T 0) ∧
    ConvexCover.SquareCover (sampled 0) (chordRadius o T two 0) (blocks 0)
      (ConvexCover.matchedPatch midpoint midpoint
        (p1687Polygon 0 0) (p1687Polygon 0 1) (sampled 0 0) (sampled 0 1)) :=
  witness_midpoint_check p1687Polygon p1687_witness_control
example : Fraction.le (pointDistance
    (ConvexCover.lerp midpoint (p1713Polygon 0 0) (p1713Polygon 0 1))
    (ConvexCover.lerp midpoint (sampled 0 0) (sampled 0 1))) (stateBudget o T 0) ∧
    ConvexCover.SquareCover (sampled 0) (chordRadius o T two 0) (blocks 0)
      (ConvexCover.matchedPatch midpoint midpoint
        (p1713Polygon 0 0) (p1713Polygon 0 1) (sampled 0 0) (sampled 0 1)) :=
  witness_midpoint_check p1713Polygon p1713_witness_control
example : ¬ CentralSchedule.central force := by
  intro h
  have he := h (o,o)
  have hn : ¬ Fraction.equiv (TimeSubdivision.det (o,o) (force (o,o))) z := by decide
  exact hn he

#print axioms MotionSampling.sampled_agreement
#print axioms MotionSampling.sampled_fan_comparison
#print axioms MotionSampling.sampled_radial_mesh
#print axioms MotionSampling.sampled_chord_edge_bound
#print axioms MotionSampling.sampled_chord_patch_square
#print axioms MotionSampling.sampled_chord_cover
#print axioms MotionSampling.chord_cover_budgets_vanish
#print axioms DeMotu1684.NATP00090.AreaLaw.mechanical_sampled_chord_control
#print axioms Principia1687.PropositionI.mechanical_sampled_chord_control
#print axioms Principia1713.PropositionI.mechanical_sampled_chord_control
end NewtonLimitDynamics.Polygon.MotionSamplingControls

/- Inspect compiled transitive uses, including types, definitions and private
helpers. Imports by themselves do not mark a witness-local proof as modern. -/
namespace NewtonLimitDynamics.Polygon.MotionSamplingWitnessDependencyControls
open Lean

private partial def dependencyClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then dependencyClosure env rest seen
    else
      let seen := seen.insert name
      match env.find? name with
      | none => dependencyClosure env rest seen
      | some info =>
        let uses := info.type.getUsedConstants ++
          ((info.value? true).map Expr.getUsedConstants |>.getD #[])
        dependencyClosure env (uses.toList ++ rest) seen

private def matchingPrefix? (seen : NameSet) (blockedPrefix : String) : Option Name :=
  seen.toList.find? fun name =>
    let publicName := ((privateToUserName? name).getD name).toString
    publicName.startsWith blockedPrefix

run_elab do
  let env ← Lean.getEnv
  let checks : Array (Name × Name × Array String) := #[
    (`DeMotu1684.NATP00090.AreaLaw.mechanical_sampled_chord_control,
      `DeMotu1684.NATP00090.AreaLaw.canonical_polygon_eq_run,
      #["DeMotu1684.AreaLaw.", "DeMotu1684.NATP00089.", "Principia1687.", "Principia1713."]),
    (`Principia1687.PropositionI.mechanical_sampled_chord_control,
      `Principia1687.PropositionI.canonical_polygon_eq_run,
      #["DeMotu1684.", "Principia1713.", "ModernLib."]),
    (`Principia1713.PropositionI.mechanical_sampled_chord_control,
      `Principia1713.PropositionI.canonical_polygon_eq_run,
      #["DeMotu1684.", "Principia1687.", "ModernLib."]),
    (`DeMotu1684.NATP00090.AreaLaw.mechanical_filled_chord_control,
      `DeMotu1684.NATP00090.AreaLaw.canonical_polygon_eq_run,
      #["DeMotu1684.AreaLaw.", "DeMotu1684.NATP00089.", "Principia1687.", "Principia1713."]),
    (`DeMotu1684.NATP00090.AreaLaw.eventual_mechanical_sector_area,
      `DeMotu1684.NATP00090.AreaLaw.canonical_polygon_eq_run,
      #["DeMotu1684.AreaLaw.", "DeMotu1684.NATP00089.", "Principia1687.", "Principia1713."]),
    (`Principia1687.PropositionI.mechanical_filled_chord_control,
      `Principia1687.PropositionI.canonical_polygon_eq_run,
      #["DeMotu1684.", "Principia1713.", "ModernLib."]),
    (`Principia1687.PropositionI.eventual_mechanical_sector_area,
      `Principia1687.PropositionI.canonical_polygon_eq_run,
      #["DeMotu1684.", "Principia1713.", "ModernLib."]),
    (`Principia1713.PropositionI.mechanical_filled_chord_control,
      `Principia1713.PropositionI.canonical_polygon_eq_run,
      #["DeMotu1684.", "Principia1687.", "ModernLib."]),
    (`Principia1713.PropositionI.eventual_mechanical_sector_area,
      `Principia1713.PropositionI.canonical_polygon_eq_run,
      #["DeMotu1684.", "Principia1687.", "ModernLib."]),
    (`DeMotu1684.NATP00090.AreaLaw.eventual_mechanical_sector_difference_cover,
      `DeMotu1684.NATP00090.AreaLaw.canonical_polygon_eq_run,
      #["DeMotu1684.AreaLaw.", "DeMotu1684.NATP00089.", "Principia1687.", "Principia1713."]),
    (`Principia1687.PropositionI.eventual_mechanical_sector_difference_cover,
      `Principia1687.PropositionI.canonical_polygon_eq_run,
      #["DeMotu1684.", "Principia1713.", "ModernLib."]),
    (`Principia1713.PropositionI.eventual_mechanical_sector_difference_cover,
      `Principia1713.PropositionI.canonical_polygon_eq_run,
      #["DeMotu1684.", "Principia1687.", "ModernLib."]),
    (`DeMotu1684.NATP00090.AreaLaw.eventual_mechanical_sector_difference_cover_areas,
      `DeMotu1684.NATP00090.AreaLaw.canonical_polygon_eq_run,
      #["DeMotu1684.AreaLaw.", "DeMotu1684.NATP00089.", "Principia1687.", "Principia1713."]),
    (`Principia1687.PropositionI.eventual_mechanical_sector_difference_cover_areas,
      `Principia1687.PropositionI.canonical_polygon_eq_run,
      #["DeMotu1684.", "Principia1713.", "ModernLib."]),
    (`Principia1713.PropositionI.eventual_mechanical_sector_difference_cover_areas,
      `Principia1713.PropositionI.canonical_polygon_eq_run,
      #["DeMotu1684.", "Principia1687.", "ModernLib."])]
  for (root, ownPolygon, blocked) in checks do
    unless (env.find? root).isSome do
      throwError "missing compiled witness client {root}"
    let used := dependencyClosure env [root]
    unless used.contains ownPolygon do
      throwError "{root} does not use its own canonical polygon equality"
    if root.toString.endsWith ".eventual_mechanical_sector_area" then
      let ownFiniteArea := root.getPrefix ++ `finite_geometric_sector
      unless used.contains ownFiniteArea do
        throwError "{root} does not use its own finite geometric sector proof"
    if root.toString.endsWith ".eventual_mechanical_sector_difference_cover" ||
        root.toString.endsWith ".eventual_mechanical_sector_difference_cover_areas" then
      let ownTriangle := root.getPrefix ++ `polygon_triangle_equal
      unless used.contains ownTriangle do
        throwError "{root} does not derive orientation from its own triangle chain"
      unless used.contains `NewtonLimitDynamics.Polygon.FanDifference.symmetric_difference_cover do
        throwError "{root} does not use the derived geometric difference inclusion"
    if root.toString.endsWith ".eventual_mechanical_sector_difference_cover_areas" then
      unless used.contains (root.getPrefix ++ `eventual_mechanical_sector_difference_cover) do
        throwError "{root} does not use its own sector-difference cover"
      unless used.contains `NewtonLimitDynamics.Polygon.BoxCoverArea.cover_area do
        throwError "{root} does not construct its square-union area"
      unless used.contains `NewtonLimitDynamics.Polygon.RadialTriangleCover.terminal_triangle_square_cover do
        throwError "{root} does not geometrically cover its terminal triangle"
    for blockedPrefix in blocked do
      if let some offender := matchingPrefix? used blockedPrefix then
        throwError "{root} reaches forbidden dependency {offender}"
    for usedName in used.toList do
      if let some idx := env.getModuleIdxFor? usedName then
        let owner := env.header.moduleNames[idx]!
        if owner.toString == "ModernLib" || owner.toString.startsWith "ModernLib." then
          throwError "{root} reaches modern declaration {usedName} owned by {owner}"

end NewtonLimitDynamics.Polygon.MotionSamplingWitnessDependencyControls
