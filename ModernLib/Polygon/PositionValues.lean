import ModernLib.Foundation.Polygon.PositionValues
import ModernLib.Polygon.HarmonicTimeRealization

/-!
Planar positions of the constructed harmonic state values. All magnitudes are
coordinate L1 diagnostics. Closed coordinate squares below are point sets in
this quotient plane, not state-space regions or supplied Euclidean area.
-/

namespace NewtonLimitDynamics.Polygon.PositionValues

open NewtonLimitDynamics
open TimeSubdivision
open PointBounds
open HarmonicComparison
open HarmonicAccumulation
open HarmonicDyadic
open HarmonicBinaryPrefix
open HarmonicTimeRealization
open BinaryTime
open CauchyValues

def gammaPosition (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (t : BinaryTime T hT) : PositionValue :=
  asPosition (gammaValue w T s hT hs t)

-- Modern dependency score: 149/254 (M=149, H=105; transitive project theorems/axioms).
theorem gammaPosition_within (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (x y : BinaryTime T hT) (R : Fraction)
    (hR : 0 ≤ R.num) (hxy : TimeWithin T hT x y R) :
    Within (gammaPosition w T s hT hs x).val
      (gammaPosition w T s hT hs y).val
      (Fraction.mul R (stateTimeFactor w s)) :=
  positionValue_within _ _ _
    (gamma_within w T s hT hs x y R hR hxy)

-- Modern dependency score: 153/258 (M=153, H=105; transitive project theorems/axioms).
theorem gammaPosition_uniform_continuity (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (eps : Fraction)
    (heps : 0 < eps.num) (x y : BinaryTime T hT)
    (hxy : TimeWithin T hT x y (timeTolerance w s eps)) :
    Within (gammaPosition w T s hT hs x).val
      (gammaPosition w T s hT hs y).val eps.half :=
  positionValue_within _ _ _
    (gamma_uniform_continuity w T s hT hs eps heps x y hxy)

-- Modern dependency score: 140/242 (M=140, H=102; transitive project theorems/axioms).
theorem gammaPosition_alias (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    gammaPosition w T s hT hs (Quotient.mk _ firstAlias) =
      gammaPosition w T s hT hs (Quotient.mk _ secondAlias) := by
  exact congrArg (gammaPosition w T s hT hs) (alias_time_eq T hT)

-- Modern dependency score: 140/242 (M=140, H=102; transitive project theorems/axioms).
theorem gammaPosition_left (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    gammaPosition w T s hT hs (leftTime T hT) = embedPosition s.1 := by
  apply Subtype.ext
  change positionValue (gammaValue w T s hT hs (leftTime T hT)) =
    positionValue (embed (s.1, zeroPoint))
  rw [left_endpoint_value w T s hT hs, positionValue_embed]
  rfl

-- Modern dependency score: 148/250 (M=148, H=102; transitive project theorems/axioms).
theorem gammaPosition_right (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    gammaPosition w T s hT hs (rightTime T hT) =
      asPosition (endpointValue w T s hT hs) := by
  exact congrArg asPosition (right_endpoint_value w T s hT hs)

-- Modern dependency score: 148/249 (M=148, H=101; transitive project theorems/axioms).
theorem gammaPosition_zero_time (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (hzero : T.num = 0) :
    gammaPosition w T s hT hs (Quotient.mk _ b) =
      embedPosition s.1 := by
  apply Subtype.ext
  change positionValue (gammaValue w T s hT hs (Quotient.mk _ b)) =
    positionValue (embed (s.1, zeroPoint))
  rw [zero_time_value b w T s hT hs hzero, positionValue_embed]
  rfl

-- Modern dependency score: 141/243 (M=141, H=102; transitive project theorems/axioms).
theorem gammaPosition_zero_state_norm (b : Nat → Bool)
    (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (hzero : (stateNorm s).num = 0) :
    gammaPosition w T s hT hs (Quotient.mk _ b) =
      embedPosition s.1 := by
  apply Subtype.ext
  change positionValue (gammaValue w T s hT hs (Quotient.mk _ b)) =
    positionValue (embed (s.1, zeroPoint))
  rw [zero_state_norm_value b w T s hT hs hzero, positionValue_embed]
  rfl

private def sampleOne : Fraction := ⟨1, 1, by decide⟩
private def sampleZero : Fraction := ⟨0, 1, by decide⟩
private def sampleCentre : Point := (sampleZero, sampleZero)
private def sampleCorner : Point := (sampleOne, sampleOne)
private def sampleRadius : NonnegativeRadius := ⟨sampleOne, by decide⟩

-- Modern dependency score: 31/71 (M=31, H=40; transitive project theorems/axioms).
theorem sample_corner_in_square :
    CoordinateSquare sampleCentre sampleRadius
      (embedPosition sampleCorner) := by
  apply square_of_rational_coordinate_bounds
  · unfold Fraction.le
    decide
  · unfold Fraction.le
    decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_corner_L1_distance_two :
    Fraction.equiv (pointNorm (pointSub sampleCorner sampleCentre))
      (Fraction.ofInt 2) := by decide

private def sampleQuarter : Fraction := ⟨1, 4, by decide⟩
private def sampleState : Point × Point :=
  ((sampleOne, sampleZero), (sampleZero, sampleOne))
private def sampleTail : Fraction := ⟨3, 16, by decide⟩
private def sampleLower : Fraction := ⟨39, 512, by decide⟩

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_position_level_one :
    Fraction.equiv
      (distance (positionState (endpoint sampleOne sampleQuarter sampleState 1))
        (positionState sampleState))
      ⟨135, 512, by decide⟩ := by decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_tail_one :
    Fraction.equiv (HarmonicDyadic.tailCap
      sampleOne sampleQuarter sampleState 1) sampleTail := by decide

-- Modern dependency score: 78/162 (M=78, H=84; transitive project theorems/axioms).
theorem sample_position_lower_all_levels (j : Nat) (hj : 1 ≤ j) :
    Fraction.le sampleLower
      (distance (positionState (endpoint sampleOne sampleQuarter sampleState j))
        (positionState sampleState)) := by
  let e₁ := endpoint sampleOne sampleQuarter sampleState 1
  let eⱼ := endpoint sampleOne sampleQuarter sampleState j
  have hs : DyadicSmallTime sampleOne sampleQuarter := by
    unfold DyadicSmallTime Fraction.le
    decide
  have hj' : 1 + (j - 1) = j := by omega
  have hgap := HarmonicDyadic.finite_gap_error sampleOne sampleQuarter
    sampleState (by decide) hs (j - 1) 1
  rw [hj'] at hgap
  have hgap' : Fraction.le
      (distance (positionState e₁) (positionState eⱼ))
      (HarmonicDyadic.tailCap sampleOne sampleQuarter sampleState 1) :=
    Fraction.magnitudes.le_trans (position_nonexpansive e₁ eⱼ)
      (Fraction.le_equiv_left (stateSub_norm_symm e₁ eⱼ) hgap)
  have htri := stateSub_triangle
    (positionState e₁) (positionState eⱼ) (positionState sampleState)
  have hchain := Fraction.magnitudes.le_trans htri
    (Fraction.add_le_add_right hgap'
      (distance (positionState eⱼ) (positionState sampleState)))
  have hL : Fraction.equiv (Fraction.add sampleTail sampleLower)
      (distance (positionState e₁) (positionState sampleState)) :=
    Fraction.equiv_trans (by decide)
      (Fraction.equiv_symm sample_position_level_one)
  have hR : Fraction.equiv
      (Fraction.add
        (HarmonicDyadic.tailCap sampleOne sampleQuarter sampleState 1)
        (distance (positionState eⱼ) (positionState sampleState)))
      (Fraction.add sampleTail
        (distance (positionState eⱼ) (positionState sampleState))) :=
    Fraction.add_equiv sample_tail_one (Fraction.equiv_refl _)
  have hfull := Fraction.le_equiv_right
    (Fraction.le_equiv_left hL hchain) hR
  exact le_add_cancel_left sampleTail sampleLower
    (distance (positionState eⱼ) (positionState sampleState)) hfull

-- Modern dependency score: 90/179 (M=90, H=89; transitive project theorems/axioms).
theorem sample_endpoint_position_ne_initial :
    positionValue (endpointValue sampleOne sampleQuarter sampleState
      (by decide) (by unfold DyadicSmallTime Fraction.le; decide)) ≠
    embed (positionState sampleState) := by
  intro heq
  have hnames : NameEquiv
      (mapName positionState position_nonexpansive
        (endpointName sampleOne sampleQuarter sampleState
          (by decide) (by unfold DyadicSmallTime Fraction.le; decide)))
      (constantName (positionState sampleState)) := Quotient.exact heq
  let eps : Fraction := ⟨39, 1024, by decide⟩
  have heps : 0 < eps.num := by decide
  obtain ⟨N, hN⟩ := hnames eps heps
  have hsmall : Fraction.lt
      (distance
        (positionState (endpoint sampleOne sampleQuarter sampleState (N + 1)))
        (positionState sampleState)) eps := hN (N + 1) (by omega)
  have hlower := sample_position_lower_all_levels (N + 1) (by omega)
  have hhalf : Fraction.lt eps sampleLower := by unfold Fraction.lt; decide
  have hloop := Fraction.magnitudes.lt_of_le_lt hlower hsmall
  have hloop' := Fraction.magnitudes.lt_of_lt_le hloop
    (Fraction.magnitudes.lt_implies_le hhalf)
  exact (Fraction.magnitudes.lt_irrefl sampleLower) hloop'

-- Modern dependency score: 160/264 (M=160, H=104; transitive project theorems/axioms).
theorem sample_gammaPosition_right_ne_left :
    gammaPosition sampleOne sampleQuarter sampleState
      (by decide) (by unfold DyadicSmallTime Fraction.le; decide)
      (rightTime sampleQuarter (by decide)) ≠
    gammaPosition sampleOne sampleQuarter sampleState
      (by decide) (by unfold DyadicSmallTime Fraction.le; decide)
      (leftTime sampleQuarter (by decide)) := by
  intro h
  have hneq := sample_endpoint_position_ne_initial
  apply hneq
  have hright := gammaPosition_right sampleOne sampleQuarter sampleState
    (by decide) (by unfold DyadicSmallTime Fraction.le; decide)
  have hleft := gammaPosition_left sampleOne sampleQuarter sampleState
    (by decide) (by unfold DyadicSmallTime Fraction.le; decide)
  have hsub := congrArg Subtype.val h
  rw [hright, hleft] at hsub
  exact hsub

end NewtonLimitDynamics.Polygon.PositionValues
