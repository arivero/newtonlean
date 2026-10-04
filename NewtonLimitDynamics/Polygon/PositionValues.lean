import NewtonLimitDynamics.Polygon.HarmonicTimeRealization

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

private def zero : Fraction := Fraction.ofInt 0
private def zeroPoint : Point := (zero, zero)

def positionState (s : Point × Point) : Point × Point := (s.1, zeroPoint)
def firstState (s : Point × Point) : Point × Point := ((s.1.1, zero), zeroPoint)
def secondState (s : Point × Point) : Point × Point := ((zero, s.1.2), zeroPoint)

private theorem le_add_nonnegative (a b : Fraction) (hb : 0 ≤ b.num) :
    Fraction.le a (Fraction.add a b) := by
  unfold Fraction.le Fraction.add
  dsimp
  have hp := Int.mul_nonneg (Int.mul_nonneg hb (Int.le_of_lt a.den_pos))
    (Int.le_of_lt a.den_pos)
  simp only [Int.add_mul]
  have he : a.num * (a.den * b.den) = a.num * b.den * a.den := by ac_rfl
  rw [he]
  omega

private def xGap (a b : Point × Point) : Fraction :=
  (Fraction.add a.1.1 ⟨-b.1.1.num, b.1.1.den, b.1.1.den_pos⟩).abs
private def yGap (a b : Point × Point) : Fraction :=
  (Fraction.add a.1.2 ⟨-b.1.2.num, b.1.2.den, b.1.2.den_pos⟩).abs
private def vxGap (a b : Point × Point) : Fraction :=
  (Fraction.add a.2.1 ⟨-b.2.1.num, b.2.1.den, b.2.1.den_pos⟩).abs
private def vyGap (a b : Point × Point) : Fraction :=
  (Fraction.add a.2.2 ⟨-b.2.2.num, b.2.2.den, b.2.2.den_pos⟩).abs

private theorem distance_decompose (a b : Point × Point) :
    distance a b = Fraction.add (Fraction.add (xGap a b) (yGap a b))
      (Fraction.add (vxGap a b) (vyGap a b)) := rfl

private theorem projected_distance (a b : Point × Point) :
    Fraction.equiv (distance (positionState a) (positionState b))
      (Fraction.add (xGap a b) (yGap a b)) := by
  simp only [distance, positionState, stateNorm, stateSub, pointNorm,
    pointSub, pointAdd, pointNeg, zeroPoint, zero,
    Fraction.equiv, Fraction.add, Fraction.abs, Fraction.ofInt,
    xGap, yGap]
  simp only [Int.zero_mul, Int.mul_zero, Int.add_zero,
    Int.natAbs_zero, Int.ofNat_zero, Int.neg_zero,
    Int.mul_one, Int.one_mul]

private theorem first_distance (a b : Point × Point) :
    Fraction.equiv (distance (firstState a) (firstState b)) (xGap a b) := by
  simp only [distance, firstState, stateNorm, stateSub, pointNorm,
    pointSub, pointAdd, pointNeg, zeroPoint, zero,
    Fraction.equiv, Fraction.add, Fraction.abs, Fraction.ofInt, xGap]
  simp only [Int.zero_mul, Int.mul_zero, Int.add_zero,
    Int.natAbs_zero, Int.ofNat_zero, Int.neg_zero,
    Int.mul_one, Int.one_mul]

private theorem second_distance (a b : Point × Point) :
    Fraction.equiv (distance (secondState a) (secondState b)) (yGap a b) := by
  simp only [distance, secondState, stateNorm, stateSub, pointNorm,
    pointSub, pointAdd, pointNeg, zeroPoint, zero,
    Fraction.equiv, Fraction.add, Fraction.abs, Fraction.ofInt, yGap]
  simp only [Int.zero_mul, Int.mul_zero, Int.add_zero,
    Int.natAbs_zero, Int.ofNat_zero, Int.neg_zero,
    Int.mul_one, Int.one_mul]
  ac_nf

theorem position_nonexpansive (a b : Point × Point) :
    Fraction.le (distance (positionState a) (positionState b))
      (distance a b) := by
  apply Fraction.le_equiv_left (projected_distance a b)
  rw [distance_decompose]
  exact le_add_nonnegative _ _
    (by
      unfold Fraction.add
      exact Int.add_nonneg
        (Int.mul_nonneg (Fraction.abs_num_nonnegative _)
          (Int.le_of_lt (vyGap a b).den_pos))
        (Int.mul_nonneg (Fraction.abs_num_nonnegative _)
          (Int.le_of_lt (vxGap a b).den_pos)))

theorem first_nonexpansive (a b : Point × Point) :
    Fraction.le (distance (firstState a) (firstState b))
      (distance a b) := by
  apply Fraction.le_equiv_left (first_distance a b)
  have h₁ := le_add_nonnegative (xGap a b) (yGap a b)
    (Fraction.abs_num_nonnegative _)
  have h₂ := le_add_nonnegative (Fraction.add (xGap a b) (yGap a b))
    (Fraction.add (vxGap a b) (vyGap a b)) (by
      unfold Fraction.add
      exact Int.add_nonneg
        (Int.mul_nonneg (Fraction.abs_num_nonnegative _)
          (Int.le_of_lt (vyGap a b).den_pos))
        (Int.mul_nonneg (Fraction.abs_num_nonnegative _)
          (Int.le_of_lt (vxGap a b).den_pos)))
  rw [distance_decompose]
  exact Fraction.magnitudes.le_trans h₁ h₂

theorem second_nonexpansive (a b : Point × Point) :
    Fraction.le (distance (secondState a) (secondState b))
      (distance a b) := by
  apply Fraction.le_equiv_left (second_distance a b)
  have h₁ := le_add_nonnegative (yGap a b) (xGap a b)
    (Fraction.abs_num_nonnegative _)
  have hcomm := Fraction.add_comm (yGap a b) (xGap a b)
  have h₂ := le_add_nonnegative (Fraction.add (xGap a b) (yGap a b))
    (Fraction.add (vxGap a b) (vyGap a b)) (by
      unfold Fraction.add
      exact Int.add_nonneg
        (Int.mul_nonneg (Fraction.abs_num_nonnegative _)
          (Int.le_of_lt (vyGap a b).den_pos))
        (Int.mul_nonneg (Fraction.abs_num_nonnegative _)
          (Int.le_of_lt (vxGap a b).den_pos)))
  rw [distance_decompose]
  exact Fraction.magnitudes.le_trans
    (Fraction.le_equiv_right h₁ hcomm) h₂

def mapName (f : Point × Point → Point × Point)
    (hLip : ∀ a b, Fraction.le (distance (f a) (f b)) (distance a b))
    (a : EndpointCauchyName) : EndpointCauchyName where
  approx := fun n => f (a.approx n)
  cauchy := by
    intro eps heps
    obtain ⟨N, hN⟩ := a.cauchy eps heps
    refine ⟨N, ?_⟩
    intro m n hm hn
    exact Fraction.magnitudes.lt_of_le_lt
      (hLip (a.approx m) (a.approx n)) (hN m n hm hn)

theorem mapName_equiv (f : Point × Point → Point × Point)
    (hLip : ∀ a b, Fraction.le (distance (f a) (f b)) (distance a b))
    {a b : EndpointCauchyName} (hab : NameEquiv a b) :
    NameEquiv (mapName f hLip a) (mapName f hLip b) := by
  intro eps heps
  obtain ⟨N, hN⟩ := hab eps heps
  refine ⟨N, ?_⟩
  intro n hn
  exact Fraction.magnitudes.lt_of_le_lt
    (hLip (a.approx n) (b.approx n)) (hN n hn)

def mapValue (f : Point × Point → Point × Point)
    (hLip : ∀ a b, Fraction.le (distance (f a) (f b)) (distance a b)) :
    Value → Value :=
  Quotient.lift (fun a => realize (mapName f hLip a))
    (fun _ _ h => Quotient.sound (mapName_equiv f hLip h))

theorem mapValue_embed (f : Point × Point → Point × Point)
    (hLip : ∀ a b, Fraction.le (distance (f a) (f b)) (distance a b))
    (s : Point × Point) :
    mapValue f hLip (embed s) = embed (f s) := rfl

theorem mapName_bound (f : Point × Point → Point × Point)
    (hLip : ∀ a b, Fraction.le (distance (f a) (f b)) (distance a b))
    (a b : EndpointCauchyName) (R : Fraction) (h : NameBound a b R) :
    NameBound (mapName f hLip a) (mapName f hLip b) R := by
  intro eps heps
  obtain ⟨N, hN⟩ := h eps heps
  refine ⟨N, ?_⟩
  intro n hn
  exact Fraction.magnitudes.lt_of_le_lt
    (hLip (a.approx n) (b.approx n)) (hN n hn)

theorem mapValue_within (f : Point × Point → Point × Point)
    (hLip : ∀ a b, Fraction.le (distance (f a) (f b)) (distance a b))
    (x y : Value) (R : Fraction) (h : Within x y R) :
    Within (mapValue f hLip x) (mapValue f hLip y) R := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => exact mapName_bound f hLip a b R h

def positionValue : Value → Value := mapValue positionState position_nonexpansive
def firstValue : Value → Value := mapValue firstState first_nonexpansive
def secondValue : Value → Value := mapValue secondState second_nonexpansive

theorem positionValue_embed (s : Point × Point) :
    positionValue (embed s) = embed (positionState s) :=
  mapValue_embed positionState position_nonexpansive s

theorem firstValue_embed (s : Point × Point) :
    firstValue (embed s) = embed (firstState s) :=
  mapValue_embed firstState first_nonexpansive s

theorem secondValue_embed (s : Point × Point) :
    secondValue (embed s) = embed (secondState s) :=
  mapValue_embed secondState second_nonexpansive s

theorem positionValue_idempotent (v : Value) :
    positionValue (positionValue v) = positionValue v := by
  induction v using Quotient.inductionOn with
  | _ a => rfl

theorem positionValue_within (x y : Value) (R : Fraction)
    (h : Within x y R) :
    Within (positionValue x) (positionValue y) R :=
  mapValue_within positionState position_nonexpansive x y R h

theorem firstValue_within (x y : Value) (R : Fraction)
    (h : Within x y R) :
    Within (firstValue x) (firstValue y) R :=
  mapValue_within firstState first_nonexpansive x y R h

theorem secondValue_within (x y : Value) (R : Fraction)
    (h : Within x y R) :
    Within (secondValue x) (secondValue y) R :=
  mapValue_within secondState second_nonexpansive x y R h

def PositionValue := {v : Value // positionValue v = v}

def asPosition (v : Value) : PositionValue :=
  ⟨positionValue v, positionValue_idempotent v⟩

def embedPosition (p : Point) : PositionValue :=
  asPosition (embed (p, zeroPoint))

def gammaPosition (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (t : BinaryTime T hT) : PositionValue :=
  asPosition (gammaValue w T s hT hs t)

theorem gammaPosition_within (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (x y : BinaryTime T hT) (R : Fraction)
    (hR : 0 ≤ R.num) (hxy : TimeWithin T hT x y R) :
    Within (gammaPosition w T s hT hs x).val
      (gammaPosition w T s hT hs y).val
      (Fraction.mul R (stateTimeFactor w s)) :=
  positionValue_within _ _ _
    (gamma_within w T s hT hs x y R hR hxy)

theorem gammaPosition_uniform_continuity (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (eps : Fraction)
    (heps : 0 < eps.num) (x y : BinaryTime T hT)
    (hxy : TimeWithin T hT x y (timeTolerance w s eps)) :
    Within (gammaPosition w T s hT hs x).val
      (gammaPosition w T s hT hs y).val eps.half :=
  positionValue_within _ _ _
    (gamma_uniform_continuity w T s hT hs eps heps x y hxy)

theorem gammaPosition_alias (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    gammaPosition w T s hT hs (Quotient.mk _ firstAlias) =
      gammaPosition w T s hT hs (Quotient.mk _ secondAlias) := by
  exact congrArg (gammaPosition w T s hT hs) (alias_time_eq T hT)

theorem gammaPosition_left (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    gammaPosition w T s hT hs (leftTime T hT) = embedPosition s.1 := by
  apply Subtype.ext
  change positionValue (gammaValue w T s hT hs (leftTime T hT)) =
    positionValue (embed (s.1, zeroPoint))
  rw [left_endpoint_value w T s hT hs, positionValue_embed]
  rfl

theorem gammaPosition_right (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    gammaPosition w T s hT hs (rightTime T hT) =
      asPosition (endpointValue w T s hT hs) := by
  exact congrArg asPosition (right_endpoint_value w T s hT hs)

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

theorem firstValue_positionValue (v : Value) :
    firstValue (positionValue v) = firstValue v := by
  induction v using Quotient.inductionOn with
  | _ a => rfl

theorem secondValue_positionValue (v : Value) :
    secondValue (positionValue v) = secondValue v := by
  induction v using Quotient.inductionOn with
  | _ a => rfl

def NonnegativeRadius := {R : Fraction // 0 ≤ R.num}

/-- A completed coordinate square: each planar coordinate separately has a
closed rational bound. Its corners can have L1 distance twice the radius. -/
def CoordinateSquare (centre : Point) (radius : NonnegativeRadius)
    (x : PositionValue) : Prop :=
  Within (firstValue x.val)
      (embed (firstState (centre, zeroPoint))) radius.val ∧
    Within (secondValue x.val)
      (embed (secondState (centre, zeroPoint))) radius.val

theorem square_of_eventual_coordinate_bounds
    (a : EndpointCauchyName) (centre : Point)
    (radius : NonnegativeRadius) (N : Nat)
    (hx : ∀ n : Nat, N ≤ n →
      Fraction.le
        (distance (firstState (a.approx n))
          (firstState (centre, zeroPoint))) radius.val)
    (hy : ∀ n : Nat, N ≤ n →
      Fraction.le
        (distance (secondState (a.approx n))
          (secondState (centre, zeroPoint))) radius.val) :
    CoordinateSquare centre radius (asPosition (realize a)) := by
  constructor
  · change Within (firstValue (positionValue (realize a)))
      (embed (firstState (centre, zeroPoint))) radius.val
    rw [firstValue_positionValue]
    exact nameBound_of_eventual_le _ _ _ N hx
  · change Within (secondValue (positionValue (realize a)))
      (embed (secondState (centre, zeroPoint))) radius.val
    rw [secondValue_positionValue]
    exact nameBound_of_eventual_le _ _ _ N hy

theorem square_of_rational_coordinate_bounds (p centre : Point)
    (radius : NonnegativeRadius)
    (hx : Fraction.le (distance (firstState (p, zeroPoint))
      (firstState (centre, zeroPoint))) radius.val)
    (hy : Fraction.le (distance (secondState (p, zeroPoint))
      (secondState (centre, zeroPoint))) radius.val) :
    CoordinateSquare centre radius (embedPosition p) := by
  exact square_of_eventual_coordinate_bounds
    (constantName (p, zeroPoint)) centre radius 0
    (fun _ _ => hx) (fun _ _ => hy)

private def sampleOne : Fraction := ⟨1, 1, by decide⟩
private def sampleZero : Fraction := ⟨0, 1, by decide⟩
private def sampleCentre : Point := (sampleZero, sampleZero)
private def sampleCorner : Point := (sampleOne, sampleOne)
private def sampleRadius : NonnegativeRadius := ⟨sampleOne, by decide⟩

theorem sample_corner_in_square :
    CoordinateSquare sampleCentre sampleRadius
      (embedPosition sampleCorner) := by
  apply square_of_rational_coordinate_bounds
  · unfold Fraction.le
    decide
  · unfold Fraction.le
    decide

theorem sample_corner_L1_distance_two :
    Fraction.equiv (pointNorm (pointSub sampleCorner sampleCentre))
      (Fraction.ofInt 2) := by decide

private def sampleQuarter : Fraction := ⟨1, 4, by decide⟩
private def sampleState : Point × Point :=
  ((sampleOne, sampleZero), (sampleZero, sampleOne))
private def sampleTail : Fraction := ⟨3, 16, by decide⟩
private def sampleLower : Fraction := ⟨39, 512, by decide⟩

theorem sample_position_level_one :
    Fraction.equiv
      (distance (positionState (endpoint sampleOne sampleQuarter sampleState 1))
        (positionState sampleState))
      ⟨135, 512, by decide⟩ := by decide

theorem sample_tail_one :
    Fraction.equiv (HarmonicDyadic.tailCap
      sampleOne sampleQuarter sampleState 1) sampleTail := by decide

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
    HarmonicDyadic.add_equiv sample_tail_one (Fraction.equiv_refl _)
  have hfull := Fraction.le_equiv_right
    (Fraction.le_equiv_left hL hchain) hR
  exact le_add_cancel_left sampleTail sampleLower
    (distance (positionState eⱼ) (positionState sampleState)) hfull

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
