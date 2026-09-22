import NewtonLimitDynamics.Polygon.PartitionControl

namespace NewtonLimitDynamics.Polygon.ZeroForce

open NewtonLimitDynamics
open TimeSubdivision
open PartitionControl

/-- The zero impressed acceleration used in the finite end-kick recurrence. -/
def zeroPoint : Point := (Fraction.ofInt 0, Fraction.ofInt 0)

/-- The rational-time comparison map for an inertial state.  This is built
    from the finite recurrence below; it is not an assumed continuum curve. -/
def inertialAt (p v : Point) (t : Fraction) : Point :=
  pointAdd p (pointScale t v)

private theorem pointEquiv_refl (p : Point) : pointEquiv p p :=
  ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩

private theorem pointEquiv_trans {p q r : Point} (h : pointEquiv p q) (k : pointEquiv q r) :
    pointEquiv p r :=
  ⟨Fraction.equiv_trans h.1 k.1, Fraction.equiv_trans h.2 k.2⟩

private theorem pointAdd_congr {p p' q q' : Point}
    (hp : pointEquiv p p') (hq : pointEquiv q q') :
    pointEquiv (pointAdd p q) (pointAdd p' q') := by
  constructor
  · exact Fraction.equiv_trans (Fraction.add_equiv_right q.1 hp.1)
      (Fraction.equiv_trans (Fraction.add_comm p'.1 q.1)
        (Fraction.equiv_trans (Fraction.add_equiv_right p'.1 hq.1)
          (Fraction.add_comm q'.1 p'.1)))
  · exact Fraction.equiv_trans (Fraction.add_equiv_right q.2 hp.2)
      (Fraction.equiv_trans (Fraction.add_comm p'.2 q.2)
        (Fraction.equiv_trans (Fraction.add_equiv_right p'.2 hq.2)
          (Fraction.add_comm q'.2 p'.2)))

private theorem pointScale_congr (d : Fraction) {p q : Point} (h : pointEquiv p q) :
    pointEquiv (pointScale d p) (pointScale d q) :=
  ⟨Fraction.mul_equiv_left d h.1, Fraction.mul_equiv_left d h.2⟩

private theorem add_equiv_left (c : Fraction) {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv (Fraction.add c a) (Fraction.add c b) := by
  exact Fraction.equiv_trans (Fraction.add_comm c a)
    (Fraction.equiv_trans (Fraction.add_equiv_right c h) (Fraction.add_comm b c))

private theorem inertial_add_scalar (p v s t : Fraction) :
    Fraction.equiv
      (Fraction.add (Fraction.add p (Fraction.mul s v)) (Fraction.mul t v))
      (Fraction.add p (Fraction.mul (Fraction.add s t) v)) := by
  have hsum : Fraction.equiv (Fraction.add (Fraction.mul s v) (Fraction.mul t v))
      (Fraction.mul (Fraction.add s t) v) := by
    exact Fraction.equiv_trans
      (Fraction.equiv_trans
        (Fraction.add_equiv_right (Fraction.mul t v) (Fraction.mul_comm s v))
        (add_equiv_left (Fraction.mul v s) (Fraction.mul_comm t v)))
      (Fraction.equiv_trans (Fraction.equiv_symm (Fraction.mul_add v s t))
        (Fraction.equiv_symm (Fraction.mul_comm (Fraction.add s t) v)))
  exact Fraction.equiv_trans (Fraction.add_assoc p (Fraction.mul s v) (Fraction.mul t v))
    (add_equiv_left p hsum)

/-- Inertial rational-time evolution joins by addition of elapsed times. -/
theorem inertialAt_add (p v : Point) (s t : Fraction) :
    pointEquiv (inertialAt (inertialAt p v s) v t) (inertialAt p v (Fraction.add s t)) := by
  constructor <;> apply inertial_add_scalar

private theorem zero_scale (d : Fraction) : pointEquiv (pointScale d zeroPoint) zeroPoint := by
  constructor <;> unfold pointScale zeroPoint Fraction.equiv Fraction.mul Fraction.ofInt <;> dsimp <;> simp

private theorem pointAdd_zero (p : Point) : pointEquiv (pointAdd p zeroPoint) p := by
  constructor <;> unfold pointAdd zeroPoint Fraction.equiv Fraction.add Fraction.ofInt <;> dsimp <;> simp

/-- One actual zero-force cell is exactly a drift at its stated Fraction time,
    and leaves velocity unchanged. -/
theorem endKick_zero (d : Fraction) (state : Point × Point) :
    pointEquiv (endKick d state zeroPoint).1 (inertialAt state.1 state.2 d) ∧
      pointEquiv (endKick d state zeroPoint).2 state.2 := by
  constructor
  · exact pointEquiv_refl _
  · change pointEquiv (pointAdd state.2 (pointScale d zeroPoint)) state.2
    exact pointEquiv_trans (pointAdd_congr (pointEquiv_refl _) (zero_scale d)) (pointAdd_zero state.2)

/-- Replacing a rational time by an equivalent fraction leaves its inertial
    position unchanged. -/
theorem inertialAt_time_congr (p v : Point) {s t : Fraction} (h : Fraction.equiv s t) :
    pointEquiv (inertialAt p v s) (inertialAt p v t) := by
  apply pointAdd_congr (pointEquiv_refl _)
  constructor
  · exact Fraction.equiv_trans (Fraction.mul_comm s v.1)
      (Fraction.equiv_trans (Fraction.mul_equiv_left v.1 h) (Fraction.equiv_symm (Fraction.mul_comm t v.1)))
  · exact Fraction.equiv_trans (Fraction.mul_comm s v.2)
      (Fraction.equiv_trans (Fraction.mul_equiv_left v.2 h) (Fraction.equiv_symm (Fraction.mul_comm t v.2)))

private theorem encodedPosition_zero (D : Nat) (hD : 0 < D) (s : PartitionStats) (p v : Point) :
    pointEquiv (encodedPosition D hD s p v zeroPoint)
      (inertialAt p v (duration D s.T hD)) := by
  unfold encodedPosition inertialAt
  exact pointEquiv_trans
    (pointAdd_congr (pointEquiv_refl _)
      (zero_scale (squareDuration D s.A hD)))
    (pointAdd_zero _)

private theorem encodedVelocity_zero (D : Nat) (hD : 0 < D) (s : PartitionStats) (v : Point) :
    pointEquiv (encodedVelocity D hD s v zeroPoint) v := by
  unfold encodedVelocity
  exact pointEquiv_trans
    (pointAdd_congr (pointEquiv_refl _)
      (zero_scale (duration D s.T hD)))
    (pointAdd_zero _)

/-- Every actual finite zero-force schedule reaches the inertial map at its
    elapsed rational time and retains its incoming velocity. -/
theorem partitionMotion_zero_force (D : Nat) (hD : 0 < D) (p v : Point) (weights : List Nat) :
    pointEquiv (partitionMotion D hD p v zeroPoint weights).1
      (inertialAt p v (duration D (total weights) hD)) ∧
    pointEquiv (partitionMotion D hD p v zeroPoint weights).2 v := by
  have hformula := partitionMotion_formula D hD p v zeroPoint weights
  constructor
  · exact pointEquiv_trans hformula.1
      (encodedPosition_zero D hD (stats weights) p v)
  · exact pointEquiv_trans hformula.2
      (encodedVelocity_zero D hD (stats weights) v)

/-- Addition of two common-denominator elapsed times represents their summed
    numerator. -/
theorem duration_add (D a b : Nat) (hD : 0 < D) :
    Fraction.equiv (Fraction.add (duration D a hD) (duration D b hD))
      (duration D (a + b) hD) := by
  unfold Fraction.equiv Fraction.add duration
  dsimp
  simp only [Int.ofNat_add, Int.mul_add, Int.add_mul]
  ac_rfl

/-- The finite recurrence itself restarts exactly: this is `foldl_append`, not
    an assumption about a background curve. -/
theorem partitionMotion_append (D : Nat) (hD : 0 < D) (p v : Point)
    (ws xs : List Nat) :
    partitionMotion D hD p v zeroPoint (ws ++ xs) =
      partitionMotion D hD (partitionMotion D hD p v zeroPoint ws).1
        (partitionMotion D hD p v zeroPoint ws).2 zeroPoint xs := by
  unfold partitionMotion
  rw [List.foldl_append]

private theorem inertialAt_state_congr {p p' v v' : Point} (hp : pointEquiv p p')
    (hv : pointEquiv v v') (t : Fraction) :
    pointEquiv (inertialAt p v t) (inertialAt p' v' t) :=
  pointAdd_congr hp (pointScale_congr t hv)

/-- Drifting for a rational amount `r` from the actual prefix state agrees
    with the inertial map at elapsed prefix time plus `r`. -/
theorem withinCell_position (D : Nat) (hD : 0 < D) (p v : Point)
    (pre : List Nat) (r : Fraction) :
    pointEquiv (endKick r (partitionMotion D hD p v zeroPoint pre) zeroPoint).1
      (inertialAt p v (Fraction.add (duration D (total pre) hD) r)) := by
  have hp := partitionMotion_zero_force D hD p v pre
  have hkick := endKick_zero r (partitionMotion D hD p v zeroPoint pre)
  exact pointEquiv_trans hkick.1
    (pointEquiv_trans (inertialAt_state_congr hp.1 hp.2 r)
      (inertialAt_add p v (duration D (total pre) hD) r))

/-- The same algebra applies to an in-cell physical drift; the displayed
    inequalities express that `r` lies between the prefix vertex and the next
    cell endpoint and are not used as algebraic premises. -/
theorem withinCell_position_bounded (D w : Nat) (hD : 0 < D) (p v : Point)
    (pre : List Nat) (r : Fraction)
    (_hr0 : Fraction.le (Fraction.ofInt 0) r)
    (_hrcell : Fraction.le r (duration D w hD)) :
    pointEquiv (endKick r (partitionMotion D hD p v zeroPoint pre) zeroPoint).1
      (inertialAt p v (Fraction.add (duration D (total pre) hD) r)) :=
  withinCell_position D hD p v pre r

/-- Rest is the zero-velocity specialization of the actual finite recurrence. -/
theorem partitionMotion_rest (D : Nat) (hD : 0 < D) (p : Point) (weights : List Nat) :
    pointEquiv (partitionMotion D hD p zeroPoint zeroPoint weights).1 p ∧
      pointEquiv (partitionMotion D hD p zeroPoint zeroPoint weights).2 zeroPoint := by
  have h := partitionMotion_zero_force D hD p zeroPoint weights
  constructor
  · exact pointEquiv_trans h.1 (by
      unfold inertialAt
      exact pointEquiv_trans
        (pointAdd_congr (pointEquiv_refl _) (zero_scale (duration D (total weights) hD)))
        (pointAdd_zero _))
  · exact h.2

/-- Equal rational elapsed times give equal positions even for schedules with
    different positive common denominators and different partitions. -/
theorem partitionMotion_cross_partition (D E : Nat) (hD : 0 < D) (hE : 0 < E)
    (p v : Point) (ws xs : List Nat)
    (ht : Fraction.equiv (duration D (total ws) hD) (duration E (total xs) hE)) :
    pointEquiv (partitionMotion D hD p v zeroPoint ws).1
      (partitionMotion E hE p v zeroPoint xs).1 := by
  have hleft := partitionMotion_zero_force D hD p v ws
  have hright := partitionMotion_zero_force E hE p v xs
  exact pointEquiv_trans hleft.1
    (pointEquiv_trans (inertialAt_time_congr p v ht)
      ⟨Fraction.equiv_symm hright.1.1, Fraction.equiv_symm hright.1.2⟩)

/-- Cross-partition agreement includes the unchanged terminal velocity. -/
theorem partitionMotion_cross_partition_state (D E : Nat) (hD : 0 < D) (hE : 0 < E)
    (p v : Point) (ws xs : List Nat)
    (ht : Fraction.equiv (duration D (total ws) hD) (duration E (total xs) hE)) :
    pointEquiv (partitionMotion D hD p v zeroPoint ws).1
      (partitionMotion E hE p v zeroPoint xs).1 ∧
    pointEquiv (partitionMotion D hD p v zeroPoint ws).2
      (partitionMotion E hE p v zeroPoint xs).2 := by
  constructor
  · exact partitionMotion_cross_partition D E hD hE p v ws xs ht
  · have hleft := partitionMotion_zero_force D hD p v ws
    have hright := partitionMotion_zero_force E hE p v xs
    exact pointEquiv_trans hleft.2
      ⟨Fraction.equiv_symm hright.2.1, Fraction.equiv_symm hright.2.2⟩

def scalarZero : Fraction := Fraction.ofInt 0
def scalarOne : Fraction := Fraction.ofInt 1
def scalarTwo : Fraction := Fraction.ofInt 2
def scalarHalf : Fraction := ⟨1, 2, by decide⟩

def slow (t : Fraction) : Point := (t, scalarZero)
def fast (t : Fraction) : Point := (Fraction.mul scalarTwo t, scalarZero)

/-- Same endpoint with different elapsed times: `slow(1) = fast(1/2)`. -/
theorem slow_fast_equal_endpoint : pointEquiv (slow scalarOne) (fast scalarHalf) := by
  decide

/-- At a common half-time the two velocity choices give different positions. -/
theorem slow_fast_different_half_time : ¬ pointEquiv (slow scalarHalf) (fast scalarHalf) := by
  decide

/-- Collinear samples of these distinct motions close with zero directed area.
    This is a geometric diagnostic only, not fixed-data nonuniqueness. -/
theorem slow_fast_collinear_closedBoundary :
    Fraction.equiv (closedBoundaryTwice zeroPoint (slow scalarHalf) (slow scalarOne)
      (fast scalarHalf)) scalarZero := by
  decide

/-- A concrete two-cell actual schedule has the expected inertial endpoint. -/
theorem slow_two_cell_schedule :
    pointEquiv (partitionMotion 2 (by decide) zeroPoint (slow scalarOne) zeroPoint [1, 1]).1
      (slow scalarOne) := by
  decide

end NewtonLimitDynamics.Polygon.ZeroForce
