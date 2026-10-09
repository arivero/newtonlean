import BarrowLib.Polygon.TimeSubdivision

namespace NewtonLimitDynamics.Polygon.PartitionControl

open NewtonLimitDynamics
open TimeSubdivision

/-- Integer bookkeeping for a finite common-denominator schedule.  `A` is the
    ordered pair sum accumulated before each new weight is inserted. -/
structure PartitionStats where
  T : Nat
  A : Nat
  Q : Nat

def initial : PartitionStats := ⟨0, 0, 0⟩

/-- The recurrences `T' = T + w`, `A' = A + w*T`, and `Q' = Q + w*w`. -/
def next (s : PartitionStats) (w : Nat) : PartitionStats :=
  ⟨s.T + w, s.A + w * s.T, s.Q + w * w⟩

def stats (weights : List Nat) : PartitionStats :=
  weights.foldl next initial

def total (weights : List Nat) : Nat := (stats weights).T
def cross (weights : List Nat) : Nat := (stats weights).A
def squares (weights : List Nat) : Nat := (stats weights).Q

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem next_identity (s : PartitionStats)
    (h : 2 * s.A + s.Q = s.T * s.T) (w : Nat) :
    2 * (next s w).A + (next s w).Q = (next s w).T * (next s w).T := by
  simp only [next]
  simp only [Nat.mul_add, Nat.add_mul]
  have htw : s.T * w = w * s.T := Nat.mul_comm _ _
  omega

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem stats_identity_from (s : PartitionStats)
    (h : 2 * s.A + s.Q = s.T * s.T) : (weights : List Nat) ->
    2 * (weights.foldl next s).A + (weights.foldl next s).Q =
      (weights.foldl next s).T * (weights.foldl next s).T
  | [] => h
  | w :: ws => by
      simp only [List.foldl]
      exact stats_identity_from (next s w) (next_identity s h w) ws

/-- The ordered-pair and square decomposition for every finite schedule. -/
-- Modern dependency score: 2/2 (M=2, H=0; transitive project theorems/axioms).
theorem stats_identity (weights : List Nat) :
    2 * cross weights + squares weights = total weights * total weights := by
  exact stats_identity_from initial (by decide) weights

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem next_bound (M : Nat) (s : PartitionStats) (h : s.Q ≤ M * s.T)
    (w : Nat) (hw : w ≤ M) : (next s w).Q ≤ M * (next s w).T := by
  have hww : w * w ≤ M * w := Nat.mul_le_mul_right w hw
  simp only [next, Nat.mul_add]
  omega

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem stats_bound_from (M : Nat) (s : PartitionStats) (h : s.Q ≤ M * s.T)
    (weights : List Nat) (hw : ∀ w ∈ weights, w ≤ M) :
    (weights.foldl next s).Q ≤ M * (weights.foldl next s).T := by
  induction weights generalizing s with
  | nil => exact h
  | cons w ws ih =>
      simp only [List.mem_cons] at hw
      simp only [List.foldl]
      exact ih (next s w) (next_bound M s h w (hw w (Or.inl rfl)))
        (fun x hx => hw x (Or.inr hx))

/-- A max-cell estimate for the finite square coefficient. -/
-- Modern dependency score: 2/2 (M=2, H=0; transitive project theorems/axioms).
theorem stats_bound (M : Nat) (weights : List Nat) (hw : ∀ w ∈ weights, w ≤ M) :
    squares weights ≤ M * total weights := by
  exact stats_bound_from M initial (by change 0 ≤ M * 0; omega) weights hw

/-- Zero weights are admitted by the recurrence; strict positive mesh cells are
    an additional hypothesis when a nondegenerate partition is required. -/
def positiveWeights (weights : List Nat) : Prop := ∀ w ∈ weights, 0 < w

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem natDen_pos (D : Nat) (hD : 0 < D) : (0 : Int) < D := by omega

/-- The common-denominator duration `w/D`. -/
def duration (D w : Nat) (hD : 0 < D) : Fraction := ⟨w, D, natDen_pos D hD⟩

def squareDuration (D w : Nat) (hD : 0 < D) : Fraction := ⟨w, D * D, by
  exact Int.mul_pos (natDen_pos D hD) (natDen_pos D hD)⟩

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem duration_positive (D w : Nat) (hD : 0 < D) (hw : 0 < w) :
    Fraction.positive (duration D w hD) := by
  change 0 < (w : Int)
  omega

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
private theorem scalar_step_position (D A T w : Nat) (hD : 0 < D) (p v a : Fraction) :
    Fraction.equiv
      (Fraction.add
        (Fraction.add (Fraction.add p (Fraction.mul (duration D T hD) v))
          (Fraction.mul (squareDuration D A hD) a))
        (Fraction.mul (duration D w hD)
          (Fraction.add v (Fraction.mul (duration D T hD) a))))
      (Fraction.add
        (Fraction.add p (Fraction.mul (duration D (T + w) hD) v))
        (Fraction.mul (squareDuration D (A + w * T) hD) a)) := by
  unfold Fraction.equiv Fraction.add Fraction.mul duration squareDuration
  dsimp
  simp only [Int.natCast_add, Int.natCast_mul, Int.add_mul, Int.mul_add]
  ac_rfl

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
private theorem scalar_step_velocity (D T w : Nat) (hD : 0 < D) (v a : Fraction) :
    Fraction.equiv
      (Fraction.add (Fraction.add v (Fraction.mul (duration D T hD) a))
        (Fraction.mul (duration D w hD) a))
      (Fraction.add v (Fraction.mul (duration D (T + w) hD) a)) := by
  unfold Fraction.equiv Fraction.add Fraction.mul duration
  dsimp
  simp only [Int.natCast_add, Int.add_mul]
  ac_rfl

-- Modern dependency score: 0/10 (M=0, H=10; transitive project theorems/axioms).
private theorem endKick_congr (d : Fraction) {x y : Point × Point} (a : Point)
    (h : pointEquiv x.1 y.1 ∧ pointEquiv x.2 y.2) :
    pointEquiv (endKick d x a).1 (endKick d y a).1 ∧
      pointEquiv (endKick d x a).2 (endKick d y a).2 := by
  constructor
  · exact pointAdd_congr h.1 (pointScale_congr d h.2)
  · exact pointAdd_congr h.2 ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩

def encodedPosition (D : Nat) (hD : 0 < D) (s : PartitionStats) (p v a : Point) : Point :=
  pointAdd (pointAdd p (pointScale (duration D s.T hD) v))
    (pointScale (squareDuration D s.A hD) a)

def encodedVelocity (D : Nat) (hD : 0 < D) (s : PartitionStats) (v a : Point) : Point :=
  pointAdd v (pointScale (duration D s.T hD) a)

def encodedState (D : Nat) (hD : 0 < D) (s : PartitionStats) (p v a : Point) : Point × Point :=
  (encodedPosition D hD s p v a, encodedVelocity D hD s v a)

/-- The actual finite polygonal schedule, constructed only by repeated
    `TimeSubdivision.endKick` cells of duration `w/D`. -/
def partitionMotion (D : Nat) (hD : 0 < D) (p v a : Point) (weights : List Nat) : Point × Point :=
  weights.foldl (fun state w => endKick (duration D w hD) state a) (p, v)

-- Modern dependency score: 3/3 (M=3, H=0; transitive project theorems/axioms).
private theorem encoded_step (D : Nat) (hD : 0 < D) (s : PartitionStats) (w : Nat)
    (p v a : Point) :
    pointEquiv (endKick (duration D w hD) (encodedState D hD s p v a) a).1
      (encodedState D hD (next s w) p v a).1 ∧
    pointEquiv (endKick (duration D w hD) (encodedState D hD s p v a) a).2
      (encodedState D hD (next s w) p v a).2 := by
  constructor <;> constructor
  · exact scalar_step_position D s.A s.T w hD p.1 v.1 a.1
  · exact scalar_step_position D s.A s.T w hD p.2 v.2 a.2
  · exact scalar_step_velocity D s.T w hD v.1 a.1
  · exact scalar_step_velocity D s.T w hD v.2 a.2

-- Modern dependency score: 5/16 (M=5, H=11; transitive project theorems/axioms).
private theorem fold_encoded (D : Nat) (hD : 0 < D) (s : PartitionStats)
    (state : Point × Point) (p v a : Point)
    (hstate : pointEquiv state.1 (encodedState D hD s p v a).1 ∧
      pointEquiv state.2 (encodedState D hD s p v a).2) : (weights : List Nat) ->
    pointEquiv (weights.foldl (fun x w => endKick (duration D w hD) x a) state).1
      (encodedState D hD (weights.foldl next s) p v a).1 ∧
    pointEquiv (weights.foldl (fun x w => endKick (duration D w hD) x a) state).2
      (encodedState D hD (weights.foldl next s) p v a).2
  | [] => hstate
  | w :: ws => by
      simp only [List.foldl]
      have hkick := endKick_congr (duration D w hD) a hstate
      have hencoded := encoded_step D hD s w p v a
      exact fold_encoded D hD (next s w) _ p v a
        ⟨pointEquiv_trans hkick.1 hencoded.1, pointEquiv_trans hkick.2 hencoded.2⟩ ws

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
private theorem initial_encoded (D : Nat) (hD : 0 < D) (p v a : Point) :
    pointEquiv p (encodedState D hD initial p v a).1 ∧
      pointEquiv v (encodedState D hD initial p v a).2 := by
  constructor <;> constructor <;>
    unfold encodedState encodedPosition encodedVelocity initial pointAdd pointScale duration squareDuration
      Fraction.equiv Fraction.add Fraction.mul <;> dsimp <;> simp <;> ac_rfl

/-- The finite end-kick schedule has velocity `v + (T/D)a` and position
    `p + (T/D)v + (A/D²)a`, componentwise up to rational representation. -/
-- Modern dependency score: 7/18 (M=7, H=11; transitive project theorems/axioms).
theorem partitionMotion_formula (D : Nat) (hD : 0 < D) (p v a : Point) (weights : List Nat) :
    pointEquiv (partitionMotion D hD p v a weights).1
      (encodedPosition D hD (stats weights) p v a) ∧
    pointEquiv (partitionMotion D hD p v a weights).2
      (encodedVelocity D hD (stats weights) v a) := by
  exact fold_encoded D hD initial (p, v) p v a (initial_encoded D hD p v a) weights

/-- A finite rational comparison map; this is a formula, not an assumed
    limiting trajectory. -/
def candidate (p v a : Point) (t : Fraction) : Point :=
  pointAdd (pointAdd p (pointScale t v)) (pointScale (Fraction.half (Fraction.mul t t)) a)

def residualCoefficient (D Q : Nat) (hD : 0 < D) : Fraction :=
  Fraction.half (squareDuration D Q hD)

def meshCoefficient (D M T : Nat) (hD : 0 < D) : Fraction :=
  Fraction.half (squareDuration D (M * T) hD)

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
private theorem candidate_residual_scalar (D A Q T : Nat) (hD : 0 < D)
    (h : 2 * A + Q = T * T) (p v a : Fraction) :
    Fraction.equiv
      (Fraction.add (Fraction.add p (Fraction.mul (duration D T hD) v))
        (Fraction.mul (Fraction.half (Fraction.mul (duration D T hD) (duration D T hD))) a))
      (Fraction.add
        (Fraction.add (Fraction.add p (Fraction.mul (duration D T hD) v))
          (Fraction.mul (squareDuration D A hD) a))
        (Fraction.mul (residualCoefficient D Q hD) a)) := by
  have hi : (2 : Int) * (A : Int) + (Q : Int) = (T : Int) * (T : Int) := by omega
  unfold Fraction.equiv Fraction.add Fraction.mul duration squareDuration residualCoefficient
  simp only [Fraction.half, squareDuration]
  simp only [Int.natCast_mul, Int.add_mul, Int.mul_add]
  rw [← hi]
  simp only [Int.add_mul, Int.mul_add]
  ac_rfl

/-- At the finite terminal time, the candidate differs from the constructed
    polygon position by exactly `Q/(2D²)` times the common acceleration. -/
-- Modern dependency score: 5/5 (M=5, H=0; transitive project theorems/axioms).
theorem candidate_residual (D : Nat) (hD : 0 < D) (p v a : Point) (weights : List Nat) :
    pointEquiv (candidate p v a (duration D (total weights) hD))
      (pointAdd (encodedPosition D hD (stats weights) p v a)
        (pointScale (residualCoefficient D (squares weights) hD) a)) := by
  constructor
  · exact candidate_residual_scalar D (cross weights) (squares weights) (total weights) hD
      (stats_identity weights) p.1 v.1 a.1
  · exact candidate_residual_scalar D (cross weights) (squares weights) (total weights) hD
      (stats_identity weights) p.2 v.2 a.2

/-- The terminal residual stated against the actual recursively constructed
    polygon endpoint. -/
-- Modern dependency score: 13/26 (M=13, H=13; transitive project theorems/axioms).
theorem candidate_partitionMotion_residual (D : Nat) (hD : 0 < D)
    (p v a : Point) (weights : List Nat) :
    pointEquiv (candidate p v a (duration D (total weights) hD))
      (pointAdd (partitionMotion D hD p v a weights).1
        (pointScale (residualCoefficient D (squares weights) hD) a)) := by
  have hcandidate := candidate_residual D hD p v a weights
  have hmotion := partitionMotion_formula D hD p v a weights
  exact pointEquiv_trans hcandidate
    (pointAdd_congr (pointEquiv_symm hmotion.1)
      ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩)

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem residual_nonnegative (D Q : Nat) (hD : 0 < D) :
    Fraction.le (Fraction.ofInt 0) (residualCoefficient D Q hD) := by
  unfold Fraction.le Fraction.ofInt residualCoefficient Fraction.half squareDuration
  dsimp
  omega

-- Modern dependency score: 4/4 (M=4, H=0; transitive project theorems/axioms).
theorem residual_mesh_bound (D M : Nat) (hD : 0 < D) (weights : List Nat)
    (hw : ∀ w ∈ weights, w ≤ M) :
    Fraction.le (residualCoefficient D (squares weights) hD)
      (meshCoefficient D M (total weights) hD) := by
  have hq := stats_bound M weights hw
  have hi : (squares weights : Int) ≤ (M * total weights : Int) := by omega
  unfold Fraction.le residualCoefficient meshCoefficient Fraction.half squareDuration
  dsimp
  have hp : 0 < (2 : Int) * ((D : Int) * (D : Int)) :=
    Int.mul_pos (by decide) (Int.mul_pos (natDen_pos D hD) (natDen_pos D hD))
  apply Int.mul_le_mul_of_nonneg_right hi (Int.le_of_lt hp)

end NewtonLimitDynamics.Polygon.PartitionControl
