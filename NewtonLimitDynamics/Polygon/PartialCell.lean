import NewtonLimitDynamics.Polygon.ZeroForce

namespace NewtonLimitDynamics.Polygon.PartialCell

open NewtonLimitDynamics
open TimeSubdivision
open PartitionControl
open ZeroForce

/-- The actual state after a finite prefix schedule followed by one partial
    cell of duration `u/D`.  It is the end-kick recurrence applied to the
    actual prefix state; no formula for the motion is assumed. -/
def partialState (D : Nat) (hD : 0 < D) (p v a : Point) (weights : List Nat) (u : Nat) :
    Point × Point :=
  endKick (duration D u hD) (partitionMotion D hD p v a weights) a

/-- The drift position reached `u/D` into the next cell: the actual prefix
    position moved by the actual prefix velocity. -/
def actualPartialPosition (D : Nat) (hD : 0 < D) (p v a : Point)
    (weights : List Nat) (u : Nat) : Point :=
  pointAdd (partitionMotion D hD p v a weights).1
    (pointScale (duration D u hD) (partitionMotion D hD p v a weights).2)

/-- The partial position is the position component of the end-kick step. -/
theorem partialState_position (D : Nat) (hD : 0 < D) (p v a : Point)
    (weights : List Nat) (u : Nat) :
    (partialState D hD p v a weights u).1 = actualPartialPosition D hD p v a weights u := rfl

/-- The terminal kick does not alter the drift position: the position component
    of an end-kick step is independent of the accelerative force applied at its end. -/
theorem endKick_position_kick_free (d : Fraction) (state : Point × Point) (a b : Point) :
    (endKick d state a).1 = (endKick d state b).1 := rfl

/-- The partial state is literally the recurrence on the appended schedule. -/
theorem partialState_append (D : Nat) (hD : 0 < D) (p v a : Point)
    (weights : List Nat) (u : Nat) :
    partialState D hD p v a weights u = partitionMotion D hD p v a (weights ++ [u]) := by
  unfold partialState partitionMotion
  rw [List.foldl_append]
  rfl

/-- Appending one weight applies the statistics recurrence once. -/
theorem stats_append (weights : List Nat) (u : Nat) :
    stats (weights ++ [u]) = next (stats weights) u := by
  unfold stats
  rw [List.foldl_append]
  rfl

theorem total_append (weights : List Nat) (u : Nat) :
    total (weights ++ [u]) = total weights + u := by
  unfold total
  rw [stats_append]
  rfl

theorem squares_append (weights : List Nat) (u : Nat) :
    squares (weights ++ [u]) = squares weights + u * u := by
  unfold squares
  rw [stats_append]
  rfl

private theorem pointEquiv_trans {p q r : Point} (h : pointEquiv p q) (k : pointEquiv q r) :
    pointEquiv p r :=
  ⟨Fraction.equiv_trans h.1 k.1, Fraction.equiv_trans h.2 k.2⟩

/-- Exact residual at the sample time `(T+u)/D` inside the next cell: the
    constructed candidate exceeds the actual partial position by
    `((Q+u*u)/(2D²))*a`.  Derived from the appended schedule's statistics. -/
theorem candidate_partial_residual (D : Nat) (hD : 0 < D) (p v a : Point)
    (weights : List Nat) (u : Nat) :
    pointEquiv (candidate p v a (duration D (total weights + u) hD))
      (pointAdd (actualPartialPosition D hD p v a weights u)
        (pointScale (residualCoefficient D (squares weights + u * u) hD) a)) := by
  have h := candidate_partitionMotion_residual D hD p v a (weights ++ [u])
  rw [total_append, squares_append, ← partialState_append, partialState_position] at h
  exact h

/-- Within-cell mesh bound on the square statistic: a partial duration inside a
    designated next cell of weight `w` (`0 ≤ u` is automatic in `Nat`). -/
theorem partial_squares_bound (M w u : Nat) (weights : List Nat)
    (hM : ∀ x ∈ weights, x ≤ M) (hw : w ≤ M) (hu : u ≤ w) :
    squares weights + u * u ≤ M * (total weights + u) := by
  have hall : ∀ x ∈ weights ++ [u], x ≤ M := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hM x h
    · rw [List.mem_singleton.mp h]
      exact Nat.le_trans hu hw
  have hb := stats_bound M (weights ++ [u]) hall
  rw [squares_append, total_append] at hb
  exact hb

/-- The corresponding Fraction coefficient bound:
    `(Q+u*u)/(2D²) ≤ M*(T+u)/(2D²)`. -/
theorem partial_residual_mesh_bound (D M w u : Nat) (hD : 0 < D) (weights : List Nat)
    (hM : ∀ x ∈ weights, x ≤ M) (hw : w ≤ M) (hu : u ≤ w) :
    Fraction.le (residualCoefficient D (squares weights + u * u) hD)
      (meshCoefficient D M (total weights + u) hD) := by
  have hq := partial_squares_bound M w u weights hM hw hu
  have hi : ((squares weights + u * u : Nat) : Int) ≤ ((M * (total weights + u) : Nat) : Int) :=
    Int.ofNat_le.mpr hq
  unfold Fraction.le residualCoefficient meshCoefficient Fraction.half squareDuration
  dsimp
  have hp : 0 < (2 : Int) * ((D : Int) * (D : Int)) :=
    Int.mul_pos (by decide) (Int.mul_pos (by omega) (by omega))
  exact Int.mul_le_mul_of_nonneg_right hi (Int.le_of_lt hp)

/-- Boundary `u = w`: the partial position is the actual next vertex. -/
theorem partial_full_cell (D : Nat) (hD : 0 < D) (p v a : Point)
    (weights : List Nat) (w : Nat) :
    actualPartialPosition D hD p v a weights w =
      (partitionMotion D hD p v a (weights ++ [w])).1 := by
  rw [← partialState_append]
  rfl

private theorem zero_drift_scalar (D : Nat) (hD : 0 < D) (x y : Fraction) :
    Fraction.equiv (Fraction.add x (Fraction.mul (duration D 0 hD) y)) x := by
  unfold Fraction.equiv Fraction.add Fraction.mul duration
  dsimp
  simp only [Int.ofNat_zero, Int.zero_mul, Int.add_zero]
  ac_rfl

/-- Boundary `u = 0`: the partial position is the actual prefix vertex. -/
theorem partial_zero (D : Nat) (hD : 0 < D) (p v a : Point) (weights : List Nat) :
    pointEquiv (actualPartialPosition D hD p v a weights 0)
      (partitionMotion D hD p v a weights).1 :=
  ⟨zero_drift_scalar D hD _ _, zero_drift_scalar D hD _ _⟩

/-- Boundary `a = 0`: the actual partial position lies on the inertial map at
    `(T+u)/D`. -/
theorem partial_zero_force (D : Nat) (hD : 0 < D) (p v : Point)
    (weights : List Nat) (u : Nat) :
    pointEquiv (actualPartialPosition D hD p v zeroPoint weights u)
      (inertialAt p v (duration D (total weights + u) hD)) := by
  have h := (partitionMotion_zero_force D hD p v (weights ++ [u])).1
  rw [total_append, ← partialState_append, partialState_position] at h
  exact h

end NewtonLimitDynamics.Polygon.PartialCell
