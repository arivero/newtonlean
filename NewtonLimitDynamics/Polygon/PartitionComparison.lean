import NewtonLimitDynamics.Polygon.PartialCell

namespace NewtonLimitDynamics.Polygon.PartitionComparison

open NewtonLimitDynamics
open TimeSubdivision
open PartitionControl

private theorem add_equiv_left (c : Fraction) {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv (Fraction.add c a) (Fraction.add c b) :=
  Fraction.equiv_trans (Fraction.add_comm c a)
    (Fraction.equiv_trans (Fraction.add_equiv_right c h) (Fraction.add_comm b c))

private theorem mul_equiv_right (c : Fraction) {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv (Fraction.mul a c) (Fraction.mul b c) :=
  Fraction.equiv_trans (Fraction.mul_comm a c)
    (Fraction.equiv_trans (Fraction.mul_equiv_left c h) (Fraction.mul_comm c b))

private theorem mul_equiv {a b c d : Fraction} (h : Fraction.equiv a b)
    (k : Fraction.equiv c d) : Fraction.equiv (Fraction.mul a c) (Fraction.mul b d) :=
  Fraction.equiv_trans (mul_equiv_right c h) (Fraction.mul_equiv_left b k)

private theorem half_equiv {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv (Fraction.half a) (Fraction.half b) := by
  unfold Fraction.equiv Fraction.half at *
  dsimp
  calc a.num * (2 * b.den) = 2 * (a.num * b.den) := by ac_rfl
    _ = 2 * (b.num * a.den) := by rw [h]
    _ = b.num * (2 * a.den) := by ac_rfl

private theorem pointEquiv_trans {p q r : Point} (h : pointEquiv p q) (k : pointEquiv q r) :
    pointEquiv p r :=
  ⟨Fraction.equiv_trans h.1 k.1, Fraction.equiv_trans h.2 k.2⟩

private theorem pointEquiv_symm {p q : Point} (h : pointEquiv p q) : pointEquiv q p :=
  ⟨Fraction.equiv_symm h.1, Fraction.equiv_symm h.2⟩

private theorem candidate_scalar_congr {s t : Fraction} (h : Fraction.equiv s t)
    (p v a : Fraction) :
    Fraction.equiv
      (Fraction.add (Fraction.add p (Fraction.mul s v)) (Fraction.mul (Fraction.half (Fraction.mul s s)) a))
      (Fraction.add (Fraction.add p (Fraction.mul t v)) (Fraction.mul (Fraction.half (Fraction.mul t t)) a)) :=
  Fraction.equiv_trans
    (Fraction.add_equiv_right _ (add_equiv_left p (mul_equiv_right v h)))
    (add_equiv_left _ (mul_equiv_right a (half_equiv (mul_equiv h h))))

/-- The constructed candidate depends only on the represented rational time. -/
theorem candidate_time_congr (p v a : Point) {s t : Fraction} (h : Fraction.equiv s t) :
    pointEquiv (candidate p v a s) (candidate p v a t) :=
  ⟨candidate_scalar_congr h p.1 v.1 a.1, candidate_scalar_congr h p.2 v.2 a.2⟩

/-- Two arbitrary finite schedules, with possibly different common denominators
    and cells, reaching the same rational time: their actual positions, each
    corrected by its own exact residual `(Q/(2D²))*a`, agree.  The candidate
    serves only as the common algebraic comparison term. -/
theorem partition_comparison (D E : Nat) (hD : 0 < D) (hE : 0 < E) (p v a : Point)
    (ws ws' : List Nat)
    (ht : Fraction.equiv (duration D (total ws) hD) (duration E (total ws') hE)) :
    pointEquiv
      (pointAdd (partitionMotion D hD p v a ws).1
        (pointScale (residualCoefficient D (squares ws) hD) a))
      (pointAdd (partitionMotion E hE p v a ws').1
        (pointScale (residualCoefficient E (squares ws') hE) a)) :=
  pointEquiv_trans (pointEquiv_symm (candidate_partitionMotion_residual D hD p v a ws))
    (pointEquiv_trans (candidate_time_congr p v a ht)
      (candidate_partitionMotion_residual E hE p v a ws'))

private theorem velocity_scalar_congr {s t : Fraction} (h : Fraction.equiv s t) (v a : Fraction) :
    Fraction.equiv (Fraction.add v (Fraction.mul s a)) (Fraction.add v (Fraction.mul t a)) :=
  add_equiv_left v (mul_equiv_right a h)

/-- Two arbitrary schedules reaching equivalent rational times have equivalent
    actual velocities; no correction term is needed. -/
theorem velocity_comparison (D E : Nat) (hD : 0 < D) (hE : 0 < E) (p v a : Point)
    (ws ws' : List Nat)
    (ht : Fraction.equiv (duration D (total ws) hD) (duration E (total ws') hE)) :
    pointEquiv (partitionMotion D hD p v a ws).2 (partitionMotion E hE p v a ws').2 :=
  pointEquiv_trans (partitionMotion_formula D hD p v a ws).2
    (pointEquiv_trans
      (show pointEquiv (encodedVelocity D hD (stats ws) v a)
          (encodedVelocity E hE (stats ws') v a) from
        ⟨velocity_scalar_congr ht v.1 a.1, velocity_scalar_congr ht v.2 a.2⟩)
      (pointEquiv_symm (partitionMotion_formula E hE p v a ws').2))

/-- Sample times inside cells: two schedules, each followed by a partial final
    drift (`u/D` and `u'/E`), reaching equivalent rational times.  Their actual
    partial positions agree after each is corrected by its own residual
    `((Q+u*u)/(2D²))*a`.  Derived through the appended schedules. -/
theorem partial_comparison (D E : Nat) (hD : 0 < D) (hE : 0 < E) (p v a : Point)
    (ws ws' : List Nat) (u u' : Nat)
    (ht : Fraction.equiv (duration D (total ws + u) hD) (duration E (total ws' + u') hE)) :
    pointEquiv
      (pointAdd (PartialCell.actualPartialPosition D hD p v a ws u)
        (pointScale (residualCoefficient D (squares ws + u * u) hD) a))
      (pointAdd (PartialCell.actualPartialPosition E hE p v a ws' u')
        (pointScale (residualCoefficient E (squares ws' + u' * u') hE) a)) := by
  have h := partition_comparison D E hD hE p v a (ws ++ [u]) (ws' ++ [u'])
    (by rw [PartialCell.total_append, PartialCell.total_append]; exact ht)
  rw [PartialCell.squares_append, PartialCell.squares_append,
    ← PartialCell.partialState_append, ← PartialCell.partialState_append,
    PartialCell.partialState_position, PartialCell.partialState_position] at h
  exact h

/-- Packaged gap statement: two schedules reaching one rational time differ
    only along `a`, through two nonnegative coefficients each bounded by its
    own largest-cell coefficient `M*T/(2D²)` (largest cell times elapsed time,
    halved). -/
theorem partition_gap (D E M M' : Nat) (hD : 0 < D) (hE : 0 < E) (p v a : Point)
    (ws ws' : List Nat) (hw : ∀ w ∈ ws, w ≤ M) (hw' : ∀ w ∈ ws', w ≤ M')
    (ht : Fraction.equiv (duration D (total ws) hD) (duration E (total ws') hE)) :
    ∃ c c' : Fraction,
      Fraction.le (Fraction.ofInt 0) c ∧ Fraction.le c (meshCoefficient D M (total ws) hD) ∧
      Fraction.le (Fraction.ofInt 0) c' ∧ Fraction.le c' (meshCoefficient E M' (total ws') hE) ∧
      pointEquiv (pointAdd (partitionMotion D hD p v a ws).1 (pointScale c a))
        (pointAdd (partitionMotion E hE p v a ws').1 (pointScale c' a)) :=
  ⟨_, _, residual_nonnegative D _ hD, residual_mesh_bound D M hD ws hw,
    residual_nonnegative E _ hE, residual_mesh_bound E M' hE ws' hw',
    partition_comparison D E hD hE p v a ws ws' ht⟩

end NewtonLimitDynamics.Polygon.PartitionComparison
