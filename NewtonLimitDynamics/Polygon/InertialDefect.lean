import NewtonLimitDynamics.Polygon.ZeroForce

namespace NewtonLimitDynamics.Polygon.InertialDefect

open NewtonLimitDynamics
open TimeSubdivision
open ZeroForce
open PartitionControl

/-- The directed determinant of two rational-time inertial samples. -/
def inertialEdge (p v : Point) (s t : Fraction) : Fraction :=
  det (inertialAt p v s) (inertialAt p v t)

/-- Three samples of the same finite zero-force comparison map have an
    additive directed determinant.  The identity is finite Fraction arithmetic. -/
theorem inertialEdge_compose (p v : Point) (s t u : Fraction) :
    Fraction.equiv
      (Fraction.add (inertialEdge p v s t) (inertialEdge p v t u))
      (inertialEdge p v s u) := by
  unfold Fraction.equiv Fraction.add inertialEdge det inertialAt pointAdd pointScale
    Fraction.mul Fraction.add
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- Determinant of a degenerate connector. -/
theorem inertialEdge_self (p v : Point) (s : Fraction) :
    Fraction.equiv (inertialEdge p v s s) (Fraction.ofInt 0) := by
  unfold Fraction.equiv inertialEdge det Fraction.add Fraction.mul Fraction.ofInt
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- Directed determinant along a finite list, including its final connector. -/
def inertialWalk (p v : Point) (a b : Fraction) : List Fraction → Fraction
  | [] => inertialEdge p v a b
  | t :: ts => Fraction.add (inertialEdge p v a t) (inertialWalk p v t b ts)

private theorem add_equiv_left (c : Fraction) {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv (Fraction.add c a) (Fraction.add c b) := by
  exact Fraction.equiv_trans (Fraction.add_comm c a)
    (Fraction.equiv_trans (Fraction.add_equiv_right c h) (Fraction.add_comm b c))

/-- Every finite collinear walk telescopes to its end connector. -/
theorem inertialWalk_eq_edge (p v : Point) (a b : Fraction) (times : List Fraction) :
    Fraction.equiv (inertialWalk p v a b times) (inertialEdge p v a b) := by
  induction times generalizing a with
  | nil => exact Fraction.equiv_refl _
  | cons t ts ih =>
      exact Fraction.equiv_trans (add_equiv_left _ (ih t))
        (inertialEdge_compose p v a t b)

/-- Any finite closed polygon sampled from an inertial recurrence has zero
    signed doubled determinant sum, for any start, times, and velocity. -/
theorem inertialWalk_closed (p v : Point) (a : Fraction) (times : List Fraction) :
    Fraction.equiv (inertialWalk p v a a times) (Fraction.ofInt 0) := by
  exact Fraction.equiv_trans (inertialWalk_eq_edge p v a a times)
    (inertialEdge_self p v a)

/-- The four-vertex boundary used by the finite scheduling diagnostic is a
    special case of the arbitrary closed walk. -/
theorem inertial_closedBoundaryTwice (p v : Point) (a b c d : Fraction) :
    Fraction.equiv
      (closedBoundaryTwice (inertialAt p v a) (inertialAt p v b)
        (inertialAt p v c) (inertialAt p v d)) (Fraction.ofInt 0) := by
  exact Fraction.equiv_trans
    (Fraction.add_assoc (inertialEdge p v a b) (inertialEdge p v b c)
      (Fraction.add (inertialEdge p v c d) (inertialEdge p v d a)))
    (inertialWalk_closed p v a [b, c, d])

private def fracNeg (a : Fraction) : Fraction := ⟨-a.num, a.den, a.den_pos⟩

private theorem fracNeg_congr {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv (fracNeg a) (fracNeg b) := by
  unfold Fraction.equiv fracNeg at *
  dsimp at *
  simpa only [Int.neg_mul] using congrArg Neg.neg h

private theorem mul_equiv_right (c : Fraction) {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv (Fraction.mul a c) (Fraction.mul b c) := by
  exact Fraction.equiv_trans (Fraction.mul_comm a c)
    (Fraction.equiv_trans (Fraction.mul_equiv_left c h) (Fraction.mul_comm c b))

private theorem add_equiv {a b c d : Fraction} (h : Fraction.equiv a b)
    (k : Fraction.equiv c d) : Fraction.equiv (Fraction.add a c) (Fraction.add b d) :=
  Fraction.equiv_trans (Fraction.add_equiv_right c h) (add_equiv_left b k)

private theorem mul_equiv {a b c d : Fraction} (h : Fraction.equiv a b)
    (k : Fraction.equiv c d) : Fraction.equiv (Fraction.mul a c) (Fraction.mul b d) :=
  Fraction.equiv_trans (mul_equiv_right c h) (Fraction.mul_equiv_left b k)

/-- The represented directed determinant respects point equivalence. -/
theorem det_congr {a a' b b' : Point} (ha : pointEquiv a a')
    (hb : pointEquiv b b') : Fraction.equiv (det a b) (det a' b') := by
  unfold det
  exact add_equiv (mul_equiv ha.1 hb.2) (fracNeg_congr (mul_equiv ha.2 hb.1))

theorem closedBoundaryTwice_congr {a a' b b' c c' d d' : Point}
    (ha : pointEquiv a a') (hb : pointEquiv b b')
    (hc : pointEquiv c c') (hd : pointEquiv d d') :
    Fraction.equiv (closedBoundaryTwice a b c d) (closedBoundaryTwice a' b' c' d') := by
  unfold closedBoundaryTwice
  exact add_equiv (add_equiv (det_congr ha hb) (det_congr hb hc))
    (add_equiv (det_congr hc hd) (det_congr hd ha))

/-- Four arbitrary actual zero-force schedules (possibly with different
    partitions) have a vanishing signed determinant boundary. -/
theorem partitionMotion_closedBoundaryTwice (D : Nat) (hD : 0 < D)
    (p v : Point) (w₀ w₁ w₂ w₃ : List Nat) :
    Fraction.equiv
      (closedBoundaryTwice
        (partitionMotion D hD p v zeroPoint w₀).1
        (partitionMotion D hD p v zeroPoint w₁).1
        (partitionMotion D hD p v zeroPoint w₂).1
        (partitionMotion D hD p v zeroPoint w₃).1)
      (Fraction.ofInt 0) := by
  exact Fraction.equiv_trans
    (closedBoundaryTwice_congr
      (partitionMotion_zero_force D hD p v w₀).1
      (partitionMotion_zero_force D hD p v w₁).1
      (partitionMotion_zero_force D hD p v w₂).1
      (partitionMotion_zero_force D hD p v w₃).1)
    (inertial_closedBoundaryTwice p v
      (duration D (total w₀) hD) (duration D (total w₁) hD)
      (duration D (total w₂) hD) (duration D (total w₃) hD))

end NewtonLimitDynamics.Polygon.InertialDefect
