import NewtonLimitDynamics

namespace NewtonLimitDynamics.Polygon.CompositionControls
open NewtonLimitDynamics TimeSubdivision Parallelogram ImpulseComposition

private def p (x y : Int) : Point := (Fraction.ofInt x,Fraction.ofInt y)
private def half : Fraction := ⟨1,2,by decide⟩

-- Nonorthogonal directions, translated origin, and fractional elapsed time.
example : pointEquiv (ZeroForce.inertialAt (p 2 (-1))
    (pointAdd (p 3 1) (p (-1) 3)) half) (p 3 1) :=
  pointEquiv_trans
    (Principia1687.Laws.corollary1_endpoint_reconstruction
      (p 2 (-1)) (p 3 1) (p (-1) 3) half (by decide)) (by decide)

example : pointEquiv (ZeroForce.inertialAt (p 2 (-1))
    (pointAdd (p 3 1) (p (-1) 3)) half) (p 3 1) :=
  pointEquiv_trans
    (Principia1713.Laws.corollary1_endpoint_reconstruction
      (p 2 (-1)) (p 3 1) (p (-1) 3) half (by decide)) (by decide)

example : pointEquiv (ZeroForce.inertialAt (p 2 (-1))
    (pointAdd (p 3 1) (p (-1) 3)) half) (p 3 1) :=
  pointEquiv_trans
    (DeMotu1684.Composition.natp00090_lemma1_endpoint_reconstruction
      (p 2 (-1)) (p 3 1) (p (-1) 3) half (by decide)) (by decide)

-- Rational representatives need not have the same denominator.
example (u v : Point) : pointEquiv
    (ZeroForce.inertialAt (p 0 0) (pointAdd u v) (⟨2,4,by decide⟩ : Fraction))
    (diagonal (p 0 0) (pointScale half u) (pointScale half v)) :=
  pointEquiv_trans
    (ZeroForce.inertialAt_time_congr _ _ (show Fraction.equiv
      (⟨2,4,by decide⟩ : Fraction) half by decide))
    (uniform_impulse_diagonal _ _ _ _)

-- Degenerate forces are handled by composition, not intersection uniqueness.
example : pointEquiv (ZeroForce.inertialAt (p 7 2)
    (pointAdd (p 1 0) (p 2 0)) half)
    (diagonal (p 7 2) (pointScale half (p 1 0)) (pointScale half (p 2 0))) :=
  (Principia1713.Laws.corollary1_uniform_impulse_model _ _ _ _).1
example : pointEquiv (ZeroForce.inertialAt (p 7 2)
    (pointAdd (p 1 0) (p (-1) 0)) half) (p 7 2) :=
  pointEquiv_trans (uniform_impulse_diagonal _ _ _ _) (by decide)
example : pointEquiv (ZeroForce.inertialAt (p 7 2)
    (pointAdd (p 1 0) (p 0 0)) (Fraction.ofInt 0)) (p 7 2) :=
  pointEquiv_trans (uniform_impulse_diagonal _ _ _ _) (by decide)

-- One line alone does not locate the opposite corner.
example : ParallelThrough (p 1 5) (p 1 0) (p 0 1) ∧
    ¬ pointEquiv (p 1 5) (diagonal (p 0 0) (p 1 0) (p 0 1)) := by unfold ParallelThrough; decide
-- Both lines still fail when the directions are parallel.
example : ParallelThrough (p 9 0) (p 1 0) (p 2 0) ∧
    ParallelThrough (p 9 0) (p 2 0) (p 1 0) ∧
    ¬ pointEquiv (p 9 0) (diagonal (p 0 0) (p 1 0) (p 2 0)) := by unfold ParallelThrough; decide

-- The proof is used by the actual recurrence, for every sampled field.
example (a : CentralSchedule.Field) (h k : Fraction) (s : Point × Point) :
    pointEquiv (CentralSchedule.cell a k (CentralSchedule.cell a h s)).1
      (diagonal (CentralSchedule.cell a h s).1 (pointScale k s.2)
        (pointScale k (pointScale h (a (CentralSchedule.cell a h s).1)))) :=
  next_arrival_diagonal a h k s

#print axioms Principia1687.Laws.corollary1_endpoint_reconstruction
#print axioms Principia1713.Laws.corollary1_uniform_impulse_model
#print axioms DeMotu1684.Composition.natp00090_lemma1_endpoint_reconstruction
#print axioms ImpulseComposition.next_arrival_diagonal
end NewtonLimitDynamics.Polygon.CompositionControls
