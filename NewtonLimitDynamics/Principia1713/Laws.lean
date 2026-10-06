import NewtonLimitDynamics.Polygon.ImpulseComposition

/-! 1713 Laws Corollary 1, NATP00081 par7–8:
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par8.
This edition explicitly gives impulses at A, uniform separate motion,
`per Legem II` for unchanged transverse approach and `per Legem I` for the
diagonal rectilinear continuation. Those mechanical laws are the premises
of the finite rational impulse/uniform-motion model, not geometric theorems.
The two parallel constraints and their unique intersection are proved in the
shared elementary kernel. No premise from the 1687 proof is imported. -/

namespace Principia1713.Laws
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision Parallelogram

theorem corollary1_endpoint_reconstruction (p u v : Point) (t : Fraction)
    (h : (TimeSubdivision.det (pointScale t u) (pointScale t v)).num ≠ 0) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) := by
  have hl := ImpulseComposition.uniform_endpoint_lines p u v t
  exact ImpulseComposition.endpoint_from_components p (pointScale t u) (pointScale t v)
    (ZeroForce.inertialAt p (pointAdd u v) t) h hl.1 hl.2

/-- Separate impulses at A followed by Law I's uniform motion. The same
diagonal identity holds at every rational elapsed time, including degenerate
directions where the two-line uniqueness argument would not apply. -/
theorem corollary1_uniform_impulse_model (p u v : Point) (t : Fraction) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) ∧
    ParallelThrough (ZeroForce.inertialAt p (pointAdd u v) t)
      (ZeroForce.inertialAt p u t) (pointScale t v) ∧
    ParallelThrough (ZeroForce.inertialAt p (pointAdd u v) t)
      (ZeroForce.inertialAt p v t) (pointScale t u) :=
  ⟨ImpulseComposition.uniform_impulse_diagonal p u v t,
    ImpulseComposition.uniform_endpoint_lines p u v t⟩

end Principia1713.Laws
