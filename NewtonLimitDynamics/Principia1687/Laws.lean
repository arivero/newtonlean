import NewtonLimitDynamics.Polygon.ImpulseComposition

/-! 1687 Laws Corollary 1, NATP00076 par7–8:
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par8.
The proof keeps the transverse approach unchanged and locates the body at the
intersection of BD and CD. Unlike 1713 it does not explicitly cite Laws II/I
here, or explicitly specify initial impulses and subsequent uniform motion.
The first result reconstructs that finite geometric inference; the second
is a rational uniform-impulse specialization using the stated mechanical
model, not a claim that the additional clauses occur in the 1687 text. -/

namespace Principia1687.Laws
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision Parallelogram

theorem corollary1_endpoint_reconstruction (p u v : Point) (t : Fraction)
    (h : (TimeSubdivision.det (pointScale t u) (pointScale t v)).num ≠ 0) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) := by
  have hl := ImpulseComposition.uniform_endpoint_lines p u v t
  exact ImpulseComposition.endpoint_from_components p (pointScale t u) (pointScale t v)
    (ZeroForce.inertialAt p (pointAdd u v) t) h hl.1 hl.2

/-- Modern rational specialization, with additive impulse changes and
uniform subsequent motion supplied by the finite mechanical model. -/
theorem corollary1_uniform_impulse_model (p u v : Point) (t : Fraction) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) :=
  ImpulseComposition.uniform_impulse_diagonal p u v t

end Principia1687.Laws
