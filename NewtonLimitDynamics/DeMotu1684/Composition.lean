import NewtonLimitDynamics.Polygon.ImpulseComposition

/-! De Motu composition witnesses remain distinct. NATP00090 par10–11 has
Lemma 1 and the unchanged-transverse-approach/intersection proof:
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par11.
Its Law 2 citation is a marked addition, not a resolved chronology. NATP00089
par7 states the simultaneous/successive-force assertion as a hypothesis;
par9's altered marginal labels do not license inventing a proof there:
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par7.
The latter theorem is only a modern finite use of additive impulse motion.
Neither witness inherits the printed limiting lemmas or the 1713 wording. -/

namespace DeMotu1684.Composition
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision Parallelogram

theorem natp00090_lemma1_endpoint_reconstruction (p u v : Point) (t : Fraction)
    (h : (TimeSubdivision.det (pointScale t u) (pointScale t v)).num ≠ 0) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) := by
  have hl := ImpulseComposition.uniform_endpoint_lines p u v t
  exact ImpulseComposition.endpoint_from_components p (pointScale t u) (pointScale t v)
    (ZeroForce.inertialAt p (pointAdd u v) t) h hl.1 hl.2

/-- A model consequence of the composition hypothesis, not a historical
proof of NATP00089's hypothesis or an import of NATP00090's Lemma 1. -/
theorem natp00089_composition_model (p u v : Point) (t : Fraction) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) :=
  ImpulseComposition.uniform_impulse_diagonal p u v t

end DeMotu1684.Composition
