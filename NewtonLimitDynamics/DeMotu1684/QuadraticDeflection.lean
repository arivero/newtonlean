import NewtonLimitDynamics.Common.Quadratic

namespace DeMotu1684
open NewtonLimitDynamics

/-- ratio denotes the geometrically constructed deflection/time-square ratio.
    Its construction is a separate obligation. First-state numbering unverified. -/
def QuadraticInitialDeflection {Q : Type} (g : Magnitudes Q)
    (ratio : Q → Q) (coefficient : Q) : Prop :=
  g.positive coefficient ∧ Ultimate g ratio coefficient

end DeMotu1684
