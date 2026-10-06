import BarrowLib.Polygon.TimeSubdivision

namespace NewtonLimitDynamics.Polygon.ZeroForce

open NewtonLimitDynamics
open TimeSubdivision

/-- The zero impressed acceleration used in the finite end-kick recurrence. -/
def zeroPoint : Point := (Fraction.ofInt 0, Fraction.ofInt 0)

/-- The rational-time affine map for an inertial state. Agreement with the
    actual finite recurrence is proved in `partitionMotion_zero_force`. -/
def inertialAt (p v : Point) (t : Fraction) : Point :=
  pointAdd p (pointScale t v)

end NewtonLimitDynamics.Polygon.ZeroForce
