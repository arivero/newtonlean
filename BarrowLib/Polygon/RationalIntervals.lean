/-! Rational interval bisection, using core arithmetic. The definition below
records the midpoint operation; its order and gap identities are proved inline
at their uses. Core Rat encodes arithmetic, not historical availability.
Legacy callers keep their existing unreduced midpoint expression until their
domains migrate, and convert only arithmetic comparisons through the bridge.
-/
namespace NewtonLimitDynamics.Polygon.RationalIntervals

/-- The rational point halfway between two endpoints. -/
def midpoint (a b : Rat) : Rat := (a + b) / 2

end NewtonLimitDynamics.Polygon.RationalIntervals
