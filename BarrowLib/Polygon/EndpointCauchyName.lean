import BarrowLib.Polygon.StateDistance

namespace NewtonLimitDynamics.Polygon.HarmonicDyadic
open NewtonLimitDynamics
open TimeSubdivision
open PointBounds
open HarmonicComparison

structure EndpointCauchyName where
  approx : Nat → Point × Point
  cauchy : ∀ eps : Fraction, 0 < eps.num →
    ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
      Fraction.lt (stateNorm (stateSub (approx m) (approx n))) eps

end NewtonLimitDynamics.Polygon.HarmonicDyadic
