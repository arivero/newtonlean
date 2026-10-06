import ModernLib.Foundation.Polygon.CauchyValues
import BarrowLib.Polygon.GeometricTail

/-! A shared closed-value bound from an actual name's adjacent geometric
estimate. Applications supply their derived finite estimate and coefficient. -/

namespace NewtonLimitDynamics.Polygon.TailValues
open NewtonLimitDynamics
open HarmonicDyadic CauchyValues FiniteEstimates

theorem approximant_bound (a : EndpointCauchyName) (A : Fraction) (hA : 0 ≤ A.num)
    (hadj : ∀ j, Fraction.le (distance (a.approx (j+1)) (a.approx j))
      (GeometricTail.tailCap A (j+1))) (m : Nat) :
    Within (embed (a.approx m)) (realize a) (GeometricTail.tailCap A m) := by
  apply nameBound_of_eventual_le _ _ _ m
  intro n hn
  have he : m+(n-m)=n := by omega
  have hb := GeometricTail.finite_gap a.approx A hA hadj (n-m) m
  rw [he] at hb
  exact Fraction.le_equiv_left (stateDistance_symm _ _) hb

end NewtonLimitDynamics.Polygon.TailValues
