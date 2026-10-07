import BarrowLib.Polygon.QuadraticEstimates
import ModernLib.Foundation.Polygon.CauchyValues
import ModernLib.Foundation.Polygon.PositionValues
import BarrowLib.Polygon.GeometricTail

/-! Actual centre-at-infinity polygon endpoints converge to the explicit
quadratic state at every nonnegative rational time. Cauchy names are derived
from the finite half-mesh error, with no supplied curve or small window. -/

namespace NewtonLimitDynamics.Polygon.ParallelQuadraticEndpoint
open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates BoundedIteration KinematicEstimates QuadraticEstimates
open HarmonicDyadic HarmonicTimeRealization CauchyValues PositionValues

def endpoint (a : Point) (T : Fraction) (s : Point × Point) (j : Nat) : Point × Point :=
  run (fun _ => a) (duration T j) s (blocks j)

def quadraticState (a : Point) (T : Fraction) (s : Point × Point) : Point × Point :=
  (quadraticPosition T s a,pointAdd s.2 (pointScale T a))

def coefficient (a : Point) (T : Fraction) : Fraction :=
  Fraction.mul (Fraction.mul T T).half (pointNorm a)

-- Modern dependency score: 0/3 (M=0, H=3; transitive project theorems/axioms).
theorem coefficient_nonnegative (a : Point) (T : Fraction) (hT : 0 ≤ T.num) :
    0 ≤ (coefficient a T).num :=
  Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hT hT) (pointNorm_nonnegative a)

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem full_elapsed (T : Fraction) (j : Nat) :
    Fraction.equiv (time (duration T j) (blocks j)) T := by
  simp [time,duration,blocks,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_pow]
  ac_nf

/-- The exact finite error has only the position half-mesh term. -/
-- Modern dependency score: 1/42 (M=1, H=41; transitive project theorems/axioms).
theorem endpoint_error (a : Point) (T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (j : Nat) :
    Fraction.equiv (distance (endpoint a T s j) (quadraticState a T s))
      (duration (coefficient a T) j) := by
  have hc := constant_run_formula a (duration T j) s (blocks j)
  have he := full_elapsed T j
  have hp := Fraction.equiv_trans
    (pointDistance_equiv hc.1 (pointEquiv_symm (quadratic_time_congr _ T s a he)))
    (half_mesh_bias (duration T j) s a hT (blocks j))
  have hv : pointEquiv (endpoint a T s j).2 (quadraticState a T s).2 :=
    pointEquiv_trans hc.2 (pointAdd_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
      (pointScale_ratio_congr he ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩))
  have hzero := Fraction.equiv_trans
    (pointDistance_equiv hv ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
    (pointDistance_self_zero (quadraticState a T s).2)
  apply Fraction.equiv_trans (Fraction.add_equiv hp hzero)
  apply Fraction.equiv_trans (Fraction.add_zero _)
  apply Fraction.equiv_trans
    (Fraction.mul_equiv (RationalIntervals.half_equiv
      (Fraction.mul_equiv he (Fraction.equiv_refl _))) (Fraction.equiv_refl _))
  simp only [coefficient,duration,Fraction.equiv,Fraction.mul,Fraction.half]
  ac_nf

def endpointName (a : Point) (T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num) :
    EndpointCauchyName where
  approx := endpoint a T s
  cauchy := by
    intro eps heps
    obtain ⟨N,hN⟩ := duration_eventually_small (coefficient a T) eps.half
      (coefficient_nonnegative a T hT) heps
    refine ⟨N,fun m n hm hn => ?_⟩
    have ha := Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv (endpoint_error a T s hT m)) (hN m hm)
    have hb := Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (Fraction.equiv_trans (stateDistance_symm _ _) (endpoint_error a T s hT n))) (hN n hn)
    exact Fraction.magnitudes.lt_of_le_lt (stateDistance_triangle _ (quadraticState a T s) _)
      (Fraction.magnitudes.lt_of_lt_le (Fraction.add_lt_add ha hb) (Fraction.le_of_equiv (Fraction.half_add_self eps)))

def endpointValue (a : Point) (T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num) : Value :=
  realize (endpointName a T s hT)

-- Modern dependency score: 10/78 (M=10, H=68; transitive project theorems/axioms).
theorem endpointValue_eq (a : Point) (T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num) :
    endpointValue a T s hT = embed (quadraticState a T s) := by
  apply Quotient.sound
  intro eps heps
  obtain ⟨N,hN⟩ := duration_eventually_small (coefficient a T) eps
    (coefficient_nonnegative a T hT) heps
  exact ⟨N,fun n hn => Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (endpoint_error a T s hT n)) (hN n hn)⟩

end NewtonLimitDynamics.Polygon.ParallelQuadraticEndpoint
