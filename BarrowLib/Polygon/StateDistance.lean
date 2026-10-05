import BarrowLib.Polygon.FiniteEstimates
import BarrowLib.Polygon.DyadicArithmetic

namespace NewtonLimitDynamics.Polygon.HarmonicComparison
open NewtonLimitDynamics
open TimeSubdivision
def stateSub (s t : Point × Point) : Point × Point :=
  (pointSub s.1 t.1, pointSub s.2 t.2)

end NewtonLimitDynamics.Polygon.HarmonicComparison

namespace NewtonLimitDynamics.Polygon.HarmonicDyadic
open NewtonLimitDynamics
open TimeSubdivision
open PointBounds
open HarmonicComparison
private theorem pointNeg_congr {p q : Point} (hp : pointEquiv p q) :
    pointEquiv (pointNeg p) (pointNeg q) :=
  ⟨neg_equiv hp.1, neg_equiv hp.2⟩

private theorem pointSub_congr {p p' q q' : Point}
    (hp : pointEquiv p p') (hq : pointEquiv q q') :
    pointEquiv (pointSub p q) (pointSub p' q') :=
  pointAdd_congr hp (pointNeg_congr hq)

theorem stateSub_congr {s s' t t' : Point × Point}
    (hs : stateEquiv s s') (ht : stateEquiv t t') :
    stateEquiv (stateSub s t) (stateSub s' t') :=
  ⟨pointSub_congr hs.1 ht.1, pointSub_congr hs.2 ht.2⟩

theorem stateSub_norm_symm (a b : Point × Point) :
    Fraction.equiv (stateNorm (stateSub a b)) (stateNorm (stateSub b a)) :=
  FiniteEstimates.stateDistance_symm a b

end NewtonLimitDynamics.Polygon.HarmonicDyadic

namespace NewtonLimitDynamics.Polygon.HarmonicAccumulation
open NewtonLimitDynamics
open TimeSubdivision
open PointBounds
open HarmonicComparison
open HarmonicDyadic
open FiniteEstimates
theorem stateSub_triangle (a b c : Point × Point) :
    Fraction.le (stateNorm (stateSub a c))
      (Fraction.add (stateNorm (stateSub a b)) (stateNorm (stateSub b c))) :=
  stateDistance_triangle a b c

theorem stateSub_self_norm_zero (s : Point × Point) :
    Fraction.equiv (stateNorm (stateSub s s)) (Fraction.ofInt 0) := stateDistance_self_zero s

end NewtonLimitDynamics.Polygon.HarmonicAccumulation
