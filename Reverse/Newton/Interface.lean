import BarrowLib.Polygon.ZeroForce

/-!
PHYSICAL STAGE:
  Shared Newtonian endpoint: the kinematic and impulse premises in the exact
  shape consumed by the historical Law I and Law II files.
MATHEMATICAL CONTENT:
  A structure over BarrowLib's rational coordinate model: a drift map and a
  velocity update, each equivalent to the Barrow-level affine and additive
  maps. Time and magnitudes are `Fraction`; positions, velocities and
  calibrated impulses are `Point`.
INPUT PARAMETERS:
  None. Mass has already been absorbed into the calibrated impulse.
OUTPUT PARAMETERS:
  `motion` and `update`, the arguments of `Principia1687.Laws.InertialMotion`,
  `Principia1713.Laws.InertialMotion`, `Principia1687.Laws.AdditiveImpulse`,
  `Principia1713.Laws.AdditiveImpulse`, `DeMotu1684.NATP00090.Laws.InertialMotion`
  and `DeMotu1684.NATP00090.Laws.CalibratedChange`.
PROVED HERE:
  The canonical model inhabits the interface, so the target is consistent;
  the NATP00090 calibrated-change and nonnegative-time shapes follow from the
  printed-edition shapes.
ASSUMED HERE:
  Nothing. This file states the target and derives nothing physical.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/Classical` must produce a `NewtonInterface` from the semiclassical
  centre-of-mass limit; `Reverse/Principia` will apply the edition-local
  historical theorems to its fields. The central force schedule consumed by
  the Proposition I cells is a separate input, to be produced from the
  gravitational sector later.

STATUS: theorem (consistency and the two derived shapes); definitions otherwise.
-/

namespace Reverse.Newton
open NewtonLimitDynamics NewtonLimitDynamics.Polygon NewtonLimitDynamics.Polygon.TimeSubdivision

/-- The Newtonian data consumed by the historical route. `inertial` is the
body of the 1687/1713 `InertialMotion` predicate and `additive` the body of
the 1687/1713 `AdditiveImpulse` predicate. Nothing here mentions a force law,
a mass parameter or a trajectory existence claim. -/
structure NewtonInterface where
  motion : Point → Point → Fraction → Point
  update : Point → Point → Point
  inertial : ∀ p v t, pointEquiv (motion p v t) (ZeroForce.inertialAt p v t)
  additive : ∀ u v, pointEquiv (update u v) (pointAdd u v)

/-- The Barrow-level model itself satisfies the interface, so the target is
inhabited. The reverse chain's task is to reach it from the modern parent. -/
def canonical : NewtonInterface where
  motion := ZeroForce.inertialAt
  update := pointAdd
  inertial := fun _ _ _ => ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩
  additive := fun _ _ => ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩

/-- NATP00090 Lex 2 shape: the outgoing minus incoming velocity is the
calibrated impulse. Derived from the additive shape. -/
theorem calibrated_change (N : NewtonInterface) (v j : Point) :
    pointEquiv (pointSub (N.update v j) v) j :=
  pointEquiv_trans
    (pointSub_congr (N.additive v j) ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩)
    (pointSub_add_self_left_equiv v j)

/-- NATP00090 Lex 1 shape: inertia for nonnegative elapsed times, a
restriction of the unrestricted printed-edition shape. -/
theorem inertial_nonnegative (N : NewtonInterface) (p v : Point) (t : Fraction)
    (_ : 0 ≤ t.num) : pointEquiv (N.motion p v t) (ZeroForce.inertialAt p v t) :=
  N.inertial p v t

end Reverse.Newton
