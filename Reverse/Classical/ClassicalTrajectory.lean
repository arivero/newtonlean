import Reverse.Matter.NeutralMatter
import BarrowLib.Polygon.ZeroForce

/-!
PHYSICAL STAGE:
  Semiclassical centre-of-mass dynamics of the neutral bodies, decomposed
  into its ingredients. The relevant parameter is ε = ℏ / S_CM → 0 for the
  centre-of-mass action; microscopic ℏ stays as upstream, and internal
  quantum structure persists.
MATHEMATICAL CONTENT:
  Four interfaces, one assumption each:
  (1) `HasLocalizedCOMTrajectory`: a localized state defines one classical
      centre-of-mass trajectory per initial position and momentum, starting
      at the initial position and depending on the time value rather than
      on its rational representative.
  (2) `HasFreeCOMDynamics`: for free motion the momentum is conserved and
      the position advances, over any interval, by the interval times the
      velocity of the current momentum. This is Hamilton's equations for a
      conserved momentum in finite-increment form, exact for the quadratic
      free Hamiltonian; the Hamiltonian limit itself (commutator/iℏ →
      Poisson bracket, Wigner → Liouville, Ehrenfest, WKB) is what is
      assumed.
  (3) `HasMomentumVelocityRelation`: the velocity of the momentum m v is v,
      with the velocity map respecting value equivalence. On the fibre the
      kinetic energy is p²/(2m) (`kinetic_energy_on_fibre`) and its
      momentum derivative is p/m; the derivative step is unformalized, so
      the relation is an interface. `NewtonLaws.lean` proves the consistency
      K = ½ p · v with the fibre kinetic energy.
  (4) `HasImpulseDynamics`: an impulse changes the momentum additively,
      p⁺ = p⁻ + J.
  Commutativity of the classical observable algebra is presupposed by (1)
  and is not stated separately.
INPUT PARAMETERS:
  Effective masses of the bodies.
OUTPUT PARAMETERS:
  Position, momentum, velocity and kick maps on the shared coordinate model.
PROVED HERE:
  Nothing; `NewtonLaws.lean` derives the Law I and Law II shapes from
  (1)–(4).
ASSUMED HERE:
  (1)–(4). A generic quantum state satisfies none of (1); the time window
  and spreading control that make (1) hold are not modelled. None of the
  four consumes the zero-invC fibre formally; the link is the consistency
  theorem in `NewtonLaws.lean`.
OPEN PROBLEMS USED:
  None named; semiclassical analysis under hypotheses to be stated.
NEXT REDUCTION:
  `Reverse/Classical/NewtonLaws.lean`.

STATUS: effective-theory assumptions.
-/

namespace Reverse.Classical
open Reverse.Parent Reverse.Matter
open NewtonLimitDynamics NewtonLimitDynamics.Polygon NewtonLimitDynamics.Polygon.TimeSubdivision

variable {I : MatterInputs}

/-- (1) Localized centre-of-mass trajectories: position and momentum of a
body as functions of initial position, initial momentum and time. -/
structure HasLocalizedCOMTrajectory (M : HasStableNeutralMatter I) where
  position : M.Body → Point → Point → Fraction → Point
  momentum : M.Body → Point → Point → Fraction → Point
  position_initial : ∀ b q p, pointEquiv (position b q p (Fraction.ofInt 0)) q
  position_time_congr : ∀ b q p {t t' : Fraction}, Fraction.equiv t t' →
    pointEquiv (position b q p t) (position b q p t')

/-- (2) Free centre-of-mass dynamics: conserved momentum and uniform
increments at the velocity of the current momentum. -/
structure HasFreeCOMDynamics {M : HasStableNeutralMatter I}
    (T : HasLocalizedCOMTrajectory M) where
  velocity : M.Body → Point → Point
  momentum_conserved : ∀ b q p t, pointEquiv (T.momentum b q p t) p
  uniform_increment : ∀ b q p t s,
    pointEquiv (T.position b q p (Fraction.add t s))
      (pointAdd (T.position b q p t) (pointScale s (velocity b (T.momentum b q p t))))

/-- (3) Momentum–velocity relation p = m v, in the inverted form the
derivations use, with value-congruence of the velocity map. -/
structure HasMomentumVelocityRelation {M : HasStableNeutralMatter I}
    {T : HasLocalizedCOMTrajectory M} (D : HasFreeCOMDynamics T) where
  velocity_congr : ∀ b {p p' : Point}, pointEquiv p p' →
    pointEquiv (D.velocity b p) (D.velocity b p')
  velocity_of_momentum : ∀ b v,
    pointEquiv (D.velocity b (pointScale (M.body b).mass v)) v

/-- (4) Impulsive dynamics: an impulse adds to the momentum. -/
structure HasImpulseDynamics (M : HasStableNeutralMatter I) where
  kick : M.Body → Point → Point → Point
  momentum_additive : ∀ b p J, pointEquiv (kick b p J) (pointAdd p J)

end Reverse.Classical
