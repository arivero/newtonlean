import Reverse.NonRelativistic.Limit
import Reverse.Newton.Interface

/-!
PHYSICAL STAGE:
  Semiclassical limit of the effective centre-of-mass theory of the neutral
  bodies. The relevant parameter is ε = ℏ / S_CM → 0 for the centre-of-mass
  action; microscopic ℏ stays as upstream (`hbar_preserved`), and internal
  quantum structure persists.
MATHEMATICAL CONTENT:
  The interface bundling the three distinct ingredients of a classical
  trajectory, and its composition into the shared Newton interface.
INPUT PARAMETERS:
  Galilean structure from the nonrelativistic limit, effective masses.
OUTPUT PARAMETERS:
  Drift and velocity-update maps in the Law I / Law II shapes.
PROVED HERE:
  `newtonInterface`: the composition into `NewtonInterface`, using the
  Galilean additive composition.
ASSUMED HERE:
  The interface merges, for now, three statements that a later pass must
  separate: (1) the observable algebra becomes commutative; (2) the quantum
  dynamics approaches Hamiltonian dynamics (Wigner → Liouville, commutator/iℏ
  → Poisson bracket, Ehrenfest, WKB are candidate routes); (3) a localised
  state defines a single trajectory over a stated time window with
  controlled spreading. A generic quantum state satisfies none of (3).
OPEN PROBLEMS USED:
  None named; semiclassical analysis under hypotheses to be stated.
NEXT REDUCTION:
  `Reverse/Chain.lean`, then `Reverse/Principia`.

STATUS: effective-theory assumption; the composition is a theorem.
-/

namespace Reverse.Classical
open Reverse.Parent Reverse.KK Reverse.Strong Reverse.Matter Reverse.RelativisticQM
open Reverse.NonRelativistic Reverse.Newton
open NewtonLimitDynamics NewtonLimitDynamics.Polygon NewtonLimitDynamics.Polygon.TimeSubdivision

variable {I : MatterInputs} {M : HasStableNeutralMatter I}

/-- Semiclassical centre-of-mass limit: classical drift and impulse update,
with the update additive in the Galilean composition of velocities. -/
structure HasSemiclassicalCOMLimit {S : StableParticleSector M}
    (L : HasNonrelativisticLimit S) where
  motion : Point → Point → Fraction → Point
  update : Point → Point → Point
  inertial : ∀ p v t, pointEquiv (motion p v t) (ZeroForce.inertialAt p v t)
  additive : ∀ u v, pointEquiv (update u v) (L.galilean.composeVelocity u v)

/-- The Newton interface produced by the semiclassical limit. -/
def HasSemiclassicalCOMLimit.newtonInterface {S : StableParticleSector M}
    {L : HasNonrelativisticLimit S} (hSC : HasSemiclassicalCOMLimit L) : NewtonInterface where
  motion := hSC.motion
  update := hSC.update
  inertial := hSC.inertial
  additive := fun u v => pointEquiv_trans (hSC.additive u v) (L.galilean.compose_additive u v)

end Reverse.Classical
