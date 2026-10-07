import Reverse.Matter.NeutralMatter
import Reverse.NonRelativistic.KineticEnergy
import Reverse.NonRelativistic.VelocityComposition
import BarrowLib.Polygon.PointAlgebra

/-!
PHYSICAL STAGE:
  Relativistic quantum particle dynamics of stable composites: the
  low-energy, fixed-particle sector of the parent quantum field theory
  restricted to the neutral bodies. The chain is
    QFT → stable composite sector → relativistic quantum particle dynamics,
  so an interacting relativistic many-particle quantum mechanics is never
  taken as fundamental.
MATHEMATICAL CONTENT:
  The sector carries the fundamental parameters still containing ℏ and
  invC, for each body a kinetic-energy function satisfying the
  rest-subtracted dispersion relation at the sector's kappa = invC², and
  the collinear velocity-composition law at the same kappa.
INPUT PARAMETERS:
  ℏ, invC, G, effective masses of the neutral bodies.
OUTPUT PARAMETERS:
  Kinetic energy of each body as a function of coordinate momentum.
PROVED HERE:
  Nothing.
ASSUMED HERE:
  Each stable composite obeys E² = m²c⁴ + p²c² for its centre-of-mass
  motion, in the square-root-free form of `RestSubtractedDispersion`, and
  collinear velocities compose by the relativistic law in the relational
  form of `IsCollinearComposition`. Both are Poincaré kinematics taken as
  premises; deriving them from a boost law is the next kinematic step.
OPEN PROBLEMS USED:
  Existence of positive-mass stable sectors in an interacting QFT.
NEXT REDUCTION:
  `Reverse/NonRelativistic/ZeroInvCFibre.lean`.

STATUS: well-established physics, stated as an interface.
-/

namespace Reverse.RelativisticQM
open Reverse.Parent Reverse.Matter Reverse.NonRelativistic
open NewtonLimitDynamics NewtonLimitDynamics.Polygon.TimeSubdivision

/-- Squared magnitude of a coordinate momentum. -/
def normSq (p : Point) : Scalar :=
  Fraction.add (Fraction.mul p.1 p.1) (Fraction.mul p.2 p.2)

/-- Stable-particle sector over the neutral bodies, at fundamental
parameters `params`: the dispersion relation of each body and the collinear
velocity-composition law, both at kappa = invC². -/
structure StableParticleSector {I : MatterInputs} (M : HasStableNeutralMatter I) where
  params : FundamentalParameters
  kinetic : M.Body → Point → Scalar
  dispersion : ∀ b p, RestSubtractedDispersion params.kappa (M.body b).mass (normSq p)
    (kinetic b p)
  composeCollinear : Fraction → Fraction → Fraction
  compose_law : ∀ v w, Composition.IsCollinearComposition params.kappa v w
    (composeCollinear v w)

end Reverse.RelativisticQM
