import Reverse.Matter.NeutralMatter
import Reverse.NonRelativistic.KineticEnergy
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
  invC, and for each body a kinetic-energy function satisfying the
  rest-subtracted dispersion relation at the sector's invC.
INPUT PARAMETERS:
  ℏ, invC, G, effective masses of the neutral bodies.
OUTPUT PARAMETERS:
  Kinetic energy of each body as a function of coordinate momentum.
PROVED HERE:
  Nothing.
ASSUMED HERE:
  Each stable composite obeys E² = m²c⁴ + p²c² for its centre-of-mass
  motion, in the square-root-free form of `RestSubtractedDispersion`. This
  is Poincaré kinematics of a positive-mass state, taken as a premise.
OPEN PROBLEMS USED:
  Existence of positive-mass stable sectors in an interacting QFT.
NEXT REDUCTION:
  `Reverse/NonRelativistic/Limit.lean`.

STATUS: well-established physics, stated as an interface.
-/

namespace Reverse.RelativisticQM
open Reverse.Parent Reverse.KK Reverse.Strong Reverse.Matter Reverse.NonRelativistic
open NewtonLimitDynamics NewtonLimitDynamics.Polygon.TimeSubdivision

/-- Squared magnitude of a coordinate momentum. -/
def normSq (p : Point) : Scalar :=
  Fraction.add (Fraction.mul p.1 p.1) (Fraction.mul p.2 p.2)

variable {C : GaugeSector} {hConf : HasConfinement C} {hΛ : HasColourScale C}
  {H : HadronSector C hConf hΛ} {hGap : HasMassGap C} {hNuc : HasStableNucleons H}
  {em : GaugeSector} {hem : em.factor = .u1} {hactive : em.coupling.num ≠ 0}

/-- Stable-particle sector over the neutral bodies, at fundamental
parameters `params`. -/
structure StableParticleSector (M : HasStableNeutralMatter hGap hNuc em hem hactive) where
  params : FundamentalParameters
  kinetic : M.Body → Point → Scalar
  dispersion : ∀ b p, RestSubtractedDispersion (Fraction.mul params.invC params.invC)
    (M.body b).mass (normSq p) (kinetic b p)

end Reverse.RelativisticQM
