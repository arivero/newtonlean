import Reverse.RelativisticQM.StableParticleSector

/-!
PHYSICAL STAGE:
  Nonrelativistic limit invC → 0 of the stable composite sector, and the
  Galilean kinematics that Newton's laws presuppose: common absolute time,
  Galilean velocity composition, uniform inertial motion.
MATHEMATICAL CONTENT:
  The fibre `invC = 0`, the limit interface carrying a sector on the fibre
  with ℏ and G unchanged, the Galilean structure on the shared coordinate
  model, and the derived Newtonian kinetic energy on the fibre.
INPUT PARAMETERS:
  invC, ℏ, G, body masses.
OUTPUT PARAMETERS:
  Absolute rational time and additive velocity composition; invC = 0.
PROVED HERE:
  `kinetic_energy_newtonian`: on the fibre every body's kinetic energy is
  p²/(2m), with m the effective composite mass.
ASSUMED HERE:
  The Galilean structure. It should follow from the Poincaré → Galilei
  contraction; until that contraction is formalized, additive velocity
  composition is an interface field, and so is the preservation of ℏ and G
  by the limit.
OPEN PROBLEMS USED:
  None. The contraction is textbook mathematics awaiting formalization.
NEXT REDUCTION:
  `Reverse/Classical/SemiclassicalLimit.lean`.

STATUS: theorem (kinetic energy); effective-theory assumption (Galilean
structure, parameter preservation).
-/

namespace Reverse.NonRelativistic
open Reverse.Parent Reverse.KK Reverse.Strong Reverse.Matter Reverse.RelativisticQM
open NewtonLimitDynamics NewtonLimitDynamics.Polygon.TimeSubdivision

/-- The nonrelativistic fibre: invC is exactly zero. -/
def OnFibre (P : FundamentalParameters) : Prop := P.invC.num = 0

/-- Galilean structure on the shared coordinate model: time is the rational
parameter of `Point → Point → Fraction → Point` maps, and velocities compose
additively. To be derived from the contraction in a later pass. -/
structure GalileanStructure where
  composeVelocity : Point → Point → Point
  compose_additive : ∀ u v, pointEquiv (composeVelocity u v) (pointAdd u v)

variable {C : GaugeSector} {hConf : HasConfinement C} {hΛ : HasColourScale C}
  {H : HadronSector C hConf hΛ} {hGap : HasMassGap C} {hNuc : HasStableNucleons H}
  {em : GaugeSector} {hem : em.factor = .u1} {hactive : em.coupling.num ≠ 0}
  {M : HasStableNeutralMatter hGap hNuc em hem hactive}

/-- Nonrelativistic limit of a stable-particle sector: a sector on the fibre
with ℏ and G unchanged, together with Galilean kinematics. -/
structure HasNonrelativisticLimit (S : StableParticleSector M) where
  limit : StableParticleSector M
  on_fibre : OnFibre limit.params
  hbar_preserved : limit.params.hbar = S.params.hbar
  gravity_preserved : limit.params.gravitationalCoupling = S.params.gravitationalCoupling
  galilean : GalileanStructure

/-- On the fibre each body's kinetic energy is Newtonian, with the effective
composite mass in the denominator. -/
theorem kinetic_energy_newtonian {S : StableParticleSector M}
    (L : HasNonrelativisticLimit S) (b : M.Body) (p : Point) :
    Fraction.equiv (L.limit.kinetic b p)
      (Fraction.quotient (normSq p) (twice (M.body b).mass)
        (twice_positive (M.body b).mass_positive)) := by
  have h0 : L.limit.params.invC.num = 0 := L.on_fibre
  have hu : (Fraction.mul L.limit.params.invC L.limit.params.invC).num = 0 := by
    show L.limit.params.invC.num * L.limit.params.invC.num = 0
    rw [h0, Int.zero_mul]
  exact kinetic_energy_at_zero_invC (M.body b).mass_positive hu (L.limit.dispersion b p)

end Reverse.NonRelativistic
