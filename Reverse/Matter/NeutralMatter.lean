import Reverse.Strong.Confinement

/-!
PHYSICAL STAGE:
  Formation of ordinary matter: nucleons and electrons bound
  electromagnetically into neutral composites, before any classical limit.
  Quantum mechanics is part of the mechanism that produces the objects whose
  centre-of-mass motion later becomes classical, so microscopic ℏ is untouched
  here.
MATHEMATICAL CONTENT:
  A composite body carrier with effective mass and net charge, the neutral
  matter interface, and the leading-order vanishing of the Coulomb product
  between neutral bodies.
INPUT PARAMETERS:
  Electromagnetic coupling (nonzero), hadron masses, the mass gap.
OUTPUT PARAMETERS:
  Effective inertial masses and net charges of bodies.
PROVED HERE:
  `coulomb_leading_zero`: Q₁ Q₂ = 0 for neutral bodies, so the leading
  Coulomb interaction between distant neutral bodies vanishes while gravity
  may remain. Higher multipoles and macroscopic currents are outside this
  statement.
ASSUMED HERE:
  Existence of stable neutral composites with positive effective mass. Their
  type depends on the mass gap (absence of long-range colour forces), on the
  nucleon hypothesis and on an active u(1) sector, so every downstream use
  carries those dependencies visibly.
OPEN PROBLEMS USED:
  Nuclear and atomic many-body theory, through the existence assumption.
NEXT REDUCTION:
  `Reverse/RelativisticQM/StableParticleSector.lean`.

STATUS: physical hypothesis (binding), formal consequence (Coulomb product).
-/

namespace Reverse.Matter
open Reverse.Parent Reverse.KK Reverse.Strong NewtonLimitDynamics

/-- A composite body as the long-distance sector sees it: effective inertial
mass and net charge. The mass is an output of strong and electromagnetic
binding; the parent has no such parameter. -/
structure CompositeBody where
  mass : Scalar
  mass_positive : Fraction.positive mass
  netCharge : Scalar

/-- Net charge zero. Multipole and current data are separate conditions. -/
def CompositeBody.Neutral (B : CompositeBody) : Prop := B.netCharge.num = 0

/-- Stable neutral composite matter. The explicit parameters are the physical
prerequisites of the construction, carried in the type. -/
structure HasStableNeutralMatter {C : GaugeSector} {hConf : HasConfinement C}
    {hΛ : HasColourScale C} {H : HadronSector C hConf hΛ}
    (hGap : HasMassGap C) (hNuc : HasStableNucleons H)
    (em : GaugeSector) (hem : em.factor = .u1) (hactive : em.coupling.num ≠ 0) where
  Body : Type
  body : Body → CompositeBody
  neutral : ∀ b, (body b).Neutral

/-- Leading Coulomb product between two neutral bodies vanishes. -/
theorem HasStableNeutralMatter.coulomb_leading_zero {C : GaugeSector}
    {hConf : HasConfinement C} {hΛ : HasColourScale C} {H : HadronSector C hConf hΛ}
    {hGap : HasMassGap C} {hNuc : HasStableNucleons H} {em : GaugeSector}
    {hem : em.factor = .u1} {hactive : em.coupling.num ≠ 0}
    (M : HasStableNeutralMatter hGap hNuc em hem hactive) (b₁ b₂ : M.Body) :
    (Fraction.mul (M.body b₁).netCharge (M.body b₂).netCharge).num = 0 := by
  have h : (M.body b₁).netCharge.num = 0 := M.neutral b₁
  show (M.body b₁).netCharge.num * (M.body b₂).netCharge.num = 0
  rw [h, Int.zero_mul]

end Reverse.Matter
