import Reverse.Strong.Confinement
import Reverse.Matter.ElectronSector

/-!
PHYSICAL STAGE:
  Formation of ordinary matter: nucleons and electrons bound
  electromagnetically into neutral composites, before any classical limit.
  Quantum mechanics is part of the mechanism that produces the objects whose
  centre-of-mass motion later becomes classical, so microscopic ℏ is untouched
  here.
MATHEMATICAL CONTENT:
  The bundle of matter inputs; a composite body carrier with constituent
  counts and effective mass; the net charge computed from the constituents'
  charges; the neutral matter interface; consequences.
INPUT PARAMETERS:
  Electromagnetic coupling (nonzero), nucleon and electron charges and
  masses, the mass gap, confinement.
OUTPUT PARAMETERS:
  Effective inertial masses and (zero) net charges of bodies.
PROVED HERE:
  `coulomb_leading_zero`: Q₁ Q₂ = 0 for neutral bodies, so the leading
    Coulomb interaction between distant neutral bodies vanishes while gravity
    may remain. Higher multipoles and macroscopic currents are outside this
    statement.
  `protons_need_electrons`: a neutral body containing a proton contains an
    electron, so neutral matter with protons requires the charged-lepton
    sector.
  `constituents_singlet`, `constituents_massive`: the constituents are colour
    singlets with positive masses, from confinement and the gap.
ASSUMED HERE:
  Existence of stable neutral composites with positive effective mass. The
  effective mass is the constituent mass minus binding energy; binding
  energies are not modelled, so `mass` stays a field with its positivity.
  `massGap` and `confinement` are consumed by the theorems above and not by
  the construction of the bodies: the absence of long-range colour forces
  that the gap should justify is not representable until spatial
  interactions are modelled.
OPEN PROBLEMS USED:
  Nuclear and atomic many-body theory, through the existence assumption.
NEXT REDUCTION:
  `Reverse/RelativisticQM/StableParticleSector.lean`.

STATUS: physical hypothesis (binding), formal consequences (charges,
singlets, masses).
-/

namespace Reverse.Matter
open Reverse.Parent Reverse.KK Reverse.Strong NewtonLimitDynamics

/-- Everything the matter sector takes from the stages above, by name. -/
structure MatterInputs where
  colour : GaugeSector
  electromagnetic : GaugeSector
  colour_factor : colour.factor = .su 3
  electromagnetic_factor : electromagnetic.factor = .u1
  electromagnetic_active : electromagnetic.coupling.num ≠ 0
  colourScale : HasColourScale colour
  massGap : HasMassGap colour
  confinement : HasConfinement colour
  nucleons : HasStableNucleons colour colourScale
  electron : HasStableElectronLikeState electromagnetic

/-- The matter inputs read off a weak decoupling together with the strong
and lepton hypotheses on its residual sectors. -/
def MatterInputs.ofWeakDecoupling {S : FourDimensionalSector} (W : HasWeakDecoupling S)
    (hΛ : HasColourScale W.colour) (hGap : HasMassGap W.colour)
    (hConf : HasConfinement W.colour) (hNuc : HasStableNucleons W.colour hΛ)
    (hElectron : HasStableElectronLikeState W.electromagnetic) : MatterInputs where
  colour := W.colour
  electromagnetic := W.electromagnetic
  colour_factor := W.colour_factor
  electromagnetic_factor := W.electromagnetic_factor
  electromagnetic_active := W.electromagnetic_active
  colourScale := hΛ
  massGap := hGap
  confinement := hConf
  nucleons := hNuc
  electron := hElectron

/-- A composite body as the long-distance sector sees it: constituent counts
and an effective inertial mass. The mass is an output of strong and
electromagnetic binding; the parent has no such parameter. -/
structure CompositeBody where
  protons : Nat
  neutrons : Nat
  electrons : Nat
  mass : Scalar
  mass_positive : Fraction.positive mass

/-- Net charge computed from the constituents and their charges. -/
def netCharge (I : MatterInputs) (B : CompositeBody) : Scalar :=
  Fraction.add
    (Fraction.add (Fraction.mul (Fraction.ofInt B.protons) I.nucleons.protonCharge)
      (Fraction.mul (Fraction.ofInt B.neutrons) I.nucleons.neutronCharge))
    (Fraction.mul (Fraction.ofInt B.electrons) I.electron.charge)

/-- Stable neutral composite matter. Neutrality is a condition on the
constituent counts relative to the charges supplied by the nucleon and
electron sectors. -/
structure HasStableNeutralMatter (I : MatterInputs) where
  Body : Type
  body : Body → CompositeBody
  neutral : ∀ b, (netCharge I (body b)).num = 0

/-- Leading Coulomb product between two neutral bodies vanishes. -/
theorem HasStableNeutralMatter.coulomb_leading_zero {I : MatterInputs}
    (M : HasStableNeutralMatter I) (b₁ b₂ : M.Body) :
    (Fraction.mul (netCharge I (M.body b₁)) (netCharge I (M.body b₂))).num = 0 := by
  show (netCharge I (M.body b₁)).num * (netCharge I (M.body b₂)).num = 0
  rw [M.neutral b₁, Int.zero_mul]

/-- A neutral body with a proton has an electron: neutral matter containing
protons requires the charged-lepton sector. -/
theorem HasStableNeutralMatter.protons_need_electrons {I : MatterInputs}
    (M : HasStableNeutralMatter I) (b : M.Body) (hZ : 0 < (M.body b).protons) :
    0 < (M.body b).electrons := by
  refine Nat.pos_of_ne_zero (fun hE0 => ?_)
  have h := M.neutral b
  simp only [netCharge, Fraction.add, Fraction.mul, Fraction.ofInt, hE0,
    I.nucleons.neutronCharge_zero, Int.natCast_zero, Int.mul_zero, Int.zero_mul,
    Int.mul_one, Int.one_mul, Int.add_zero, Int.zero_add] at h
  have hp : (0 : Int) < (M.body b).protons := Int.ofNat_pos.mpr hZ
  have hpos := Int.mul_pos (Int.mul_pos (Int.mul_pos hp I.nucleons.protonCharge_positive)
    I.nucleons.neutronCharge.den_pos) I.electron.charge.den_pos
  ac_nf at h hpos
  omega

/-- The constituents are colour singlets, from confinement. -/
theorem constituents_singlet (I : MatterInputs) :
    I.colour.singlet I.nucleons.proton.val ∧ I.colour.singlet I.nucleons.neutron.val :=
  I.nucleons.singlet I.confinement

/-- The constituents have positive masses, from the gap and the electron
hypothesis. -/
theorem constituents_massive (I : MatterInputs) :
    Fraction.positive (I.colour.mass I.nucleons.proton.val) ∧
      Fraction.positive (I.colour.mass I.nucleons.neutron.val) ∧
      Fraction.positive (I.electromagnetic.mass I.electron.electron) :=
  ⟨(I.nucleons.masses_positive I.massGap).1, (I.nucleons.masses_positive I.massGap).2,
    I.electron.mass_positive⟩

end Reverse.Matter
