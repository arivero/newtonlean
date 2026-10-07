import Reverse.Classical.NewtonLaws

/-!
PHYSICAL STAGE:
  The whole chain, from the quantum Kaluza–Klein parent to the Newton
  interface, with every hypothesis explicit in the argument list.
MATHEMATICAL CONTENT:
  Composition of the stage interfaces. The computational content of
  `modern_to_newton` is the derivation of the Law shapes from the
  centre-of-mass assumptions; every earlier hypothesis enters through the
  types of the later ones, so the compiled dependency graph shows the full
  list. The relativistic sector and the zero-invC fibre are consumed by the
  kinetic-energy and consistency theorems, and by nothing in the Law-shape
  construction: that gap is recorded in the README as the next derivation.
INPUT PARAMETERS:
  The parent's fundamental parameters at the point `a`.
OUTPUT PARAMETERS:
  A `NewtonInterface`; invC = 0 on the fibre; ℏ and G carried unchanged to the
  fibre sector.
PROVED HERE:
  `modern_to_newton` (composition), `modern_to_newton_kinetic` (each body's
  Newtonian kinetic energy on the fibre with its effective mass),
  `modern_to_newton_velocity_addition` (collinear velocity composition is
  v + w on the fibre) and `modern_to_newton_velocity_consistent`
  (K = ½ p · v on the fibre).
ASSUMED HERE:
  Everything listed in the argument list; see each stage's header.
OPEN PROBLEMS USED:
  Mass gap, confinement, through `hGap` and `hConf` inside the matter
  inputs.
NEXT REDUCTION:
  `Reverse/Principia`: apply the edition-local historical theorems to the
  output, once the law files are committed.

STATUS: formal consequence of assumptions.
-/

namespace Reverse
open Reverse.Parent Reverse.KK Reverse.Strong Reverse.Matter Reverse.RelativisticQM
open Reverse.NonRelativistic Reverse.Classical Reverse.Newton
open NewtonLimitDynamics NewtonLimitDynamics.Polygon.TimeSubdivision

/-- The modern parent reduced to the Newton interface of one neutral body.
Each argument is one named physical or mathematical hypothesis; none is
hidden in the parent. The zero-invC fibre is absent from this list: the
Law I / Law II shapes follow from the centre-of-mass assumptions (1)–(4)
stated on the bodies, and the fibre enters through the theorems below. -/
def modern_to_newton
    (F : QuantumKKFamily) (a : F.Params)
    (hKK : HasKKReduction F)
    (hWeak : HasWeakDecoupling (hKK.reduce a))
    (hΛ : HasColourScale hWeak.colour)
    (hGap : HasMassGap hWeak.colour)
    (hConf : HasConfinement hWeak.colour)
    (hNuc : HasStableNucleons hWeak.colour hΛ)
    (hElectron : HasStableElectronLikeState hWeak.electromagnetic)
    (hBound : HasStableNeutralMatter
      (MatterInputs.ofWeakDecoupling hWeak hΛ hGap hConf hNuc hElectron))
    (hT : HasLocalizedCOMTrajectory hBound)
    (hD : HasFreeCOMDynamics hT)
    (hPV : HasMomentumVelocityRelation hD)
    (hJ : HasImpulseDynamics hBound)
    (b : hBound.Body) : NewtonInterface :=
  Classical.newtonInterface hPV hJ b

/-- On the zero-invC fibre, each neutral body's kinetic energy is Newtonian
with the effective composite mass, which the parent never contained as a
parameter. -/
theorem modern_to_newton_kinetic
    (F : QuantumKKFamily) (a : F.Params)
    (hKK : HasKKReduction F)
    (hWeak : HasWeakDecoupling (hKK.reduce a))
    (hΛ : HasColourScale hWeak.colour)
    (hGap : HasMassGap hWeak.colour)
    (hConf : HasConfinement hWeak.colour)
    (hNuc : HasStableNucleons hWeak.colour hΛ)
    (hElectron : HasStableElectronLikeState hWeak.electromagnetic)
    (hBound : HasStableNeutralMatter
      (MatterInputs.ofWeakDecoupling hWeak hΛ hGap hConf hNuc hElectron))
    (S : StableParticleSector hBound)
    (_hparams : S.params = F.fundamental a)
    (hZ : HasZeroInvCFibre S) (b : hBound.Body) (p : Point) :
    Fraction.equiv (hZ.fibre.kinetic b p)
      (Fraction.quotient (normSq p) (twice (hBound.body b).mass)
        (twice_positive (hBound.body b).mass_positive)) :=
  kinetic_energy_on_fibre hZ b p

/-- On the zero-invC fibre the sector's collinear velocity composition is
Galilean: v ⊕ w = v + w. -/
theorem modern_to_newton_velocity_addition
    (F : QuantumKKFamily) (a : F.Params)
    (hKK : HasKKReduction F)
    (hWeak : HasWeakDecoupling (hKK.reduce a))
    (hΛ : HasColourScale hWeak.colour)
    (hGap : HasMassGap hWeak.colour)
    (hConf : HasConfinement hWeak.colour)
    (hNuc : HasStableNucleons hWeak.colour hΛ)
    (hElectron : HasStableElectronLikeState hWeak.electromagnetic)
    (hBound : HasStableNeutralMatter
      (MatterInputs.ofWeakDecoupling hWeak hΛ hGap hConf hNuc hElectron))
    (S : StableParticleSector hBound)
    (_hparams : S.params = F.fundamental a)
    (hZ : HasZeroInvCFibre S) (v w : Fraction) :
    Fraction.equiv (hZ.fibre.composeCollinear v w) (Fraction.add v w) :=
  collinear_velocity_additive_on_fibre hZ v w

/-- The classical velocity relation used for the Law shapes agrees with the
fibre kinetic energy: K = ½ p · v. This is the formal link between the
nonrelativistic reduction and the centre-of-mass assumptions. -/
theorem modern_to_newton_velocity_consistent
    (F : QuantumKKFamily) (a : F.Params)
    (hKK : HasKKReduction F)
    (hWeak : HasWeakDecoupling (hKK.reduce a))
    (hΛ : HasColourScale hWeak.colour)
    (hGap : HasMassGap hWeak.colour)
    (hConf : HasConfinement hWeak.colour)
    (hNuc : HasStableNucleons hWeak.colour hΛ)
    (hElectron : HasStableElectronLikeState hWeak.electromagnetic)
    (hBound : HasStableNeutralMatter
      (MatterInputs.ofWeakDecoupling hWeak hΛ hGap hConf hNuc hElectron))
    (S : StableParticleSector hBound)
    (_hparams : S.params = F.fundamental a)
    (hZ : HasZeroInvCFibre S)
    (hT : HasLocalizedCOMTrajectory hBound)
    (hD : HasFreeCOMDynamics hT)
    (hPV : HasMomentumVelocityRelation hD)
    (b : hBound.Body) (p : Point) :
    Fraction.equiv (hZ.fibre.kinetic b p) (Fraction.half (dot p (hD.velocity b p))) :=
  kinetic_half_momentum_velocity hZ hPV b p

end Reverse
