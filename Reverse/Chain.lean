import Reverse.Classical.SemiclassicalLimit

/-!
PHYSICAL STAGE:
  The whole chain, from the quantum Kaluza–Klein parent to the Newton
  interface, with every hypothesis explicit in the argument list.
MATHEMATICAL CONTENT:
  Composition of the stage interfaces. The computational content of
  `modern_to_newton` is the semiclassical stage's output; every earlier
  hypothesis enters through the types of the later ones, so the compiled
  dependency graph shows the full list.
INPUT PARAMETERS:
  The parent's fundamental parameters at the point `a`.
OUTPUT PARAMETERS:
  A `NewtonInterface`; invC = 0 on the fibre; ℏ and G carried unchanged to the
  fibre sector.
PROVED HERE:
  `modern_to_newton` (composition) and `modern_to_newton_kinetic` (each
  body's Newtonian kinetic energy on the fibre with its effective mass).
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

/-- The modern parent reduced to the Newton interface. Each argument is one
named physical or mathematical hypothesis; none is hidden in the parent. -/
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
    (S : StableParticleSector hBound)
    (_hparams : S.params = F.fundamental a)
    (hZ : HasZeroInvCFibre S)
    (hSC : HasSemiclassicalCOMLimit hZ) : NewtonInterface :=
  hSC.newtonInterface

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

end Reverse
