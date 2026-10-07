import Reverse.Chain
import NewtonLimitDynamics.Historical.LawI
import NewtonLimitDynamics.Historical.LawII

/-!
PHYSICAL STAGE:
  The meeting point of the two routes. The Newton interface produced by the
  reverse chain satisfies the edition-local law predicates of the historical
  route, for each witness separately: NATP00090 (De Motu), 1687 and 1713.
MATHEMATICAL CONTENT:
  Each predicate's body is the corresponding interface field, so every
  bridge is an application; the chain corollary bundles them for the
  interface of `modern_to_newton`.
INPUT PARAMETERS:
  None beyond the chain's hypothesis list.
OUTPUT PARAMETERS:
  The `motion` and `update` arguments of the historical law predicates.
PROVED HERE:
  `lawI_1687`, `lawI_1713`, `lex1_NATP00090`, `lawII_1687`, `lawII_1713`,
  `lex2_NATP00090`, `modern_to_newton_laws`.
ASSUMED HERE:
  Nothing. The historical files are imported for their predicates only;
  no historical proof is re-derived or modified, and no historical file
  imports this one.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  Proposition I needs, in addition, the central impulse schedule consumed
  by `mechanicalCell`; producing it from the gravitational sector is the
  next stage of the reverse route.

STATUS: theorem (applications of definitions).
-/

namespace Reverse.Principia
open Reverse Reverse.Parent Reverse.KK Reverse.Strong Reverse.Matter Reverse.Classical
open Reverse.Newton

theorem lawI_1687 (N : NewtonInterface) : Principia1687.Laws.InertialMotion N.motion :=
  N.inertial

theorem lawI_1713 (N : NewtonInterface) : Principia1713.Laws.InertialMotion N.motion :=
  N.inertial

theorem lex1_NATP00090 (N : NewtonInterface) :
    DeMotu1684.NATP00090.Laws.InertialMotion N.motion :=
  fun p v t _ => N.inertial p v t

theorem lawII_1687 (N : NewtonInterface) : Principia1687.Laws.AdditiveImpulse N.update :=
  N.additive

theorem lawII_1713 (N : NewtonInterface) : Principia1713.Laws.AdditiveImpulse N.update :=
  N.additive

theorem lex2_NATP00090 (N : NewtonInterface) :
    DeMotu1684.NATP00090.Laws.CalibratedChange N.update :=
  calibrated_change N

/-- The interface produced by the reverse chain satisfies every edition's
law predicates. -/
theorem modern_to_newton_laws
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
    (b : hBound.Body) :
    let N := modern_to_newton F a hKK hWeak hΛ hGap hConf hNuc hElectron hBound hT hD hPV hJ b
    Principia1687.Laws.InertialMotion N.motion ∧ Principia1713.Laws.InertialMotion N.motion ∧
      DeMotu1684.NATP00090.Laws.InertialMotion N.motion ∧
      Principia1687.Laws.AdditiveImpulse N.update ∧ Principia1713.Laws.AdditiveImpulse N.update ∧
      DeMotu1684.NATP00090.Laws.CalibratedChange N.update :=
  ⟨lawI_1687 _, lawI_1713 _, lex1_NATP00090 _, lawII_1687 _, lawII_1713 _, lex2_NATP00090 _⟩

end Reverse.Principia
