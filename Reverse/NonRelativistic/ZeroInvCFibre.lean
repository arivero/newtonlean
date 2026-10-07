import Reverse.RelativisticQM.StableParticleSector

/-!
PHYSICAL STAGE:
  The zero-invC fibre of the stable composite sector: the candidate
  nonrelativistic sector, obtained by evaluating the parameterized
  kinematics at invC = 0 with ℏ and G unchanged.
MATHEMATICAL CONTENT:
  The fibre interface and the theorems that hold on it. Evaluation on the
  fibre is distinguished from a limiting process: nothing here says that a
  family of finite-c sectors converges to the fibre as invC → 0. The defect
  identities in `KineticEnergy.lean` and `VelocityComposition.lean` bound
  how far a finite-kappa relation is from its fibre value; turning them into
  a convergence statement is future work, and until then this file is a
  fibre, under that name.
INPUT PARAMETERS:
  invC, ℏ, G, body masses.
OUTPUT PARAMETERS:
  A sector with invC = 0, hence kappa = 0.
PROVED HERE:
  `kinetic_energy_on_fibre`: on the fibre every body's kinetic energy is
  p²/(2m), with m the effective composite mass.
  `collinear_velocity_additive_on_fibre`: on the fibre the sector's
  collinear velocity composition is v + w.
ASSUMED HERE:
  Existence of the fibre sector with ℏ and G unchanged. Galilean kinematics
  is no longer part of this interface; the remaining kinematic and
  dynamical assumptions live in `Reverse/Classical`.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/Classical`.

STATUS: theorem (kinetic energy); effective-theory assumption (fibre sector
with parameter preservation).
-/

namespace Reverse.NonRelativistic
open Reverse.Parent Reverse.Matter Reverse.RelativisticQM
open NewtonLimitDynamics NewtonLimitDynamics.Polygon.TimeSubdivision

/-- The zero-invC fibre: invC is exactly zero. -/
def OnFibre (P : FundamentalParameters) : Prop := P.invC.num = 0

theorem OnFibre.kappa_zero {P : FundamentalParameters} (h : OnFibre P) : P.kappa.num = 0 := by
  have h0 : P.invC.num = 0 := h
  show P.invC.num * P.invC.num = 0
  rw [h0, Int.zero_mul]

variable {I : MatterInputs} {M : HasStableNeutralMatter I}

/-- Zero-invC fibre of a stable-particle sector: a sector on the fibre with
ℏ and G unchanged. This is evaluation at invC = 0, not a limit statement. -/
structure HasZeroInvCFibre (S : StableParticleSector M) where
  fibre : StableParticleSector M
  on_fibre : OnFibre fibre.params
  hbar_preserved : fibre.params.hbar = S.params.hbar
  gravity_preserved : fibre.params.gravitationalCoupling = S.params.gravitationalCoupling

/-- On the fibre each body's kinetic energy is Newtonian, with the effective
composite mass in the denominator. -/
theorem kinetic_energy_on_fibre {S : StableParticleSector M}
    (Z : HasZeroInvCFibre S) (b : M.Body) (p : Point) :
    Fraction.equiv (Z.fibre.kinetic b p)
      (Fraction.quotient (normSq p) (twice (M.body b).mass)
        (twice_positive (M.body b).mass_positive)) :=
  kinetic_energy_at_zero_invC (M.body b).mass_positive Z.on_fibre.kappa_zero
    (Z.fibre.dispersion b p)

/-- On the fibre the sector's collinear velocity composition is Galilean. -/
theorem collinear_velocity_additive_on_fibre {S : StableParticleSector M}
    (Z : HasZeroInvCFibre S) (v w : Fraction) :
    Fraction.equiv (Z.fibre.composeCollinear v w) (Fraction.add v w) :=
  Composition.galilean_fibre Z.on_fibre.kappa_zero (Z.fibre.compose_law v w)

end Reverse.NonRelativistic
