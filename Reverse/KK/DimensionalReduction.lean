import Reverse.Parent.QuantumKKFamily

/-!
PHYSICAL STAGE:
  Kaluza–Klein reduction of the parent to four-dimensional gravity plus gauge
  sectors. With the ansatz
    ds_D² = g_μν dx^μ dx^ν + h_ab (dy^a + K^a_A A^A_μ dx^μ)(dy^b + K^b_B A^B_ν dx^ν)
  the higher-dimensional curvature produces, schematically,
    R_D ⇝ R_4 − ¼ C_AB F^A_μν F^{B μν} + scalar/moduli terms + ⋯ .
  The gauge sector therefore arises from geometry; it is never postulated as
  an independent Yang–Mills action.
MATHEMATICAL CONTENT:
  Carriers for a gauge sector and for the reduced four-dimensional theory,
  and the reduction interface with its two classical identities as fields.
INPUT PARAMETERS:
  G_D, compactification radius, internal isometry algebra and volume.
OUTPUT PARAMETERS:
  G (four-dimensional), gauge algebra, massive mode scale, gauge couplings.
PROVED HERE:
  Nothing.
ASSUMED HERE:
  (1) The reduced gauge algebra equals the internal isometry algebra.
  (2) G · Vol(K) = G_D.
  (3) The massive KK tower decouples below `massiveModeScale`. This is
      distinct from the fate of the massless gauge zero modes, which survive
      a small radius; their removal is never assumed anywhere in Reverse/.
OPEN PROBLEMS USED:
  None. (1) and (2) are classical computations to be formalized later.
NEXT REDUCTION:
  `Reverse/KK/WeakSector.lean`.

STATUS: assumption below the cutoff (decoupling); formalizable classical
identities (gauge algebra, coupling relation) stated as interface fields.
-/

namespace Reverse.KK
open Reverse.Parent NewtonLimitDynamics

/-- One gauge sector of the reduced theory: its algebra factor, coupling,
and physical spectrum carrier with a distinguished vacuum, masses and three
separate predicates. `gaugeInvariant` is invariance under local gauge
transformations (Gauss law); `singlet` is triviality under the global group
of the factor, "colour singlet" for su(3) and "neutral" for u(1); a
gauge-invariant state can still carry global charge, so the two differ.
`asymptotic` marks states that appear as free particles at large distances.
The vacuum is separated so that a mass gap can leave it massless. -/
structure GaugeSector where
  factor : GaugeFactor
  coupling : Scalar
  Spectrum : Type
  vacuum : Spectrum
  mass : Spectrum → Scalar
  gaugeInvariant : Spectrum → Prop
  singlet : Spectrum → Prop
  asymptotic : Spectrum → Prop

/-- The four-dimensional output of a reduction: gravity with coupling `G`,
the gauge algebra by factor, the scale of the massive internal tower, and the
reduced quantum theory as an opaque carrier. -/
structure FourDimensionalSector where
  newtonCoupling : Scalar
  gaugeAlgebra : List GaugeFactor
  massiveModeScale : Scalar
  theory : QuantumTheory

/-- KK reduction interface. The two identities are the classical content of
the ansatz; the decoupling of the massive tower is an assumption below the
cutoff, made visible by the positive scale. -/
structure HasKKReduction (F : QuantumKKFamily) where
  reduce : F.Params → FourDimensionalSector
  gauge_from_isometries : ∀ a, (reduce a).gaugeAlgebra = F.internal.isometryAlgebra
  newton_from_volume : ∀ a, Fraction.equiv
    (Fraction.mul (reduce a).newtonCoupling
      (F.internal.volume (F.fundamental a).compactificationRadius))
    (F.fundamental a).gravitationalCoupling
  massive_scale_positive : ∀ a, Fraction.positive (reduce a).massiveModeScale

end Reverse.KK
