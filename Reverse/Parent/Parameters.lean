import BarrowLib.Common.RationalMagnitudes

/-!
PHYSICAL STAGE:
  Parameter vocabulary for the whole reverse chain.
MATHEMATICAL CONTENT:
  Names for the modern parameters whose fate the reduction must decide, the
  possible fates, the scalar type used wherever the formalization manipulates
  a parameter, and the fundamental dimensionful parameters of the parent.
INPUT PARAMETERS:
  None.
OUTPUT PARAMETERS:
  `FundamentalParameters` (ℏ, invC, G_D, compactification radius, Λ).
PROVED HERE:
  Nothing.
ASSUMED HERE:
  Nothing. `currentFate` is a record of what later files establish.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/Parent/QuantumKKFamily.lean` attaches these parameters to a
  quantum family.

STATUS: definitions.
-/

namespace Reverse.Parent

/-- Scalar used for the parameters the formalization manipulates: the shared
interface's unnormalised signed rationals. Lean core has no real field, and
the fibre `invC = 0` is exact here. Irrational constants enter only through
the algebraic relations they satisfy, never through a decimal value. -/
abbrev Scalar := NewtonLimitDynamics.Fraction

/-- Gauge factors named at the algebra level. The global group form (SU(3)
against PSU(3), for example) is deliberately absent from this datum; only
the Lie algebra is fixed by Kaluza–Klein isometries. -/
inductive GaugeFactor
  | su (n : Nat)
  | u1
  deriving DecidableEq, Repr

/-- Modern parameters tracked by the programme. Each must eventually be
classified by a `Fate`; the classification is part of the result. -/
inductive ParameterName
  | hbar
  | invC
  /-- G_D before reduction, G after it. -/
  | gravitationalCoupling
  | cosmologicalConstant
  | compactificationRadius
  | gaugeCoupling (factor : GaugeFactor)
  | electromagneticCoupling
  | fermiCoupling
  | weakMixing
  | yukawa
  | symmetryBreakingScale
  /-- Λ_colour, produced by dimensional transmutation rather than present
  in the parent. -/
  | colourScale
  | particleMass
  | charge
  deriving DecidableEq, Repr

/-- What can happen to a parameter along the chain. Independently sending
every constant to zero is one possibility among these, and the wrong one
for most entries. -/
inductive Fate
  | toZero
  | toInfinity
  | remainsFinite
  | combinesIntoInvariant
  | integratedOut
  | confined
  | unobservable
  | survivesEffective
  | undetermined
  deriving DecidableEq, Repr

/-- Fate established by the formalization so far. Expectations live in the
README; this table changes only when a Lean file decides a fate. -/
def currentFate : ParameterName → Fate
  | _ => .undetermined

/-- Fundamental dimensionful parameters of the parent family. `invC` replaces
`c`, so the nonrelativistic fibre is `invC.num = 0` rather than an infinite
velocity. Units are a later concern; no field here is dimensionless. The
Newtonian particle mass is absent on purpose: it is an output of the strong
and electromagnetic sectors, see `Reverse/Matter`. -/
structure FundamentalParameters where
  hbar : Scalar
  invC : Scalar
  gravitationalCoupling : Scalar
  compactificationRadius : Scalar
  cosmologicalConstant : Scalar

end Reverse.Parent
