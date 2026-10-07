import Reverse.Parent.Parameters

/-!
PHYSICAL STAGE:
  The modern parent: a quantum family whose classical geometric action is
  D-dimensional Einstein gravity,
    S_D[g] = (c³ / 16π G_D) ∫ R_D(g) √|g| d^D X,
  with gauge structure to arise from the internal geometry. The family is
  taken below the cutoff M_D, the D-dimensional Planck scale fixed by G_D, ℏ
  and c; what completes it above M_D, a string or matrix root, is left open
  and never invoked. The quantum theory is denoted 𝒬_ℏ(S_D). A path-integral expression Z = ∫ 𝒟g e^{iS_D/ℏ}
  is orientation only; nothing below depends on its existence.
MATHEMATICAL CONTENT:
  Opaque carriers: a quantum theory as a pair of types, internal geometry as
  dimension, isometry algebra and volume function, and the family as a
  parameter type with its fundamental parameters and theory at each point.
INPUT PARAMETERS:
  `FundamentalParameters` at each point of `Params`.
OUTPUT PARAMETERS:
  Same; the internal isometry algebra and volume for the KK stage.
PROVED HERE:
  Nothing.
ASSUMED HERE:
  That a quantum theory exists at each parameter point, as an opaque carrier.
  No Hilbert space, operator algebra, dynamics or renormalization is modelled.
OPEN PROBLEMS USED:
  Completion of gravity above the cutoff M_D, in the weak sense that the
  carrier below M_D is assumed to exist; no property of the completion is
  used.
NEXT REDUCTION:
  `Reverse/KK/DimensionalReduction.lean`.

STATUS: physical hypothesis (existence of the family), encoded as carriers.
-/

namespace Reverse.Parent

/-- Opaque quantum theory: observables and states as carriers. No algebra,
no expectation pairing and no path integral are modelled at this stage. -/
structure QuantumTheory where
  Observable : Type
  State : Type

/-- Internal geometry at the level the KK stage needs: its dimension, its
isometry algebra listed by factor, and its volume as a function of the
compactification radius. Global group structure is absent on purpose. -/
structure InternalGeometry where
  dimension : Nat
  isometryAlgebra : List GaugeFactor
  volume : Scalar → Scalar

/-- Label for the classical geometric action of the parent. PLACEHOLDER: a
name only, with no formal content until the action and its reduction are
formalized. It records the intended Einstein–Hilbert starting point so that
the KK stage's identities can later be derived from it. -/
inductive ClassicalAction
  | einsteinHilbert
  | einsteinHilbertWithCosmologicalConstant
  deriving DecidableEq, Repr

/-- A quantum family over D = 4 + internal dimensions. The parameter type is
abstract; the fundamental parameters and the theory are read off at each
point. `internal` is the full internal geometry of the parent, before any
weak-related structure is decoupled. No point is marked as Newtonian. -/
structure QuantumKKFamily where
  Params : Type
  fundamental : Params → FundamentalParameters
  internal : InternalGeometry
  classicalAction : ClassicalAction
  theory : Params → QuantumTheory

/-- The parent's classical action is Einstein–Hilbert, with or without a
cosmological term. A label, see `ClassicalAction`. -/
def HasEinsteinHilbertAction (F : QuantumKKFamily) : Prop :=
  F.classicalAction = .einsteinHilbert ∨
    F.classicalAction = .einsteinHilbertWithCosmologicalConstant

/-- Total spacetime dimension D. -/
def QuantumKKFamily.dimension (F : QuantumKKFamily) : Nat :=
  4 + F.internal.dimension

end Reverse.Parent
