import Reverse.Parent.QuantumKKFamily

/-!
PHYSICAL STAGE:
  Candidate residual internal geometry. The full internal space K_full of
  the parent also carries the weak-related structure; the working scenario
  is that after weak decoupling what remains is a five-dimensional residual
  geometry K₅ ∼ CP² × S¹, whose isometry algebra is su(3) ⊕ u(1). The datum
  below is that residual candidate, never the selected fundamental geometry.
MATHEMATICAL CONTENT:
  One named candidate datum. Its volume function is left as a parameter of
  the candidate because the normalisation of CP² and the circle radius are
  separate choices.
INPUT PARAMETERS:
  Compactification radius.
OUTPUT PARAMETERS:
  Isometry algebra `[su 3, u1]`, dimension 5.
PROVED HERE:
  Nothing.
ASSUMED HERE:
  Nothing. Recording a candidate claims neither dynamical selection of it
  nor that it is the parent's full internal geometry.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/KK/DimensionalReduction.lean`.

STATUS: definitions.
-/

namespace Reverse.Parent

/-- Candidate residual geometry K₅ ∼ CP² × S¹ at the algebra level:
dimension 5 and isometry algebra su(3) ⊕ u(1). It is what the weak
decoupling is expected to leave of the full internal space; whether the
global gauge group is SU(3) × U(1), a quotient, or something else is
undecided by this datum. -/
def candidateCP2xS1 (volume : Scalar → Scalar) : InternalGeometry where
  dimension := 5
  isometryAlgebra := [.su 3, .u1]
  volume := volume

end Reverse.Parent
