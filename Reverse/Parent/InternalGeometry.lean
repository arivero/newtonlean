import Reverse.Parent.QuantumKKFamily

/-!
PHYSICAL STAGE:
  Candidate internal geometries. The working scenario permits a
  five-dimensional internal space of the type K₅ ∼ CP² × S¹, whose isometry
  algebra is su(3) ⊕ u(1).
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
  Nothing. Recording a candidate claims no dynamical selection of it.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/KK/DimensionalReduction.lean`.

STATUS: definitions.
-/

namespace Reverse.Parent

/-- K₅ ∼ CP² × S¹ at the algebra level: dimension 5 and isometry algebra
su(3) ⊕ u(1). Whether the global gauge group is SU(3) × U(1), a quotient, or
something else is undecided by this datum. -/
def candidateCP2xS1 (volume : Scalar → Scalar) : InternalGeometry where
  dimension := 5
  isometryAlgebra := [.su 3, .u1]
  volume := volume

end Reverse.Parent
