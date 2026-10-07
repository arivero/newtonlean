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
  separate choices. Fermions on K₅: CP² has no spin structure (its signature
  is 1, which Rokhlin's theorem excludes for a spin 4-manifold) and admits
  spin^c structures, so Dirac fermions on CP² × S¹ exist as fields charged
  under the u(1). When fermions are placed on the residual geometry, that
  is a stated hypothesis tying their existence to the electromagnetic
  factor.
INPUT PARAMETERS:
  Compactification radius.
OUTPUT PARAMETERS:
  Isometry algebra `[su 3, u1]`, dimension 5.
PROVED HERE:
  Nothing.
ASSUMED HERE:
  Nothing. Recording a candidate claims neither dynamical selection of it
  nor that it is the parent's full internal geometry. No fermion content is
  placed on K₅ yet; see the spin^c remark above.
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
undecided by this datum. Fermions on it need a spin^c structure, hence a
u(1) charge. -/
def candidateCP2xS1 (volume : Scalar → Scalar) : InternalGeometry where
  dimension := 5
  isometryAlgebra := [.su 3, .u1]
  volume := volume

end Reverse.Parent
