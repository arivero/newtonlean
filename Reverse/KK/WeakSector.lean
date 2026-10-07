import Reverse.KK.DimensionalReduction

/-!
PHYSICAL STAGE:
  Decoupling of the weak/Fermi sector before the low-energy matter sector is
  reached, leaving quantum gravity with su(3) ⊕ u(1) gauge structure and
  matter degrees of freedom.
MATHEMATICAL CONTENT:
  The candidate parameters whose suppression could achieve the decoupling,
  and the interface describing the residual sectors.
INPUT PARAMETERS:
  Weak gauge coupling, symmetry-breaking scale, Fermi coupling, mixing data,
  Yukawa data.
OUTPUT PARAMETERS:
  A colour sector with nonzero coupling and an electromagnetic sector with
  nonzero coupling; the list of weak parameters the decoupling suppresses.
PROVED HERE:
  Nothing.
ASSUMED HERE:
  Existence of the residual sectors with both couplings nonzero. Which weak
  parameter must be sent where is left as data of the decoupling.
  Neutron stability after beta decay is suppressed is a physical
  interpretation recorded here, never a theorem.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/Strong/Confinement.lean`.

STATUS: physical hypothesis.
-/

namespace Reverse.KK
open Reverse.Parent

/-- Candidate parameters whose suppression could decouple the weak sector.
The interface records which ones a given decoupling suppresses; it does not
decide the question. -/
inductive WeakParameter
  | gaugeCoupling
  | breakingScale
  | fermiCoupling
  | mixing
  | yukawa
  deriving DecidableEq, Repr

/-- Residual low-energy gauge content after weak decoupling. The colour
coupling stays nonzero because confinement needs it; the electromagnetic
coupling stays nonzero because atoms need it. -/
structure HasWeakDecoupling (S : FourDimensionalSector) where
  colour : GaugeSector
  electromagnetic : GaugeSector
  colour_factor : colour.factor = .su 3
  electromagnetic_factor : electromagnetic.factor = .u1
  colour_active : colour.coupling.num ≠ 0
  electromagnetic_active : electromagnetic.coupling.num ≠ 0
  suppressed : List WeakParameter

end Reverse.KK
