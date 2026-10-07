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
  The residual factors descend from the internal isometry algebra, given
  the KK identity.
ASSUMED HERE:
  Existence of the residual sectors inside the reduced gauge content, with
  both couplings nonzero. Which weak parameter must be sent where is left as
  data of the decoupling. The electroweak compactification itself, the
  mechanism that removes the weak-related internal structure, is outside
  this pass.
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

/-- Residual low-energy gauge content after weak decoupling. Both residual
factors are members of the reduced gauge algebra produced by the KK stage,
and both residual spectra map into the states of the reduced theory, so no
unrelated su(3) or u(1) can be introduced here. The colour coupling stays
nonzero because confinement needs it; the electromagnetic coupling stays
nonzero because atoms need it. The maps into the reduced state space record
the parent relation only; injectivity and the subsector structure are not
claimed. -/
structure HasWeakDecoupling (S : FourDimensionalSector) where
  colour : GaugeSector
  electromagnetic : GaugeSector
  colour_factor : colour.factor = .su 3
  electromagnetic_factor : electromagnetic.factor = .u1
  colour_in_reduced : colour.factor ∈ S.gaugeAlgebra
  electromagnetic_in_reduced : electromagnetic.factor ∈ S.gaugeAlgebra
  colour_states : colour.Spectrum → S.theory.State
  electromagnetic_states : electromagnetic.Spectrum → S.theory.State
  colour_active : colour.coupling.num ≠ 0
  electromagnetic_active : electromagnetic.coupling.num ≠ 0
  suppressed : List WeakParameter

/-- The residual factors come from the internal isometries: a formal
consequence of the KK identity and the membership fields. -/
theorem HasWeakDecoupling.colour_from_isometries {F : QuantumKKFamily}
    (hKK : HasKKReduction F) (a : F.Params) (W : HasWeakDecoupling (hKK.reduce a)) :
    W.colour.factor ∈ F.internal.isometryAlgebra :=
  hKK.gauge_from_isometries a ▸ W.colour_in_reduced

theorem HasWeakDecoupling.electromagnetic_from_isometries {F : QuantumKKFamily}
    (hKK : HasKKReduction F) (a : F.Params) (W : HasWeakDecoupling (hKK.reduce a)) :
    W.electromagnetic.factor ∈ F.internal.isometryAlgebra :=
  hKK.gauge_from_isometries a ▸ W.electromagnetic_in_reduced

end Reverse.KK
